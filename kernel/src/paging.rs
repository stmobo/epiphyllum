use core::convert::{TryFrom, TryInto};
use core::ptr::NonNull;
use x86_64::instructions::tlb;
use x86_64::VirtAddr;

use crate::asm;
use crate::asm::cpuid::FeatureFlags;
use crate::malloc::{physical_mem, AllocationError, PhysicalMemory, VirtualMemory};
use crate::multiboot::MultibootInfo;

mod index;
mod structs;
mod tables;

pub use index::PageHierarchyIndex;
pub use structs::PageData;
pub use tables::{PageTable, PageTableEntry};

pub const PAGE_MASK: usize = 0xFFFF_FFFF_FFFF_F000;

pub const KERNEL_STACK_BASE: usize = 0xFFFF_FF00_0000_0000;
pub const KERNEL_BASE: usize = 0xFFFF_C400_0000_0000;
pub const KERNEL_HEAP_BASE: usize = 0xFFFF_C080_0000_0000;
pub const PHYSICAL_MAP_BASE: usize = 0xFFFF_8100_0000_0000;
pub const HIGHER_HALF_START: usize = 0xFFFF_8000_0000_0000;

// const MAX_PHYSICAL_MEMORY: usize = KERNEL_HEAP_BASE - PHYSICAL_MAP_BASE;

// const KERNEL_STACK_PML4_IDX: usize = 0b111_111_110;
const KERNEL_BASE_PML4_IDX: usize = 0b110_001_000;
const KERNEL_HEAP_PML4_IDX: usize = 0b110_000_001;
const PHYSICAL_MAP_PML4_IDX: usize = 0b100_000_010;
const HIGHER_HALF_PML4_IDX: usize = 0b100_000_000;

pub fn is_page_aligned<T: Into<usize>>(value: T) -> bool {
    let v: usize = value.into();
    v & (!PAGE_MASK) == 0
}

pub fn round_to_next_page<T: Into<usize>>(value: T) -> usize {
    let v: usize = value.into();
    if v & (!PAGE_MASK) != 0 {
        (v & PAGE_MASK) + 0x1000
    } else {
        v
    }
}

pub fn round_to_prev_page<T: Into<usize>>(value: T) -> usize {
    let v: usize = value.into();
    v & PAGE_MASK
}

pub fn init_paging_metadata<'a>(mb: &'a MultibootInfo) {
    structs::initialize(mb);
}

#[derive(Debug, Clone)]
pub struct PageTableMetadata {
    ref_count: u16,
}

pub fn map_virtual_address(virt_addr: usize, phys_addr: usize) -> bool {
    let table_index = PageHierarchyIndex::from_vaddr(virt_addr);
    let pml4t_idx = table_index.pml4t_index().unwrap();
    let pdpt_idx = table_index.pdpt_index().unwrap();
    let pd_idx = table_index.pd_index().unwrap();
    let pt_offset = (virt_addr >> 12) & 0x1FF;

    let pml4t = PageTable::get_pml4t();
    let mut tlb_reload_required = false;

    let pdpt;
    if !pml4t.get_entry(pml4t_idx).unwrap().present() {
        let table_addr = physical_mem::allocate(0x1000);
        if table_addr.is_err() {
            return false;
        }

        pml4t
            .map_addr(pml4t_idx, table_addr.unwrap())
            .expect("failed to map PDPT");

        pdpt = unsafe { PageTable::get_pdpt(pml4t_idx) };
        tlb::flush(VirtAddr::new(((pdpt as *mut PageTable) as usize) as u64));

        pdpt.clear();

        tlb_reload_required = true;
    } else {
        pdpt = unsafe { PageTable::get_pdpt(pml4t_idx) };
    }

    let pd;
    if !pdpt.get_entry(pdpt_idx).unwrap().present() {
        let table_addr = physical_mem::allocate(0x1000);
        if table_addr.is_err() {
            return false;
        }

        pdpt.map_addr(pdpt_idx, table_addr.unwrap())
            .expect("failed to map PD");

        pd = unsafe { PageTable::get_pd(pml4t_idx, pdpt_idx) };
        tlb::flush(VirtAddr::new(((pd as *mut PageTable) as usize) as u64));

        pd.clear();

        tlb_reload_required = true;
    } else {
        pd = unsafe { PageTable::get_pd(pml4t_idx, pdpt_idx) };
    }

    let pt: &'static mut PageTable;
    if !pd.get_entry(pd_idx).unwrap().present() {
        let table_addr = physical_mem::allocate(0x1000);
        if table_addr.is_err() {
            return false;
        }

        pd.map_addr(pd_idx, table_addr.unwrap())
            .expect("failed to map PT");

        pt = unsafe { PageTable::get_pt(pml4t_idx, pdpt_idx, pd_idx) };
        tlb::flush(VirtAddr::new(((pt as *mut PageTable) as usize) as u64));

        pt.clear();

        tlb_reload_required = true;
    } else {
        pt = unsafe { PageTable::get_pt(pml4t_idx, pdpt_idx, pd_idx) };
    }

    let entry = pt.get_entry(pt_offset).unwrap();
    if entry.physical_address() == phys_addr {
        pt.map_addr(pt_offset, phys_addr)
            .expect("failed to map page");
        return true;
    }

    pt.map_addr(pt_offset, phys_addr)
        .expect("failed to map page");

    if tlb_reload_required {
        tlb::flush_all();
    } else {
        tlb::flush(VirtAddr::new(virt_addr as u64));
    }

    return true;
}

pub fn unmap_virtual_address(virt_addr: usize) {
    let table_index = PageHierarchyIndex::from_vaddr(virt_addr);
    if let Some(table) = table_index.get_table() {
        let pt_offset = (virt_addr >> 12) & 0x1FF;
        table.unmap_entry(pt_offset).expect("failed to unmap page");

        tlb::flush(VirtAddr::new(virt_addr as u64));
    }
}

pub fn get_mapping(virt_addr: usize) -> Option<PageTableEntry> {
    let virt_addr = virt_addr & PAGE_MASK;

    let pml4_idx: usize = (virt_addr >> 39) & 0x1FF;
    let pdp_idx: usize = (virt_addr >> 30) & 0x1FF;
    let pd_idx: usize = (virt_addr >> 21) & 0x1FF;
    let pt_idx: usize = (virt_addr >> 12) & 0x1FF;

    let pml4t = PageTable::get_pml4t();
    if pml4t.get_entry(pml4_idx).unwrap().present() {
        let pdpt = unsafe { PageTable::get_pdpt(pml4_idx) };

        if pdpt.get_entry(pdp_idx).unwrap().present() {
            let pd = unsafe { PageTable::get_pd(pml4_idx, pdp_idx) };

            if pd.get_entry(pd_idx).unwrap().present() {
                let pt = unsafe { PageTable::get_pt(pml4_idx, pdp_idx, pd_idx) };

                return pt.get_entry(pt_idx).ok();
            }
        }
    }

    None
}

pub fn remap_boot_identity_paging() {
    let n_remapped_pdpts = KERNEL_HEAP_PML4_IDX - PHYSICAL_MAP_PML4_IDX;
    let pml4t = PageTable::get_pml4t();

    /* Remap as many PDPTs pointing to the lower half of the address
     * space into the higher half as we can.
     * This is going to get cleaned up later when we set up the 'real' physical
     * mappings, anyways.
     */
    for i in 0..n_remapped_pdpts {
        let from_ent = pml4t.get_entry(i).unwrap();

        if from_ent.present() {
            pml4t
                .set_entry(i + PHYSICAL_MAP_PML4_IDX, from_ent)
                .expect("failed to copy PML4T mapping");

            pml4t.unmap_entry(i).expect("failed to unmap old entry");
        }
    }

    tlb::flush_all();
}

#[allow(unused_must_use)]
pub fn reserve_bootstrap_physical_pages() {
    unsafe {
        let pml4t = PageTable::get_pml4t();
        for (pml4_idx, ent) in pml4t
            .iter()
            .enumerate()
            .skip(HIGHER_HALF_PML4_IDX - 1)
            .filter(|p| p.1.present())
        {
            physical_mem::allocate_at(ent.physical_address(), 0x1000);
            let pdpt = PageTable::get_pdpt(pml4_idx);

            for (pdpt_idx, ent) in pdpt.iter().enumerate().filter(|e| e.1.present()) {
                physical_mem::allocate_at(ent.physical_address(), 0x1000);
                let pd = PageTable::get_pd(pml4_idx, pdpt_idx);

                for (pd_idx, ent) in pd.iter().enumerate().filter(|e| e.1.present()) {
                    physical_mem::allocate_at(ent.physical_address(), 0x1000);
                    let pt = PageTable::get_pt(pml4_idx, pdpt_idx, pd_idx);

                    for ent in pt.iter().filter(|e| e.present()) {
                        physical_mem::allocate_at(ent.physical_address(), 0x1000);
                    }
                }
            }
        }
    }
}

fn init_physical_map_gb_pages(window: VirtualMemory) -> Result<usize, AllocationError> {
    let pdpt = PhysicalMemory::new(0x1000)?;

    if !map_virtual_address(window.address(), pdpt.address()) {
        return Err(AllocationError::CouldNotMapAddress);
    }

    let table = window.address() as *mut PageTable;

    for i in 0..512usize {
        let phys_addr = i << 30;
        unsafe {
            let mut pte = PageTableEntry::new();
            pte.set_physical_address(phys_addr);
            pte.set_present(true);
            pte.set_page_size(true);
            (*table).set_entry(i, pte).unwrap();
        }
    }

    unmap_virtual_address(window.address());

    Ok(pdpt.into_address())
}

fn init_physical_map_mb_pages(window: VirtualMemory) -> Result<usize, AllocationError> {
    let pdpt = PhysicalMemory::new(0x1000)?;

    // allocate page directories in chunks of 128 pages (= 0.5 MiB)
    let table = window.address() as *mut PageTable;
    let mut chunk_addrs: [usize; 4] = [0, 0, 0, 0];

    // create mappings within each page directory
    for chunk in 0..4 {
        let block = PhysicalMemory::new(128 * 0x1000)?;
        let block_addr = block.address();

        for chunk_page in 0..128usize {
            let pdp_no = (chunk * 128) + chunk_page;
            let pd_addr = block_addr + (chunk_page * 0x1000);

            if !map_virtual_address(window.address(), pd_addr) {
                for addr in chunk_addrs.iter() {
                    let addr = *addr;
                    if addr != 0 {
                        unsafe {
                            physical_mem::deallocate(addr, 128 * 0x1000);
                        }
                    }
                }
                return Err(AllocationError::CouldNotMapAddress);
            }

            for pd_offset in 0..512usize {
                let phys_addr = (pdp_no << 30) | (pd_offset << 21);
                unsafe {
                    let mut pte = PageTableEntry::new();
                    pte.set_physical_address(phys_addr);
                    pte.set_present(true);
                    pte.set_page_size(true);

                    (*table).set_entry(pd_offset, pte).unwrap();
                }
            }
        }

        chunk_addrs[chunk] = block.into_address();
    }

    // create mappings within the PDPT
    if !map_virtual_address(window.address(), pdpt.address()) {
        return Err(AllocationError::CouldNotMapAddress);
    }

    for pdp_no in 0..512usize {
        let chunk = pdp_no / 128;
        let chunk_page = pdp_no % 128;
        let pd_addr = chunk_addrs[chunk] + (chunk_page * 0x1000);

        unsafe {
            (*table)
                .map_addr(pdp_no, pd_addr)
                .map_err(|_| AllocationError::CouldNotMapAddress)?;
        }
    }

    unmap_virtual_address(window.address());
    Ok(pdpt.into_address())
}

pub fn initialize_direct_physical_mappings() -> Result<(), AllocationError> {
    let window = VirtualMemory::new(0x1000)?;

    let pdpt = if FeatureFlags::GB_PAGES.supported() {
        println!("paging: CPU supports GB pages");
        init_physical_map_gb_pages(window)?
    } else {
        println!("paging: CPU does not support GB pages");
        init_physical_map_mb_pages(window)?
    };

    // swap in the mappings
    let pml4t = PageTable::get_pml4t();
    let old_pdpt = pml4t.get_entry(PHYSICAL_MAP_PML4_IDX).unwrap();
    pml4t
        .map_addr(PHYSICAL_MAP_PML4_IDX, pdpt)
        .map_err(|_| AllocationError::CouldNotMapAddress)?;
    asm::reload_cr3();

    // clean up old physical mappings
    unsafe {
        let pdpt_addr = old_pdpt.physical_address();
        let old_pdpt: *mut PageTable = old_pdpt.page().unwrap().as_mut_ptr() as *mut PageTable;

        for pdpt_idx in 0..512usize {
            let pdpe = (*old_pdpt).get_entry(pdpt_idx).unwrap();
            if !pdpe.present() {
                continue;
            }

            let pd = pdpe.page().unwrap().as_mut_ptr() as *mut PageTable;
            for pd_idx in 0..512usize {
                let pde = (*pd).get_entry(pd_idx).unwrap();
                if !pde.present() {
                    continue;
                }

                let pt_addr = pde.physical_address();
                physical_mem::deallocate(pt_addr, 0x1000);
            }

            let pd_addr = pdpe.physical_address();
            physical_mem::deallocate(pd_addr, 0x1000);
        }

        physical_mem::deallocate(pdpt_addr, 0x1000);
    }

    Ok(())
}

pub fn offset_direct_map<T: TryInto<usize>>(phys_addr: T) -> usize {
    if let Ok(offset) = phys_addr.try_into() {
        PHYSICAL_MAP_BASE + offset
    } else {
        panic!("could not convert offset into usize");
    }
}

pub fn direct_map_pointer<T>(ptr: *const T) -> *const T {
    offset_direct_map(ptr as usize) as *const T
}

pub fn direct_map_pointer_mut<T>(ptr: *mut T) -> *mut T {
    offset_direct_map(ptr as usize) as *mut T
}

#[repr(transparent)]
#[derive(Debug, Ord, PartialOrd, Eq, PartialEq)]
pub struct PhysicalPointer<T>(NonNull<T>);

impl<T> PhysicalPointer<T> {
    pub fn new(addr: usize) -> Option<PhysicalPointer<T>> {
        Some(PhysicalPointer(NonNull::new(addr as *mut T)?))
    }

    pub unsafe fn new_unchecked(addr: usize) -> PhysicalPointer<T> {
        PhysicalPointer(NonNull::new_unchecked(addr as *mut T))
    }

    pub fn address(self) -> usize {
        self.0.as_ptr() as usize
    }

    pub fn virtual_address(self) -> usize {
        PHYSICAL_MAP_BASE + self.address()
    }

    pub fn as_ptr(self) -> *const T {
        self.virtual_address() as *const T
    }

    pub fn as_mut_ptr(self) -> *mut T {
        self.virtual_address() as *mut T
    }

    pub unsafe fn as_ref(&self) -> &T {
        &*(self.0.as_ptr() as *const T)
    }

    pub unsafe fn as_mut(&mut self) -> &mut T {
        &mut *(self.0.as_ptr() as *mut T)
    }
}

impl<T> Clone for PhysicalPointer<T> {
    fn clone(&self) -> Self {
        PhysicalPointer(self.0.clone())
    }
}

impl<T> Copy for PhysicalPointer<T> {}

impl<T> From<PhysicalMemory> for PhysicalPointer<T> {
    fn from(mem_block: PhysicalMemory) -> Self {
        unsafe { Self::new_unchecked(mem_block.into_address()) }
    }
}

impl<T> TryFrom<PageTableEntry> for PhysicalPointer<T> {
    type Error = PageTableEntry;

    fn try_from(value: PageTableEntry) -> Result<Self, PageTableEntry> {
        if !value.present() {
            return Err(value);
        }

        PhysicalPointer::new(value.physical_address()).ok_or(value)
    }
}

impl<T> TryFrom<usize> for PhysicalPointer<T> {
    type Error = usize;

    fn try_from(value: usize) -> Result<Self, usize> {
        PhysicalPointer::new(value).ok_or(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::malloc::{physical_mem, AllocationError, PhysicalMemory, VirtualMemory};
    use core::ptr;
    use kernel_test_macro::kernel_test;

    #[kernel_test]
    fn test_physical_mapping() {
        let phys = PhysicalMemory::new(0x1000).unwrap();
        let virt = VirtualMemory::new(0x1000).unwrap();

        if !map_virtual_address(virt.address(), phys.address()) {
            panic!(
                "could not map virtual address {:#018x} => {:#018x}",
                virt.address(),
                phys.address()
            );
        }

        let p: PhysicalPointer<u64> = phys.address().try_into().unwrap();
        let virt_p = p.as_mut_ptr();
        unsafe {
            ptr::write_volatile(virt_p, 0xA5A5DEADC0DEA5A5);
            drop(virt_p);
        }

        let mapped_p = virt.address() as *const u64;
        unsafe {
            assert_eq!(
                ptr::read_volatile(mapped_p),
                0xA5A5DEADC0DEA5A5,
                "read differing values from virtual addresses {:#018x} and {:#018x}",
                virt.address(),
                p.virtual_address()
            );
        };

        unmap_virtual_address(virt.address());
    }
}
