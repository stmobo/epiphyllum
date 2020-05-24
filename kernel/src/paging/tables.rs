use core::ops::{Index, IndexMut};

use crate::asm;
use crate::malloc::{physical_mem, AllocationError, PhysicalMemory};

use super::{pd_idx, pdp_idx, pml4_idx, pt_idx};
use super::{PageStructure, PageTableEntry, PhysicalPointer};
use super::{HIGHER_HALF_PML4_IDX, KERNEL_HEAP_PML4_IDX, PAGE_MASK, PHYSICAL_MAP_PML4_IDX};

const PML4T_RECURSIVE_BASE: usize = 0xFFFF_FFFF_FFFF_F000;
const PDPT_RECURSIVE_BASE: usize = 0xFFFF_FFFF_FFE0_0000;
const PD_RECURSIVE_BASE: usize = 0xFFFF_FFFF_C000_0000;
const PT_RECURSIVE_BASE: usize = 0xFFFF_FF80_0000_0000;

#[repr(transparent)]
pub struct PageTable {
    entries: [PageTableEntry; 512],
}

impl PageTable {
    pub fn new() -> Result<PhysicalPointer<PageTable>, AllocationError> {
        let page = PhysicalMemory::new(0)?.into_address();
        let mut ptr: PhysicalPointer<PageTable> =
            PhysicalPointer::new(page).ok_or(AllocationError::InvalidAllocation)?;

        let m = unsafe { ptr.as_mut() };
        for i in 0usize..512 {
            m.clear_entry(i).unwrap();
        }

        Ok(ptr)
    }

    pub fn map_addr(&mut self, index: usize, phys_addr: usize) -> Result<(), usize> {
        let mut entry = self.get_entry(index)?;

        entry.set_physical_address(phys_addr);
        entry.set_present(true);

        self.set_entry(index, entry)
    }

    pub fn unmap_entry(&mut self, index: usize) -> Result<PageTableEntry, usize> {
        let mut entry = self.get_entry(index)?;
        entry.set_present(false);
        self.set_entry(index, entry)?;
        Ok(entry)
    }

    pub fn get_entry(&self, index: usize) -> Result<PageTableEntry, usize> {
        if index >= 512 {
            return Err(index);
        }

        unsafe { Ok(self.table_ptr().add(index).read_volatile()) }
    }

    pub fn set_entry(&mut self, index: usize, entry: PageTableEntry) -> Result<(), usize> {
        if index >= 512 {
            return Err(index);
        }

        unsafe {
            self.table_mut_ptr().add(index).write_volatile(entry);
        }

        Ok(())
    }

    pub fn clear_entry(&mut self, index: usize) -> Result<(), usize> {
        self.set_entry(index, PageTableEntry::new())
    }

    pub fn table_addr(&self) -> usize {
        self.entries.as_ptr() as usize
    }

    pub fn table_mut_ptr(&mut self) -> *mut PageTableEntry {
        self.entries.as_mut_ptr()
    }

    pub fn table_ptr(&self) -> *const PageTableEntry {
        self.entries.as_ptr()
    }

    pub fn clear(&mut self) {
        let p = self.table_mut_ptr();
        for i in 0..512 {
            unsafe { p.add(i).write_volatile(PageTableEntry::new()) };
        }
    }

    /// Get a reference to the recursively-mapped PML4T.
    pub fn get_pml4t() -> &'static mut PageTable {
        unsafe {
            let pml4t = PML4T_RECURSIVE_BASE as *mut PageTable;
            &mut *pml4t
        }
    }

    /// Get a reference to a recursively-mapped PD Pointer Table.
    pub unsafe fn get_pdpt(pdp_idx: usize) -> &'static mut PageTable {
        let pdp_addr = PDPT_RECURSIVE_BASE + (0x1000 * pdp_idx);
        &mut *(pdp_addr as *mut PageTable)
    }

    /// Get a reference to a recursively-mapped Page Directory.
    pub unsafe fn get_pd(pdp_idx: usize, pd_idx: usize) -> &'static mut PageTable {
        let pd_addr = PD_RECURSIVE_BASE + (0x20_0000 * pdp_idx) + (0x1000 * pd_idx);
        &mut *(pd_addr as *mut PageTable)
    }

    /// Get a reference to a recursively-mapped Page Table.
    pub unsafe fn get_pt(pdp_idx: usize, pd_idx: usize, pt_idx: usize) -> &'static mut PageTable {
        let pt_addr =
            PT_RECURSIVE_BASE + (0x4000_0000 * pdp_idx) + (0x20_0000 * pd_idx) + (0x1000 * pt_idx);
        &mut *(pt_addr as *mut PageTable)
    }

    pub fn iter(&self) -> impl Iterator<Item = &PageTableEntry> {
        self.entries.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut PageTableEntry> {
        self.entries.iter_mut()
    }
}

impl Index<usize> for PageTable {
    type Output = PageTableEntry;

    fn index(&self, index: usize) -> &Self::Output {
        &self.entries[index]
    }
}

impl IndexMut<usize> for PageTable {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.entries[index]
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub enum PageLevel {
    PML4,
    PDP,
    PD,
    PT,
}

impl PageLevel {
    pub fn page_alignment(self) -> Option<usize> {
        match self {
            PageLevel::PDP => Some(1 << 30),
            PageLevel::PD => Some(1 << 21),
            PageLevel::PT => Some(1 << 12),
            PageLevel::PML4 => None,
        }
    }

    pub fn alignment_mask(self) -> Option<usize> {
        self.page_alignment().map(|a| a - 1)
    }

    pub fn is_aligned(self, address: usize) -> bool {
        (address & self.alignment_mask().unwrap()) == 0
    }

    pub fn child_level(self) -> Option<PageLevel> {
        match self {
            PageLevel::PML4 => Some(PageLevel::PDP),
            PageLevel::PDP => Some(PageLevel::PD),
            PageLevel::PD => Some(PageLevel::PT),
            PageLevel::PT => None,
        }
    }

    pub fn parent_level(self) -> Option<PageLevel> {
        match self {
            PageLevel::PML4 => None,
            PageLevel::PDP => Some(PageLevel::PML4),
            PageLevel::PD => Some(PageLevel::PDP),
            PageLevel::PT => Some(PageLevel::PD),
        }
    }

    pub fn address_offset(self, vaddr: usize) -> usize {
        match self {
            PageLevel::PML4 => pml4_idx(vaddr),
            PageLevel::PDP => pdp_idx(vaddr),
            PageLevel::PD => pd_idx(vaddr),
            PageLevel::PT => pt_idx(vaddr),
        }
    }
}

/// Maps a 4K page into the current virtual address space directly, using the
/// recursive page table mappings.
pub unsafe fn direct_map_virtual_address(virt_addr: usize, phys_addr: usize) -> bool {
    let pml4t_idx = pml4_idx(virt_addr);
    let pdpt_idx = pdp_idx(virt_addr);
    let pd_idx = pd_idx(virt_addr);
    let pt_offset = pt_idx(virt_addr);

    let pml4t = PageTable::get_pml4t();
    let mut tlb_reload_required = false;

    let pdpt;
    if !pml4t.get_entry(pml4t_idx).unwrap().present() {
        let table_addr = physical_mem::allocate(0);
        if table_addr.is_err() {
            return false;
        }

        pml4t
            .map_addr(pml4t_idx, table_addr.unwrap())
            .expect("failed to map PDPT");

        pdpt = PageTable::get_pdpt(pml4t_idx);
        asm::invlpg((pdpt as *mut PageTable) as usize);

        pdpt.clear();

        tlb_reload_required = true;
    } else {
        pdpt = PageTable::get_pdpt(pml4t_idx);
    }

    let pd;
    if !pdpt.get_entry(pdpt_idx).unwrap().present() {
        let table_addr = physical_mem::allocate(0);
        if table_addr.is_err() {
            return false;
        }

        pdpt.map_addr(pdpt_idx, table_addr.unwrap())
            .expect("failed to map PD");

        pd = PageTable::get_pd(pml4t_idx, pdpt_idx);
        asm::invlpg((pd as *mut PageTable) as usize);

        pd.clear();

        tlb_reload_required = true;
    } else {
        pd = PageTable::get_pd(pml4t_idx, pdpt_idx);
    }

    let pt: &'static mut PageTable;
    if !pd.get_entry(pd_idx).unwrap().present() {
        let table_addr = physical_mem::allocate(0);
        if table_addr.is_err() {
            return false;
        }

        pd.map_addr(pd_idx, table_addr.unwrap())
            .expect("failed to map PT");

        pt = PageTable::get_pt(pml4t_idx, pdpt_idx, pd_idx);
        asm::invlpg((pt as *mut PageTable) as usize);

        pt.clear();

        tlb_reload_required = true;
    } else {
        pt = PageTable::get_pt(pml4t_idx, pdpt_idx, pd_idx);
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
        asm::reload_cr3();
    } else {
        asm::invlpg(virt_addr);
    }

    true
}

/// Unmaps a 4K page from the current virtual address space directly, using the
/// recursive page table mappings.
pub unsafe fn direct_unmap_virtual_address(virt_addr: usize) {
    let virt_addr = virt_addr & PAGE_MASK;
    let pml4_idx = pml4_idx(virt_addr);
    let pdp_idx = pdp_idx(virt_addr);
    let pd_idx = pd_idx(virt_addr);
    let pt_idx = pt_idx(virt_addr);

    let pml4t = PageTable::get_pml4t();
    if pml4t.get_entry(pml4_idx).unwrap().present() {
        let pdpt = PageTable::get_pdpt(pml4_idx);
        let pdpe = pdpt.get_entry(pdp_idx).unwrap();

        if pdpe.present() && !pdpe.page_size() {
            let pd = PageTable::get_pd(pml4_idx, pdp_idx);
            let pde = pd.get_entry(pd_idx).unwrap();

            if pde.present() && !pde.page_size() {
                let pt = PageTable::get_pt(pml4_idx, pdp_idx, pd_idx);
                pt.clear_entry(pt_idx).expect("failed to unmap page");
                asm::invlpg(virt_addr);
            }
        }
    }
}

pub unsafe fn direct_get_mapping(virt_addr: usize) -> Option<PageTableEntry> {
    let virt_addr = virt_addr & PAGE_MASK;

    let pml4_idx = pml4_idx(virt_addr);
    let pdp_idx = pdp_idx(virt_addr);
    let pd_idx = pd_idx(virt_addr);
    let pt_idx = pt_idx(virt_addr);

    let pml4t = PageTable::get_pml4t();
    if pml4t.get_entry(pml4_idx).unwrap().present() {
        let pdpt = PageTable::get_pdpt(pml4_idx);

        if pdpt.get_entry(pdp_idx).unwrap().present() {
            let pd = PageTable::get_pd(pml4_idx, pdp_idx);

            if pd.get_entry(pd_idx).unwrap().present() {
                let pt = PageTable::get_pt(pml4_idx, pdp_idx, pd_idx);

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

    asm::reload_cr3();
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
            physical_mem::allocate_at(ent.physical_address(), 0);
            let pdpt = PageTable::get_pdpt(pml4_idx);

            for (pdpt_idx, ent) in pdpt.iter().enumerate().filter(|e| e.1.present()) {
                physical_mem::allocate_at(ent.physical_address(), 0);
                let pd = PageTable::get_pd(pml4_idx, pdpt_idx);

                for (pd_idx, ent) in pd.iter().enumerate().filter(|e| e.1.present()) {
                    physical_mem::allocate_at(ent.physical_address(), 0);
                    let pt = PageTable::get_pt(pml4_idx, pdpt_idx, pd_idx);

                    for ent in pt.iter().filter(|e| e.present()) {
                        physical_mem::allocate_at(ent.physical_address(), 0);
                    }
                }
            }
        }

        // reserve the bootstrap PML4T itself as well
        let cr3 = asm::get_cr3();
        physical_mem::allocate_at(cr3.address(), 0);

        // ensure the zero page is not allocated
        physical_mem::allocate_at(0, 0);
    }
}
