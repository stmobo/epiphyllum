use core::convert::{TryFrom, TryInto};
use core::mem;
use core::ptr::NonNull;

use crate::asm;
use crate::asm::cpuid::FeatureFlags;
use crate::malloc::{physical_mem, PhysicalMemory, VirtualMemory};
use crate::multiboot::MultibootInfo;
use crate::task;

mod address_space;
mod direct;
mod entry;
mod structs;
mod table;

pub use address_space::{AddressSpace, MappingError};
pub use direct::*;
pub use structs::*;
pub use table::*;

pub use entry::PageTableEntry;

pub const PAGE_MASK: usize = 0xFFFF_FFFF_FFFF_F000;

/// The topmost (minimum) address of the bootstrap kernel stack.
pub const KERNEL_STACK_BASE: usize = 0xFFFF_FF00_0000_0000;

/// The kernel image base address.
pub const KERNEL_BASE: usize = 0xFFFF_C400_0000_0000;

/// The kernel heap base address.
pub const KERNEL_HEAP_BASE: usize = 0xFFFF_C080_0000_0000;

/// The direct physical map base address.
pub const PHYSICAL_MAP_BASE: usize = 0xFFFF_8100_0000_0000;

/// The lowest address in the higher half.
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

pub const fn pt_idx(vaddr: usize) -> usize {
    (vaddr >> 12) & 0x1FF
}

pub const fn pd_idx(vaddr: usize) -> usize {
    (vaddr >> 21) & 0x1FF
}

pub const fn pdp_idx(vaddr: usize) -> usize {
    (vaddr >> 30) & 0x1FF
}

pub const fn pml4_idx(vaddr: usize) -> usize {
    (vaddr >> 39) & 0x1FF
}

pub fn init_paging_metadata<'a>(mb: &'a MultibootInfo) {
    structs::initialize(mb);
}

pub fn get_page_mapping(vaddr: usize) -> Option<(PageLevel, PageTableEntry)> {
    if task::scheduler_initialized() {
        let space = task::current_address_space();
        space.get_mapping(vaddr)
    } else {
        let space = unsafe { AddressSpace::current() };
        space.get_mapping(vaddr)
    }
}

pub fn map_pages(vaddr: usize, paddr: usize, n_pages: usize) {
    if task::scheduler_initialized() {
        let mut space = task::current_address_space();
        space.map_page_range(vaddr, paddr, n_pages)
    } else {
        let mut space = unsafe { AddressSpace::current() };
        space.map_page_range(vaddr, paddr, n_pages)
    }
}

pub fn unmap_pages(vaddr: usize, n_pages: usize) -> Result<(), PageLevel> {
    if task::scheduler_initialized() {
        let mut space = task::current_address_space();
        space.unmap_page_range(vaddr, n_pages)
    } else {
        let mut space = unsafe { AddressSpace::current() };
        space.unmap_page_range(vaddr, n_pages)
    }
}

fn init_physical_map_gb_pages(window: VirtualMemory) -> PDPT {
    let pdpt_addr = PhysicalMemory::new(0)
        .expect("could not allocate physical memory")
        .into_address();
    let table = window.address() as *mut PageTableEntry;

    unsafe {
        if !direct_map_virtual_address(window.address(), pdpt_addr) {
            panic!("could not map virtual address");
        }

        for i in 0..512usize {
            let mut pte = PageTableEntry::from_address(i << 30);
            pte.set_page_size(true);
            table.add(i).write_volatile(pte);
        }

        direct_unmap_virtual_address(window.address());

        let ptr: PhysicalPointer<PageTableEntry> = PhysicalPointer::new_unchecked(pdpt_addr);
        let pdpt: PDPT = mem::transmute(ptr);
        pdpt
    }
}

fn init_physical_map_mb_pages(window: VirtualMemory) -> PDPT {
    let pdpt_addr = PhysicalMemory::new(0)
        .expect("could not allocate physical memory")
        .into_address();

    // allocate page directories in chunks of 128 pages (= 0.5 MiB)
    let table = window.address() as *mut PageTableEntry;
    let mut chunk_addrs: [usize; 4] = [0, 0, 0, 0];

    // create mappings within each page directory
    for chunk in 0..4 {
        let block = PhysicalMemory::new(7).expect("could not allocate physical memory");
        let block_addr = block.address();

        for chunk_page in 0..128usize {
            let pdp_no = (chunk * 128) + chunk_page;
            let pd_addr = block_addr + (chunk_page * 0x1000);

            unsafe {
                if !direct_map_virtual_address(window.address(), pd_addr) {
                    panic!("could not map page directory");
                }
            }

            for pd_offset in 0..512usize {
                let phys_addr = (pdp_no << 30) | (pd_offset << 21);
                unsafe {
                    let mut pte = PageTableEntry::from_address(phys_addr);
                    pte.set_page_size(true);
                    table.add(pd_offset).write_volatile(pte);
                }
            }
        }

        chunk_addrs[chunk] = block.into_address();
    }

    unsafe {
        // create mappings within the PDPT
        if !direct_map_virtual_address(window.address(), pdpt_addr) {
            panic!("could not map PDPT");
        }

        for pdp_no in 0..512usize {
            let chunk = pdp_no / 128;
            let chunk_page = pdp_no % 128;
            let pd_addr = chunk_addrs[chunk] + (chunk_page * 0x1000);

            table
                .add(pdp_no)
                .write_volatile(PageTableEntry::from_address(pd_addr));
        }

        direct_unmap_virtual_address(window.address());

        let ptr: PhysicalPointer<PageTableEntry> = PhysicalPointer::new_unchecked(pdpt_addr);
        let pdpt: PDPT = mem::transmute(ptr);
        pdpt
    }
}

pub fn initialize_direct_physical_mappings() {
    let window = VirtualMemory::new(0x1000).expect("could not allocate virtual memory window");

    let pdpt = if FeatureFlags::GB_PAGES.supported() {
        println!("paging: CPU supports GB pages");
        init_physical_map_gb_pages(window)
    } else {
        println!("paging: CPU does not support GB pages");
        init_physical_map_mb_pages(window)
    };

    unsafe {
        // swap in the mappings
        let mut pml4t = PML4T::current();
        let old_pdpt = pml4t.get(PHYSICAL_MAP_BASE).unwrap();

        pml4t.set_by_index(
            PHYSICAL_MAP_PML4_IDX,
            PageTableEntry::from_address(pdpt.address()),
        );

        asm::reload_cr3();

        // init stuff for tables and clean up old physical mappings
        let pdpt_addr = old_pdpt.address();

        for pdpt_idx in 0..512usize {
            let pdpe = old_pdpt.get_by_index(pdpt_idx);
            if !pdpe.present() {
                continue;
            }

            let pd = PageDirectory::from_table_entry(pdpe).unwrap();
            for pd_idx in 0..512usize {
                let pde = pd.get_by_index(pd_idx);
                if !pde.present() {
                    continue;
                }

                let pt_addr = pde.physical_address();
                physical_mem::deallocate(pt_addr, 0);
            }

            let pd_addr = pdpe.physical_address();
            physical_mem::deallocate(pd_addr, 0);
        }

        physical_mem::deallocate(pdpt_addr, 0);
    }

    println!("paging: initialized direct physical memory map");
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
        &*self.as_ptr()
    }

    pub unsafe fn as_mut(&mut self) -> &mut T {
        &mut *self.as_mut_ptr()
    }
}

impl<T> Clone for PhysicalPointer<T> {
    fn clone(&self) -> Self {
        PhysicalPointer(self.0.clone())
    }
}

impl<T> Copy for PhysicalPointer<T> {}

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
    use crate::malloc::{PhysicalMemory, VirtualMemory};
    use core::ptr;
    use kernel_test_macro::kernel_test;

    #[kernel_test]
    fn test_physical_mapping() {
        let phys = PhysicalMemory::new(0).unwrap();
        let virt = VirtualMemory::new(0x1000).unwrap();

        unsafe {
            if !direct_map_virtual_address(virt.address(), phys.address()) {
                panic!(
                    "could not map virtual address {:#018x} => {:#018x}",
                    virt.address(),
                    phys.address()
                );
            }

            let p: PhysicalPointer<u64> = phys.as_physical_ptr();
            let virt_p = p.as_mut_ptr();

            ptr::write_volatile(virt_p, 0xA5A5DEADC0DEA5A5);
            drop(virt_p);

            let mapped_p = virt.address() as *const u64;
            assert_eq!(
                ptr::read_volatile(mapped_p),
                0xA5A5DEADC0DEA5A5,
                "read differing values from virtual addresses {:#018x} and {:#018x}",
                virt.address(),
                p.virtual_address()
            );

            direct_unmap_virtual_address(virt.address());
        }
    }
}
