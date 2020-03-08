use core::ops;
use x86_64::instructions::tlb;

use crate::malloc;

pub const PAGE_MASK: usize = 0xFFFF_FFFF_FFFF_F000;

const PML4T_RECURSIVE_BASE: usize = 0xFFFF_FFFF_FFFF_F000;
const PDPT_RECURSIVE_BASE: usize = 0xFFFF_FFFF_FFE0_0000;
const PD_RECURSIVE_BASE: usize = 0xFFFF_FFFF_C000_0000;
const PT_RECURSIVE_BASE: usize = 0xFFFF_FF80_0000_0000;

pub const KERNEL_STACK_BASE: usize = 0xFFFF_FF00_0000_0000;
pub const KERNEL_BASE: usize = 0xFFFF_C400_0000_0000;
pub const KERNEL_HEAP_BASE: usize = 0xFFFF_C080_0000_0000;
pub const PHYSICAL_MAP_BASE: usize = 0xFFFF_8100_0000_0000;
pub const HIGHER_HALF_START: usize = 0xFFFF_8000_0000_0000;

const MAX_PHYSICAL_MEMORY: usize = KERNEL_HEAP_BASE - PHYSICAL_MAP_BASE;

// const KERNEL_STACK_PML4_IDX: usize = 0b111_111_110;
// const KERNEL_BASE_PML4_IDX: usize = 0b110_001_000;
const KERNEL_HEAP_PML4_IDX: usize = 0b110_000_001;
const PHYSICAL_MAP_PML4_IDX: usize = 0b100_000_010;
const HIGHER_HALF_PML4_IDX: usize = 0b100_000_000;

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
#[repr(transparent)]
pub struct PageTableEntry {
    entry: u64,
}

impl PageTableEntry {
    pub fn new() -> PageTableEntry {
        PageTableEntry { entry: 0 }
    }

    pub fn physical_address(&self) -> usize {
        ((self.entry as usize) & PAGE_MASK) as usize
    }

    pub fn set_physical_address(&mut self, addr: usize) {
        let aligned = (addr & PAGE_MASK) as u64;
        self.entry = aligned | (self.entry & 0xFFF);
    }

    pub fn present(&self) -> bool {
        (self.entry & 1) > 0
    }

    pub fn set_present(&mut self, present: bool) {
        if present {
            self.entry = self.entry | 1;
        } else {
            self.entry = self.entry & !1;
        }
    }
}

#[repr(transparent)]
pub struct PageTable {
    entries: [PageTableEntry; 512],
}

impl PageTable {
    pub fn map_addr(&mut self, index: usize, phys_addr: usize) {
        self.entries[index].set_physical_address(phys_addr);
        self.entries[index].set_present(true);
    }

    pub fn table_addr(&self) -> usize {
        (self as *const PageTable) as usize
    }

    pub fn clear(&mut self) {
        for e in self.entries.iter_mut() {
            e.entry = 0;
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
    unsafe fn get_pdpt(pdp_idx: usize) -> &'static mut PageTable {
        let pdp_addr = PDPT_RECURSIVE_BASE + (0x1000 * pdp_idx);
        &mut *(pdp_addr as *mut PageTable)
    }

    /// Get a reference to a recursively-mapped Page Directory.
    unsafe fn get_pd(pdp_idx: usize, pd_idx: usize) -> &'static mut PageTable {
        let pd_addr = PD_RECURSIVE_BASE + (0x20_0000 * pdp_idx) + (0x1000 * pd_idx);
        &mut *(pd_addr as *mut PageTable)
    }

    /// Get a reference to a recursively-mapped Page Table.
    unsafe fn get_pt(pdp_idx: usize, pd_idx: usize, pt_idx: usize) -> &'static mut PageTable {
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

impl ops::Index<usize> for PageTable {
    type Output = PageTableEntry;

    fn index(&self, idx: usize) -> &Self::Output {
        &self.entries[idx]
    }
}

impl ops::IndexMut<usize> for PageTable {
    fn index_mut(&mut self, idx: usize) -> &mut Self::Output {
        &mut self.entries[idx]
    }
}

#[derive(Debug, Clone, Copy, PartialOrd, PartialEq, Eq, Ord)]
pub enum PageHierarchyIndex {
    PML4T,
    PDPT(usize),
    PD(usize, usize),
    PT(usize, usize, usize),
}

impl PageHierarchyIndex {
    /// Check to see if all of this index's structure indices are valid.
    pub fn is_valid(&self) -> bool {
        match &self {
            PageHierarchyIndex::PML4T => true,
            PageHierarchyIndex::PDPT(i1) => *i1 <= 512,
            PageHierarchyIndex::PD(i1, i2) => *i1 <= 512 && *i2 <= 512,
            PageHierarchyIndex::PT(i1, i2, i3) => *i1 <= 512 && *i2 <= 512 && *i3 <= 512,
        }
    }

    /// Get an index for the page table corresponding to a given
    /// virtual address.
    pub fn from_vaddr(virt_addr: usize) -> PageHierarchyIndex {
        PageHierarchyIndex::PT(
            (virt_addr >> 39) & 0x1FF,
            (virt_addr >> 30) & 0x1FF,
            (virt_addr >> 21) & 0x1FF,
        )
    }

    /// Gets a reference to a page table without checking if indices are
    /// valid or if higher-level paging structures are mapped.
    pub unsafe fn get_table_unchecked(self) -> &'static mut PageTable {
        match self {
            PageHierarchyIndex::PML4T => PageTable::get_pml4t(),
            PageHierarchyIndex::PDPT(pml4t_idx) => PageTable::get_pdpt(pml4t_idx),
            PageHierarchyIndex::PD(pml4t_idx, pdpt_idx) => PageTable::get_pd(pml4t_idx, pdpt_idx),
            PageHierarchyIndex::PT(pml4t_idx, pdpt_idx, pd_idx) => {
                PageTable::get_pt(pml4t_idx, pdpt_idx, pd_idx)
            }
        }
    }

    /// Consume this index and get an index for its parent PDPT.
    pub fn associated_pdpt(self) -> Option<PageHierarchyIndex> {
        if !self.is_valid() {
            return None;
        }

        let pml4t = PageTable::get_pml4t();
        match self {
            PageHierarchyIndex::PML4T => None,
            PageHierarchyIndex::PDPT(pml4t_idx)
            | PageHierarchyIndex::PD(pml4t_idx, _)
            | PageHierarchyIndex::PT(pml4t_idx, _, _) => Some(PageHierarchyIndex::PDPT(pml4t_idx)),
        }
    }

    /// Consume this index and get an index for its parent page directory.
    pub fn pd_index(self) -> Option<PageHierarchyIndex> {
        match self {
            PageHierarchyIndex::PML4T | PageHierarchyIndex::PDPT(_) => None,
            PageHierarchyIndex::PD(pml4t_idx, pdpt_idx)
            | PageHierarchyIndex::PT(pml4t_idx, pdpt_idx, _) => {
                Some(PageHierarchyIndex::PD(pml4t_idx, pdpt_idx))
            }
        }
    }

    /// Get the actual paging structure this index refers to.
    pub fn get_table(self) -> Option<&'static mut PageTable> {
        if !self.is_valid() {
            return None;
        }

        let pml4t = PageTable::get_pml4t();
        match self {
            PageHierarchyIndex::PML4T => {
                return Some(pml4t);
            }
            PageHierarchyIndex::PDPT(pml4t_idx) => {
                let pte: &PageTableEntry = &pml4t[pml4t_idx];
                if pte.present() {
                    return unsafe { Some(PageTable::get_pdpt(pml4t_idx)) };
                }

                return None;
            }
            PageHierarchyIndex::PD(pml4t_idx, pdpt_idx) => {
                let pte: &PageTableEntry = &pml4t[pml4t_idx];
                if pte.present() {
                    let pdpt = unsafe { PageTable::get_pdpt(pml4t_idx) };
                    let pte = pdpt[pdpt_idx];

                    if pte.present() {
                        return unsafe { Some(PageTable::get_pd(pml4t_idx, pdpt_idx)) };
                    }
                }

                return None;
            }
            PageHierarchyIndex::PT(pml4t_idx, pdpt_idx, pd_idx) => {
                let pte: &PageTableEntry = &pml4t[pml4t_idx];
                if pte.present() {
                    let pdpt = unsafe { PageTable::get_pdpt(pml4t_idx) };
                    let pte = pdpt[pdpt_idx];

                    if pte.present() {
                        let pd = unsafe { PageTable::get_pd(pml4t_idx, pdpt_idx) };
                        let pte = pd[pd_idx];

                        if pte.present() {
                            return unsafe { Some(PageTable::get_pt(pml4t_idx, pdpt_idx, pd_idx)) };
                        }
                    }
                }

                return None;
            }
        }
    }
}

pub fn get_mapping(virt_addr: usize) -> Option<PageTableEntry> {
    if (virt_addr & 0xFFF) > 0 {
        return None;
    }

    let pml4_idx: usize = (virt_addr >> 39) & 0x1FF;
    let pdp_idx: usize = (virt_addr >> 30) & 0x1FF;
    let pd_idx: usize = (virt_addr >> 21) & 0x1FF;
    let pt_idx: usize = (virt_addr >> 12) & 0x1FF;

    let pml4t = PageTable::get_pml4t();
    if pml4t[pml4_idx].present() {
        let pdpt = unsafe { PageTable::get_pdpt(pml4_idx) };

        if pdpt[pdp_idx].present() {
            let pd = unsafe { PageTable::get_pd(pml4_idx, pdp_idx) };

            if pd[pd_idx].present() {
                let pt = unsafe { PageTable::get_pt(pml4_idx, pdp_idx, pd_idx) };

                return Some(pt[pt_idx]);
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
     */
    for i in 0..n_remapped_pdpts {
        let from_ent = pml4t[i];

        if from_ent.present() {
            pml4t[i + PHYSICAL_MAP_PML4_IDX] = from_ent;
            pml4t[i].set_present(false);
        }
    }

    tlb::flush_all();
}

pub fn reserve_bootstrap_physical_pages() {
    unsafe {
        let pml4t = PageTable::get_pml4t();
        for (pml4_idx, ent) in pml4t
            .iter()
            .enumerate()
            .skip(HIGHER_HALF_PML4_IDX - 1)
            .filter(|p| p.1.present())
        {
            malloc::allocate_physical_memory_at(ent.physical_address(), 0x1000);
            let pdpt = PageTable::get_pdpt(pml4_idx);

            for (pdpt_idx, ent) in pdpt.iter().enumerate().filter(|e| e.1.present()) {
                malloc::allocate_physical_memory_at(ent.physical_address(), 0x1000);
                let pd = PageTable::get_pd(pml4_idx, pdpt_idx);

                for (pd_idx, ent) in pd.iter().enumerate().filter(|e| e.1.present()) {
                    malloc::allocate_physical_memory_at(ent.physical_address(), 0x1000);
                    let pt = PageTable::get_pt(pml4_idx, pdpt_idx, pd_idx);

                    for ent in pt.iter().filter(|e| e.present()) {
                        malloc::allocate_physical_memory_at(ent.physical_address(), 0x1000);
                    }
                }
            }
        }
    }
}

pub fn physical_memory_offset(phys_addr: usize) -> Option<usize> {
    if phys_addr >= MAX_PHYSICAL_MEMORY {
        return None;
    }

    Some(PHYSICAL_MAP_BASE + phys_addr)
}

pub fn physical_memory<T>(ptr: *const T) -> Option<*const T> {
    physical_memory_offset(ptr as usize).map(|v| v as *const T)
}

pub fn physical_address<T, U: Into<usize>>(addr: U) -> Option<*const T> {
    physical_memory_offset(addr.into()).map(|v| v as *const T)
}

pub fn physical_memory_mut<T>(ptr: *mut T) -> Option<*mut T> {
    physical_memory_offset(ptr as usize).map(|v| v as *mut T)
}

pub fn physical_address_mut<T, U: Into<usize>>(addr: U) -> Option<*mut T> {
    physical_memory_offset(addr.into()).map(|v| v as *mut T)
}
