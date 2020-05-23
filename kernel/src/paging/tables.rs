use core::convert::{TryFrom, TryInto};
use core::mem;
use core::ops::{Index, IndexMut};

use crate::asm;
use crate::asm::cpuid::FeatureFlags;
use crate::lock::OnceCell;
use crate::malloc::{AllocationError, PhysicalMemory};

use super::PageData;
use super::PhysicalPointer;
use super::{KERNEL_BASE_PML4_IDX, KERNEL_HEAP_PML4_IDX, PAGE_MASK, PHYSICAL_MAP_PML4_IDX};

const PML4T_RECURSIVE_BASE: usize = 0xFFFF_FFFF_FFFF_F000;
const PDPT_RECURSIVE_BASE: usize = 0xFFFF_FFFF_FFE0_0000;
const PD_RECURSIVE_BASE: usize = 0xFFFF_FFFF_C000_0000;
const PT_RECURSIVE_BASE: usize = 0xFFFF_FF80_0000_0000;

static PHYSICAL_MAP_PDPT: OnceCell<usize> = OnceCell::new();
static HEAP_PDPT: OnceCell<usize> = OnceCell::new();
static KERNEL_BASE_PDPT: OnceCell<usize> = OnceCell::new();

pub unsafe fn initialize(physical_map_pdpt: usize) {
    let pml4t = PageTable::get_pml4t();
    let heap = pml4t.get_entry(KERNEL_HEAP_PML4_IDX).unwrap();
    let base = pml4t.get_entry(KERNEL_BASE_PML4_IDX).unwrap();

    PHYSICAL_MAP_PDPT
        .set(physical_map_pdpt)
        .expect("already initialized");

    HEAP_PDPT
        .set(heap.physical_address())
        .expect("already initialized");

    KERNEL_BASE_PDPT
        .set(base.physical_address())
        .expect("already initialized");
}

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

    pub fn page<T>(&self) -> Option<PhysicalPointer<T>> {
        PhysicalPointer::new(self.physical_address())
    }

    pub fn present(&self) -> bool {
        (self.entry & 1) > 0
    }

    pub fn set_present(&mut self, present: bool) {
        if present {
            self.entry |= 1;
        } else {
            self.entry &= !1;
        }
    }

    pub fn writable(&self) -> bool {
        (self.entry & 2) != 0
    }

    pub fn set_writable(&mut self, writable: bool) {
        if writable {
            self.entry |= 2;
        } else {
            self.entry &= !2;
        }
    }

    pub fn page_size(&self) -> bool {
        (self.entry & (1 << 7)) != 0
    }

    pub fn set_page_size(&mut self, ps: bool) {
        if ps {
            self.entry |= 1 << 7;
        } else {
            self.entry &= !(1 << 7);
        }
    }
}

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
            self.table_mut_ptr().add(index)
                .write_volatile(entry);
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

#[derive(Debug, Copy, Clone)]
pub enum MappingError {
    AllocationFailure(AllocationError),
    AlreadyMapped,
}

pub struct PageTableMetadata {
    refcount: u64,
}

#[derive(Copy, Clone)]
struct Resolved(PhysicalPointer<PageTable>, PageLevel);

#[repr(transparent)]
pub struct AddressSpace {
    pml4t: PhysicalPointer<PageTable>,
}

impl AddressSpace {
    pub unsafe fn current() -> AddressSpace {
        let pml4t = asm::get_cr3();
        super::add_page_ref(pml4t.address());

        AddressSpace { pml4t }
    }

    pub fn new() -> Result<AddressSpace, AllocationError> {
        let mut space = PageTable::new().map(|pml4t| AddressSpace { pml4t })?;

        unsafe {
            let page = space.pml4t.address();
            let m = space.pml4t.as_mut();

            // map recursive entry:
            m.map_addr(511, page).unwrap();

            // map in the kernel executable PDPT:
            let base_pdpt = *KERNEL_BASE_PDPT.get().unwrap();
            m.map_addr(KERNEL_BASE_PML4_IDX, base_pdpt).unwrap();
            super::add_page_ref(base_pdpt);

            // map in the kernel heap PDPT:
            let heap_pdpt = *HEAP_PDPT.get().unwrap();
            m.map_addr(KERNEL_HEAP_PML4_IDX, heap_pdpt).unwrap();
            super::add_page_ref(heap_pdpt);

            // physical map PDPT:
            let map_pdpt = *PHYSICAL_MAP_PDPT.get().unwrap();
            m.map_addr(PHYSICAL_MAP_PML4_IDX, map_pdpt).unwrap();
            super::add_page_ref(map_pdpt);
        }

        Ok(space)
    }

    /// Loads this address space into CR3.
    pub unsafe fn load(&self) {
        asm::set_cr3(self.pml4t);
    }

    /// Get whether this address space is currently loaded into CR3.
    pub fn is_loaded(&self) -> bool {
        asm::get_cr3().address() == self.pml4t.address()
    }

    /// Resolves a virtual address in this space into a (Table, Level) pair.
    ///
    /// If the result is Ok, then the virtual address is mapped into the
    /// address space, and the returned table contains the mapping for this page.
    ///
    /// If the result is Err, then the virtual address is _not_ mapped into the
    /// address space, and the returned table contains the closest ancestor
    /// table that is present in the address space.
    fn resolve_raw(&self, vaddr: usize) -> Result<Resolved, Resolved> {
        unsafe {
            let pml4e = self.pml4t.as_ref().get_entry(pml4_idx(vaddr)).unwrap();
            let pdpt: PhysicalPointer<PageTable> = pml4e
                .try_into()
                .or(Err(Resolved(self.pml4t, PageLevel::PML4)))?;

            let pdpe = pdpt.as_ref().get_entry(pdp_idx(vaddr)).unwrap();
            if pdpe.present() && pdpe.page_size() {
                // this is a 1GiB page
                return Ok(Resolved(pdpt, PageLevel::PDP));
            }

            let pd: PhysicalPointer<PageTable> =
                pdpe.try_into().or(Err(Resolved(pdpt, PageLevel::PDP)))?;
            let pde = pd.as_ref().get_entry(pd_idx(vaddr)).unwrap();
            if pde.present() && pde.page_size() {
                // this is a 2MiB page
                return Ok(Resolved(pd, PageLevel::PD));
            }

            // otherwise, it's a 4KiB page
            let pt: PhysicalPointer<PageTable> =
                pde.try_into().or(Err(Resolved(pd, PageLevel::PD)))?;
            let pte = pt.as_ref().get_entry(pt_idx(vaddr)).unwrap();
            let resolved = Resolved(pt, PageLevel::PT);

            if pte.present() {
                Ok(resolved)
            } else {
                Err(resolved)
            }
        }
    }

    /// Gets the physical page mapping for a virtual address in this address
    /// space, if one exists.
    pub fn get_mapping(&self, vaddr: usize) -> Option<(PageLevel, PageTableEntry)> {
        self.resolve_raw(vaddr).ok().map(|r| {
            let table = r.0;
            unsafe {
                let entry = match r.1 {
                    PageLevel::PML4 => unreachable!(), // should not get here
                    PageLevel::PDP => table.as_ref().get_entry(pdp_idx(vaddr)).unwrap(),
                    PageLevel::PD => table.as_ref().get_entry(pd_idx(vaddr)).unwrap(),
                    PageLevel::PT => table.as_ref().get_entry(pt_idx(vaddr)).unwrap(),
                };

                (r.1, entry)
            }
        })
    }

    /// Checks if a page is mapped within this address space.
    pub fn is_mapped(&self, vaddr: usize) -> bool {
        self.get_mapping(vaddr).is_some()
    }

    /// Gets the page table that covers the given address at the given
    /// granularity, if it exists.
    pub fn get_table(&self, vaddr: usize, level: PageLevel) -> Option<PhysicalPointer<PageTable>> {
        if level == PageLevel::PML4 {
            return Some(self.pml4t);
        }

        unsafe {
            let pml4e = self.pml4t.as_ref().get_entry(pml4_idx(vaddr)).unwrap();
            let pdpt: PhysicalPointer<PageTable> = pml4e.try_into().ok()?;
            if level == PageLevel::PDP {
                return Some(pdpt);
            }

            let pdpe = pdpt.as_ref().get_entry(pdp_idx(vaddr)).unwrap();
            if pdpe.present() && pdpe.page_size() {
                return None;
            }

            let pd: PhysicalPointer<PageTable> = pdpe.try_into().ok()?;
            if level == PageLevel::PD {
                return Some(pd);
            }

            let pde = pd.as_ref().get_entry(pd_idx(vaddr)).unwrap();
            if pde.present() && pde.page_size() {
                return None;
            }

            pde.try_into().ok()
        }
    }

    fn create_child_table(
        &self,
        mut cur: PhysicalPointer<PageTable>,
        index: usize,
    ) -> Result<PhysicalPointer<PageTable>, MappingError> {
        let child_table = PageTable::new().map_err(MappingError::AllocationFailure)?;

        unsafe {
            let cur_table = cur.as_mut();
            cur_table.map_addr(index, child_table.address()).unwrap();

            if self.is_loaded() {
                self.load();
            }

            Ok(child_table)
        }
    }

    fn increment_pte_refs(pte: PageTableEntry, level: PageLevel) {
        if let Some(page_data) = super::page_metadata() {
            let pfn_start = pte.physical_address() >> 12;
            let pfn_count = match level {
                PageLevel::PT => 1,
                PageLevel::PD => 512,
                PageLevel::PDP => 512 * 512,
                PageLevel::PML4 => unimplemented!(),
            };

            for pfn in pfn_start..(pfn_start + pfn_count) {
                unsafe { page_data[pfn].increment_refs() };
            }
        }
    }

    fn decrement_pte_refs(pte: PageTableEntry, level: PageLevel, page_data: &'static [PageData]) {
        let pfn_start = pte.physical_address() >> 12;
        let pfn_count = match level {
            PageLevel::PT => 1,
            PageLevel::PD => 512,
            PageLevel::PDP => 512 * 512,
            PageLevel::PML4 => unimplemented!(),
        };

        for pfn in pfn_start..(pfn_start + pfn_count) {
            unsafe { page_data[pfn].decrement_refs() };
        }
    }

    fn decrement_table_refs(
        mut ptr: PhysicalPointer<PageTable>,
        level: PageLevel,
        page_data: &'static [PageData],
    ) {
        let table = unsafe { ptr.as_mut() };

        for i in 0..512 {
            let entry = table.get_entry(i).unwrap();
            if level == PageLevel::PT || entry.page_size() {
                Self::decrement_pte_refs(entry, level, page_data);
            } else {
                let next_lvl = match level {
                    PageLevel::PT => unreachable!(),
                    PageLevel::PD => PageLevel::PT,
                    PageLevel::PDP => PageLevel::PD,
                    PageLevel::PML4 => PageLevel::PDP,
                };

                if let Ok(ptr) = entry.try_into() {
                    Self::decrement_table_refs(ptr, next_lvl, page_data);
                }

                let table_pfn = entry.physical_address() >> 12;
                unsafe { page_data[table_pfn].decrement_refs() };
            }
        }
    }

    fn cleanup_mapping(pte: PageTableEntry, level: PageLevel) {
        if let Some(page_data) = super::page_metadata() {
            if level == PageLevel::PT || pte.page_size() {
                Self::decrement_pte_refs(pte, level, page_data);
            } else if let Ok(ptr) = PhysicalPointer::<PageTable>::try_from(pte) {
                Self::decrement_table_refs(ptr, level, page_data);
            }
        }
    }

    /// Sets a mapping within this address space, replacing any previous
    /// mapping(s) for that address.
    pub fn set_mapping(
        &mut self,
        vaddr: usize,
        mut mapping: PageTableEntry,
        level: PageLevel,
    ) -> Result<(), MappingError> {
        assert_ne!(level, PageLevel::PML4, "invalid level for page mapping");
        assert_eq!(
            mapping.physical_address() & level.alignment_mask().unwrap(),
            0,
            "attempted to map unaligned page at {:#018x} to {:#018x}",
            vaddr,
            mapping.physical_address()
        );

        assert!(
            FeatureFlags::GB_PAGES.supported() || (level != PageLevel::PDP),
            "attempted to map in GB page without arch support"
        );

        if level == PageLevel::PDP || level == PageLevel::PD {
            mapping.set_page_size(true);
        } else {
            mapping.set_page_size(false);
        }

        unsafe {
            let pml4 = pml4_idx(vaddr);
            let pml4e = self.pml4t.as_ref().get_entry(pml4).unwrap();
            let mut pdpt = PhysicalPointer::<PageTable>::try_from(pml4e)
                .or_else(|_| self.create_child_table(self.pml4t, pml4))?;

            // Get the PDPE for this mapping.
            let pdp = pdp_idx(vaddr);
            let pdpe = pdpt.as_ref().get_entry(pdp).unwrap();

            // Map in the given page at PDP-level
            if level == PageLevel::PDP {
                if pdpe.present() {
                    // clean up previous mapping
                    Self::cleanup_mapping(pdpe, PageLevel::PDP);
                }

                Self::increment_pte_refs(mapping, PageLevel::PDP);
                pdpt.as_mut().set_entry(pdp, mapping).unwrap();

                if self.is_loaded() {
                    // reload TLB
                    self.load();
                }

                return Ok(());
            }

            let mut pd: PhysicalPointer<PageTable>;
            if pdpe.present() && pdpe.page_size() {
                // there was a page mapping here, clean it up and make a
                // new child page directory
                Self::cleanup_mapping(pdpe, PageLevel::PDP);
                pd = self.create_child_table(pdpt, pdp)?;
            } else {
                // try to get or make a new child page directory
                pd = PhysicalPointer::<PageTable>::try_from(pdpe)
                    .or_else(|_| self.create_child_table(pdpt, pdp))?;
            }

            let pd_i = pd_idx(vaddr);
            let pde = pd.as_ref().get_entry(pd_i).unwrap();

            // Map in the given page at PD-level
            if level == PageLevel::PD {
                if pde.present() {
                    Self::cleanup_mapping(pde, PageLevel::PD);
                }

                Self::increment_pte_refs(mapping, PageLevel::PD);
                pd.as_mut().set_entry(pd_i, mapping).unwrap();

                if self.is_loaded() {
                    self.load();
                }

                return Ok(());
            }

            // Get or make the page table for this mapping:
            let mut pt: PhysicalPointer<PageTable>;
            if pde.present() && pde.page_size() {
                Self::cleanup_mapping(pde, PageLevel::PD);
                pt = self.create_child_table(pd, pd_i)?;
            } else {
                pt = PhysicalPointer::<PageTable>::try_from(pde)
                    .or_else(|_| self.create_child_table(pd, pd_i))?;
            }

            let pt_i = pt_idx(vaddr);
            let pte = pt.as_ref().get_entry(pt_i).unwrap();
            if pte.present() {
                Self::cleanup_mapping(pte, PageLevel::PT);
            }

            Self::increment_pte_refs(mapping, PageLevel::PT);
            pt.as_mut().set_entry(pt_i, mapping).unwrap();

            if self.is_loaded() {
                asm::invlpg(vaddr);
            }

            Ok(())
        }
    }

    /// Remove a range of mapped pages, with granularity corresponding to
    /// the given page-level.
    ///
    /// For example, removing pages with PDP granularity will unmap all pages
    /// with the same PML4 offset and PDP offset as the given virtual address.
    ///
    /// Attempting to unmap an address with finer granularity than it was
    /// originally mapped with will result in an error, with the error value
    /// being the mapped page's granularity.
    pub fn remove_mapping(&mut self, vaddr: usize, level: PageLevel) -> Result<(), PageLevel> {
        unsafe {
            let pml4e = self.pml4t.as_ref().get_entry(pml4_idx(vaddr)).unwrap();
            if level == PageLevel::PML4 {
                Self::cleanup_mapping(pml4e, PageLevel::PML4);
                self.pml4t.as_mut().clear_entry(pml4_idx(vaddr)).unwrap();

                if self.is_loaded() {
                    self.load();
                }

                return Ok(());
            }

            let mut pdpt = match PhysicalPointer::<PageTable>::try_from(pml4e) {
                Ok(v) => v,
                Err(_) => return Ok(()),
            };

            // Get the PDPE for this mapping.
            let pdpe = pdpt.as_ref().get_entry(pdp_idx(vaddr)).unwrap();
            if !pdpe.present() {
                // translation cannot continue further
                return Ok(());
            }

            if level == PageLevel::PDP {
                // Common cleanup code for pages and tables
                Self::cleanup_mapping(pdpe, PageLevel::PDP);
                pdpt.as_mut().clear_entry(pdp_idx(vaddr)).unwrap();

                if self.is_loaded() {
                    self.load();
                }

                return Ok(());
            }

            if pdpe.page_size() {
                return Err(PageLevel::PDP);
            }

            // Same deal with page directory:
            let mut pd = match PhysicalPointer::<PageTable>::try_from(pdpe) {
                Ok(v) => v,
                Err(_) => return Ok(()),
            };

            let pde = pd.as_ref().get_entry(pd_idx(vaddr)).unwrap();
            if !pde.present() {
                return Ok(());
            }

            if level == PageLevel::PD {
                Self::cleanup_mapping(pde, PageLevel::PD);
                pd.as_mut().clear_entry(pd_idx(vaddr)).unwrap();

                if self.is_loaded() {
                    self.load();
                }

                return Ok(());
            }

            if pde.page_size() {
                return Err(PageLevel::PD);
            }

            // Move on to page table:
            let mut pt = match PhysicalPointer::<PageTable>::try_from(pde) {
                Ok(v) => v,
                Err(_) => return Ok(()),
            };

            let pte = pt.as_ref().get_entry(pt_idx(vaddr)).unwrap();
            Self::cleanup_mapping(pte, PageLevel::PT);
            pt.as_mut().clear_entry(pt_idx(vaddr)).unwrap();

            if self.is_loaded() {
                asm::invlpg(vaddr);
            }
        }

        Ok(())
    }

    /// Convenience function for mapping a single page with 4K granularity.
    pub fn map_page(&mut self, vaddr: usize, paddr: usize) -> Result<(), MappingError> {
        let mut pte = PageTableEntry::new();
        pte.set_physical_address(paddr);
        pte.set_present(true);

        self.set_mapping(vaddr, pte, PageLevel::PT)
    }

    /// Convenience function for unmapping a single page with 4K granularity.
    pub fn unmap_page(&mut self, vaddr: usize) -> Result<(), PageLevel> {
        self.remove_mapping(vaddr, PageLevel::PT)
    }

    /// Convenience function for unmapping a range of pages with 4K granularity.
    pub fn unmap_page_range(&mut self, vaddr: usize, n_pages: usize) -> Result<(), PageLevel> {
        for i in 0..n_pages {
            self.unmap_page(vaddr + (0x1000 * i))?;
        }

        Ok(())
    }

    /// Convenience function for mapping a range of pages with 4K granularity.
    pub fn map_page_range(
        &mut self,
        vaddr: usize,
        paddr: usize,
        n_pages: usize,
    ) -> Result<(), MappingError> {
        for i in 0..n_pages {
            let res = self.map_page(vaddr + (i * 0x1000), paddr + (i * 0x1000));
            if res.is_err() {
                mem::drop(self.unmap_page_range(vaddr, n_pages));
                return res;
            }
        }

        Ok(())
    }
}

impl Drop for AddressSpace {
    fn drop(&mut self) {
        unsafe {
            super::remove_page_ref(self.pml4t.address());
        }
    }
}

unsafe impl Send for AddressSpace {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::malloc::physical_mem;
    use crate::malloc::VirtualMemory;
    use crate::rng::MersenneTwister64;
    use crate::test::TEST_SEED;
    use kernel_test_macro::kernel_test;

    #[kernel_test]
    fn test_map() {
        let mut addr_space = unsafe { AddressSpace::current() };
        let pmem = PhysicalMemory::new(2).unwrap();
        let vmem = VirtualMemory::new(0x4000).unwrap();
        let paddr = pmem.address();
        let vaddr = vmem.address();

        addr_space.map_page_range(vaddr, paddr, 4).unwrap();

        let mut rng = MersenneTwister64::new(TEST_SEED);
        unsafe {
            for i in 0..(0x4000 / 8) {
                let v = (vaddr as *mut u64).offset(i);
                let p: *mut u64 = pmem.as_ptr().as_mut_ptr();
                let p = p.offset(i);

                if i & 1 == 0 {
                    v.write_volatile(rng.generate());
                } else {
                    p.write_volatile(rng.generate());
                }
            }

            rng.seed(TEST_SEED);
            for i in 0..(0x4000 / 8) {
                let v = (vaddr as *mut u64).offset(i);
                let p: *mut u64 = pmem.as_ptr().as_mut_ptr();
                let p = p.offset(i);

                let val = rng.generate();
                assert_eq!(
                    v.read_volatile(),
                    val,
                    "read incorrect value from virtual address {:#018x}",
                    v as usize
                );

                assert_eq!(
                    p.read_volatile(),
                    val,
                    "read incorrect value from physical address {:#018x}",
                    paddr + (i as usize * 8)
                );
            }
        }

        drop(pmem);
        addr_space.unmap_page_range(vaddr, 4).unwrap();
    }

    #[kernel_test]
    fn test_refcount() {
        let pmem = PhysicalMemory::new(0).unwrap();
        let paddr = pmem.address();
        let vaddr = 0x10000;
        let pfn = paddr >> 12;

        unsafe {
            let page_data = crate::paging::page_metadata().unwrap();
            let mut space = AddressSpace::current();

            // The refcount should be 1 after the PhysicalMemory constructor:
            assert_eq!(
                page_data[pfn].refcount(),
                1,
                "incorrect refcount for allocated page"
            );

            // Mapping the page adds a reference:
            space.map_page(vaddr, paddr).expect("could not map page");
            assert_eq!(
                page_data[pfn].refcount(),
                2,
                "incorrect refcount for mapped page"
            );

            // Ensure we can't overwrite the referenced page:
            let alloc_test = physical_mem::allocate_at(paddr, 0);
            assert_eq!(
                alloc_test,
                Err(AllocationError::AlreadyAllocated),
                "incorrectly overwrote test allocation"
            );

            // PhysicalMemory's Drop code should decrement the refcount:
            drop(pmem);
            assert_eq!(
                page_data[pfn].refcount(),
                1,
                "incorrect refcount for mapped page"
            );

            // The page should still be allocated however:
            let alloc_test = physical_mem::allocate_at(paddr, 0);
            assert_eq!(
                alloc_test,
                Err(AllocationError::AlreadyAllocated),
                "incorrectly overwrote test allocation"
            );

            // Check the reference counts on the page tables:
            // PML4T and PDPT are shared (most likely), but PDs and PTs should
            // be uniquely mapped.
            let pd = space.get_table(vaddr, PageLevel::PD).unwrap();
            let pt = space.get_table(vaddr, PageLevel::PT).unwrap();

            assert_eq!(
                page_data[pd.address() >> 12].refcount(),
                1,
                "incorrect refcount for page directory at {:#018x} (pfn {})",
                pd.address(),
                pd.address() >> 12
            );

            assert_eq!(
                page_data[pt.address() >> 12].refcount(),
                1,
                "incorrect refcount for page table at {:#018x} (pfn {})",
                pt.address(),
                pt.address() >> 12
            );

            // Unmapping the page should decrement its refcount:
            space.unmap_page(vaddr).unwrap();
            assert_eq!(
                page_data[pfn].refcount(),
                0,
                "incorrect refcount for unmapped page"
            );

            // Since the refcount went to zero, it should be free for
            // re-allocation:
            let alloc_test = physical_mem::allocate_at(paddr, 0);
            assert_eq!(
                alloc_test,
                Ok(paddr),
                "could not re-allocate test allocation"
            );

            // Clean up:
            physical_mem::deallocate(paddr, 0);
            assert_eq!(
                page_data[pfn].refcount(),
                0,
                "incorrect refcount for deallocated page"
            );
        }
    }
}
