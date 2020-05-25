use super::{pd_idx, pdp_idx, pml4_idx, pt_idx};
use super::{PageLevel, PageTableEntry, PhysicalPointer};
use super::{KERNEL_BASE_PML4_IDX, KERNEL_HEAP_PML4_IDX, PHYSICAL_MAP_PML4_IDX};
use crate::asm;
use crate::asm::cpuid::FeatureFlags;
use crate::malloc::{physical_mem, AllocationError, PhysicalMemory};

#[derive(Debug, Clone)]
#[repr(transparent)]
pub struct RawPageTable {
    phys_addr: PhysicalPointer<PageTableEntry>,
}

impl RawPageTable {
    pub fn new() -> Result<RawPageTable, AllocationError> {
        let page = PhysicalMemory::new(0)?;
        let ptr: *mut PageTableEntry = page.as_mut_ptr();

        unsafe {
            for i in 0..512 {
                ptr.add(i).write_volatile(PageTableEntry::new());
            }
        }

        let phys_addr = page.as_physical_ptr();
        page.leak();

        if let Some(page_data) = super::page_metadata() {
            unsafe {
                page_data[phys_addr.address() >> 12].decrement_refs(false);
            }
        }

        Ok(RawPageTable { phys_addr })
    }

    fn from_table_entry(entry: PageTableEntry) -> Option<RawPageTable> {
        if entry.present() {
            Some(RawPageTable {
                phys_addr: entry.page()?,
            })
        } else {
            None
        }
    }

    pub fn address(&self) -> usize {
        self.phys_addr.address()
    }

    pub fn as_ptr(&self) -> *const PageTableEntry {
        self.phys_addr.as_ptr()
    }

    pub fn as_mut_ptr(&mut self) -> *mut PageTableEntry {
        self.phys_addr.as_mut_ptr()
    }

    pub fn get_entry(&self, index: usize) -> PageTableEntry {
        debug_assert!(
            index < 512,
            "invalid index into page table ({} >= 512)",
            index
        );

        unsafe { self.as_ptr().add(index).read_volatile() }
    }

    pub fn set_entry(&mut self, index: usize, val: PageTableEntry) {
        debug_assert!(
            index < 512,
            "invalid index into page table ({} >= 512)",
            index
        );

        unsafe { self.as_mut_ptr().add(index).write_volatile(val) };
    }
}

unsafe impl Send for RawPageTable {}

pub trait PageStructure {
    /// Get a reference to the raw page table for this structure.
    fn table(&self) -> &RawPageTable;

    /// Get a mutable reference to the raw page table for this structure.
    fn table_mut(&mut self) -> &mut RawPageTable;

    /// Extract an index into this structure from a virtual address.
    fn index(vaddr: usize) -> usize;

    /// Get the level at which this structure sits in the paging hierarchy.
    fn level() -> PageLevel;

    /// Deallocates this table.
    ///
    /// Specifically, this method should:
    /// - Decrement refcounts for all terminal mappings in this structure, and
    /// - Decrement the refcounts for all child tables referenced by this
    ///   structure.
    unsafe fn cleanup(&mut self);

    /// Get the physical address of this table.
    fn address(&self) -> usize {
        self.table().address()
    }

    /// Get a raw entry in this table by its index.
    fn get_by_index(&self, index: usize) -> PageTableEntry {
        self.table().get_entry(index)
    }

    /// Get a raw entry in this table.
    fn get_entry(&self, vaddr: usize) -> PageTableEntry {
        self.table().get_entry(Self::index(vaddr))
    }

    /// Set a raw entry in this table.
    ///
    /// This will not affect page reference counts.
    fn set_entry(&mut self, vaddr: usize, val: PageTableEntry) {
        self.table_mut().set_entry(Self::index(vaddr), val)
    }

    /// Clear an entry in this table.
    ///
    /// This will not affect page reference counts.
    fn clear_entry(&mut self, vaddr: usize) {
        self.set_entry(vaddr, PageTableEntry::new());
    }
}

unsafe fn add_table_ref<T: PageStructure>(table: &T) {
    super::add_mapping_refs(table.address(), PageLevel::PT);
}

unsafe fn remove_table_ref<T: PageStructure>(table: &mut T, dealloc: bool) {
    let physical_address = table.address();
    if let Some(page_data) = super::page_metadata() {
        let count = page_data[physical_address >> 12].decrement_refs(false);

        if count == 0 && dealloc {
            table.cleanup();
            physical_mem::deallocate_pfn(physical_address >> 12);
        }
    }
}

// Note: C is the _child table_ type
#[derive(Debug)]
pub enum PageStructureChild<C: PageStructure> {
    Page(PageTableEntry),
    Table(C),
    None,
}

#[derive(Debug, Clone)]
#[repr(transparent)]
pub struct PML4T(RawPageTable);

impl PageStructure for PML4T {
    fn table(&self) -> &RawPageTable {
        &self.0
    }

    fn table_mut(&mut self) -> &mut RawPageTable {
        &mut self.0
    }

    fn index(vaddr: usize) -> usize {
        pml4_idx(vaddr)
    }

    fn level() -> PageLevel {
        PageLevel::PML4
    }

    unsafe fn cleanup(&mut self) {
        for i in 0..511 {
            self.cleanup_entry(i);
        }

        let pml4e = self.get_by_index(511);
        if let Some(pdpt) = PDPT::from_table_entry(pml4e) {
            if pdpt.address() != self.address() {
                self.cleanup_entry(511);
            }
        }
    }
}

impl PML4T {
    /// Get the currently-loaded PML4T as referenced by the CR3 register.
    pub unsafe fn current() -> PML4T {
        let table = asm::get_cr3();
        add_table_ref(&table);
        table
    }

    /// Create a new PML4T.
    ///
    /// The newly-created PML4T will have all empty mappings except for the
    /// last slot (index 511), which will contain a recursive mapping.
    pub fn new() -> Result<PML4T, AllocationError> {
        let mut table = PML4T(RawPageTable::new()?);

        unsafe {
            add_table_ref(&table);
        }

        // Add recursive mapping:
        table
            .0
            .set_entry(511, PageTableEntry::from_address(table.address()));

        Ok(table)
    }

    /// Get a child PDPT referenced by this table.
    pub fn get(&self, vaddr: usize) -> Option<PDPT> {
        PDPT::from_table_entry(self.get_entry(vaddr))
    }

    /// Get a child PDPT referenced by this table, or create a new one if no
    /// such table is present for the given virtual address.
    pub fn ensure_table(&mut self, vaddr: usize) -> PDPT {
        if let Some(pdpt) = self.get(vaddr) {
            pdpt
        } else {
            let pdpt = PDPT::new().expect("could not create PDPT");
            self.map_table(vaddr, &pdpt);
            pdpt
        }
    }

    /// Add a mapping for the given virtual address that references the given
    /// PDPT.
    pub fn map_table(&mut self, vaddr: usize, table: &PDPT) {
        self.cleanup_entry(pml4_idx(vaddr));
        self.set_entry(vaddr, PageTableEntry::from_address(table.address()));
        unsafe { add_table_ref(table) };
    }

    /// Clear the mapping for the given virtual address, if any.
    pub fn clear(&mut self, vaddr: usize) {
        self.cleanup_entry(pml4_idx(vaddr));
        self.clear_entry(vaddr);
    }

    fn cleanup_entry(&mut self, index: usize) {
        let entry = self.0.get_entry(index);
        if !entry.present() {
            return;
        }

        let dealloc = (index != KERNEL_HEAP_PML4_IDX)
            && (index != KERNEL_BASE_PML4_IDX)
            && (index != PHYSICAL_MAP_PML4_IDX);

        unsafe {
            remove_table_ref(&mut PDPT::from_table_entry(entry).unwrap(), dealloc);
        }
    }
}

impl Drop for PML4T {
    fn drop(&mut self) {
        unsafe { remove_table_ref(self, true) };
    }
}

#[derive(Debug)]
#[repr(transparent)]
pub struct PDPT(RawPageTable);

impl PageStructure for PDPT {
    fn table(&self) -> &RawPageTable {
        &self.0
    }

    fn table_mut(&mut self) -> &mut RawPageTable {
        &mut self.0
    }

    fn index(vaddr: usize) -> usize {
        pdp_idx(vaddr)
    }

    fn level() -> PageLevel {
        PageLevel::PDP
    }

    unsafe fn cleanup(&mut self) {
        for i in 0..512 {
            self.cleanup_entry(i);
        }
    }
}

impl PDPT {
    /// Create a new, empty PDPT.
    pub fn new() -> Result<PDPT, AllocationError> {
        Ok(PDPT(RawPageTable::new()?))
    }

    /// Get the mapping for the given virtual address within this table, if any.
    pub fn get(&self, vaddr: usize) -> PageStructureChild<PageDirectory> {
        let entry = self.get_entry(vaddr);
        if !entry.present() {
            PageStructureChild::None
        } else if entry.page_size() {
            PageStructureChild::Page(entry)
        } else {
            PageStructureChild::Table(PageDirectory::from_table_entry(entry).unwrap())
        }
    }

    /// Get the child page directory that is mapped for a virtual address
    /// within this table.
    ///
    /// If the virtual address is unmapped or if a 1 GiB page is already mapped
    /// to this virtual address, a new PD will be allocated and replace the
    /// prior mapping.
    pub fn ensure_table(&mut self, vaddr: usize) -> PageDirectory {
        match self.get(vaddr) {
            PageStructureChild::Table(pd) => pd,
            PageStructureChild::Page(_) | PageStructureChild::None => {
                let pd = PageDirectory::new().expect("could not create page directory");
                self.map_table(vaddr, &pd);
                pd
            }
        }
    }

    /// Map a virtual address to a child page directory.
    pub fn map_table(&mut self, vaddr: usize, table: &PageDirectory) {
        self.cleanup_entry(pdp_idx(vaddr));
        self.set_entry(vaddr, PageTableEntry::from_address(table.address()));
        unsafe { add_table_ref(table) };
    }

    /// Map a virtual address to a 1 GiB page.
    pub fn map_page(&mut self, vaddr: usize, mut page: PageTableEntry) {
        assert!(
            PageLevel::PDP.is_aligned(page.physical_address()),
            "attempted to map unaligned physical address {:#018x}",
            page.physical_address()
        );

        assert!(
            FeatureFlags::GB_PAGES.supported(),
            "attempted to map in GB page without arch support"
        );

        page.set_page_size(true);
        page.set_present(true);

        self.cleanup_entry(pdp_idx(vaddr));
        self.set_entry(vaddr, page);
        unsafe { super::add_mapping_refs(page.physical_address(), PageLevel::PDP) };
    }

    /// Clear the mapping for a virtual address, if any.
    pub fn clear(&mut self, vaddr: usize) {
        self.cleanup_entry(pdp_idx(vaddr));
        self.clear_entry(vaddr);
    }

    fn cleanup_entry(&mut self, index: usize) {
        let entry = self.0.get_entry(index);
        if !entry.present() {
            return;
        }

        unsafe {
            if entry.page_size() {
                super::remove_mapping_refs(entry.physical_address(), PageLevel::PDP);
            } else {
                remove_table_ref(&mut PageDirectory::from_table_entry(entry).unwrap(), true);
            }
        }
    }

    pub fn from_table_entry(entry: PageTableEntry) -> Option<PDPT> {
        Some(PDPT(RawPageTable::from_table_entry(entry)?))
    }
}

#[derive(Debug)]
#[repr(transparent)]
pub struct PageDirectory(RawPageTable);

impl PageStructure for PageDirectory {
    fn table(&self) -> &RawPageTable {
        &self.0
    }

    fn table_mut(&mut self) -> &mut RawPageTable {
        &mut self.0
    }

    fn index(vaddr: usize) -> usize {
        pd_idx(vaddr)
    }

    fn level() -> PageLevel {
        PageLevel::PD
    }

    unsafe fn cleanup(&mut self) {
        for i in 0..512 {
            self.cleanup_entry(i);
        }
    }
}

impl PageDirectory {
    /// Create a new, empty page directory.
    pub fn new() -> Result<PageDirectory, AllocationError> {
        Ok(PageDirectory(RawPageTable::new()?))
    }

    /// Get the mapping for a virtual address within this table.
    pub fn get(&self, vaddr: usize) -> PageStructureChild<PageTable> {
        let entry = self.get_entry(vaddr);
        if !entry.present() {
            PageStructureChild::None
        } else if entry.page_size() {
            PageStructureChild::Page(entry)
        } else {
            PageStructureChild::Table(PageTable::from_table_entry(entry).unwrap())
        }
    }

    /// Get the child page table that is mapped for a virtual address within
    /// this table.
    ///
    /// If the virtual address is unmapped or if a 2 MiB page is already mapped
    /// to this virtual address, a new table will be allocated and replace the
    /// prior mapping.
    pub fn ensure_table(&mut self, vaddr: usize) -> PageTable {
        match self.get(vaddr) {
            PageStructureChild::Table(pt) => pt,
            PageStructureChild::Page(_) | PageStructureChild::None => {
                let pt = PageTable::new().expect("could not create page directory");
                self.map_table(vaddr, &pt);
                pt
            }
        }
    }

    /// Map a virtual address to a child page table.
    pub fn map_table(&mut self, vaddr: usize, table: &PageTable) {
        self.cleanup_entry(pd_idx(vaddr));
        self.set_entry(vaddr, PageTableEntry::from_address(table.address()));
        unsafe { add_table_ref(table) };
    }

    /// Map a virtual address to a 2 MiB page.
    pub fn map_page(&mut self, vaddr: usize, mut page: PageTableEntry) {
        assert!(
            PageLevel::PD.is_aligned(page.physical_address()),
            "attempted to map unaligned physical address {:#018x}",
            page.physical_address()
        );

        page.set_page_size(true);
        page.set_present(true);

        self.cleanup_entry(pd_idx(vaddr));
        self.set_entry(vaddr, page);
        unsafe { super::add_mapping_refs(page.physical_address(), PageLevel::PD) };
    }

    /// Clear the mapping for a virtual address, if any.
    pub fn clear(&mut self, vaddr: usize) {
        self.cleanup_entry(pd_idx(vaddr));
        self.clear_entry(vaddr);
    }

    fn cleanup_entry(&mut self, index: usize) {
        let entry = self.0.get_entry(index);
        if !entry.present() {
            return;
        }

        unsafe {
            if entry.page_size() {
                super::remove_mapping_refs(entry.physical_address(), PageLevel::PD);
            } else {
                remove_table_ref(&mut PageTable::from_table_entry(entry).unwrap(), true);
            }
        }
    }

    pub fn from_table_entry(entry: PageTableEntry) -> Option<PageDirectory> {
        Some(PageDirectory(RawPageTable::from_table_entry(entry)?))
    }
}

#[derive(Debug)]
#[repr(transparent)]
pub struct PageTable(RawPageTable);

impl PageStructure for PageTable {
    fn table(&self) -> &RawPageTable {
        &self.0
    }

    fn table_mut(&mut self) -> &mut RawPageTable {
        &mut self.0
    }

    fn index(vaddr: usize) -> usize {
        pt_idx(vaddr)
    }

    fn level() -> PageLevel {
        PageLevel::PT
    }

    unsafe fn cleanup(&mut self) {
        for i in 0..512 {
            self.cleanup_entry(i);
        }
    }
}

impl PageTable {
    /// Create a new, empty page table.
    pub fn new() -> Result<PageTable, AllocationError> {
        Ok(PageTable(RawPageTable::new()?))
    }

    /// Get the mapping for a virtual address within this table.
    pub fn get(&self, vaddr: usize) -> Option<PageTableEntry> {
        let entry = self.get_entry(vaddr);
        if entry.present() {
            Some(entry)
        } else {
            None
        }
    }

    /// Map a virtual address to a 4 KiB page.
    pub fn map_page(&mut self, vaddr: usize, mut entry: PageTableEntry) {
        entry.set_present(true);
        entry.set_page_size(false);

        self.cleanup_entry(pt_idx(vaddr));
        self.set_entry(vaddr, entry);
        unsafe { super::add_mapping_refs(entry.physical_address(), PageLevel::PT) };
    }

    /// Clear the mapping for a virtual address, if any.
    pub fn clear(&mut self, vaddr: usize) {
        self.cleanup_entry(pt_idx(vaddr));
        self.clear_entry(vaddr);
    }

    pub fn from_table_entry(entry: PageTableEntry) -> Option<PageTable> {
        Some(PageTable(RawPageTable::from_table_entry(entry)?))
    }

    fn cleanup_entry(&mut self, index: usize) {
        let entry = self.0.get_entry(index);
        if entry.present() {
            unsafe {
                super::remove_mapping_refs(entry.physical_address(), PageLevel::PT);
            }
        }
    }
}
