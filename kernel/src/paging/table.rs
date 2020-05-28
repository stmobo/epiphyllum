use core::mem;
use core::ptr;

use super::{pd_idx, pdp_idx, pml4_idx, pt_idx};
use super::{PageLevel, PageTableEntry, PhysicalPointer};
use super::{
    KERNEL_BASE_PML4_IDX, KERNEL_HEAP_PML4_IDX, KERNEL_STACK_PML4_IDX, PHYSICAL_MAP_PML4_IDX,
};
use crate::asm;
use crate::asm::cpuid::FeatureFlags;
use crate::lock::OnceCell;
use crate::malloc::{physical_mem, AllocationError, PhysicalMemory};

static PHYSICAL_MAP_PDPT: OnceCell<PageTableEntry> = OnceCell::new();
static HEAP_PDPT: OnceCell<PageTableEntry> = OnceCell::new();
static KERNEL_BASE_PDPT: OnceCell<PageTableEntry> = OnceCell::new();

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

pub trait PageStructure: Sized {
    fn new() -> Result<Self, AllocationError>;

    fn from_table_entry(entry: PageTableEntry) -> Option<Self>;

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

    /// Set a raw entry in this table by index.
    fn set_by_index(&mut self, index: usize, val: PageTableEntry) {
        self.table_mut().set_entry(index, val);
    }

    /// Clear an entry in this table.
    ///
    /// This will not affect page reference counts.
    fn clear_entry(&mut self, vaddr: usize) {
        self.set_entry(vaddr, PageTableEntry::new());
    }

    /// Get whether there is an entry for the given virtual address within this
    /// table.
    fn is_present(&self, vaddr: usize) -> bool {
        let pte = self.get_entry(vaddr);
        pte.present()
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

/// Create a copy of a page table.
///
/// # Safety
/// `src` must point to a valid page table of the given type.
unsafe fn copy_page_table<T: PageStructure>(src: *const PageTableEntry) -> T {
    let mut new = T::new().expect("could not allocate new table");
    let dst_ptr = new.table_mut().as_mut_ptr();
    ptr::copy_nonoverlapping(src, dst_ptr, 512);

    new
}

/// Ensures that a page table is not located at the zero page.
///
/// # Safety
/// `pte` must be a page table entry that references a valid, present page
/// table of type T.
unsafe fn ensure_nonzero_page<T: PageStructure>(entry: PageTableEntry) -> T {
    assert!(entry.present(), "referenced table is not present");
    assert!(!entry.page_size(), "referenced table is not a table");

    if let Some(table) = T::from_table_entry(entry) {
        table
    } else {
        println!(
            "paging: remapped page table ({:?}) located at invalid page {:#018x}",
            T::level(),
            entry.physical_address()
        );

        let src_ptr = super::offset_direct_map(entry.physical_address()) as *const PageTableEntry;
        copy_page_table(src_ptr)
    }
}

unsafe fn initialize_bootstrap_page_table(pt: PageTable, count_mapped: bool) {
    for l1_idx in 0..512 {
        let pte = pt.get_by_index(l1_idx);

        if !pte.present() {
            continue;
        } else if count_mapped {
            super::add_mapping_refs(pte.physical_address(), PageLevel::PT);
        }
    }

    add_table_ref(&pt);
}

unsafe fn initialize_bootstrap_page_dir(pd: PageDirectory, count_mapped: bool) {
    for l2_idx in 0..512 {
        let pde = pd.get_by_index(l2_idx);

        if !pde.present() {
            continue;
        } else if pde.page_size() {
            if count_mapped {
                // 2MiB page
                super::add_mapping_refs(pde.physical_address(), PageLevel::PD);
            }
        } else {
            let pt = ensure_nonzero_page(pde);
            initialize_bootstrap_page_table(pt, count_mapped);
        }
    }

    add_table_ref(&pd)
}

unsafe fn initialize_bootstrap_pdpt(pdpt: PDPT, count_mapped: bool) {
    for l3_idx in 0..512 {
        let pdpe = pdpt.get_by_index(l3_idx);

        if !pdpe.present() {
            continue;
        } else if pdpe.page_size() {
            if count_mapped {
                // 1GiB page
                super::add_mapping_refs(pdpe.physical_address(), PageLevel::PDP);
            }
        } else {
            let pd = ensure_nonzero_page(pdpe);
            initialize_bootstrap_page_dir(pd, count_mapped);
        }
    }

    add_table_ref(&pdpt);
}

/// Initialize reference counts for the bootstrap address space.
///
/// # Safety
/// This function should be called only once.
pub unsafe fn initialize() {
    // increment refcount for bootstrap PML4T, since the first call to
    // PML4T::load() will decrement this refcount

    direct_println!("paging: bootstrap PML4T at {:#018x}", asm::get_cr3());

    let pml4t = PML4T(RawPageTable {
        phys_addr: PhysicalPointer::new_unchecked(asm::get_cr3()),
    });

    let heap = pml4t.get_by_index(KERNEL_HEAP_PML4_IDX);
    let base = pml4t.get_by_index(KERNEL_BASE_PML4_IDX);
    let phys = pml4t.get_by_index(PHYSICAL_MAP_PML4_IDX);

    PHYSICAL_MAP_PDPT.set(phys).expect("already initialized");
    HEAP_PDPT.set(heap).expect("already initialized");
    KERNEL_BASE_PDPT.set(base).expect("already initialized");

    // increment refcounts for:
    // - kernel text pages
    // - kernel heap pages
    // - bootstrap page tables
    // Don't increment refcounts for the physical map for obvious reasons.

    for l4_idx in 0..512 {
        let pml4e = pml4t.get_by_index(l4_idx);

        if pml4e.present()
            && (l4_idx == KERNEL_BASE_PML4_IDX
                || l4_idx == KERNEL_HEAP_PML4_IDX
                || l4_idx == PHYSICAL_MAP_PML4_IDX
                || l4_idx == KERNEL_STACK_PML4_IDX)
        {
            // Increment refcounts for all referenced text/heap/stack pages,
            // and for all referenced tables
            let pdpt = ensure_nonzero_page(pml4e);
            initialize_bootstrap_pdpt(pdpt, l4_idx != PHYSICAL_MAP_PML4_IDX);
        }
    }

    add_table_ref(&pml4t);
    mem::forget(pml4t);
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

    fn new() -> Result<Self, AllocationError> {
        PML4T::new()
    }

    fn from_table_entry(_: PageTableEntry) -> Option<Self> {
        unimplemented!();
    }
}

impl PML4T {
    /// Get the currently-loaded PML4T as referenced by the CR3 register.
    pub unsafe fn current() -> PML4T {
        let table = PML4T(RawPageTable {
            phys_addr: PhysicalPointer::new_unchecked(asm::get_cr3()),
        });

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

        // Add mappings for kernel base, heap, and physical map:
        table.0.set_entry(
            KERNEL_BASE_PML4_IDX,
            KERNEL_BASE_PDPT.get().copied().unwrap(),
        );

        table
            .0
            .set_entry(KERNEL_HEAP_PML4_IDX, HEAP_PDPT.get().copied().unwrap());

        table.0.set_entry(
            PHYSICAL_MAP_PML4_IDX,
            PHYSICAL_MAP_PDPT.get().copied().unwrap(),
        );

        Ok(table)
    }

    /// Load this PML4T into the current processor's CR3 register.
    ///
    /// # Safety
    /// This function modifies processor control registers and additionally
    /// modifies processor page mappings.
    pub unsafe fn load(&self) {
        // decrement refcount for outgoing PML4T
        let _prev = PML4T(RawPageTable {
            phys_addr: PhysicalPointer::new_unchecked(asm::get_cr3()),
        });

        asm::set_cr3(self.0.phys_addr.address());

        // increment refcount for incoming PML4T
        add_table_ref(self);
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

    fn new() -> Result<Self, AllocationError> {
        PDPT::new()
    }

    fn from_table_entry(entry: PageTableEntry) -> Option<Self> {
        PDPT::from_table_entry(entry)
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
    /// If the virtual address is unmapped, a new table will be allocated.
    ///
    /// If the virtual address is already mapped as a 1GiB page, the mapping
    /// will be split into a page directory.
    pub fn ensure_table(&mut self, vaddr: usize) -> PageDirectory {
        match self.get(vaddr) {
            PageStructureChild::Table(pd) => pd,
            PageStructureChild::Page(_) => self.split_page_mapping(vaddr).unwrap(),
            PageStructureChild::None => {
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

    /// Splits a single 1GiB page mapping into a page directory that linearly
    /// maps the same physical address range.
    ///
    /// Returns an error if the page mapping for the given virtual address does
    /// not correspond to a 1GiB page.
    pub fn split_page_mapping(&mut self, vaddr: usize) -> Result<PageDirectory, PageTableEntry> {
        let pdpe = self.get_entry(vaddr);
        let start_addr = pdpe.physical_address();

        if !pdpe.present() || !pdpe.page_size() {
            // not a 1GiB page mapping
            return Err(pdpe);
        }

        let pd = PageDirectory::gb_map_table(start_addr).expect("could not create page directory");

        // No need to clean up the old page mapping, since the overall refcount
        // for those pages should not change.
        self.set_entry(vaddr, PageTableEntry::from_address(pd.address()));
        unsafe { add_table_ref(&pd) };

        Ok(pd)
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

    fn new() -> Result<Self, AllocationError> {
        PageDirectory::new()
    }

    fn from_table_entry(entry: PageTableEntry) -> Option<Self> {
        PageDirectory::from_table_entry(entry)
    }
}

impl PageDirectory {
    /// Create a new, empty page directory.
    pub fn new() -> Result<PageDirectory, AllocationError> {
        Ok(PageDirectory(RawPageTable::new()?))
    }

    /// Create a new page directory linearly mapping a GiB of physical memory.
    ///
    /// Does not adjust reference counts for the mapped pages.
    fn gb_map_table(start_addr: usize) -> Result<PageDirectory, AllocationError> {
        let mut pd = PageDirectory::new()?;
        let start_addr = start_addr & !((1 << 30) - 1);

        for i in 0..512 {
            let address = start_addr + (i << 21);
            let mut pte = PageTableEntry::from_address(address);

            pte.set_page_size(true);
            pd.set_by_index(i, pte);
        }

        Ok(pd)
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
    /// If the virtual address is unmapped, a new table will be allocated.
    ///
    /// If the virtual address is already mapped as a 2MiB page, the mapping
    /// will be split into a new page table.
    pub fn ensure_table(&mut self, vaddr: usize) -> PageTable {
        match self.get(vaddr) {
            PageStructureChild::Table(pt) => pt,
            PageStructureChild::Page(_) => self.split_page_mapping(vaddr).unwrap(),
            PageStructureChild::None => {
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

    /// Splits a single 2MiB page mapping into a page table that linearly
    /// maps the same physical address range.
    ///
    /// Returns an error if the page mapping for the given virtual address does
    /// not correspond to a 2MiB page.
    pub fn split_page_mapping(&mut self, vaddr: usize) -> Result<PageTable, PageTableEntry> {
        let pde = self.get_entry(vaddr);
        let start_addr = pde.physical_address();

        if !pde.present() || !pde.page_size() {
            return Err(pde);
        }

        let pt = PageTable::mb_map_table(start_addr).expect("could not create page table");
        self.set_entry(vaddr, PageTableEntry::from_address(pt.address()));
        unsafe { add_table_ref(&pt) };

        Ok(pt)
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

    fn new() -> Result<Self, AllocationError> {
        PageTable::new()
    }

    fn from_table_entry(entry: PageTableEntry) -> Option<Self> {
        PageTable::from_table_entry(entry)
    }
}

impl PageTable {
    /// Create a new, empty page table.
    pub fn new() -> Result<PageTable, AllocationError> {
        Ok(PageTable(RawPageTable::new()?))
    }

    /// Create a new page table linearly mapping 2 MiB of physical memory.
    ///
    /// Does not adjust reference counts for the mapped pages.
    fn mb_map_table(start_addr: usize) -> Result<PageTable, AllocationError> {
        let mut pt = PageTable::new()?;
        let start_addr = start_addr & !((1 << 21) - 1);

        for i in 0..512 {
            let address = start_addr + (i << 12);
            pt.set_by_index(i, PageTableEntry::from_address(address));
        }

        Ok(pt)
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
