use core::convert::TryInto;
use x86_64::instructions::tlb;
use x86_64::VirtAddr;

use lazy_static::lazy_static;
use spin::{Mutex, MutexGuard};

use crate::malloc::physical_mem;
use crate::structures::AVLTree;

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

// const MAX_PHYSICAL_MEMORY: usize = KERNEL_HEAP_BASE - PHYSICAL_MAP_BASE;

// const KERNEL_STACK_PML4_IDX: usize = 0b111_111_110;
// const KERNEL_BASE_PML4_IDX: usize = 0b110_001_000;
const KERNEL_HEAP_PML4_IDX: usize = 0b110_000_001;
const PHYSICAL_MAP_PML4_IDX: usize = 0b100_000_010;
const HIGHER_HALF_PML4_IDX: usize = 0b100_000_000;

lazy_static! {
    pub static ref PAGING_METADATA: Mutex<AVLTree<PageHierarchyIndex, PageTableMetadata>> =
        Mutex::new(AVLTree::new());
}

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

fn get_paging_metadata() -> MutexGuard<'static, AVLTree<PageHierarchyIndex, PageTableMetadata>> {
    PAGING_METADATA.lock()
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

    pub fn writable(&self) -> bool {
        (self.entry & 2) != 0
    }

    pub fn set_writable(&mut self, writable: bool) {
        if writable {
            self.entry = self.entry | 2;
        } else {
            self.entry = self.entry & !2;
        }
    }
}

#[repr(transparent)]
pub struct PageTable {
    entries: [PageTableEntry; 512],
}

impl PageTable {
    pub fn map_addr(&mut self, index: usize, phys_addr: usize) -> Result<(), usize> {
        let mut entry = self.get_entry(index)?;

        entry.set_physical_address(phys_addr);
        entry.set_present(true);

        self.set_entry(index, entry)
    }

    pub fn unmap_entry(&mut self, index: usize) -> Result<(), usize> {
        let mut entry = self.get_entry(index)?;
        entry.set_present(false);
        self.set_entry(index, entry)
    }

    pub fn get_entry(&self, index: usize) -> Result<PageTableEntry, usize> {
        use core::ptr;
        if index >= 512 {
            return Err(index);
        }

        let p = self.table_addr() as *const PageTableEntry;
        unsafe { Ok(ptr::read_volatile(p.offset(index as isize))) }
    }

    pub fn set_entry(&mut self, index: usize, entry: PageTableEntry) -> Result<(), usize> {
        use core::ptr;
        if index >= 512 {
            return Err(index);
        }

        let p = self.table_addr() as *mut PageTableEntry;
        unsafe {
            ptr::write_volatile(p.offset(index as isize), entry);
        }

        Ok(())
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

#[derive(Debug, Clone, Copy, PartialOrd, PartialEq, Eq, Ord)]
pub enum PageHierarchyIndex {
    PML4T,
    PDPT(u16),
    PD(u32),
    PT(u32),
}

impl PageHierarchyIndex {
    /// Check to see if all of this index's structure indices are valid.
    pub fn is_valid(&self) -> bool {
        match &self {
            PageHierarchyIndex::PML4T => true,
            PageHierarchyIndex::PDPT(i) => PageHierarchyIndex::extract_pdpt_indexes(*i) < 512,
            PageHierarchyIndex::PD(i) => {
                let (pml4t_idx, pdpt_idx) = PageHierarchyIndex::extract_pd_indexes(*i);
                pml4t_idx < 512 && pdpt_idx < 512
            }
            PageHierarchyIndex::PT(i) => {
                let (pml4t_idx, pdpt_idx, pd_idx) = PageHierarchyIndex::extract_pt_indexes(*i);
                pml4t_idx < 512 && pdpt_idx < 512 && pd_idx < 512
            }
        }
    }

    pub fn pdpt(pml4t_index: u16) -> PageHierarchyIndex {
        PageHierarchyIndex::PDPT((pml4t_index & 0x1FF) as u16)
    }

    pub fn pd(pml4t_index: u32, pdpt_index: u32) -> PageHierarchyIndex {
        PageHierarchyIndex::PD(((pml4t_index & 0x1FF) << 9) | (pdpt_index & 0x1FF))
    }

    pub fn pt(pml4t_index: u32, pdpt_index: u32, pd_index: u32) -> PageHierarchyIndex {
        PageHierarchyIndex::PT(
            ((pml4t_index & 0x1FF) << 18) | ((pdpt_index & 0x1FF) << 9) | (pd_index & 0x1FF),
        )
    }

    fn extract_pdpt_indexes(i: u16) -> usize {
        (i & 0x1FF) as usize
    }

    fn extract_pd_indexes(i: u32) -> (usize, usize) {
        (((i >> 9) & 0x1FF) as usize, (i & 0x1FF) as usize)
    }

    fn extract_pt_indexes(i: u32) -> (usize, usize, usize) {
        (
            ((i >> 18) & 0x1FF) as usize,
            ((i >> 9) & 0x1FF) as usize,
            (i & 0x1FF) as usize,
        )
    }

    pub fn pml4t_index(&self) -> Option<usize> {
        match &self {
            PageHierarchyIndex::PML4T => None,
            PageHierarchyIndex::PDPT(i) => Some(PageHierarchyIndex::extract_pdpt_indexes(*i)),
            PageHierarchyIndex::PD(i) => Some(((i >> 9) & 0x1FF) as usize),
            PageHierarchyIndex::PT(i) => Some(((i >> 18) & 0x1FF) as usize),
        }
    }

    pub fn pdpt_index(&self) -> Option<usize> {
        match &self {
            PageHierarchyIndex::PML4T | PageHierarchyIndex::PDPT(_) => None,
            PageHierarchyIndex::PD(i) => Some(((*i) & 0x1FF) as usize),
            PageHierarchyIndex::PT(i) => Some((((*i) >> 9) & 0x1FF) as usize),
        }
    }

    pub fn pd_index(&self) -> Option<usize> {
        match &self {
            PageHierarchyIndex::PML4T | PageHierarchyIndex::PDPT(_) | PageHierarchyIndex::PD(_) => {
                None
            }
            PageHierarchyIndex::PT(i) => Some(((*i) & 0x1FF) as usize),
        }
    }

    /// Get an index for the page table corresponding to a given
    /// virtual address.
    pub fn from_vaddr(virt_addr: usize) -> PageHierarchyIndex {
        PageHierarchyIndex::PT(((virt_addr >> 21) & 0x7FFFFFF) as u32)
    }

    /// Gets a reference to a page table without checking if indices are
    /// valid or if higher-level paging structures are mapped.
    pub unsafe fn get_table_unchecked(self) -> &'static mut PageTable {
        match self {
            PageHierarchyIndex::PML4T => PageTable::get_pml4t(),
            PageHierarchyIndex::PDPT(i) => {
                PageTable::get_pdpt(PageHierarchyIndex::extract_pdpt_indexes(i))
            }
            PageHierarchyIndex::PD(i) => {
                let (pml4t_idx, pdpt_idx) = PageHierarchyIndex::extract_pd_indexes(i);
                PageTable::get_pd(pml4t_idx, pdpt_idx)
            }
            PageHierarchyIndex::PT(i) => {
                let (pml4t_idx, pdpt_idx, pd_idx) = PageHierarchyIndex::extract_pt_indexes(i);
                PageTable::get_pt(pml4t_idx, pdpt_idx, pd_idx)
            }
        }
    }

    pub fn parent(self) -> Option<PageHierarchyIndex> {
        match &self {
            PageHierarchyIndex::PML4T => None,
            PageHierarchyIndex::PDPT(_) => Some(PageHierarchyIndex::PML4T),
            PageHierarchyIndex::PD(i) => {
                let (pml4t_idx, _) = PageHierarchyIndex::extract_pd_indexes(*i);
                Some(PageHierarchyIndex::PDPT(pml4t_idx as u16))
            }
            PageHierarchyIndex::PT(i) => {
                let (pml4t_idx, pdpt_idx, _) = PageHierarchyIndex::extract_pt_indexes(*i);
                Some(PageHierarchyIndex::PD(((pml4t_idx << 9) | pdpt_idx) as u32))
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
            PageHierarchyIndex::PDPT(i) => {
                let pml4t_idx = PageHierarchyIndex::extract_pdpt_indexes(i);
                let pte: PageTableEntry = pml4t.get_entry(pml4t_idx).unwrap();

                if pte.present() {
                    return unsafe { Some(PageTable::get_pdpt(pml4t_idx)) };
                }

                return None;
            }
            PageHierarchyIndex::PD(i) => {
                let (pml4t_idx, pdpt_idx) = PageHierarchyIndex::extract_pd_indexes(i);
                let pte: PageTableEntry = pml4t.get_entry(pml4t_idx).unwrap();

                if pte.present() {
                    let pdpt = unsafe { PageTable::get_pdpt(pml4t_idx) };
                    let pte = pdpt.get_entry(pdpt_idx).unwrap();

                    if pte.present() {
                        return unsafe { Some(PageTable::get_pd(pml4t_idx, pdpt_idx)) };
                    }
                }

                return None;
            }
            PageHierarchyIndex::PT(i) => {
                let (pml4t_idx, pdpt_idx, pd_idx) = PageHierarchyIndex::extract_pt_indexes(i);
                let pte: PageTableEntry = pml4t.get_entry(pml4t_idx).unwrap();

                if pte.present() {
                    let pdpt = unsafe { PageTable::get_pdpt(pml4t_idx) };
                    let pte = pdpt.get_entry(pdpt_idx).unwrap();

                    if pte.present() {
                        let pd = unsafe { PageTable::get_pd(pml4t_idx, pdpt_idx) };
                        let pte = pd.get_entry(pd_idx).unwrap();

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

#[derive(Debug, Clone)]
pub struct PageTableMetadata {
    ref_count: u16,
}

fn add_page_table_ref(index: PageHierarchyIndex) {
    if index == PageHierarchyIndex::PML4T {
        return;
    }

    let mut metadata_tree = get_paging_metadata();
    if let Some(mut node) = metadata_tree.get_mut(&index) {
        node.ref_count += 1;
    } else {
        metadata_tree
            .insert(index, PageTableMetadata { ref_count: 1 })
            .expect("could not add page table metadata to tree");

        if let Some(parent) = index.parent() {
            if parent != PageHierarchyIndex::PML4T {
                drop(metadata_tree);
                return add_page_table_ref(parent);
            }
        }
    }
}

fn remove_page_table_ref(index: PageHierarchyIndex) {
    if !index.is_valid() || index == PageHierarchyIndex::PML4T {
        return;
    }

    let mut metadata_tree = get_paging_metadata();
    let mut should_delete = false;

    if let Some(mut node) = metadata_tree.get_mut(&index) {
        node.ref_count -= 1;
        should_delete = node.ref_count == 0;
    }

    if should_delete {
        metadata_tree.remove(&index);
        let parent = index.parent().unwrap();
        let table = index.get_table().unwrap();
        let parent_table = parent.get_table().unwrap();

        match parent {
            PageHierarchyIndex::PML4T => parent_table
                .unmap_entry(index.pml4t_index().unwrap())
                .unwrap(),
            PageHierarchyIndex::PDPT(_) => parent_table
                .unmap_entry(index.pdpt_index().unwrap())
                .unwrap(),
            PageHierarchyIndex::PD(_) => {
                parent_table.unmap_entry(index.pd_index().unwrap()).unwrap()
            }
            _ => {}
        }

        let paddr = table.table_addr();
        unsafe {
            physical_mem::deallocate(paddr, 0x1000);
        }

        if parent != PageHierarchyIndex::PML4T {
            drop(metadata_tree);
            return remove_page_table_ref(parent);
        }
    }
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
        let table_addr = unsafe { physical_mem::allocate(0x1000) };
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
        let table_addr = unsafe { physical_mem::allocate(0x1000) };
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
        let table_addr = unsafe { physical_mem::allocate(0x1000) };
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

    let replaced_mapping = entry.present();
    pt.map_addr(pt_offset, phys_addr)
        .expect("failed to map page");

    if !replaced_mapping {
        add_page_table_ref(table_index);
    }

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

        remove_page_table_ref(table_index);
        tlb::flush(VirtAddr::new(virt_addr as u64));
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
        let mut metadata_tree = get_paging_metadata();

        let pml4t = PageTable::get_pml4t();
        let mut pml4t_rc = 0;

        for (pml4_idx, ent) in pml4t
            .iter()
            .enumerate()
            .skip(HIGHER_HALF_PML4_IDX - 1)
            .filter(|p| p.1.present())
        {
            pml4t_rc += 1;

            physical_mem::allocate_at(ent.physical_address(), 0x1000);
            let pdpt = PageTable::get_pdpt(pml4_idx);
            let mut pdpt_rc = 0;

            for (pdpt_idx, ent) in pdpt.iter().enumerate().filter(|e| e.1.present()) {
                pdpt_rc += 1;

                physical_mem::allocate_at(ent.physical_address(), 0x1000);
                let pd = PageTable::get_pd(pml4_idx, pdpt_idx);
                let mut pd_rc = 0;

                for (pd_idx, ent) in pd.iter().enumerate().filter(|e| e.1.present()) {
                    pd_rc += 1;

                    physical_mem::allocate_at(ent.physical_address(), 0x1000);
                    let pt = PageTable::get_pt(pml4_idx, pdpt_idx, pd_idx);
                    let mut pt_rc = 0;

                    for ent in pt.iter().filter(|e| e.present()) {
                        pt_rc += 1;
                        physical_mem::allocate_at(ent.physical_address(), 0x1000);
                    }

                    let index =
                        PageHierarchyIndex::pt(pml4_idx as u32, pdpt_idx as u32, pd_idx as u32);

                    let metadata = PageTableMetadata { ref_count: pt_rc };

                    metadata_tree.insert(index, metadata);
                }

                let index = PageHierarchyIndex::pd(pml4_idx as u32, pdpt_idx as u32);
                let metadata = PageTableMetadata { ref_count: pd_rc };

                metadata_tree.insert(index, metadata);
            }

            let index = PageHierarchyIndex::pdpt(pml4_idx as u16);
            let metadata = PageTableMetadata { ref_count: pdpt_rc };

            metadata_tree.insert(index, metadata);
        }

        let index = PageHierarchyIndex::PML4T;
        let metadata = PageTableMetadata {
            ref_count: pml4t_rc,
        };

        metadata_tree.insert(index, metadata);
    }
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
