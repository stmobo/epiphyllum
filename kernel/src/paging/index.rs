use super::{PageTable, PageTableEntry};

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

    pub const fn pml4t() -> PageHierarchyIndex {
        PageHierarchyIndex::PML4T
    }

    pub const fn pdpt(pml4t_index: u16) -> PageHierarchyIndex {
        PageHierarchyIndex::PDPT((pml4t_index & 0x1FF) as u16)
    }

    pub const fn pd(pml4t_index: u32, pdpt_index: u32) -> PageHierarchyIndex {
        PageHierarchyIndex::PD(((pml4t_index & 0x1FF) << 9) | (pdpt_index & 0x1FF))
    }

    pub const fn pt(pml4t_index: u32, pdpt_index: u32, pd_index: u32) -> PageHierarchyIndex {
        PageHierarchyIndex::PT(
            ((pml4t_index & 0x1FF) << 18) | ((pdpt_index & 0x1FF) << 9) | (pd_index & 0x1FF),
        )
    }

    const fn extract_pdpt_indexes(i: u16) -> usize {
        (i & 0x1FF) as usize
    }

    const fn extract_pd_indexes(i: u32) -> (usize, usize) {
        (((i >> 9) & 0x1FF) as usize, (i & 0x1FF) as usize)
    }

    const fn extract_pt_indexes(i: u32) -> (usize, usize, usize) {
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
    pub const fn from_vaddr(virt_addr: usize) -> PageHierarchyIndex {
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
