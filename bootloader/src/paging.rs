use core::ops;
use x86_64::instructions::tlb;
use x86_64::VirtAddr;

extern "C" {
    static _loader_start: u8;
    static _loader_end: u8;
}

fn loader_start_addr() -> usize {
    unsafe {
        (&_loader_start as *const u8) as usize
    }
}

fn loader_end_addr() -> usize {
    unsafe {
        (&_loader_end as *const u8) as usize
    }
}

pub const PAGE_MASK: usize = 0xFFFF_FFFF_FFFF_F000;

#[derive(Debug, Clone, Copy)]
pub struct PageFrameRange {
    start_addr: usize,
    end_addr: usize,
    cur_alloc_end: usize,
    valid: bool
}

#[derive(Debug, Clone)]
pub struct PageFrameAllocator {
    ranges: [PageFrameRange; 16],
    n_ranges: usize,
}

impl PageFrameAllocator {
    pub fn new() -> PageFrameAllocator {
        PageFrameAllocator {
            ranges: [PageFrameRange {
                start_addr: 0,
                end_addr: 0,
                cur_alloc_end: 0,
                valid: false
            }; 16],
            n_ranges: 0
        }
    }

    /// Prevents the allocator from allocating pages in a specific range.
    pub fn restrict_range(&mut self, from_addr: usize, to_addr: usize) {
        let from_page = from_addr & PAGE_MASK;
        let to_page = (to_addr & PAGE_MASK) + 0x1000;

        for i in 0..16 {
            let mut pf_range = self.ranges[i];

            if !pf_range.valid || (pf_range.end_addr - pf_range.start_addr) < 0x1000 {
                continue;
            }
            
            if (pf_range.end_addr > from_page) && (to_page > pf_range.start_addr) {
                /* If we have a spare range, add it */
                if self.n_ranges < 16 && pf_range.start_addr < from_page && pf_range.end_addr > to_page {
                    let old_end_addr = pf_range.end_addr;
                    pf_range.end_addr = from_page;

                    if (old_end_addr - to_page) >= 0x1000 {
                        self.ranges[self.n_ranges] = PageFrameRange {
                            start_addr: to_page,
                            end_addr: old_end_addr,
                            cur_alloc_end: to_page,
                            valid: true
                        };
                
                        self.n_ranges += 1;
                    }
                } else if pf_range.end_addr > to_page {
                    pf_range.start_addr = to_page;
                    pf_range.cur_alloc_end = to_page;
                } else if pf_range.start_addr < from_page {
                    pf_range.end_addr = from_page;
                }

                if (pf_range.end_addr - pf_range.start_addr) < 0x1000 {
                    pf_range.valid = false;
                }

                self.ranges[i] = pf_range;
            }
        }
    }

    /// Add a specific range of available memory that we can allocate from.
    pub fn add_range(&mut self, from_addr: usize, to_addr: usize) {
        if self.n_ranges >= 16 {
            return;
        }

        /* Make sure that we don't create a range that overlaps the loader. */
        let mut from_addr = from_addr & PAGE_MASK;
        let mut to_addr = to_addr & PAGE_MASK;
        let loader_start_page: usize = loader_start_addr() & PAGE_MASK;
        let loader_end_page: usize = (loader_end_addr() & PAGE_MASK) + 0x1000;

        if (to_addr > loader_start_page) && (loader_end_page > from_addr) {
            if from_addr < loader_start_page && to_addr > loader_end_page {
                /* Create two ranges (if possible): 
                 * one for [from_addr, loader_start_page], and
                 * one for [loader_end_page, to_addr]
                 */

                if (loader_start_page - from_addr) >= 0x1000 {
                    self.add_range(from_addr, loader_start_page);
                }

                if (to_addr - loader_end_page) >= 0x1000 {
                    self.add_range(loader_end_page, to_addr);
                }

                return;
            } else if from_addr < loader_start_page {
                /* Truncate range to [from_addr, loader_start_page] */
                to_addr = loader_start_page;
            } else if to_addr > loader_end_page {
                /* Truncate range from [loader_end_page, to_addr] */
                from_addr = loader_end_page;
            } else {
                /* Range is completely within the loader address space */
                return;
            }
        }

        /* Make sure we only accept ranges of page size or greater. */
        if to_addr < from_addr || (to_addr - from_addr) < 0x1000 {
            return;
        }

        /* Initialize the new range. */
        self.ranges[self.n_ranges] = PageFrameRange {
            start_addr: from_addr,
            end_addr: to_addr,
            cur_alloc_end: from_addr,
            valid: true
        };

        self.n_ranges += 1;
    }

    /// Allocate a contiguous block of physical memory pages.
    /// 
    /// Panics if the request cannot be satisfied from any available memory
    /// ranges.
    pub fn allocate(&mut self, n_pages: u64) -> usize {
        if n_pages == 0 {
            panic!("attempted to allocate 0 pages");
        }

        for pf_range in self.ranges.iter_mut() {
            if !pf_range.valid || (pf_range.end_addr - pf_range.cur_alloc_end) < 0x1000 {
                continue;
            }
            
            let alloc_end = pf_range.cur_alloc_end + ((n_pages as usize) * 0x1000);
            if alloc_end > pf_range.end_addr {
                continue;
            }
    
            let alloc_start = pf_range.cur_alloc_end;
            pf_range.cur_alloc_end = alloc_end;

            return alloc_start;
        }

        panic!("no page frame ranges available to satisfy request for {} frames", n_pages);
    }

    /// Get the number of memory ranges available to this allocator.
    pub fn n_ranges(&self) -> usize {
        self.ranges.iter()
            .filter(|r| r.valid && (r.end_addr - r.cur_alloc_end) >= 0x1000)
            .count()
    }
}


#[derive(Debug, Clone, Copy, Eq, PartialEq)]
#[repr(transparent)]
pub struct PageTableEntry {
    entry: u64,
}

impl PageTableEntry {
    pub fn set_physical_address(&mut self, addr: usize) {
        let aligned = (addr & !0xFFF) as u64;
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

const PML4T_RECURSIVE_BASE: usize = 0xFFFF_FFFF_FFFF_F000;
const PDPT_RECURSIVE_BASE: usize  = 0xFFFF_FFFF_FFE0_0000;
const PD_RECURSIVE_BASE: usize    = 0xFFFF_FFFF_C000_0000;
const PT_RECURSIVE_BASE: usize    = 0xFFFF_FF80_0000_0000;

#[repr(transparent)]
pub struct PageTable {
    entries: [PageTableEntry; 512]
}

impl PageTable {
    pub fn map_addr(&mut self, index: usize, phys_addr: usize) {
        self.entries[index].set_physical_address(phys_addr);
        self.entries[index].set_present(true);
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
    pub fn get_pdp(pdp_idx: usize) -> &'static mut PageTable {
        unsafe {
            let pdp_addr = PDPT_RECURSIVE_BASE + (0x1000 * pdp_idx);
            &mut *(pdp_addr as *mut PageTable)
        }
    }

    /// Get a reference to a recursively-mapped Page Directory.
    pub fn get_pd(pdp_idx: usize, pd_idx: usize) -> &'static mut PageTable {
        unsafe {
            let pd_addr = PD_RECURSIVE_BASE + (0x20_0000 * pdp_idx) + (0x1000 * pd_idx);
            &mut *(pd_addr as *mut PageTable)
        }
    }

    /// Get a reference to a recursively-mapped Page Table.
    pub fn get_pt(pdp_idx: usize, pd_idx: usize, pt_idx: usize) -> &'static mut PageTable {
        unsafe {
            let pt_addr = PT_RECURSIVE_BASE + (0x4000_0000 * pdp_idx) + (0x20_0000 * pd_idx) + (0x1000 * pt_idx);
            &mut *(pt_addr as *mut PageTable)
        }
    }
}

impl ops::Index<usize> for PageTable {
    type Output = PageTableEntry;

    fn index (&self, idx: usize) -> &Self::Output {
        &self.entries[idx]
    }
}

impl ops::IndexMut<usize> for PageTable {
    fn index_mut (&mut self, idx: usize) -> &mut Self::Output {
        &mut self.entries[idx]
    }
}

/// Change the mapping for the given virtual address.
/// 
/// Allocates memory as needed for page tables, etc.
pub fn map_address (pf_allocator: &mut PageFrameAllocator, phys_addr: usize, virt_addr: usize) {
    if (phys_addr & 0xFFF) > 0 {
        panic!("attempt to map unaligned physical address {:#016x}", phys_addr);
    }

    if (virt_addr & 0xFFF) > 0 {
        panic!("attempt to map unaligned virtual address {:#016x}", virt_addr);
    }

    let pml4_idx: usize = (virt_addr >> 39) & 0x1FF;
    let pdp_idx: usize = (virt_addr >> 30) & 0x1FF;
    let pd_idx: usize = (virt_addr >> 21) & 0x1FF;
    let pt_idx: usize = (virt_addr >> 12) & 0x1FF;

    let pml4t = PageTable::get_pml4t();

    let pdpt;
    if !pml4t[pml4_idx].present() {
        /* Allocate a new PDPT for this vaddr. */
        let pdpt_phys = pf_allocator.allocate(1);
        pml4t.map_addr(pml4_idx, pdpt_phys);

        pdpt = PageTable::get_pdp(pml4_idx);
        pdpt.clear();
    } else {
        pdpt = PageTable::get_pdp(pml4_idx);
    }

    let pd;
    if !pdpt[pdp_idx].present() {
        /* Make a new PD: */
        let pd_phys = pf_allocator.allocate(1);
        pdpt.map_addr(pdp_idx, pd_phys);

        pd = PageTable::get_pd(pml4_idx, pdp_idx);
        pd.clear();
    } else {
        pd = PageTable::get_pd(pml4_idx, pdp_idx);
    }

    let pt;
    if !pd[pd_idx].present() {
        /* Make a new PT: */
        let pt_phys = pf_allocator.allocate(1);
        pd.map_addr(pd_idx, pt_phys);

        pt = PageTable::get_pt(pml4_idx, pdp_idx, pd_idx);
        pt.clear();
    } else {
        pt = PageTable::get_pt(pml4_idx, pdp_idx, pd_idx);
    }

    pt.map_addr(pt_idx, phys_addr);
    tlb::flush(VirtAddr::new(virt_addr as u64));
}
