use core::mem;
use core::ops;
use x86_64::instructions::tlb;
use x86_64::VirtAddr;

extern "C" {
    static _loader_start: *const u8;
    static _loader_end: *const u8;
}

fn loader_start_addr() -> usize {
    unsafe {
        mem::transmute(&_loader_start)
    }
}

fn loader_end_addr() -> usize {
    unsafe {
        mem::transmute(&_loader_end)
    }
}

const PAGE_MASK: usize = 0xFFFF_FFFF_FFFF_F000;

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

    pub fn add_range(&mut self, from_addr: usize, to_addr: usize) {
        if self.n_ranges >= 16 {
            return;
        }

        if (from_addr & 0xFFF) > 0 {
            panic!("from_addr={:#016x} is not page-aligned", from_addr);
        }

        if (to_addr & 0xFFF) > 0 {
            panic!("to_addr={:#016x} is not page-aligned", to_addr);
        }

        /* Make sure that we don't create a range that overlaps the loader. */
        let mut from_addr = from_addr;
        let mut to_addr = to_addr;
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
}


#[repr(transparent)]
pub struct PageTableEntry {
    entry: u64,
}

impl PageTableEntry {
    pub unsafe fn referenced_table(&self) -> &'static mut PageTable {
        mem::transmute(self.physical_address())
    }

    pub fn physical_address(&self) -> usize {
        (self.entry & !0xFFF) as usize
    }

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

#[repr(transparent)]
pub struct PageTable {
    entries: [PageTableEntry; 512]
}

impl PageTable {
    pub fn allocate_new(pf_allocator: &mut PageFrameAllocator) -> &'static mut PageTable {
        let addr = pf_allocator.allocate(1);
        let table: &'static mut PageTable = unsafe { mem::transmute(addr) };

        for e in table.entries.iter_mut() {
            e.entry = 0;
        }

        table
    }

    pub fn map_addr(&mut self, index: usize, phys_addr: usize) {
        self.entries[index].set_physical_address(phys_addr);
        self.entries[index].set_present(true);
    }

    pub fn map_table(&mut self, index: usize, table: &PageTable) {
        let addr: usize = unsafe { mem::transmute(table) };
        self.map_addr(index, addr);
    }

    pub fn table_addr(&self) -> usize {
        unsafe { mem::transmute(self) }
    }

    /// Get a reference to the recursively-mapped PML4T.
    pub fn get_pml4t() -> &'static mut PageTable {
        unsafe {
            mem::transmute(0xFFFF_FFFF_FFFF_F000 as usize)
        }
    }

    /// Get a reference to a recursively-mapped PD Pointer Table.
    pub fn get_pdp(pdp_idx: usize) -> &'static mut PageTable {
        unsafe {
            mem::transmute(0xFFFF_FFFF_FFE0_0000 + (0x1000 * pdp_idx))
        }
    }

    /// Get a reference to a recursively-mapped Page Directory.
    pub fn get_pd(pdp_idx: usize, pd_idx: usize) -> &'static mut PageTable {
        unsafe {
            mem::transmute(
                0xFFFF_FFFF_C000_0000 +
                (0x20_1000 * pdp_idx) +
                (0x1000 * pd_idx)
            )
        }
    }

    /// Get a reference to a recursively-mapped Page Table
    pub fn get_pt(pdp_idx: usize, pd_idx: usize, pt_idx: usize) -> &'static mut PageTable {
        unsafe {
            mem::transmute(
                0xFFFF_FF80_C000_0000 + 
                (0x4000_1000 * pdp_idx) + 
                (0x20_0000 * pd_idx) + 
                (0x1000 * pt_idx)
            )
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

pub fn map_addr(pf_allocator: &mut PageFrameAllocator, phys_addr: usize, virt_addr: usize) {
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
        pdpt = PageTable::allocate_new(pf_allocator);
        pml4t.map_table(pml4_idx, &pdpt);
    } else {
        pdpt = unsafe { pml4t[pml4_idx].referenced_table() };
    }

    let pd;
    if !pdpt[pdp_idx].present() {
        pd = PageTable::allocate_new(pf_allocator);
        pdpt.map_table(pdp_idx, &pd);
    } else {
        pd = unsafe { pdpt[pdp_idx].referenced_table() };
    }

    let pt;
    if !pd[pd_idx].present() {
        pt = PageTable::allocate_new(pf_allocator);
        pd.map_table(pd_idx, &pt);
    } else {
        pt = unsafe { pd[pd_idx].referenced_table() };
    }

    pt.map_addr(pt_idx, phys_addr);
    tlb::flush(VirtAddr::new(virt_addr as u64));
}
