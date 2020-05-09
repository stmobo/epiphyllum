use alloc_crate::vec::Vec;
use core::ops::Bound;

use super::AllocationError;
use crate::lock::LockedGlobal;
use crate::paging::{is_page_aligned, round_to_next_page, round_to_prev_page};
use crate::structures::AVLTree;

static KERNEL_VMA: LockedGlobal<VirtualMemoryAllocator> = LockedGlobal::new();

#[derive(Debug, Clone)]
struct VirtualMemoryRange {
    start: usize,
    end: usize,
    free: bool,
}

impl VirtualMemoryRange {
    fn new(start: usize, end: usize) -> VirtualMemoryRange {
        if !is_page_aligned(start) || !is_page_aligned(end) {
            panic!(
                "attempted to create non-aligned virtual memory range at {:#016x} - {:#016x}",
                start, end
            );
        }

        if end < start {
            panic!(
                "attempt to create invalid virtual memory range ({:#016x} < {:#016x})",
                end, start
            );
        }

        VirtualMemoryRange {
            start: start,
            end: end,
            free: false,
        }
    }

    fn size(&self) -> usize {
        return self.end - self.start;
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct FreeListEntry {
    address: usize,
    size: usize,
}

impl FreeListEntry {
    fn new(range: &VirtualMemoryRange) -> FreeListEntry {
        FreeListEntry {
            address: range.start,
            size: range.size(),
        }
    }
}

struct VirtualMemoryAllocator {
    regions: AVLTree<usize, VirtualMemoryRange>, /* indexed by address */
    free: Vec<FreeListEntry>,
}

impl VirtualMemoryAllocator {
    fn new() -> VirtualMemoryAllocator {
        VirtualMemoryAllocator {
            regions: AVLTree::new(),
            free: Vec::new(),
        }
    }

    /// Adds a region to the region tree and to the free list (if necessary).
    /// The caller is responsible for re-sorting the list afterwards!
    fn add_range(&mut self, mut range: VirtualMemoryRange, free: bool) {
        if free {
            self.free.push(FreeListEntry::new(&range));
        }

        range.free = free;
        self.regions
            .insert(range.start, range)
            .expect("could not add allocator for virtual memory range");
    }

    /// Remove an entry from the free list.
    /// The caller is responsible for re-sorting the list afterwards!
    fn remove_free_list_entry(&mut self, range: &VirtualMemoryRange) {
        let entry = FreeListEntry::new(range);
        let idx = self
            .free
            .binary_search(&entry)
            .expect("could not find memory range in free list");

        self.free.swap_remove(idx);
    }

    pub fn register_memory(&mut self, start: usize, end: usize) {
        let start = round_to_next_page(start);
        let end = round_to_prev_page(end);
        self.add_range(VirtualMemoryRange::new(start, end), true);
        self.free.sort_unstable();
    }

    pub fn allocate(&mut self, size: usize) -> Result<usize, AllocationError> {
        let alloc_sz = round_to_next_page(size);

        if self.free.len() == 0 || self.free[0].size < size {
            return Err(AllocationError::NoFreeVirtualMemory);
        }

        /* Pull the free region with the largest size off the list, and
         * get its region entry.
         */
        let free_ent = self.free.swap_remove(0);
        let mut range = self
            .regions
            .get_mut(&free_ent.address)
            .expect("free list / region tree mismatch");

        /* Mark this region as in-use. */
        range.free = false;

        /* If there's more than a page's worth of free space at the end of
         * this region, add it back as a new region.
         */
        let alloc_start = range.start;
        let alloc_end = range.start + alloc_sz;
        if range.size() - alloc_sz >= 0x1000 {
            let new_range = VirtualMemoryRange::new(alloc_end, range.end);
            range.end = alloc_end;
            drop(range);

            self.add_range(new_range, true);
        }

        self.free.sort_unstable();

        Ok(alloc_start)
    }

    pub fn allocate_at(&mut self, start: usize, end: usize) -> Result<usize, AllocationError> {
        let start = round_to_prev_page(start);
        let end = round_to_next_page(end);

        let alloc_sz = end - start;
        if alloc_sz < 0x1000 {
            return Err(AllocationError::InvalidAllocation);
        }

        /* Do preliminary checks. */
        let opt = self.regions.upper_bound(Bound::Included(&start));
        if opt.is_none() {
            return Err(AllocationError::ReservedMemory);
        }

        let (key, range) = opt.unwrap();
        if !range.free || range.end < end {
            return Err(AllocationError::ReservedMemory);
        }

        let key = *key;
        let mut range = self.regions.remove(&key).unwrap();

        /* Remove the region from the free list and mark it as in use. */
        self.remove_free_list_entry(&range);
        range.free = false;

        if range.start < start && start - range.start >= 0x1000 {
            /* There's extra free space at the start of the region; re-add it */
            self.add_range(VirtualMemoryRange::new(range.start, start), true);
            range.start = start;
        }

        if range.end > end && range.end - end >= 0x1000 {
            /* Same thing, but with extra space at the end of the region */
            self.add_range(VirtualMemoryRange::new(end, range.end), true);
            range.end = end;
        }

        /* Add the allocated region itself. */
        self.add_range(range, false);
        self.free.sort_unstable();

        Ok(start)
    }

    pub fn deallocate(&mut self, start: usize, size: usize) {
        let alloc_sz = round_to_next_page(size);
        let end = start + alloc_sz;

        /*
         * We might modify the start address for the found range when
         * coalescing blocks together, so go ahead and remove the node from the
         * tree.
         */
        let opt = self.regions.remove(&start);
        if opt.is_none() {
            panic!(
                "Attempt to free unallocated virtual memory range {:#016x} - {:#016x}",
                start, end
            );
        }

        let mut range = opt.unwrap();
        if range.free {
            panic!(
                "Attempt to double-free virtual memory range {:#016x} - {:#016x}",
                start, end
            );
        }

        /* Determine if adjacent regions are free; if so, we can merge them. */
        if let Some((key, next)) = self.regions.lower_bound(Bound::Excluded(&start)) {
            /* Remove next range: */
            if next.free && next.start == end {
                let key = *key;
                drop(next);

                let next = self.regions.remove(&key).unwrap();
                range.end = next.end;
                self.remove_free_list_entry(&next);
            }
        }

        if let Some((_, prev)) = self.regions.upper_bound_mut(Bound::Excluded(&start)) {
            /* Remove middle range: */
            if prev.free && prev.end == range.start {
                prev.end = range.end;
            } else {
                self.add_range(range, true);
            }
        } else {
            /* Insert middle range back into region tree / free list: */
            self.add_range(range, true);
        }

        self.free.sort_unstable();
    }
}

unsafe impl Send for VirtualMemoryAllocator {}
unsafe impl Sync for VirtualMemoryAllocator {}

pub unsafe fn initialize(boot_heap_pages: u64) {
    use crate::paging::{KERNEL_BASE, KERNEL_HEAP_BASE};
    let mut l = KERNEL_VMA.init(|| VirtualMemoryAllocator::new()).lock();

    l.register_memory(KERNEL_HEAP_BASE, KERNEL_BASE);
    let mut cur_addr = KERNEL_HEAP_BASE;

    for _ in 0..(boot_heap_pages as usize) {
        l.allocate_at(cur_addr, cur_addr + 0x1000)
            .expect("could not initialize bootstrap pages");

        cur_addr += 0x1000;
    }
}

/// Allocate virtual memory pages from the kernel heap.
///
/// The size of the memory request is in bytes; if the size is not already a
/// multiple of the page size, it will be rounded up accordingly.
pub fn allocate(size: usize) -> Result<usize, AllocationError> {
    KERNEL_VMA.lock().allocate(size)
}

/// Allocate a specific address range from the kernel heap space.
///
/// The given `start` and `end` addresses, if not already page-aligned, will
/// be rounded down and up (respectively) to align them to page boundaries.
pub fn allocate_at(start: usize, end: usize) -> Result<usize, AllocationError> {
    KERNEL_VMA.lock().allocate_at(start, end)
}

/// Deallocate virtual memory pages from the kernel heap.
///
/// The allocation memory address and size must match a previous call
/// to [allocate_kernel_heap_pages] or []
pub fn deallocate(addr: usize, size: usize) {
    KERNEL_VMA.lock().deallocate(addr, size);
}
