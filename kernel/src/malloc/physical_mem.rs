use crate::paging;
use crate::paging::PAGE_MASK;
use crate::structures::AVLTree;

use alloc_crate::rc::Rc;
use alloc_crate::vec::Vec;
use core::cell::{Ref, RefCell, RefMut};
use core::cmp::Ordering;
use core::mem;
use core::ops::Bound;

use crate::lock::LockedGlobal;

use super::{AllocationError, MemoryPageAllocator};

const BUDDY_ALLOC_MAX_SIZE: usize = 0x1000usize << 8; // bytes
const BUDDY_ALLOC_ALIGN_MASK: usize = !(BUDDY_ALLOC_MAX_SIZE - 1);

static KERNEL_PMA: LockedGlobal<PhysicalMemoryAllocator> = LockedGlobal::new();

#[derive(Debug, Clone)]
pub struct BuddyAllocator {
    mem_addr: usize,
    region_end: usize,
    ord_0_bitmap: [u64; 4],
    ord_1_bitmap: [u64; 2],
    ord_2_bitmap: u64,
    hi_ord_bitmap: u64,
    n_blocks: [u16; 9],
    free_bytes: usize,
    usage_list_idx: usize,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum BuddyAllocatorError {
    RegionTooSmall(usize),
    RegionTooLarge(usize),
}

impl BuddyAllocator {
    fn new(addr: usize, region_len: usize) -> Result<BuddyAllocator, BuddyAllocatorError> {
        if region_len < 0x1000 {
            return Err(BuddyAllocatorError::RegionTooSmall(region_len));
        } else if region_len > (0x1000 * 1024) {
            return Err(BuddyAllocatorError::RegionTooLarge(region_len));
        }

        let mut ord = 8u64;
        let mut block_sz = 0x1000usize << 8;
        let mut remaining_region_size = region_len & PAGE_MASK;
        let mut cur_addr = addr;

        let mut allocator = BuddyAllocator {
            mem_addr: addr,
            region_end: addr + region_len,
            ord_0_bitmap: [0; 4],
            ord_1_bitmap: [0; 2],
            ord_2_bitmap: 0,
            hi_ord_bitmap: 0,
            n_blocks: [0; 9],
            free_bytes: 0,
            usage_list_idx: 0,
        };

        while remaining_region_size > 0 {
            if remaining_region_size >= block_sz {
                let block_n = allocator.get_block_for_addr(cur_addr, ord);
                allocator.set_block_state(ord, block_n, true);

                cur_addr += block_sz;
                remaining_region_size -= block_sz;
            } else {
                ord -= 1;
                block_sz >>= 1;
            }
        }

        Ok(allocator)
    }

    fn split_block(&mut self, order: u64, index: usize) {
        if order == 0 || order > 8 {
            panic!("attempted to split block of invalid order {}", order);
        }

        if index > (1 << (8 - order)) {
            panic!(
                "invalid index {} for order {} within buddy allocator",
                index, order
            );
        }

        self.set_block_state(order, index, false);
        self.set_block_state(order - 1, index << 1, true);
        self.set_block_state(order - 1, (index << 1) + 1, true);
    }

    fn find_free_block_single(&self, order: u64) -> Option<usize> {
        for i in 0..(1 << (8 - order)) {
            if self.get_block_state(order, i) {
                return Some(i);
            }
        }

        None
    }

    fn allocate_block(&mut self, order: u64) -> Option<usize> {
        if self.n_blocks[order as usize] > 0 {
            if let Some(idx) = self.find_free_block_single(order) {
                self.set_block_state(order, idx, false);

                return Some(idx);
            }

            panic!(
                "Inconsistent buddy allocator state: could not find free block with count = {}",
                self.n_blocks[order as usize]
            );
        } else {
            for ord in (order + 1)..9 {
                if self.n_blocks[ord as usize] > 0 {
                    let n_levels = ord - order;
                    for i in 0..n_levels {
                        let cur_lvl = ord - i;
                        let block = self.find_free_block_single(cur_lvl).unwrap();
                        self.split_block(cur_lvl, block);
                    }

                    break;
                }
            }

            if let Some(idx) = self.find_free_block_single(order) {
                self.set_block_state(order, idx, false);
                Some(idx)
            } else {
                None
            }
        }
    }

    fn allocate_specific_block(&mut self, order: u64, index: usize) -> bool {
        if order > 8 {
            panic!("attempted to allocate block of invalid order {}", order);
        }

        if index > (1 << (8 - order)) {
            panic!(
                "invalid index {} for order {} within buddy allocator",
                index, order
            );
        }

        if !self.get_block_state(order, index) {
            let mut cur_idx = index;

            /* try to look upwards and see if we can split blocks to make this
             * one free
             */
            for split_ord in (order + 1)..9 {
                cur_idx >>= 1;
                if self.get_block_state(split_ord, cur_idx) {
                    /* Perform the splits */
                    let n_ords = split_ord - order;
                    for i in 0..n_ords {
                        let idx = index >> (n_ords - i);
                        self.split_block(split_ord - i, idx);
                    }

                    /* Allocate the requested block */
                    self.set_block_state(order, index, false);

                    return true;
                }
            }
        } else {
            self.set_block_state(order, index, false);
            return true;
        }

        false
    }

    fn free_block(&mut self, order: u64, index: usize) {
        if order > 8 {
            panic!("attempted to free block of invalid order {}", order);
        }

        if index > (1 << (8 - order)) {
            panic!(
                "invalid index {} for order {} within buddy allocator",
                index, order
            );
        }

        if order < 8 {
            let buddy = index ^ 1;
            if self.get_block_state(order, buddy) {
                self.set_block_state(order, buddy, false);
                self.free_block(order + 1, index >> 1);
            }
        } else {
            self.set_block_state(order, index, true);
        }
    }
    fn get_block_for_addr(&self, addr: usize, order: u64) -> usize {
        let offset = addr - self.mem_addr;
        offset / (0x1000usize << order)
    }

    fn get_addr_for_block(&self, order: u64, index: usize) -> usize {
        let offset = (0x1000usize << order) * index;
        self.mem_addr + offset
    }

    fn get_block_state(&self, order: u64, index: usize) -> bool {
        match order {
            0 => (self.ord_0_bitmap[index / 64] & (1u64 << (index % 64))) != 0,
            1 => (self.ord_1_bitmap[index / 64] & (1u64 << (index % 64))) != 0,
            2 => (self.ord_2_bitmap & (1u64 << index % 64)) != 0,
            3..=8 => {
                let t = (1u64 << (8 - order)) - 1;
                let bit = t + ((index as u64) & t);
                (self.hi_ord_bitmap & (1 << bit)) != 0
            }
            _ => panic!("invalid order {} for buddy allocator", order),
        }
    }

    fn set_block_state(&mut self, order: u64, index: usize, state: bool) {
        if state {
            self.n_blocks[order as usize] += 1;
            self.free_bytes += (0x1000 << order) as usize;
        } else {
            self.n_blocks[order as usize] -= 1;
            self.free_bytes -= (0x1000 << order) as usize;
        }

        match order {
            0 => {
                if state {
                    self.ord_0_bitmap[index / 64] |= 1u64 << (index % 64);
                } else {
                    self.ord_0_bitmap[index / 64] &= !(1u64 << (index % 64));
                }
            }
            1 => {
                if state {
                    self.ord_1_bitmap[index / 64] |= 1u64 << (index % 64);
                } else {
                    self.ord_1_bitmap[index / 64] &= !(1u64 << (index % 64));
                }
            }
            2 => {
                if state {
                    self.ord_2_bitmap |= 1u64 << index % 64;
                } else {
                    self.ord_2_bitmap &= !(1u64 << index % 64);
                }
            }
            3..=8 => {
                let t = 1u64 << (8 - order);
                let bit = (t - 1) + ((index as u64) % t);
                if state {
                    self.hi_ord_bitmap |= 1u64 << bit;
                } else {
                    self.hi_ord_bitmap &= !(1u64 << bit);
                }
            }
            _ => panic!("invalid order {} for buddy allocator", order),
        }
    }

    fn round_allocation_size(size: usize) -> u64 {
        for i in 0..9 {
            if (0x1000usize << i) >= size {
                return i;
            }
        }

        9
    }

    pub fn allocate(&mut self, order: u64) -> Option<usize> {
        if order > 8 {
            return None;
        }

        let ret = self
            .allocate_block(order)
            .map(|idx| self.get_addr_for_block(order, idx));

        ret
    }

    pub fn allocate_at(&mut self, addr: usize, order: u64) -> Option<usize> {
        if order > 8 {
            return None;
        }

        let block = self.get_block_for_addr(addr, order);
        if self.allocate_specific_block(order, block) {
            Some(self.get_addr_for_block(order, block))
        } else {
            None
        }
    }

    pub fn deallocate(&mut self, addr: usize, order: u64) {
        if order > 8 {
            return;
        }

        let block_idx = self.get_block_for_addr(addr, order);
        self.free_block(order, block_idx);
    }

    pub fn get_range(allocator: &BuddyAllocator) -> (usize, usize) {
        (allocator.mem_addr, allocator.region_end)
    }
}

#[derive(Debug)]
pub struct FreeMemoryRange {
    range_start: usize,
    range_end: usize,
}

impl FreeMemoryRange {
    fn new(range_start: usize, range_end: usize) -> FreeMemoryRange {
        FreeMemoryRange {
            range_start,
            range_end,
        }
    }

    fn size(&self) -> usize {
        self.range_end - self.range_start
    }
}

impl PartialOrd for FreeMemoryRange {
    fn partial_cmp(&self, other: &FreeMemoryRange) -> Option<Ordering> {
        Some(self.size().cmp(&other.size()).reverse())
    }
}

impl Ord for FreeMemoryRange {
    fn cmp(&self, other: &FreeMemoryRange) -> Ordering {
        self.size().cmp(&other.size()).reverse()
    }
}

impl PartialEq for FreeMemoryRange {
    fn eq(&self, other: &FreeMemoryRange) -> bool {
        self.size() == other.size()
    }
}

impl Eq for FreeMemoryRange {}

#[derive(Debug, Clone)]
#[repr(transparent)]
pub struct BuddyAllocatorWrapper {
    allocator: Rc<RefCell<BuddyAllocator>>,
}

impl BuddyAllocatorWrapper {
    fn new(addr: usize, region_len: usize) -> BuddyAllocatorWrapper {
        BuddyAllocatorWrapper {
            allocator: Rc::new(RefCell::new(BuddyAllocator::new(addr, region_len).unwrap())),
        }
    }

    fn borrow(&self) -> Ref<'_, BuddyAllocator> {
        self.allocator.borrow()
    }

    fn borrow_mut(&self) -> RefMut<'_, BuddyAllocator> {
        self.allocator.borrow_mut()
    }

    fn usage_list_idx(&self) -> usize {
        self.allocator.borrow().usage_list_idx
    }

    fn set_usage_idx(&self, idx: usize) {
        let mut l = self.allocator.borrow_mut();
        l.usage_list_idx = idx;
    }

    fn swap_usage_indices(&self, other: &BuddyAllocatorWrapper) {
        use core::ptr;

        if ptr::eq(self, other) {
            return;
        }

        let mut r1 = self.borrow_mut();
        let mut r2 = other.borrow_mut();

        mem::swap(&mut r1.usage_list_idx, &mut r2.usage_list_idx);
    }

    fn free_bytes(&self) -> usize {
        self.allocator.borrow().free_bytes
    }

    fn start_address(&self) -> usize {
        self.allocator.borrow().mem_addr
    }

    fn get_range(&self) -> (usize, usize) {
        let l = self.borrow();
        (l.mem_addr, l.region_end)
    }

    fn allocate(&self, order: u64) -> Option<usize> {
        self.borrow_mut().allocate(order)
    }

    fn allocate_at(&self, addr: usize, order: u64) -> Option<usize> {
        self.borrow_mut().allocate_at(addr, order)
    }

    fn deallocate(&self, addr: usize, order: u64) {
        self.borrow_mut().deallocate(addr, order)
    }
}

#[derive(Debug)]
pub struct PhysicalMemoryRange {
    range_start: usize,
    range_end: usize,
    free: Vec<FreeMemoryRange>,
    allocator_tree: AVLTree<usize, BuddyAllocatorWrapper>, /* Organized by memory range address */
    allocator_usage_list: Vec<BuddyAllocatorWrapper>,      /* Sorted by free space amount. */
}

impl PhysicalMemoryRange {
    fn new(addr: usize, len: usize) -> PhysicalMemoryRange {
        if addr & 0x1000 != 0 {
            panic!(
                "attempted to create unaligned physical memory range at {:#016x}",
                addr
            );
        }

        let new_range = PhysicalMemoryRange {
            range_start: addr,
            range_end: addr + len,
            free: vec![FreeMemoryRange::new(addr, addr + len)],
            allocator_tree: AVLTree::<usize, BuddyAllocatorWrapper>::new(),
            allocator_usage_list: Vec::new(),
        };

        new_range
    }

    fn add_allocator(&mut self, wrapper: BuddyAllocatorWrapper) {
        let idx = self.allocator_usage_list.len();
        wrapper.set_usage_idx(idx);

        self.allocator_usage_list.push(wrapper.clone());
        self.usage_list_sift_up(idx);

        self.allocator_tree
            .insert(wrapper.start_address(), wrapper)
            .expect("could not add allocator for physical memory range");
    }

    fn usage_list_sift_up(&mut self, idx: usize) {
        if idx == 0 {
            return;
        }

        let parent_idx = (idx - 1) >> 1;
        let parent = &self.allocator_usage_list[parent_idx];
        let child = &self.allocator_usage_list[idx];

        if child.free_bytes() > parent.free_bytes() {
            child.swap_usage_indices(parent);

            drop(parent);
            drop(child);

            self.allocator_usage_list.swap(idx, parent_idx);
            return self.usage_list_sift_up(parent_idx);
        }
    }

    fn usage_list_sift_down(&mut self, idx: usize) {
        if self.allocator_usage_list.len() >= idx {
            return;
        }

        let mut swap_idx = idx;
        let mut swap_child: &BuddyAllocatorWrapper = &self.allocator_usage_list[idx];

        if let Some(c1) = self.allocator_usage_list.get((idx << 1) + 1) {
            if c1.free_bytes() > swap_child.free_bytes() {
                swap_idx = (idx << 1) + 1;
                swap_child = &self.allocator_usage_list[swap_idx];
            }
        }

        if let Some(c2) = self.allocator_usage_list.get((idx << 1) + 2) {
            if c2.free_bytes() > swap_child.free_bytes() {
                swap_idx = (idx << 1) + 2;
                swap_child = &self.allocator_usage_list[swap_idx];
            }
        }

        if swap_idx != idx {
            self.allocator_usage_list[idx].swap_usage_indices(swap_child);
            drop(swap_child);

            self.allocator_usage_list.swap(swap_idx, idx);
            return self.usage_list_sift_down(swap_idx);
        }
    }

    /// Allocate a specific range of addresses within this PhysicalMemoryRange.
    ///
    /// Buffers allocated at specific addresses must not cross megabyte boundaries!
    pub fn allocate_at(
        &mut self,
        range_start: usize,
        range_end: usize,
    ) -> Result<usize, AllocationError> {
        let allocators_start =
            self.range_start + ((range_start - self.range_start) & BUDDY_ALLOC_ALIGN_MASK);

        let order = BuddyAllocator::round_allocation_size(range_end - range_start);

        if let Some((_, node)) = self
            .allocator_tree
            .upper_bound_mut(Bound::Included(&range_start))
        {
            let (start_address, end_address) = node.get_range();
            if start_address <= range_start && end_address >= range_end {
                let ret = node.allocate_at(range_start, order);
                let idx = node.usage_list_idx();
                drop(node);

                self.usage_list_sift_down(idx);

                return ret.ok_or(AllocationError::NoFreePhysicalMemory);
            }
        }

        let allocators_end: usize;
        if allocators_start + BUDDY_ALLOC_MAX_SIZE <= self.range_end {
            allocators_end = allocators_start + BUDDY_ALLOC_MAX_SIZE;
        } else {
            allocators_end = self.range_end;
        }

        /* Sweep through the free list and see if any currently-free areas
         * intersect the range.
         */
        let mut intersect_range: Option<usize> = None;
        for (i, cur) in self.free.iter().enumerate() {
            if cur.range_start <= allocators_start && cur.range_end >= allocators_end {
                intersect_range = Some(i);
                break;
            }

            /* We don't handle partial overlaps for now. */
        }

        if intersect_range.is_none() {
            return Err(AllocationError::InvalidAllocation);
        }

        let range = self.free.swap_remove(intersect_range.unwrap());
        if range.range_start < allocators_start && allocators_start - range.range_start >= 0x1000 {
            self.free
                .push(FreeMemoryRange::new(range.range_start, allocators_start));
        }

        if allocators_end < range.range_end && range.range_end - allocators_end >= 0x1000 {
            self.free
                .push(FreeMemoryRange::new(allocators_end, range.range_end));
        }

        self.free.sort_unstable();

        /* Insert our new allocator. */
        let wrapper =
            BuddyAllocatorWrapper::new(allocators_start, allocators_end - allocators_start);
        let ret = wrapper.allocate_at(range_start, order);
        self.add_allocator(wrapper);

        return ret.ok_or(AllocationError::NoFreePhysicalMemory);
    }

    pub fn allocate(&mut self, size: usize) -> Result<usize, AllocationError> {
        let order = BuddyAllocator::round_allocation_size(size);

        if let Some(wrapper) = self.allocator_usage_list.get(0) {
            let mut allocator = wrapper.borrow_mut();
            if let Some(addr) = allocator.allocate(order) {
                let idx = allocator.usage_list_idx;
                drop(allocator);
                drop(wrapper);

                self.usage_list_sift_down(idx);
                return Ok(addr);
            }
        }

        if let Some(cur_free_head) = self.free.get_mut(0) {
            let mut new_allocator_sz = cur_free_head.range_end - cur_free_head.range_start;
            if new_allocator_sz > BUDDY_ALLOC_MAX_SIZE {
                new_allocator_sz = BUDDY_ALLOC_MAX_SIZE;
            }

            let start_addr = cur_free_head.range_start;
            cur_free_head.range_start += new_allocator_sz;
            if cur_free_head.range_start >= cur_free_head.range_end {
                drop(cur_free_head);

                self.free.swap_remove(0);
                self.free.sort_unstable();
            }

            let wrapper = BuddyAllocatorWrapper::new(start_addr, new_allocator_sz);
            let ret = wrapper.allocate(order);
            self.add_allocator(wrapper);

            return ret.ok_or(AllocationError::NoFreePhysicalMemory);
        }

        Err(AllocationError::NoFreePhysicalMemory)
    }

    pub fn deallocate(&mut self, addr: usize, size: usize) {
        if self.allocator_tree.is_empty() {
            return;
        }

        let order = BuddyAllocator::round_allocation_size(size);
        if let Some((_, wrapper)) = self.allocator_tree.upper_bound_mut(Bound::Included(&addr)) {
            wrapper.deallocate(addr, order);
            let idx = wrapper.usage_list_idx();

            drop(wrapper);
            self.usage_list_sift_up(idx);
        }
    }
}

#[derive(Debug)]
pub struct PhysicalMemoryAllocator {
    ranges: Vec<PhysicalMemoryRange>,
}

impl PhysicalMemoryAllocator {
    pub fn new() -> PhysicalMemoryAllocator {
        PhysicalMemoryAllocator { ranges: Vec::new() }
    }

    pub unsafe fn register_range(&mut self, addr: usize, len: usize) {
        self.ranges.push(PhysicalMemoryRange::new(addr, len));
    }

    pub fn allocate(&mut self, size: usize) -> Result<usize, AllocationError> {
        for r in self.ranges.iter_mut() {
            if let Ok(addr) = r.allocate(size) {
                return Ok(addr);
            }
        }

        Err(AllocationError::NoFreePhysicalMemory)
    }

    pub fn allocate_at(&mut self, addr: usize, size: usize) -> Result<usize, AllocationError> {
        for r in self.ranges.iter_mut() {
            if r.range_start <= addr && r.range_end >= (addr + size) {
                return r.allocate_at(addr, addr + size);
            }
        }

        Err(AllocationError::ReservedMemory)
    }

    pub fn deallocate(&mut self, addr: usize, size: usize) {
        for r in self.ranges.iter_mut() {
            if addr >= r.range_start && addr < r.range_end {
                r.deallocate(addr, size);
            }
        }
    }
}

unsafe impl Send for PhysicalMemoryAllocator {}

pub fn initialize() {
    KERNEL_PMA.init(|| PhysicalMemoryAllocator::new());
}

/// Register a range of physical memory with the allocator.
pub unsafe fn register(addr: usize, len: usize) {
    KERNEL_PMA.lock().register_range(addr, len);
}

/// Allocate a given amount of physical memory in bytes.
///
/// The given size must be a multiple of the page size!
pub fn allocate(size: usize) -> Result<usize, AllocationError> {
    KERNEL_PMA.lock().allocate(size)
}

/// Allocate a given amount of physical memory in bytes at a specific address.
///
/// The given size must be a multiple of the page size, and the allocated
/// buffer must not cross a megabyte boundary.
pub unsafe fn allocate_at(addr: usize, size: usize) -> Result<usize, AllocationError> {
    KERNEL_PMA.lock().allocate_at(addr, size)
}

/// Deallocate a previously-allocated physical memory range.
///
/// The size passed to this function must be the same size as
/// passed to the original allocation call!
pub unsafe fn deallocate(addr: usize, size: usize) {
    KERNEL_PMA.lock().deallocate(addr, size);
}

impl MemoryPageAllocator for PhysicalMemoryAllocator {
    fn allocate(size: usize) -> Result<usize, AllocationError> {
        allocate(size)
    }

    unsafe fn allocate_at(addr: usize, size: usize) -> Result<usize, AllocationError> {
        let order = BuddyAllocator::round_allocation_size(paging::round_to_next_page(size));
        let alloc_end = addr + (0x1000usize << order);

        if (addr & BUDDY_ALLOC_ALIGN_MASK) != (alloc_end & BUDDY_ALLOC_ALIGN_MASK) {
            panic!("physical address allocation request for {:#016x} ({:#08x} bytes) crosses megabyte boundaries", addr, size);
        }

        allocate_at(addr, size)
    }

    unsafe fn deallocate(addr: usize, size: usize) {
        deallocate(addr, size)
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::malloc;
    use crate::malloc::tests::TestAlloc;
    use crate::rng::MersenneTwister64;
    use crate::test::TEST_SEED;

    use alloc_crate::vec::Vec;
    use kernel_test_macro::kernel_test;

    const PMA_TEST_ALLOCS: usize = 500;
    const PMA_TEST_MAX_PAGE_ALLOC: u64 = 20;

    #[kernel_test]
    fn test_pma() {
        let mut rng = MersenneTwister64::new(TEST_SEED);
        let mut allocs: Vec<TestAlloc> = Vec::with_capacity(PMA_TEST_ALLOCS);

        for i in 0..PMA_TEST_ALLOCS {
            let n_pages = rng.generate() % PMA_TEST_MAX_PAGE_ALLOC;
            let size = (n_pages as usize) * 0x1000;

            let addr = match allocate(size) {
                Ok(a) => a,
                Err(e) => panic!(
                    "alloc {} failed (seed: {:#x}, size {:#x}) - {:?}",
                    i, TEST_SEED, size, e
                ),
            };

            allocs.push(TestAlloc { addr, size });
        }

        allocs.sort();
        for i in 0..(allocs.len() - 1) {
            // ensure this alloc does not overlap the next one
            let this_end = allocs[i].addr + allocs[i].size;
            let next_start = allocs[i + 1].addr;

            // next_start >= allocs[i].0 is guaranteed because we sorted the
            // allocs list
            assert!(
                next_start >= this_end,
                "found overlapping allocations: {} and {}",
                allocs[i],
                allocs[i + 1]
            );
        }

        for alloc in allocs {
            unsafe {
                deallocate(alloc.addr, alloc.size);
            }
        }
    }
}
