use crate::avl_tree::AVLTree;
use crate::paging;
use crate::paging::PAGE_MASK;

use alloc::vec::Vec;
use core::cmp::Ordering;

use lazy_static::lazy_static;
use spin::Mutex;

const BUDDY_ALLOC_MAX_SIZE: usize = 0x1000usize << 8; // bytes
const BUDDY_ALLOC_ALIGN_MASK: usize = !(BUDDY_ALLOC_MAX_SIZE - 1);

lazy_static! {
    pub static ref KERNEL_PHYS_ALLOC: Mutex<PhysicalMemoryAllocator> =
        Mutex::new(PhysicalMemoryAllocator { ranges: Vec::new() });
}

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

        if order < 8 && index != 255 && self.get_block_state(order, index + 1) {
            self.set_block_state(order, index + 1, false);
            self.free_block(order + 1, index >> 1);
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
                let t = 1u64 << (8 - order);
                let bit = (t - 1) + ((index as u64) % t);
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

    pub unsafe fn allocate(&mut self, order: u64) -> Option<usize> {
        if order > 8 {
            return None;
        }

        let ret = self
            .allocate_block(order)
            .map(|idx| self.get_addr_for_block(order, idx));

        ret
    }

    pub unsafe fn allocate_at(&mut self, addr: usize, order: u64) -> Option<usize> {
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

    pub unsafe fn deallocate(&mut self, addr: usize, order: u64) {
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

impl PartialEq for BuddyAllocator {
    fn eq(&self, other: &BuddyAllocator) -> bool {
        self.mem_addr == other.mem_addr
    }
}

impl Eq for BuddyAllocator {}

impl PartialOrd for BuddyAllocator {
    fn partial_cmp(&self, other: &BuddyAllocator) -> Option<Ordering> {
        Some(self.mem_addr.cmp(&other.mem_addr))
    }
}

impl Ord for BuddyAllocator {
    fn cmp(&self, other: &BuddyAllocator) -> Ordering {
        self.mem_addr.cmp(&other.mem_addr)
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
}

#[derive(Debug)]
pub struct PhysicalMemoryRange {
    range_start: usize,
    range_end: usize,
    free: Vec<FreeMemoryRange>,
    allocator_tree: AVLTree<BuddyAllocator, usize>, /* Organized by memory range address */
    allocator_usage_list: Vec<*mut BuddyAllocator>, /* Sorted by free space amount. */
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
            allocator_tree: AVLTree::<BuddyAllocator, usize>::new(),
            allocator_usage_list: Vec::new(),
        };

        new_range
    }

    unsafe fn usage_list_sift_up(&mut self, idx: usize) {
        use core::mem::swap;
        if idx == 0 {
            return;
        }

        let parent_idx = (idx - 1) >> 1;
        let parent = self.allocator_usage_list[parent_idx];
        let child = self.allocator_usage_list[idx];

        if (*child).free_bytes > (*parent).free_bytes {
            let t = self.allocator_usage_list[parent_idx];
            self.allocator_usage_list[parent_idx] = self.allocator_usage_list[idx];
            self.allocator_usage_list[idx] = t;

            swap(&mut (*child).usage_list_idx, &mut (*parent).usage_list_idx);
            return self.usage_list_sift_up(parent_idx);
        }
    }

    unsafe fn usage_list_sift_down(&mut self, idx: usize) {
        use core::mem::swap;
        let mut swap_idx = idx;

        if let Some(c1) = self.allocator_usage_list.get_mut((idx << 1) + 1) {
            let c1 = *c1;
            if (*c1).free_bytes > (*self.allocator_usage_list[swap_idx]).free_bytes {
                swap_idx = (idx << 1) + 1;
            }
        }

        if let Some(c2) = self.allocator_usage_list.get_mut((idx << 1) + 2) {
            let c2 = *c2;
            if (*c2).free_bytes > (*self.allocator_usage_list[swap_idx]).free_bytes {
                swap_idx = (idx << 1) + 2;
            }
        }

        if swap_idx != idx {
            let cur = self.allocator_usage_list[idx];
            let larger = self.allocator_usage_list[swap_idx];

            let t = self.allocator_usage_list[swap_idx];
            self.allocator_usage_list[swap_idx] = self.allocator_usage_list[idx];
            self.allocator_usage_list[idx] = t;

            swap(&mut (*cur).usage_list_idx, &mut (*larger).usage_list_idx);
            return self.usage_list_sift_up(swap_idx);
        }
    }

    /// Allocate a specific range of addresses within this PhysicalMemoryRange.
    ///
    /// Buffers allocated at specific addresses must not cross megabyte boundaries!
    pub unsafe fn allocate_at(&mut self, range_start: usize, range_end: usize) -> Option<usize> {
        let allocators_start =
            self.range_start + ((range_start - self.range_start) & BUDDY_ALLOC_ALIGN_MASK);
        let order = BuddyAllocator::round_allocation_size(range_end - range_start);
        let p = self as *mut PhysicalMemoryRange;

        if let Some(node) = self
            .allocator_tree
            .search_interval_mut(range_start, BuddyAllocator::get_range)
        {
            if node.mem_addr <= range_start && node.region_end >= range_end {
                let ret = node.allocate_at(range_start, order);
                (*p).usage_list_sift_down(node.usage_list_idx);

                return ret;
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
         * If any do, add new allocators to cover the intersecting areas.
         */

        let mut insert_range: Option<FreeMemoryRange> = None;
        for cur in self.free.iter_mut() {
            if cur.range_start == allocators_start && cur.range_end == allocators_end {
                /* Exactly intersecting ranges: delete this range. */
                cur.range_end = cur.range_start;
                break;
            } else if cur.range_start <= allocators_start && cur.range_end >= allocators_end {
                /* Current free area completely contains the forbidden region */
                insert_range = Some(FreeMemoryRange::new(allocators_end, cur.range_end));
                cur.range_end = allocators_start;
                break;
            } else if allocators_end > cur.range_start && cur.range_end > allocators_start {
                /* Otherwise intersecting ranges: */
                if cur.range_start <= allocators_start {
                    cur.range_end = allocators_start;
                } else if cur.range_end >= allocators_end {
                    cur.range_start = allocators_end;
                }
            }
        }

        if let Some(r) = insert_range {
            self.free.push(r);
        }

        /* Sweep through the free list _again_, double checking to ensure we didn't leave
         * any invalid free regions.
         */
        self.free
            .retain(|range| range.range_start < range.range_end);

        /* Insert our new allocator. */
        let new_allocator =
            BuddyAllocator::new(allocators_start, allocators_end - allocators_start).unwrap();
        let r = self
            .allocator_tree
            .insert(new_allocator.mem_addr, new_allocator);

        r.usage_list_idx = self.allocator_usage_list.len();

        self.allocator_usage_list.push(r as *mut BuddyAllocator);
        let ret = r.allocate_at(range_start, order);
        self.usage_list_sift_up(self.allocator_usage_list.len() - 1);

        return ret;
    }

    pub fn allocate(&mut self, size: usize) -> Option<usize> {
        let order = BuddyAllocator::round_allocation_size(size);
        unsafe {
            if let Some(head_allocator) = self.allocator_usage_list.get_mut(0) {
                let head_allocator = *head_allocator;
                if let Some(addr) = (*head_allocator).allocate(order) {
                    self.usage_list_sift_down((*head_allocator).usage_list_idx);
                    return Some(addr);
                }
            }

            if let Some(cur_free_head) = self.free.get_mut(0) {
                let mut new_allocator_sz = cur_free_head.range_end - cur_free_head.range_start;
                if new_allocator_sz > BUDDY_ALLOC_MAX_SIZE {
                    new_allocator_sz = BUDDY_ALLOC_MAX_SIZE;
                }

                let new_allocator =
                    BuddyAllocator::new(cur_free_head.range_start, new_allocator_sz).unwrap();

                cur_free_head.range_start += new_allocator_sz;
                if cur_free_head.range_start >= cur_free_head.range_end {
                    drop(cur_free_head);
                    self.free.swap_remove(0);
                }

                let r = self
                    .allocator_tree
                    .insert(new_allocator.mem_addr, new_allocator);
                r.usage_list_idx = self.allocator_usage_list.len();
                self.allocator_usage_list.push(r as *mut BuddyAllocator);

                let ret = r.allocate(order);
                self.usage_list_sift_up(self.allocator_usage_list.len() - 1);

                return ret;
            }
        }

        None
    }

    pub unsafe fn deallocate(&mut self, addr: usize, size: usize) {
        if self.allocator_tree.is_empty() {
            return;
        }

        let p = self as *mut PhysicalMemoryRange;
        let order = BuddyAllocator::round_allocation_size(size);
        if let Some(node) = self
            .allocator_tree
            .search_interval_mut(addr, BuddyAllocator::get_range)
        {
            node.deallocate(addr, order);
            (*p).usage_list_sift_up(node.usage_list_idx);
        }
    }
}

#[derive(Debug)]
pub struct PhysicalMemoryAllocator {
    ranges: Vec<PhysicalMemoryRange>,
}

impl PhysicalMemoryAllocator {
    pub unsafe fn register_range(&mut self, addr: usize, len: usize) {
        self.ranges.push(PhysicalMemoryRange::new(addr, len));
    }

    pub unsafe fn allocate(&mut self, size: usize) -> Option<usize> {
        for r in self.ranges.iter_mut() {
            if let Some(addr) = r.allocate(size) {
                return Some(addr);
            }
        }

        None
    }

    pub unsafe fn allocate_at(&mut self, addr: usize, size: usize) -> Option<usize> {
        for r in self.ranges.iter_mut() {
            if r.range_start <= addr && r.range_end >= (addr + size) {
                return r.allocate_at(addr, addr + size);
            }
        }

        None
    }

    pub unsafe fn deallocate(&mut self, addr: usize, size: usize) {
        for r in self.ranges.iter_mut() {
            if addr >= r.range_start && addr <= r.range_end {
                r.deallocate(addr, size);
            }
        }
    }
}

unsafe impl Send for PhysicalMemoryAllocator {}

/// Register a range of physical memory with the allocator.
pub unsafe fn register_physical_memory(addr: usize, len: usize) {
    let mut l = KERNEL_PHYS_ALLOC.lock();
    l.register_range(addr, len);
}

/// Allocate a given amount of physical memory in bytes.
///
/// The given size must be a multiple of the page size!
pub unsafe fn allocate_physical_memory(size: usize) -> Option<usize> {
    let mut l = KERNEL_PHYS_ALLOC.lock();
    l.allocate(size)
}

/// Allocate a given amount of physical memory in bytes at a specific address.
///
/// The given size must be a multiple of the page size, and the allocated
/// buffer must not cross a megabyte boundary.
pub unsafe fn allocate_physical_memory_at(addr: usize, size: usize) -> Option<usize> {
    let mut l = KERNEL_PHYS_ALLOC.lock();
    l.allocate_at(addr, size)
}

/// Deallocate a previously-allocated physical memory range.
///
/// The size passed to this function must be the same size as
/// passed to the original allocation call!
pub unsafe fn deallocate_physical_memory(addr: usize, size: usize) {
    let mut l = KERNEL_PHYS_ALLOC.lock();
    l.deallocate(addr, size);
}

/// Represents an owned, allocated block of physical memory.
///
/// This can be used as a safer interface to the physical memory allocator;
/// deallocating physical memory correctly is handled automatically via
/// Drop.
#[derive(Debug)]
pub struct PhysicalMemory {
    address: usize,
    size: usize,
}

impl PhysicalMemory {
    /// Allocate a specific
    pub fn new(size: usize) -> Option<PhysicalMemory> {
        let alloc_sz;
        if size & 0xFFF != 0 {
            alloc_sz = (size & PAGE_MASK) + 0x1000;
        } else {
            alloc_sz = size;
        }

        unsafe {
            allocate_physical_memory(alloc_sz).map(|address| PhysicalMemory {
                address,
                size: alloc_sz,
            })
        }
    }

    pub fn new_at(addr: usize, size: usize) -> Option<PhysicalMemory> {
        let addr = addr & PAGE_MASK;

        let alloc_sz;
        if size & 0xFFF != 0 {
            alloc_sz = (size & PAGE_MASK) + 0x1000;
        } else {
            alloc_sz = size;
        }

        let order = BuddyAllocator::round_allocation_size(alloc_sz);
        let alloc_end = addr + (0x1000usize << order);

        if (addr & BUDDY_ALLOC_ALIGN_MASK) != (alloc_end & BUDDY_ALLOC_ALIGN_MASK) {
            panic!("physical address allocation request for {:#016x} ({:#08x} bytes) crosses megabyte boundaries", addr, size);
        }

        unsafe {
            allocate_physical_memory_at(addr, alloc_sz).map(|address| PhysicalMemory {
                address,
                size: alloc_sz,
            })
        }
    }

    pub fn address(&self) -> usize {
        self.address & PAGE_MASK
    }

    pub fn size(&self) -> usize {
        self.size
    }

    pub fn as_u64(&self) -> u64 {
        self.address() as u64
    }

    pub fn as_ptr<T>(&self) -> *const T {
        paging::physical_address(self.address()).unwrap()
    }

    pub fn as_mut_ptr<T>(&self) -> *mut T {
        paging::physical_address_mut(self.address()).unwrap()
    }
}

impl Drop for PhysicalMemory {
    fn drop(&mut self) {
        unsafe { deallocate_physical_memory(self.address(), self.size()) }
    }
}
