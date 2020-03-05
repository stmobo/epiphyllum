use alloc::alloc::Layout;
use alloc::boxed::Box;
use alloc::vec::Vec;
use core::cmp::Ordering;
use core::ptr;

use crate::paging;
use crate::paging::PAGE_MASK;

use lazy_static::lazy_static;
use spin::Mutex;

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
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum BuddyAllocatorError {
    RegionTooSmall,
    RegionTooLarge,
}

impl BuddyAllocator {
    fn new(addr: usize, region_len: usize) -> Result<BuddyAllocator, BuddyAllocatorError> {
        if region_len < 0x1000 {
            return Err(BuddyAllocatorError::RegionTooSmall);
        } else if region_len > (0x1000 * 1024) {
            return Err(BuddyAllocatorError::RegionTooLarge);
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
        };

        while remaining_region_size > 0 {
            if remaining_region_size >= block_sz {
                let block_n = allocator.get_block_for_addr(cur_addr, ord);
                allocator.set_block_state(ord, block_n, true);
                allocator.n_blocks[ord as usize] += 1;

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
        self.n_blocks[order as usize] -= 1;
        self.n_blocks[(order - 1) as usize] += 2;
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
                self.n_blocks[order as usize] -= 1;

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
                self.n_blocks[order as usize] -= 1;
                Some(idx)
            } else {
                None
            }
        }
    }

    fn mark_range_used_recursive(
        &mut self,
        order: u64,
        index: usize,
        start_addr: usize,
        end_addr: usize,
    ) {
        let block_start = self.get_addr_for_block(order, index);
        let block_end = self.get_addr_for_block(order, index + 1);

        if ((block_end == start_addr) && (end_addr == block_start))
            || ((block_end > start_addr) && (end_addr > block_start))
        {
            /* Specified range intersects (or exactly overlaps) with this block.
             * Subdivide and attempt to mark children as in-use.
             */

            if order > 0 {
                if self.get_block_state(order, index) {
                    self.split_block(order, index);
                }

                self.mark_range_used_recursive(order - 1, index << 1, start_addr, end_addr);
                self.mark_range_used_recursive(order - 1, (index << 1) + 1, start_addr, end_addr);
            } else {
                self.set_block_state(order, index, false);
            }
        }
    }

    pub fn mark_range_used(&mut self, start_addr: usize, end_addr: usize) {
        self.mark_range_used_recursive(8, 0, start_addr, end_addr);
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
            self.n_blocks[order as usize] -= 1;
            self.free_block(order + 1, index >> 1);
        } else {
            self.set_block_state(order, index, true);
            self.n_blocks[order as usize] += 1;
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

        self.allocate_block(order)
            .map(|idx| self.get_addr_for_block(order, idx))
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

impl PartialOrd for BuddyAllocator {
    fn partial_cmp(&self, other: &BuddyAllocator) -> Option<Ordering> {
        Some(self.mem_addr.cmp(&other.mem_addr))
    }
}

#[derive(Debug, Clone)]
pub struct AVLTree<T: PartialOrd> {
    data: T,
    parent: *mut AVLTree<T>,
    left: *mut AVLTree<T>,
    right: *mut AVLTree<T>,
    balance: i8,
}

impl<T: PartialOrd> AVLTree<T> {
    fn new(data: T, parent: *mut AVLTree<T>) -> AVLTree<T> {
        AVLTree {
            data,
            parent,
            left: ptr::null_mut(),
            right: ptr::null_mut(),
            balance: 0,
        }
    }

    fn search<F>(&mut self, key: usize, key_func: F) -> Option<&mut AVLTree<T>>
    where
        F: Fn(&T) -> (usize, usize),
    {
        let mut cur: *mut AVLTree<T> = self as *mut AVLTree<T>;

        loop {
            unsafe {
                let (key_ival_start, key_ival_end) = key_func(&(*cur).data);

                if key >= key_ival_start && key < key_ival_end {
                    return Some(&mut *cur);
                }

                if key < key_ival_start {
                    if (*cur).left != ptr::null_mut() {
                        cur = (*cur).left;
                    } else {
                        return None;
                    }
                } else {
                    if (*cur).right != ptr::null_mut() {
                        cur = (*cur).right;
                    } else {
                        return None;
                    }
                }
            }
        }
    }

    /// Insert a new node into this tree.
    ///
    /// Returns a tuple consisting of:
    ///   - a pointer to the new root node, and
    ///   - a reference to the inserted element.
    fn insert(&mut self, data: T) -> (*mut AVLTree<T>, &mut AVLTree<T>) {
        let mut cur: *mut AVLTree<T> = self as *mut AVLTree<T>;
        let new_node: *mut AVLTree<T>;

        unsafe {
            use alloc::alloc::alloc;
            let layout = Layout::new::<AVLTree<T>>();
            new_node = alloc(layout) as *mut AVLTree<T>;
            *new_node = AVLTree {
                data,
                parent: cur,
                left: ptr::null_mut(),
                right: ptr::null_mut(),
                balance: 0,
            };
        }

        loop {
            unsafe {
                if (*new_node).data < (*cur).data {
                    if (*cur).left != ptr::null_mut() {
                        cur = (*cur).left;
                    } else {
                        /* Insert as left subtree. */
                        (*cur).left = new_node;
                        break;
                    }
                } else {
                    if (*cur).right != ptr::null_mut() {
                        cur = (*cur).right;
                    } else {
                        (*cur).right = new_node;
                        break;
                    }
                }
            }
        }

        unsafe {
            (*new_node).parent = cur;
            let new_parent = (*new_node).retrace_insert();
            (new_parent, &mut *new_node)
        }
    }

    unsafe fn right_rotate(&mut self) -> *mut AVLTree<T> {
        let pivot = self.left;

        if pivot != ptr::null_mut() {
            self.left = (*pivot).right;
            (*pivot).right = self as *mut AVLTree<T>;

            let prev_parent = self.parent;
            if prev_parent != ptr::null_mut() {
                if (*prev_parent).left == (self as *mut AVLTree<T>) {
                    (*prev_parent).left = pivot;
                } else {
                    (*prev_parent).right = pivot;
                }
            }

            (*pivot).parent = prev_parent;
            self.parent = pivot;
        }

        pivot
    }

    unsafe fn left_rotate(&mut self) -> *mut AVLTree<T> {
        let pivot = self.right;

        if pivot != ptr::null_mut() {
            self.right = (*pivot).left;
            (*pivot).left = self as *mut AVLTree<T>;

            let prev_parent = self.parent;
            if prev_parent != ptr::null_mut() {
                if (*prev_parent).left == (self as *mut AVLTree<T>) {
                    (*prev_parent).left = pivot;
                } else {
                    (*prev_parent).right = pivot;
                }
            }

            (*pivot).parent = prev_parent;
            self.parent = pivot;
        }

        pivot
    }

    fn recurse_to_root(&mut self) -> *mut AVLTree<T> {
        if self.parent == ptr::null_mut() {
            return self as *mut AVLTree<T>;
        } else {
            unsafe { (*self.parent).recurse_to_root() }
        }
    }

    /// Retracing loop after subtree height increases.
    ///
    /// Returns the new overall root of the tree.
    unsafe fn retrace_insert(&mut self) -> *mut AVLTree<T> {
        if self.parent == ptr::null_mut() {
            return self as *mut AVLTree<T>;
        }
        if (*self.parent).right == (self as *mut AVLTree<T>) {
            /* We are right-hand child: */

            if (*self.parent).balance > 0 {
                /* Tree is unbalanced at parent. */
                if self.balance >= 0 {
                    /* Right-Right case. */
                    (*self.parent).left_rotate();
                } else {
                    /* Right-Left case. */
                    let prev_parent = self.parent;
                    self.right_rotate();
                    (*prev_parent).left_rotate();
                }
            } else {
                /* Tree is still balanced. */
                (*self.parent).balance += 1;
                if (*self.parent).balance == 1 {
                    /* Need to continue retracing. */
                    return (*self.parent).retrace_insert();
                }

                /* Otherwise, tree is perfectly balanced-- don't need to do anything further! */
            }
        } else {
            /* We are left-hand child: */
            if (*self.parent).balance < 0 {
                if self.balance <= 0 {
                    /* Left-Left case. */
                    (*self.parent).right_rotate();
                } else {
                    /* Left-Right case. */
                    let prev_parent = self.parent;
                    self.left_rotate();
                    (*prev_parent).right_rotate();
                }
            } else {
                (*self.parent).balance -= 1;
                if (*self.parent).balance == -1 {
                    return (*self.parent).retrace_insert();
                }
            }
        }

        self.recurse_to_root()
    }
}

#[derive(Debug)]
pub struct FreeMemoryRange {
    next: Option<Box<FreeMemoryRange>>,
    range_start: usize,
    range_end: usize,
}

impl FreeMemoryRange {
    fn new(range_start: usize, range_end: usize) -> FreeMemoryRange {
        FreeMemoryRange {
            next: None,
            range_start,
            range_end,
        }
    }
}

#[derive(Debug)]
pub struct PhysicalMemoryRange {
    range_start: usize,
    range_end: usize,
    free: Option<Box<FreeMemoryRange>>,
    allocator_tree: *mut AVLTree<BuddyAllocator>,
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
            free: Some(Box::new(FreeMemoryRange::new(addr, addr + len))),
            allocator_tree: ptr::null_mut(),
        };

        new_range
    }

    fn add_new_allocator(&mut self) -> Option<&mut BuddyAllocator> {
        if self.free.is_none() {
            return None;
        }

        let cur_free_head: &mut FreeMemoryRange = self.free.as_deref_mut().unwrap();

        let mut new_allocator_sz = cur_free_head.range_end - cur_free_head.range_start;
        if new_allocator_sz > (0x1000usize << 8) {
            new_allocator_sz = 0x1000usize << 8;
        }

        let new_allocator =
            BuddyAllocator::new(cur_free_head.range_start, new_allocator_sz).unwrap();

        cur_free_head.range_start += new_allocator_sz;
        if cur_free_head.range_start >= cur_free_head.range_end {
            self.free = cur_free_head.next.take();
        }

        unsafe {
            if self.allocator_tree != ptr::null_mut() {
                let (new_root, new_node) = (*self.allocator_tree).insert(new_allocator);
                self.allocator_tree = new_root;
                return Some(&mut new_node.data);
            } else {
                use alloc::alloc::alloc;

                let layout = Layout::new::<AVLTree<BuddyAllocator>>();
                self.allocator_tree = alloc(layout) as *mut AVLTree<BuddyAllocator>;
                *self.allocator_tree = AVLTree {
                    data: new_allocator,
                    parent: ptr::null_mut(),
                    left: ptr::null_mut(),
                    right: ptr::null_mut(),
                    balance: 0,
                };

                return Some(&mut (*self.allocator_tree).data);
            }
        }
    }

    unsafe fn range_mark_sweep_avl_nodes(
        cur: *mut AVLTree<BuddyAllocator>,
        range_start: usize,
        range_end: usize,
    ) {
        if cur == ptr::null_mut() {
            return;
        }

        let min_addr = (*cur).data.mem_addr;
        let max_addr = (*cur).data.region_end;

        if range_start <= max_addr && min_addr <= range_end {
            (*cur).data.mark_range_used(range_start, range_end);
        }

        if range_start <= min_addr && (*cur).left != ptr::null_mut() {
            PhysicalMemoryRange::range_mark_sweep_avl_nodes((*cur).left, range_start, range_end);
        }

        if range_end >= max_addr && (*cur).right != ptr::null_mut() {
            PhysicalMemoryRange::range_mark_sweep_avl_nodes((*cur).right, range_start, range_end);
        }
    }

    pub unsafe fn mark_range_used(&mut self, range_start: usize, range_end: usize) {
        /* Sweep all intersecting allocators: */
        PhysicalMemoryRange::range_mark_sweep_avl_nodes(
            self.allocator_tree,
            range_start,
            range_end,
        );

        /* Make sure no free areas intersect the range: */
        if self.free.is_some() {
            let mut cur: &mut FreeMemoryRange = self.free.as_deref_mut().unwrap();
            loop {
                if cur.range_start == range_start && cur.range_end == range_end {
                    /* Exactly intersecting ranges: delete this range. */
                    cur.range_start = cur.range_end;
                } else if range_end > cur.range_start && cur.range_end > range_start {
                    /* Intersecting ranges: */
                    if (cur.range_start < range_start) && (cur.range_end > range_end) {
                        /* Current free area completely contains the forbidden region */
                        let mut new_free_area: Box<FreeMemoryRange> =
                            Box::new(FreeMemoryRange::new(range_end, cur.range_end));

                        cur.range_end = range_start;
                        new_free_area.next = cur.next.take();
                        cur.next = Some(new_free_area);
                    } else if cur.range_start < range_start {
                        cur.range_end = range_start;
                    } else if cur.range_end > range_end {
                        cur.range_start = range_end;
                    }
                }

                if cur.next.is_some() {
                    cur = cur.next.as_deref_mut().unwrap();
                } else {
                    break;
                }
            }

            /* Sweep through the free list _again_, double checking to ensure we didn't leave
             * any invalid free regions.
             */

            let mut cur: &mut FreeMemoryRange = self.free.as_deref_mut().unwrap();
            loop {
                if cur.next.is_none() {
                    return;
                }

                let mut next: Box<FreeMemoryRange> = cur.next.take().unwrap();
                if next.range_start == next.range_end {
                    cur.next = next.next.take();
                } else {
                    cur.next = Some(next);
                    cur = cur.next.as_deref_mut().unwrap();
                }
            }
        }
    }

    unsafe fn allocate_search(cur: *mut AVLTree<BuddyAllocator>, order: u64) -> Option<usize> {
        if cur == ptr::null_mut() {
            return None;
        }

        if let Some(addr) = (*cur).data.allocate(order) {
            return Some(addr);
        }

        if (*cur).left != ptr::null_mut() {
            if let Some(addr) = PhysicalMemoryRange::allocate_search((*cur).left, order) {
                return Some(addr);
            }
        }

        PhysicalMemoryRange::allocate_search((*cur).right, order)
    }

    pub fn allocate(&mut self, size: usize) -> Option<usize> {
        let order = BuddyAllocator::round_allocation_size(size);
        unsafe {
            if let Some(addr) = PhysicalMemoryRange::allocate_search(self.allocator_tree, order) {
                return Some(addr);
            } else if let Some(new_allocator) = self.add_new_allocator() {
                return new_allocator.allocate(order);
            }
        }

        None
    }

    pub unsafe fn deallocate(&self, addr: usize, size: usize) {
        if self.allocator_tree == ptr::null_mut() {
            return;
        }

        let order = BuddyAllocator::round_allocation_size(size);
        if let Some(node) = (*self.allocator_tree).search(addr, BuddyAllocator::get_range) {
            node.data.deallocate(addr, order);
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

    pub unsafe fn deallocate(&mut self, addr: usize, size: usize) {
        for r in self.ranges.iter_mut() {
            if addr >= r.range_start && addr <= r.range_end {
                r.deallocate(addr, size);
            }
        }
    }

    pub unsafe fn mark_range_used(&mut self, range_start: usize, range_end: usize) {
        for r in self.ranges.iter_mut() {
            if range_end >= r.range_start && r.range_end >= range_start {
                r.mark_range_used(range_start, range_end);
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

/// Deallocate a previously-allocated physical memory range.
///
/// The size passed to this function must be the same size as
/// passed to the original allocation call!
pub unsafe fn deallocate_physical_memory(addr: usize, size: usize) {
    let mut l = KERNEL_PHYS_ALLOC.lock();
    l.deallocate(addr, size);
}

/// Mark a given region of memory as being reserved for e.g. hardware usage.
pub unsafe fn mark_physical_memory_used(range_start: usize, range_end: usize) {
    let mut l = KERNEL_PHYS_ALLOC.lock();
    l.mark_range_used(range_start, range_end);
}

/// Represents an owned, allocated block of physical memory.
///
/// This can be used as a safer interface to the physical memory allocator.
#[derive(Debug)]
pub struct PhysicalMemory {
    address: usize,
    size: usize,
}

impl PhysicalMemory {
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
