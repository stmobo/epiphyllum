use alloc::alloc::{GlobalAlloc, Layout};
use core::mem;
use core::ptr;

pub use crate::paging::KERNEL_HEAP_BASE;
use crate::paging::PAGE_MASK;

use lazy_static::lazy_static;
use spin::Mutex;

/// Used for allocations of size 8 - 512.
/// This is designed to fit specifically within 1 page, and should _always_
/// be aligned to a page boundary.
///
/// Note on bitmaps:
/// at most, we need (4096 / 8) / 8 = 64 bytes for the free-space bitmap.
///
/// We also guarantee that all allocations are aligned to their size
/// (i.e. zones that allocate blocks of size 16 are guaranteed to be aligned to 16.)
#[derive(Debug)]
#[repr(align(16))]
pub struct SmallZone {
    next: *mut SmallZone,
    count: u32,
    order: u32,
    /// Ranges from 0-6 (sizes 8 - 512)
    bitmap: [u64; 8],
}

impl SmallZone {
    /// Creates a new SmallZone header.
    fn new(order: u32) -> SmallZone {
        if order > 6 {
            panic!("invalid order {} for small zone", order);
        }

        let count = (0x1000u32 >> (order + 3)) - SmallZone::get_reserved_slots(order);
        SmallZone {
            next: ptr::null_mut(),
            count,
            order,
            bitmap: [0; 8],
        }
    }

    /// Set up this zone to have a new order.
    ///
    /// Note that this completely wipes whatever prior allocation information
    /// this zone was storing, so make sure all objects from this zone have
    /// been freed prior to reinitialization!
    unsafe fn reinitialize(&mut self, new_order: u32) {
        let count = (0x1000u32 >> (new_order + 3)) - SmallZone::get_reserved_slots(new_order);

        self.order = new_order;
        self.count = count;
        self.bitmap = [0; 8];
    }

    fn self_addr(&self) -> usize {
        (self as *const SmallZone) as usize
    }

    /// Get the size of an allocation block for this zone, in bytes.
    pub fn get_alloc_size(&self) -> usize {
        1usize << (self.order + 3)
    }

    /// Get how many slots there are _total_ within this zone.
    fn n_slots(&self) -> usize {
        0x1000usize / self.get_alloc_size()
    }

    fn get_reserved_slots(order: u32) -> u32 {
        (match order {
            0 => mem::size_of::<SmallZone>() / 8,
            1 => mem::size_of::<SmallZone>() / 16,
            2 => (mem::size_of::<SmallZone>() / 32) + 1,
            3 => (mem::size_of::<SmallZone>() / 64) + 1,
            4 => 1,
            5 => 1,
            6 => 1,
            _ => panic!("invalid order {} for small zone", order),
        }) as u32
    }

    fn get_start_slot(&self) -> usize {
        SmallZone::get_reserved_slots(self.order) as usize
    }

    fn get_max_count(&self) -> u32 {
        (0x1000u32 >> (self.order + 3)) - SmallZone::get_reserved_slots(self.order)
    }

    /// Set whether a given allocation slot is occupied or not.
    fn set_bitmap(&mut self, slot_no: usize, occupied: bool) {
        let bitmap_idx = slot_no / 64;
        let bit_idx = slot_no % 64;

        if occupied {
            self.bitmap[bitmap_idx] |= 1u64 << bit_idx
        } else {
            self.bitmap[bitmap_idx] &= !(1u64 << bit_idx)
        }
    }

    /// Get whether a given allocation slot is occupied or not.
    fn get_bitmap(&mut self, slot_no: usize) -> bool {
        let bitmap_idx = slot_no / 64;
        let bit_idx = slot_no % 64;

        (self.bitmap[bitmap_idx] & (1u64 << bit_idx)) != 0
    }

    fn find_unset(val: u64, limit: usize) -> Option<usize> {
        let mut t = 1;
        for i in 0..limit {
            if (val & t) == 0 {
                return Some(i);
            }

            t <<= 1;
        }

        None
    }

    fn find_open_slot(&self) -> Option<usize> {
        let n_slots = self.n_slots();
        let start_slot = self.get_start_slot();
        let bm0 = self.bitmap[0] >> start_slot;

        if n_slots <= 64 {
            if let Some(idx) = SmallZone::find_unset(bm0, n_slots - start_slot) {
                return Some(idx + start_slot);
            }
        } else {
            if let Some(idx) = SmallZone::find_unset(bm0, 64 - start_slot) {
                return Some(idx + start_slot);
            }

            let n_bitmaps = n_slots / 64;
            for i in 1..n_bitmaps {
                if let Some(idx) = SmallZone::find_unset(self.bitmap[i], 64) {
                    return Some(idx);
                }
            }
        }

        None
    }

    fn get_slot_address(&self, slot: usize) -> usize {
        self.self_addr() + (self.get_alloc_size() * slot)
    }

    fn full(&self) -> bool {
        self.count == 0
    }

    fn empty(&self) -> bool {
        self.count == self.get_max_count()
    }

    unsafe fn allocate(&mut self) -> usize {
        if cfg!(debug_assertions) && self.count == 0 {
            panic!(
                "requested allocation from empty zone at {:#016x}",
                self.self_addr()
            );
        }

        let slot = self.find_open_slot().unwrap();
        self.count -= 1;
        self.set_bitmap(slot, true);
        self.get_slot_address(slot)
    }

    unsafe fn deallocate(&mut self, address: usize) {
        let self_addr = self.self_addr();

        if cfg!(debug_assertions) && (address <= self_addr || (address - self_addr) >= 0x1000) {
            panic!(
                "requested deallocation of invalid address {:#016x} by {:#016x}",
                address, self_addr
            );
        }

        let slot = (address - self_addr) / self.get_alloc_size();
        if cfg!(debug_assertions) && !self.get_bitmap(slot) {
            panic!("possible free of unallocated memory at {:#016x}", address);
        }

        self.set_bitmap(slot, false);
        self.count += 1;

        if cfg!(debug_assertions) && self.count > self.get_max_count() {
            panic!(
                "possible double free in allocator {:#016x} after freeing address {:#016x}",
                self_addr, address
            );
        }
    }
}

/// Memory allocator designed for small objects (8 - 512 bytes).
#[derive(Debug)]
pub struct SmallZoneAllocator {
    heads: [*mut SmallZone; 7],
    free_list: *mut SmallZone,
}

impl SmallZoneAllocator {
    /// Initialize a SmallZoneAllocator at the given virtual memory address range.
    pub unsafe fn new(init_addr: usize, n_pages: usize) -> SmallZoneAllocator {
        let mut zone = SmallZoneAllocator {
            heads: [ptr::null_mut(); 7],
            free_list: ptr::null_mut(),
        };

        zone.add_free_pages(init_addr, n_pages);
        zone
    }

    /// Add pages to the free list for this allocator.
    ///
    //// The caller is responsible for ensuring the given pages are page-aligned
    /// and valid for heap usage!
    pub unsafe fn add_free_pages(&mut self, init_addr: usize, n_pages: usize) {
        /* Initialize all given pages as allocation zones. */
        let mut cur_addr = init_addr;
        let mut next_addr = init_addr + 0x1000;

        for i in 0..n_pages {
            let p: *mut SmallZone = cur_addr as *mut SmallZone;

            *p = SmallZone::new(0);

            if i < n_pages - 1 {
                (*p).next = next_addr as *mut SmallZone;
            } else {
                (*p).next = self.free_list;
            }

            cur_addr += 0x1000;
            next_addr += 0x1000;
        }

        self.free_list = init_addr as *mut SmallZone;
    }

    /// Pop a page off the free list and make it available for allocations
    /// of the specified order.
    unsafe fn init_new_zone_page(&mut self, order: usize) -> *mut SmallZone {
        let p = self.free_list;

        if p == ptr::null_mut() {
            panic!("no free pages left for heap allocations");
        }

        let next = (*p).next;
        self.free_list = next;

        let prev_head = self.heads[order];
        self.heads[order] = p;
        (*p).next = prev_head;
        (*p).reinitialize(order as u32);

        p
    }

    unsafe fn release_zone_page(&mut self, zone: *mut SmallZone) {
        let order = (*zone).order as usize;

        if self.heads[order] == zone {
            self.heads[order] = (*zone).next;
        } else {
            let mut prev_ptr: *mut SmallZone = self.heads[order];

            while (prev_ptr != ptr::null_mut()) && ((*prev_ptr).next != zone) {
                prev_ptr = (*prev_ptr).next;
            }
            if prev_ptr == ptr::null_mut() {
                panic!("attempted to release zone page not in allocator");
            }

            (*prev_ptr).next = (*zone).next;
        }

        (*zone).next = self.free_list;
        self.free_list = zone;
    }

    /// Allocate a chunk of memory from this allocator.
    pub unsafe fn allocate(&mut self, order: usize) -> usize {
        let mut p = self.heads[order];

        while p != ptr::null_mut() && (*p).full() {
            p = (*p).next;
        }

        if p == ptr::null_mut() {
            /* No free zones found, get a new one. */
            p = self.init_new_zone_page(order);
        }

        (*p).allocate()
    }

    /// Deallocate a chunk of memory from this allocator.
    ///
    /// The usual caveats regarding free() apply!
    pub unsafe fn deallocate(&mut self, addr: usize) {
        /* Get the page-aligned zone address. */
        let zone_addr: usize = addr & PAGE_MASK;
        let zone: *mut SmallZone = zone_addr as *mut SmallZone;

        (*zone).deallocate(addr);
        if (*zone).empty() {
            /* Nothing left in this zone, release it. */
            self.release_zone_page(zone);
        }
    }
}

unsafe impl Send for SmallZoneAllocator {}

#[derive(Debug, Clone)]
pub struct BuddyAllocator {
    mem_addr: usize,
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
    pub fn new(addr: usize, region_len: usize) -> Result<BuddyAllocator, BuddyAllocatorError> {
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

        if order < 8 && self.get_block_state(order, index + 1) {
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
            2 => (self.ord_2_bitmap ^ (1u64 << index % 64)) != 0,
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

    pub unsafe fn allocate(&mut self, size: usize) -> Option<usize> {
        if size > (0x1000usize << 8) {
            return None;
        }

        for i in 0..9 {
            if (0x1000usize << i) >= size {
                /* Allocate block of this order. */
                return self
                    .allocate_block(i)
                    .map(|idx| self.get_addr_for_block(i, idx));
            }
        }

        None
    }

    pub unsafe fn deallocate(&mut self, addr: usize, size: usize) {
        if size > (0x1000usize << 8) {
            return;
        }

        for i in 0..9 {
            if (0x1000usize << i) >= size {
                /* Deallocate block of this order. */
                let block_idx = self.get_block_for_addr(addr, i);
                self.free_block(i, block_idx);
                return;
            }
        }
    }
}

lazy_static! {
    pub static ref KERNEL_SMA: Mutex<SmallZoneAllocator> = Mutex::new(SmallZoneAllocator {
        heads: [ptr::null_mut(); 7],
        free_list: ptr::null_mut()
    });
}

pub struct KernelHeapAllocator {
    sma_ready: bool,
    // vm_alloc_ready: bool,
}

#[global_allocator]
static mut KERNEL_ALLOCATOR: KernelHeapAllocator = KernelHeapAllocator {
    sma_ready: false,
    // vm_alloc_ready: false
};

impl KernelHeapAllocator {
    fn get_layout_alloc_size(layout: Layout) -> usize {
        let mut min_block_sz: usize = layout.align();
        if layout.size() > layout.align() {
            min_block_sz = layout.size();
        }

        if !min_block_sz.is_power_of_two() {
            min_block_sz.next_power_of_two()
        } else {
            min_block_sz
        }
    }
}

unsafe impl GlobalAlloc for KernelHeapAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let min_block_sz: usize = KernelHeapAllocator::get_layout_alloc_size(layout);
        if min_block_sz <= 512 {
            /* Use small-zone allocator. */
            if !self.sma_ready {
                panic!("attempted to allocate memory prior to small-object heap init");
            }

            let mut order = 6;
            for i in 0..7 {
                if min_block_sz == (1usize << (i + 3)) {
                    order = i;
                    break;
                }
            }

            let mut l = KERNEL_SMA.lock();
            let addr = l.allocate(order);
            drop(l);

            addr as *mut u8
        } else {
            panic!("large object allocation not implemented");
        }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        let min_block_sz: usize = KernelHeapAllocator::get_layout_alloc_size(layout);
        if min_block_sz <= 512 {
            /* Block was from the small-zone allocator. */
            if !self.sma_ready {
                panic!("attempted to allocate memory prior to small-object heap init");
            }

            let mut l = KERNEL_SMA.lock();
            l.deallocate(ptr as usize);
        } else {
            panic!("large object allocation not implemented");
        }
    }
}

pub unsafe fn initialize_small_heap(init_addr: usize, n_pages: usize) {
    let mut l = KERNEL_SMA.lock();
    *l = SmallZoneAllocator::new(init_addr, n_pages);

    KERNEL_ALLOCATOR.sma_ready = true;
}

#[alloc_error_handler]
pub fn kernel_alloc_failed(layout: core::alloc::Layout) -> ! {
    panic!(
        "could not satisfy kernel heap allocation request for {} bytes",
        layout.size()
    );
}
