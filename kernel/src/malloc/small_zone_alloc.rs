use alloc_crate::alloc::Layout;
use core::iter;
use core::mem;
use core::ptr;
use core::ptr::NonNull;

use super::heap_pages;
use super::AllocationError;
use crate::lock::LockedGlobal;
use crate::paging::PAGE_MASK;
use crate::structures::Bitmask64;

static KERNEL_SMA: LockedGlobal<SmallZoneAllocator> = LockedGlobal::new();

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
    order: u32,             // Ranges from 0-6 (sizes 8 - 512)
    bitmap: [Bitmask64; 8], // note: free spaces are stored as 1's
}

// total slots per order (not incl. space occupied by zone header):
// 0: 512 (bitmap size 64 bytes)
// 1: 256
// 2: 128
// 3:  64
// 4:  32
// 5:  16
// 6:   8

impl SmallZone {
    /// Creates a new SmallZone header.
    fn new(order: u32) -> SmallZone {
        if order > 6 {
            panic!("invalid order {} for small zone", order);
        }

        let count = (0x1000u32 >> (order + 3)) - SmallZone::get_reserved_slots(order);
        let mut ret = SmallZone {
            next: ptr::null_mut(),
            count,
            order,
            bitmap: [Bitmask64::all_zeros(); 8],
        };
        Self::initialize_bitmap(order, &mut ret.bitmap);

        ret
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
        self.bitmap = [Bitmask64::all_zeros(); 8];
        Self::initialize_bitmap(new_order, &mut self.bitmap);
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

    fn initialize_bitmap(order: u32, bitmap: &mut [Bitmask64; 8]) {
        let slots = 0x1000usize >> (order + 3);
        if order <= 3 {
            for i in 0..(slots / 64) {
                bitmap[i] = Bitmask64::all_ones();
            }

            bitmap[0] = Bitmask64::n_ones(Self::get_reserved_slots(order) as u64).invert();
        } else {
            bitmap[0] = Bitmask64::n_ones(slots as u64).set(0, false);
        }
    }

    fn get_start_slot(&self) -> usize {
        SmallZone::get_reserved_slots(self.order) as usize
    }

    fn get_max_count(&self) -> u32 {
        (0x1000u32 >> (self.order + 3)) - SmallZone::get_reserved_slots(self.order)
    }

    #[inline]
    /// Split a slot number into a bitmap array index and a bit index.
    const fn split_slot(slot_no: usize) -> (usize, usize) {
        (slot_no >> 6, slot_no & 0x3F)
    }

    /// Set whether a given allocation slot is occupied or not.
    fn set_bitmap(&mut self, slot_no: usize, occupied: bool) {
        let (map_idx, bit_idx) = Self::split_slot(slot_no);
        self.bitmap[map_idx] = self.bitmap[map_idx].set(bit_idx, !occupied);
    }

    /// Get whether a given allocation slot is occupied or not.
    fn get_bitmap(&self, slot_no: usize) -> bool {
        let (map_idx, bit_idx) = Self::split_slot(slot_no);
        !self.bitmap[map_idx].get(bit_idx)
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
        for (i, bm) in self.bitmap.iter().enumerate() {
            if let Some(b) = bm.first_set_bit() {
                return Some((i * 64) + b);
            }
        }

        None
    }

    fn get_slot_address(&self, slot: usize) -> usize {
        self.self_addr() + (self.get_alloc_size() * slot)
    }

    fn slot_from_address(&self, address: usize) -> usize {
        (address - self.self_addr()) / self.get_alloc_size()
    }

    fn full(&self) -> bool {
        self.count == 0
    }

    fn empty(&self) -> bool {
        self.count == self.get_max_count()
    }

    unsafe fn allocate(&mut self) -> Result<usize, AllocationError> {
        if self.count == 0 {
            return Err(AllocationError::NoFreeVirtualMemory);
        }

        if let Some(slot) = self.find_open_slot() {
            self.count -= 1;
            self.set_bitmap(slot, true);
            Ok(self.get_slot_address(slot))
        } else {
            Err(AllocationError::NoFreeVirtualMemory)
        }
    }

    unsafe fn deallocate(&mut self, address: usize) {
        let self_addr = self.self_addr();

        debug_assert!(
            (address >= (self_addr + mem::size_of::<SmallZone>()))
                && ((address - self_addr) < 0x1000),
            "requested deallocation of invalid address {:#018x} via allocator {:#018x}",
            address,
            self_addr
        );

        let slot = self.slot_from_address(address);

        debug_assert!(slot >= Self::get_reserved_slots(self.order) as usize);
        debug_assert!(
            self.get_bitmap(slot),
            "possible free of unallocated memory at {:#018x}",
            address
        );

        self.set_bitmap(slot, false);
        self.count += 1;

        debug_assert!(
            self.count <= self.get_max_count(),
            "allocator {:#018x} state corrupt after freeing address {:#018x}",
            self_addr,
            address
        );
    }
}

/// Memory allocator designed for small objects (8 - 512 bytes).
#[derive(Debug)]
pub struct SmallZoneAllocator {
    heads: [*mut SmallZone; 7],
    free_list: *mut SmallZone,
    free_len: usize,
}

impl SmallZoneAllocator {
    /// Initialize a SmallZoneAllocator at the given virtual memory address range.
    pub unsafe fn new(init_addr: usize, n_pages: usize) -> SmallZoneAllocator {
        let mut zone = SmallZoneAllocator {
            heads: [ptr::null_mut(); 7],
            free_list: ptr::null_mut(),
            free_len: 0,
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

            ptr::write(p, SmallZone::new(0));
            if i < n_pages - 1 {
                (*p).next = next_addr as *mut SmallZone;
            } else {
                (*p).next = self.free_list;
            }

            cur_addr += 0x1000;
            next_addr += 0x1000;
        }

        self.free_list = init_addr as *mut SmallZone;
        self.free_len += n_pages;
    }

    /// Pop a page off the free list and make it available for allocations
    /// of the specified order.
    unsafe fn init_new_zone_page(
        &mut self,
        order: usize,
    ) -> Result<*mut SmallZone, AllocationError> {
        let mut p = self.free_list;

        if p == ptr::null_mut() {
            if let Ok(vaddr) = heap_pages::allocate(0x1000) {
                self.add_free_pages(vaddr, 1);
                p = self.free_list;
            }

            if p == ptr::null_mut() {
                return Err(AllocationError::NoFreeVirtualMemory);
            }
        }

        let next = (*p).next;
        self.free_list = next;
        self.free_len -= 1;

        let prev_head = self.heads[order];
        self.heads[order] = p;
        (*p).next = prev_head;
        (*p).reinitialize(order as u32);

        Ok(p)
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
        self.free_len += 1;
    }

    /// Allocate a chunk of memory from this allocator.
    pub unsafe fn allocate(&mut self, order: usize) -> Result<usize, AllocationError> {
        let mut p = self.heads[order];

        while p != ptr::null_mut() && (*p).full() {
            p = (*p).next;
        }

        if p == ptr::null_mut() {
            /* No free zones found, get a new one. */
            p = self.init_new_zone_page(order)?;
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

    pub fn reclaim_pages(&mut self) -> *mut SmallZone {
        unsafe {
            if self.free_len > 64 {
                let old_head = self.free_list;
                let mut cur = self.free_list;
                let mut prev = ptr::null_mut();
                for _ in 64..self.free_len {
                    prev = cur;
                    cur = (*cur).next;
                }

                self.free_list = cur;
                (*prev).next = ptr::null_mut();
                old_head
            } else {
                ptr::null_mut()
            }
        }
    }
}

unsafe impl Send for SmallZoneAllocator {}

pub unsafe fn initialize(init_addr: usize, n_pages: usize) {
    KERNEL_SMA.init(|| SmallZoneAllocator::new(init_addr, n_pages));
}

pub unsafe fn add_page(addr: usize) {
    KERNEL_SMA.lock().add_free_pages(addr, 1)
}

pub fn is_valid_sma_block(layout: Layout) -> bool {
    let sz = layout.size().next_power_of_two();
    (sz >= 8) && (sz <= 512)
}

pub unsafe fn allocate(layout: Layout) -> Result<usize, AllocationError> {
    if !is_valid_sma_block(layout) {
        return Err(AllocationError::InvalidAllocation);
    }

    let sz = layout.size().next_power_of_two();
    KERNEL_SMA
        .lock()
        .allocate((sz.trailing_zeros() - 3) as usize)
}

pub unsafe fn deallocate(addr: usize) {
    KERNEL_SMA.lock().deallocate(addr);
}

pub fn reclaim_pages() -> impl Iterator<Item = usize> {
    let p = KERNEL_SMA.lock().reclaim_pages();
    iter::successors(NonNull::new(p), |p| unsafe {
        NonNull::new((*p.as_ptr()).next)
    })
    .map(|p| p.as_ptr() as usize)
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::malloc;
    use crate::malloc::tests::TestAlloc;
    use crate::rng::MersenneTwister64;
    use crate::test::TEST_SEED;

    use alloc_crate::collections::VecDeque;
    use alloc_crate::vec::Vec;
    use kernel_test_macro::kernel_test;

    fn zone_alloc_test_pattern(seed: u64, rng: &mut MersenneTwister64, order: u32) {
        unsafe {
            rng.seed(seed);
            let zone_vaddr = malloc::heap_pages::allocate(0x1000).unwrap();
            let p = zone_vaddr as *mut SmallZone;

            ptr::write_bytes(zone_vaddr as *mut u8, 0, 0x1000);
            ptr::write(p, SmallZone::new(order));

            let sz = (*p).get_alloc_size();
            let slots = (*p).get_max_count() as usize;
            let reserved_slots = SmallZone::get_reserved_slots(order) as usize;
            let mut v: VecDeque<usize> = VecDeque::with_capacity(slots);

            for i in 0..slots {
                let addr = match (*p).allocate() {
                    Ok(a) => a,
                    Err(e) => panic!(
                        "alloc {} failed (seed: {:#x}, order {}) - {:?}",
                        i, seed, order, e
                    ),
                };
                let alloc_slot = (*p).slot_from_address(addr);

                assert!(
                    alloc_slot >= reserved_slots && (addr - zone_vaddr) < 0x1000,
                    "alloc {} returned invalid address {:#018x} from zone page {:#018x} (seed: {:#x}, order {})",
                    i,
                    addr,
                    zone_vaddr,
                    seed,
                    order,
                );

                let allocated = addr as *mut u8;
                let value = (alloc_slot & 0xFF) as u8;
                ptr::write_bytes(allocated, value, sz);
                v.push_back(addr);
            }

            let slice = v.make_contiguous();
            slice.sort();
            for i in 0..(slice.len() - 1) {
                let block_start = slice[i];
                let block_end = block_start + sz;
                let next_start = slice[i + 1];

                assert!(
                    next_start >= block_end,
                    "found overlapping allocations: {:#018x} and {:#018x} (seed {:#x}, order {})",
                    block_start,
                    next_start,
                    seed,
                    order
                );
            }

            rng.shuffle(slice);
            let mut alloc_no = slots;
            drop(slice);

            for _ in 0..25 {
                let blk_cnt = v.len();
                let free_cnt = slots - blk_cnt;

                let mut n_dealloc = 0;
                let mut n_alloc = 0;

                if blk_cnt > 0 {
                    n_dealloc = (rng.generate() as usize) % blk_cnt;
                }

                if free_cnt > 0 {
                    n_alloc = (rng.generate() as usize) % free_cnt;
                }

                for _ in 0..n_dealloc {
                    let addr = v.pop_front().unwrap();
                    ptr::write_bytes(addr as *mut u8, 0, sz);
                    (*p).deallocate(addr);
                }

                for _ in 0..n_alloc {
                    let addr = match (*p).allocate() {
                        Ok(a) => a,
                        Err(e) => panic!(
                            "alloc {} failed (seed: {:#x}, order {}) - {:?}",
                            alloc_no, seed, order, e
                        ),
                    };
                    let allocated = addr as *mut u8;
                    let value = ((*p).slot_from_address(addr) & 0xFF) as u8;

                    for offset in 0..sz {
                        let alloc_ptr = allocated.offset(offset as isize);
                        assert_eq!(
                            *alloc_ptr, 0,
                            "double allocation detected (seed: {:#x}, order {})",
                            seed, order
                        );
                    }

                    ptr::write_bytes(allocated, value, sz);
                    v.push_back(addr);
                    alloc_no += 1;
                }
            }

            for addr in v {
                (*p).deallocate(addr);
            }

            malloc::heap_pages::deallocate(zone_vaddr, 0x1000);
        }
    }

    #[kernel_test]
    fn test_small_zones() {
        let mut seed_gen = MersenneTwister64::new(TEST_SEED);
        let mut sub_rng = MersenneTwister64::new(0);

        for _ in 0..2 {
            for order in 0..=6 {
                zone_alloc_test_pattern(seed_gen.generate(), &mut sub_rng, order);
            }
        }
    }

    const SMA_TEST_ALLOCS: usize = 500;

    #[kernel_test]
    fn test_sma() {
        let mut rng = MersenneTwister64::new(TEST_SEED);
        let mut allocs: Vec<TestAlloc> = Vec::with_capacity(SMA_TEST_ALLOCS);

        for i in 0..SMA_TEST_ALLOCS {
            let order = (rng.generate() % 7) as usize;
            let size = 1usize << (3 + order);
            let layout = Layout::from_size_align(size, size).unwrap();

            let addr = match unsafe { allocate(layout) } {
                Ok(a) => a,
                Err(e) => panic!(
                    "alloc {} failed (seed: {:#x}, size {}) - {:?}",
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
                deallocate(alloc.addr);
            }
        }

        unsafe {
            for addr in reclaim_pages() {
                malloc::heap_pages::deallocate(addr, 0x1000);
            }
        }
    }
}
