use core::mem;
use core::ptr;

use crate::paging::PAGE_MASK;

use lazy_static::lazy_static;
use spin::Mutex;

lazy_static! {
    pub static ref KERNEL_SMA: Mutex<SmallZoneAllocator> = Mutex::new(SmallZoneAllocator {
        heads: [ptr::null_mut(); 7],
        free_list: ptr::null_mut()
    });
}

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
        use super::heap_pages;
        let mut p = self.free_list;

        if p == ptr::null_mut() {
            if let Some(vaddr) = heap_pages::allocate(0x1000) {
                self.add_free_pages(vaddr, 1);
                p = self.free_list;
            }

            if p == ptr::null_mut() {
                panic!("no free pages left for heap allocations");
            }
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
