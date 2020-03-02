use core::mem;

pub use crate::paging::KERNEL_HEAP_BASE;

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
    order: u32,             /// Ranges from 0-6 (sizes 8 - 512) 
    bitmap: [u64; 8],
}

impl SmallZone {
    pub fn new(order: u32) -> SmallZone {
        if order > 6 {
            panic!("invalid order {} for small zone", order);
        }

        let count = 0x1000u32 >> (order + 3);
        let mut zone = SmallZone {
            next: 0 as *mut SmallZone,
            count,
            order,
            bitmap: [0; 8]
        };

        let ct = zone.get_start_slot() as u32;
        zone.count -= ct;

        println!("Initialized SmallZone with order={}, count={}", order, zone.count);

        zone
    }

    fn self_addr(&self) -> usize {
        unsafe { mem::transmute(self) }
    }

    /// Get the size of an allocation block for this zone, in bytes.
    pub fn get_alloc_size(&self) -> usize {
        1usize << (self.order + 3)
    }

    /// Get how many slots there are _total_ within this zone.
    fn n_slots (&self) -> usize {
        0x1000usize / self.get_alloc_size()
    }

    fn get_start_slot (&self) -> usize {
        match self.order {
            0 => mem::size_of::<SmallZone>() / 8,
            1 => mem::size_of::<SmallZone>() / 16,
            2 => (mem::size_of::<SmallZone>() / 32) + 1,
            3 => (mem::size_of::<SmallZone>() / 64) + 1,
            4 => 1,
            5 => 1,
            6 => 1,
            _ => panic!("invalid order {} for small zone", self.order)
        }
    }

    fn set_bitmap(&mut self, slot_no: usize, state: bool) {
        let bitmap_idx = slot_no / 64;
        let bit_idx = slot_no % 64;

        if state {
            self.bitmap[bitmap_idx] |= 1u64 << bit_idx
        } else {
            self.bitmap[bitmap_idx] &= !(1u64 << bit_idx)
        }
    }

    fn get_bitmap(&mut self, slot_no: usize) -> bool {
        let bitmap_idx = slot_no / 64;
        let bit_idx = slot_no % 64;

        (self.bitmap[bitmap_idx] & (1u64 << bit_idx)) != 0
    }

    fn find_unset(val: u64, limit: usize) -> Option<usize> {
        let mut t = 1;
        for i in 0..limit {
            if (val & t) == 0 {
                println!("found index: {}", i);
                return Some(i);
            }

            t <<= 1;
        }

        None
    }

    fn find_open_slot (&self) -> Option<usize> {
        let n_slots = self.n_slots();
        let start_slot = self.get_start_slot();
        let bm0 = self.bitmap[0] >> start_slot;

        if n_slots <= 64 {
            println!("Searching for open slot in first bitmap only, {} slots", n_slots - start_slot);
            if let Some(idx) = SmallZone::find_unset(bm0, n_slots - start_slot) {
                return Some(idx + start_slot);
            }
        } else {
            println!("Searching for open slot in first bitmap, {} slots", 64 - start_slot);
            if let Some(idx) = SmallZone::find_unset(bm0, 64 - start_slot) {
                return Some(idx + start_slot);
            }

            let n_bitmaps = n_slots / 64;
            for i in 1..n_bitmaps {
                println!("Searching for open slot in bitmap {}", i);

                if let Some(idx) = SmallZone::find_unset(self.bitmap[i], 64) {
                    return Some(idx);
                }
            }
        }

        None
    }

    fn get_slot_address (&self, slot: usize) -> usize {
        self.self_addr() + (self.get_alloc_size() * slot)
    }

    pub unsafe fn allocate(&mut self) -> Option<usize> {
        if self.count == 0 {
            return None;
        }

        if let Some(slot) = self.find_open_slot() {
            self.count -= 1;
            self.set_bitmap(slot, true);
            Some(self.get_slot_address(slot))
        } else {
            self.count = 0;
            None
        }
    }

    pub unsafe fn deallocate(&mut self, address: usize) {
        let self_addr = self.self_addr();
        if address <= self_addr || (address - self_addr) >= 0x1000 {
            panic!("requested deallocation of invalid address {:#016x} by {:#016x}", address, self_addr);
        }

        let slot = (address - self_addr) / self.get_alloc_size();
        if !self.get_bitmap(slot) {
            panic!("possible free of unallocated memory at {:#016x}", address);
        }

        self.set_bitmap(slot, false);
        self.count += 1;

        if self.count >= ((self.n_slots() - self.get_start_slot()) as u32) {
            panic!("possible double free in allocator {:#016x} after freeing address {:#016x}", self_addr, address);
        }
    }
}
