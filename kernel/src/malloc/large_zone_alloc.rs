use alloc_crate::alloc::Layout;
use core::cmp::Ordering;
use core::iter;
use core::mem;
use core::ptr;
use core::ptr::NonNull;

use super::heap_pages;
use super::AllocationError;
use crate::lock::LockedGlobal;
use crate::paging::round_to_prev_page;

static KERNEL_LZA: LockedGlobal<LargeZoneAllocator> = LockedGlobal::new();

/// Memory allocator for allocations that are > 512 bytes (the threshold for
/// small-zone allocation) and < 7160 (= 8192 - 512) bytes (the threshold for
/// direct virtual memory page allocation).
///
/// This structure is the header for a two-page allocation zone, and must
/// be placed on a page boundary.
#[derive(Debug, Clone)]
pub struct LargeZone {
    header: u32,
    free_bytes: u16,
    n_blocks: u8,
    next_zone: *mut LargeZone,
    prev_zone: *mut LargeZone,
    blocks: [AllocationBlock; 16],
}

const ZONE_HEADER: u32 = 0x414C4F43; // ASCII: "ALOC"

impl LargeZone {
    fn new(addr: usize, next_zone: *mut LargeZone) -> LargeZone {
        let mut zone = LargeZone {
            header: ZONE_HEADER,
            free_bytes: 8192 - (mem::size_of::<LargeZone>() as u16),
            next_zone,
            prev_zone: ptr::null_mut(),
            n_blocks: 1,
            blocks: [AllocationBlock::empty(); 16],
        };

        zone.blocks[0].addr = addr + mem::size_of::<LargeZone>();
        zone.blocks[0].size = (8192 - mem::size_of::<LargeZone>()) as u16;
        zone.blocks[0].free = true;

        zone
    }

    unsafe fn init_at(addr: usize, next_zone: *mut LargeZone) -> *mut LargeZone {
        let p = addr as *mut LargeZone;
        ptr::write(p, LargeZone::new(addr, next_zone));

        if next_zone != ptr::null_mut() {
            (*p).prev_zone = (*next_zone).prev_zone;
            (*next_zone).prev_zone = p;

            if (*p).prev_zone != ptr::null_mut() {
                (*(*p).prev_zone).next_zone = p;
            }
        }

        p
    }

    unsafe fn zone_for_addr(addr: usize) -> *mut LargeZone {
        let addr = round_to_prev_page(addr);
        if addr < crate::paging::HIGHER_HALF_START {
            return ptr::null_mut();
        }

        let p1 = addr as *const LargeZone;
        if (*p1).header == ZONE_HEADER {
            return p1 as *mut LargeZone;
        }

        let p2 = (addr - 0x1000) as *const LargeZone;
        if (*p2).header == ZONE_HEADER {
            return p2 as *mut LargeZone;
        }

        ptr::null_mut()
    }

    fn allocate(&mut self, layout: Layout) -> Result<usize, AllocationError> {
        let align_mask = layout.align() - 1;

        let blk_count = self.n_blocks;
        for i in 0..blk_count {
            let block: &mut AllocationBlock = &mut self.blocks[i as usize];
            let effective_addr: usize;
            let effective_size: usize;
            let padding_size: usize;

            if !block.free {
                continue;
            }

            if block.addr & align_mask == 0 {
                effective_addr = block.addr;
                effective_size = block.size as usize;
                padding_size = 0;
            } else if layout.align() <= (block.size as usize) {
                padding_size = layout.align() - (block.addr & align_mask);
                effective_size = (block.size as usize) - padding_size;
                effective_addr = block.addr + padding_size;
            } else {
                continue;
            }

            if effective_size >= layout.size() {
                block.free = false;

                let excess = (effective_size - layout.size()) as u16;
                if excess >= 512 && self.n_blocks < 16 {
                    let sz = (layout.size() + padding_size) as u16;
                    let prev_addr = block.addr;

                    block.size = sz;
                    drop(block);

                    let new_block_idx = self.n_blocks as usize;
                    self.n_blocks += 1;

                    self.blocks[new_block_idx].free = true;
                    self.blocks[new_block_idx].size = excess;
                    self.blocks[new_block_idx].addr = prev_addr + (sz as usize);

                    self.free_bytes -= sz;
                } else {
                    self.free_bytes -= block.size;
                    drop(block);
                }

                let (s1, _) = self.blocks.split_at_mut(self.n_blocks as usize);
                s1.sort_unstable();

                return Ok(effective_addr);
            }
        }

        Err(AllocationError::NoFreeVirtualMemory)
    }

    fn deallocate(&mut self, addr: usize, _layout: Layout) {
        let mut block_idx: isize = -1;
        for i in 0..self.n_blocks {
            let block: &AllocationBlock = &self.blocks[i as usize];
            if block.addr <= addr && (block.addr + (block.size as usize)) > addr {
                if block.free {
                    panic!("attempted double free of allocation at {:#016x}", addr);
                }

                block_idx = i as isize;
                break;
            }
        }

        if block_idx < 0 {
            panic!("attempted to free unallocated memory at {:#016x}", addr);
        }

        let block_idx = block_idx as usize;
        if self.n_blocks == 1 {
            self.blocks.swap(0, block_idx);

            self.free_bytes = 8192 - (mem::size_of::<LargeZone>() as u16);
            self.blocks[0].addr = addr + mem::size_of::<LargeZone>();
            self.blocks[0].size = self.free_bytes;
            self.blocks[0].free = true;
        } else {
            self.free_bytes += self.blocks[block_idx].size;
            self.blocks[block_idx].free = true;

            let mut new_blk_count = self.n_blocks;

            /* Attempt to merge with next block: */
            if block_idx < (self.n_blocks - 1) as usize {
                let next_block: &mut AllocationBlock = &mut self.blocks[block_idx + 1];
                if next_block.free {
                    self.blocks[block_idx].size += next_block.size;
                    self.blocks
                        .swap(block_idx + 1, (new_blk_count - 1) as usize);
                    new_blk_count -= 1;
                }
            }

            /* Attempt to merge with preceding block: */
            if block_idx > 0 {
                let cur_sz = self.blocks[block_idx].size;
                let prev_block: &mut AllocationBlock = &mut self.blocks[block_idx - 1];

                if prev_block.free {
                    prev_block.size += cur_sz;
                    self.blocks.swap(block_idx, (new_blk_count - 1) as usize);
                    new_blk_count -= 1;
                }
            }

            /* Sort new block list. */
            self.n_blocks = new_blk_count;
            let (s1, _) = self.blocks.split_at_mut(self.n_blocks as usize);
            s1.sort_unstable();
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct AllocationBlock {
    free: bool,
    size: u16,
    addr: usize,
}

impl PartialOrd for AllocationBlock {
    fn partial_cmp(&self, other: &AllocationBlock) -> Option<Ordering> {
        self.addr.partial_cmp(&other.addr)
    }
}

impl Ord for AllocationBlock {
    fn cmp(&self, other: &AllocationBlock) -> Ordering {
        self.addr.cmp(&other.addr)
    }
}

impl PartialEq for AllocationBlock {
    fn eq(&self, other: &AllocationBlock) -> bool {
        self.addr == other.addr
    }
}

impl Eq for AllocationBlock {}

impl AllocationBlock {
    const fn empty() -> AllocationBlock {
        AllocationBlock {
            free: false,
            size: 0,
            addr: 0,
        }
    }
}

pub struct LargeZoneAllocator {
    zone_list: *mut LargeZone,
}

impl LargeZoneAllocator {
    fn new() -> LargeZoneAllocator {
        LargeZoneAllocator {
            zone_list: ptr::null_mut(),
        }
    }

    fn allocate(&mut self, layout: Layout) -> Result<usize, AllocationError> {
        let mut cur = self.zone_list;
        let sz = layout.size();

        unsafe {
            while cur != ptr::null_mut() {
                if ((*cur).free_bytes as usize) >= sz {
                    if let Ok(addr) = (*cur).allocate(layout) {
                        return Ok(addr);
                    }
                }

                cur = (*cur).next_zone;
            }

            /* Make a new zone to allocate from */
            if let Ok(vaddr) = heap_pages::allocate(0x2000) {
                self.zone_list = LargeZone::init_at(vaddr, self.zone_list);
                return (*self.zone_list).allocate(layout);
            }
        }

        Err(AllocationError::NoFreeVirtualMemory)
    }

    unsafe fn deallocate(&mut self, addr: usize, layout: Layout) {
        let zone = LargeZone::zone_for_addr(addr);

        if zone != ptr::null_mut() {
            (*zone).deallocate(addr, layout);
        }
    }

    unsafe fn add_page(&mut self, vaddr: usize) {
        self.zone_list = LargeZone::init_at(vaddr, self.zone_list);
    }

    fn reclaim_pages(&mut self) -> *mut LargeZone {
        let mut cur = self.zone_list;
        let mut reclaim_list: *mut LargeZone = ptr::null_mut();

        unsafe {
            while cur != ptr::null_mut() {
                let next = (*cur).next_zone;

                if (*cur).n_blocks == 1
                    && (*cur).blocks[0].free
                    && (*cur).blocks[0].size == (*cur).free_bytes
                {
                    // reclaim this zone
                    let prev = (*cur).prev_zone;

                    if prev != ptr::null_mut() {
                        (*prev).next_zone = next;
                    }

                    if next != ptr::null_mut() {
                        (*next).prev_zone = prev;
                    }

                    (*cur).next_zone = ptr::null_mut();
                    if reclaim_list != ptr::null_mut() {
                        (*reclaim_list).next_zone = cur;
                        (*cur).prev_zone = reclaim_list;
                        reclaim_list = cur;
                    } else {
                        reclaim_list = cur;
                        (*cur).prev_zone = ptr::null_mut();
                    }
                }

                cur = next;
            }
        }

        reclaim_list
    }
}

unsafe impl Send for LargeZoneAllocator {}
unsafe impl Sync for LargeZoneAllocator {}

pub unsafe fn initialize(init_addr: usize, n_pages: usize) {
    if n_pages % 2 == 1 {
        panic!("number of pages for LZA init must be divisible by 2");
    }

    let mut lock = KERNEL_LZA.init(|| LargeZoneAllocator::new()).lock();
    for i in 0..(n_pages / 2) {
        let addr = init_addr + (i * 0x2000);
        lock.zone_list = LargeZone::init_at(addr, lock.zone_list);
    }
}

pub fn allocate(layout: Layout) -> Result<usize, AllocationError> {
    KERNEL_LZA.lock().allocate(layout)
}

pub unsafe fn deallocate(addr: usize, layout: Layout) {
    KERNEL_LZA.lock().deallocate(addr, layout)
}

pub unsafe fn add_page(addr: usize) {
    KERNEL_LZA.lock().add_page(addr);
}

pub fn reclaim_pages() -> impl Iterator<Item = usize> {
    let p = KERNEL_LZA.lock().reclaim_pages();
    iter::successors(NonNull::new(p), |p| unsafe {
        NonNull::new((*p.as_ptr()).next_zone)
    })
    .map(|p| p.as_ptr() as usize)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::malloc;
    use crate::malloc::tests::TestAlloc;
    use crate::rng::MersenneTwister64;
    use crate::test::TEST_SEED;
    use kernel_test_macro::kernel_test;

    use alloc_crate::vec::Vec;

    unsafe fn random_alloc(
        zone: *mut LargeZone,
        rng: &mut MersenneTwister64,
    ) -> Result<(usize, Layout), AllocationError> {
        let r = rng.generate() as usize;
        let sz = 512 + (r % (7160 - 512));

        let layout = Layout::from_size_align(sz, 512).unwrap();
        Ok(((*zone).allocate(layout)?, layout))
    }

    const TEST_REPS: usize = 50;
    unsafe fn zone_alloc_test_pattern(seed: u64, rng: &mut MersenneTwister64) {
        rng.seed(seed);
        let zone_vaddr = malloc::heap_pages::allocate(0x2000).unwrap();
        ptr::write_bytes(zone_vaddr as *mut u8, 0, 0x2000);

        let zone = LargeZone::init_at(zone_vaddr, ptr::null_mut());
        let mut allocs: Vec<(usize, Layout)> = Vec::with_capacity(16);

        for _ in 0..TEST_REPS {
            if allocs.len() > 0 {
                let n_deallocs = (rng.generate() as usize) % allocs.len();

                // deallocate random blocks
                for i in 0..n_deallocs {
                    let idx = (rng.generate() as usize) % allocs.len();
                    let (addr, layout) = allocs.swap_remove(idx);

                    ptr::write_bytes(addr as *mut u8, 0, layout.size());
                    (*zone).deallocate(addr, layout);
                }
            }

            // generate a sequence of new blocks to allocate
            let mut new_blocks = [0u16; 16];
            let mut head: usize = 0;

            for i in 0..((*zone).n_blocks as usize) {
                if (*zone).blocks[i].free {
                    let mut blk_sz = (*zone).blocks[i].size;
                    while blk_sz >= 512 {
                        let m: u64;
                        if blk_sz > 512 {
                            m = rng.generate() % ((blk_sz - 512) as u64);
                        } else {
                            m = 0;
                        }

                        let b = 512 + (m as u16);
                        let mut effective_sz = b;

                        if b & 511 != 0 {
                            // round up to a multiple of 512
                            effective_sz = (b & !511) + 512;
                        }

                        if effective_sz > blk_sz {
                            break;
                        }

                        new_blocks[head] = b;
                        head += 1;
                        blk_sz -= effective_sz;
                    }
                }
            }

            if head == 0 {
                continue;
            }

            let (blk, _) = new_blocks.split_at_mut(head);
            rng.shuffle(blk);

            // allocate a subsequence of those blocks
            let n_alloc = (rng.generate() as usize) % blk.len();
            for i in 0..n_alloc {
                let sz = new_blocks[i];
                let layout = Layout::from_size_align(sz as usize, 512).unwrap();
                let addr = match (*zone).allocate(layout) {
                    Ok(a) => a,
                    Err(e) => panic!(
                        "failed to allocate block of size {} (seed: {:#x}) - {:?} (free space: {})",
                        sz,
                        seed,
                        e,
                        (*zone).free_bytes
                    ),
                };

                // make sure the address is aligned
                assert_eq!(
                    addr & 511,
                    0,
                    "allocation is not aligned (seed: {:#x}, size {})",
                    seed,
                    sz
                );

                // make sure the address is within the bounds of the zone
                assert!(
                    addr > zone_vaddr && (addr - zone_vaddr) < 0x2000,
                    "zone {:#018x} allocated out-of-bounds (addr {}, size {}, seed {:#x})",
                    zone_vaddr,
                    addr,
                    sz,
                    seed
                );

                // make sure we're not overlapping with another block
                let p = addr as *mut u8;
                for offset in 0..(sz as isize) {
                    let q = p.offset(offset);
                    assert_eq!(
                        *q, 0,
                        "double allocation detected (seed: {:#x}, size {})",
                        seed, sz
                    );
                }

                // watermark this block
                ptr::write_bytes(p, 0xA5, sz as usize);
                allocs.push((addr, layout));
            }
        }

        for (addr, layout) in allocs {
            (*zone).deallocate(addr, layout);
        }

        malloc::heap_pages::deallocate(zone_vaddr, 0x2000);
    }

    #[kernel_test]
    fn test_large_zones() {
        let mut seed_gen = MersenneTwister64::new(TEST_SEED);
        let mut sub_rng = MersenneTwister64::new(0);

        for _ in 0..20 {
            unsafe {
                zone_alloc_test_pattern(seed_gen.generate(), &mut sub_rng);
            }
        }
    }

    const LZA_TEST_ALLOCS: usize = 500;

    #[kernel_test]
    fn test_lza() {
        let mut rng = MersenneTwister64::new(TEST_SEED);
        let mut allocs: Vec<TestAlloc> = Vec::with_capacity(LZA_TEST_ALLOCS);

        for i in 0..LZA_TEST_ALLOCS {
            let size = 512 + (rng.generate() % (7160 - 512)) as usize;
            let layout = Layout::from_size_align(size, 512).unwrap();

            let addr = match allocate(layout) {
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
            let this_end = allocs[i].addr + allocs[i].size;
            let next_start = allocs[i + 1].addr;

            assert!(
                next_start >= this_end,
                "found overlapping allocations: {} and {}",
                allocs[i],
                allocs[i + 1]
            );
        }

        for alloc in allocs {
            let layout = Layout::from_size_align(alloc.size, 512).unwrap();
            unsafe {
                deallocate(alloc.addr, layout);
            }
        }

        unsafe {
            for addr in reclaim_pages() {
                malloc::heap_pages::deallocate(addr, 0x2000);
            }
        }
    }
}
