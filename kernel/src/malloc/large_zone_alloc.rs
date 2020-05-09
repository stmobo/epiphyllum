use alloc_crate::alloc::Layout;
use core::cmp::Ordering;
use core::mem;
use core::ptr;

use crate::paging::round_to_prev_page;

use lazy_static::lazy_static;
use spin::{Mutex, MutexGuard};

lazy_static! {
    static ref KERNEL_LZA: Mutex<LargeZoneAllocator> = Mutex::new(LargeZoneAllocator::new());
}

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
    blocks: [AllocationBlock; 16],
}

const ZONE_HEADER: u32 = 0x414C4F43; // ASCII: "ALOC"

impl LargeZone {
    fn new(addr: usize, next_zone: *mut LargeZone) -> LargeZone {
        let mut zone = LargeZone {
            header: ZONE_HEADER,
            free_bytes: 8192 - (mem::size_of::<LargeZone>() as u16),
            next_zone,
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

    fn allocate(&mut self, layout: Layout) -> Option<usize> {
        let align_mask = layout.align() - 1;

        let blk_count = self.n_blocks;
        for i in 0..blk_count {
            let block: &mut AllocationBlock = &mut self.blocks[i as usize];
            let effective_addr: usize;
            let effective_size: usize;
            let padding_size: usize;

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

                return Some(effective_addr);
            }
        }

        None
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

    fn allocate(&mut self, layout: Layout) -> Option<usize> {
        use super::heap_pages;

        let mut cur = self.zone_list;
        let sz = layout.size();

        unsafe {
            while cur != ptr::null_mut() {
                if ((*cur).free_bytes as usize) >= sz {
                    if let Some(addr) = (*cur).allocate(layout) {
                        return Some(addr);
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

        None
    }

    unsafe fn deallocate(&mut self, addr: usize, layout: Layout) {
        let zone = LargeZone::zone_for_addr(addr);
        if zone != ptr::null_mut() {
            (*zone).deallocate(addr, layout);
        }
    }

    unsafe fn add_pages(&mut self, addr: usize, n_pages: usize) {
        if n_pages % 2 != 0 {
            panic!("number of pages not divisible by 2");
        }

        for i in 0..(n_pages / 2) {
            let vaddr = addr + (i * 0x2000);
            self.zone_list = LargeZone::init_at(vaddr, self.zone_list);
        }
    }
}

unsafe impl Send for LargeZoneAllocator {}
unsafe impl Sync for LargeZoneAllocator {}

pub unsafe fn initialize(init_addr: usize, n_pages: usize) {
    if n_pages % 2 == 1 {
        panic!("number of pages for LZA init must be divisible by 2");
    }

    let mut lock: MutexGuard<'_, LargeZoneAllocator> = KERNEL_LZA.lock();
    for i in 0..(n_pages / 2) {
        let addr = init_addr + (i * 0x2000);
        lock.zone_list = LargeZone::init_at(addr, lock.zone_list);
    }
}

pub fn allocate(layout: Layout) -> Option<usize> {
    KERNEL_LZA.lock().allocate(layout)
}

pub unsafe fn deallocate(addr: usize, layout: Layout) {
    KERNEL_LZA.lock().deallocate(addr, layout)
}

pub unsafe fn add_pages(addr: usize, n_pages: usize) {
    KERNEL_LZA.lock().add_pages(addr, n_pages);
}
