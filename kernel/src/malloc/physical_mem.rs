use alloc_crate::rc::Rc;
use alloc_crate::vec::Vec;
use core::cell::RefCell;
use core::cmp::Ordering;
use core::mem;
use core::ops::{Bound, Range};

use super::AllocationError;
use crate::lock::LockedGlobal;
use crate::paging;
use crate::paging::{PhysicalPointer, PAGE_MASK};
use crate::structures::AVLTree;
use crate::structures::Bitmask64;

const BUDDY_ALLOC_MAX_SIZE: usize = 0x1000usize << 8; // bytes
const BUDDY_ALLOC_ALIGN_MASK: usize = !(BUDDY_ALLOC_MAX_SIZE - 1);

static KERNEL_PMA: LockedGlobal<PhysicalMemoryAllocator> = LockedGlobal::new();

#[derive(Debug, Clone)]
struct BuddyAllocator {
    mem_addr: usize,
    region_end: usize,
    ord_0_bitmap: [Bitmask64; 4],
    ord_1_bitmap: [Bitmask64; 2],
    ord_2_bitmap: Bitmask64,
    hi_ord_bitmap: Bitmask64,
    n_blocks: [u16; 9],
    free_bytes: usize,
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum BuddyAllocatorError {
    RegionTooSmall(usize),
    RegionTooLarge(usize),
}

impl BuddyAllocator {
    fn new(addr: usize, region_len: usize) -> Result<BuddyAllocator, BuddyAllocatorError> {
        if region_len < 0x1000 {
            return Err(BuddyAllocatorError::RegionTooSmall(region_len));
        } else if region_len > (0x1000 * 256) {
            return Err(BuddyAllocatorError::RegionTooLarge(region_len));
        }

        let mut ord = 8u64;
        let mut block_sz = 0x1000usize << 8;
        let mut remaining_region_size = region_len & PAGE_MASK;
        let mut cur_addr = addr;

        let mut allocator = BuddyAllocator {
            mem_addr: addr,
            region_end: addr + region_len,
            ord_0_bitmap: [Bitmask64::all_zeros(); 4],
            ord_1_bitmap: [Bitmask64::all_zeros(); 2],
            ord_2_bitmap: Bitmask64::all_zeros(),
            hi_ord_bitmap: Bitmask64::all_zeros(),
            n_blocks: [0; 9],
            free_bytes: 0,
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

        debug_assert!(self.get_block_state(order, index));

        self.set_block_state(order, index, false);
        self.set_block_state(order - 1, index << 1, true);
        self.set_block_state(order - 1, (index << 1) + 1, true);
    }

    fn find_free_block_single(&self, order: u64) -> Option<usize> {
        match order {
            0 => {
                for (i, bm) in self.ord_0_bitmap.iter().enumerate() {
                    if let Some(b) = bm.first_set_bit() {
                        return Some((i * 64) + b);
                    }
                }

                None
            }
            1 => {
                for (i, bm) in self.ord_1_bitmap.iter().enumerate() {
                    if let Some(b) = bm.first_set_bit() {
                        return Some((i * 64) + b);
                    }
                }

                None
            }
            2 => self.ord_2_bitmap.first_set_bit(),
            3..=8 => {
                let n_positions = 1u64 << (8 - order);
                let bm =
                    Bitmask64((self.hi_ord_bitmap.0 >> n_positions) & ((1u64 << n_positions) - 1));
                bm.first_set_bit()
            }
            _ => panic!("invalid order {} for buddy allocator", order),
        }
    }

    fn allocate_block(&mut self, order: u64) -> Option<usize> {
        if self.n_blocks[order as usize] > 0 {
            if let Some(idx) = self.find_free_block_single(order) {
                debug_assert!(self.get_block_state(order, idx));
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
                    let hi_block = self.find_free_block_single(ord).unwrap();
                    let mut cur_block = hi_block;

                    for i in 0..n_levels {
                        let cur_lvl = ord - i;
                        self.split_block(cur_lvl, cur_block);
                        cur_block <<= 1;
                    }

                    break;
                }
            }

            if let Some(idx) = self.find_free_block_single(order) {
                debug_assert!(self.get_block_state(order, idx));
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
            } else {
                self.set_block_state(order, index, true);
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
        let bit_idx = index & 0x3F;

        match order {
            0 => self.ord_0_bitmap[index >> 6].get(bit_idx),
            1 => self.ord_1_bitmap[index >> 6].get(bit_idx),
            2 => self.ord_2_bitmap.get(bit_idx),
            3..=8 => {
                let n_positions = 1u64 << (8 - order);
                let bit = n_positions + ((index as u64) & (n_positions - 1));
                self.hi_ord_bitmap.get(bit as usize)
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
        let bm_idx = index >> 6;
        let bit_idx = index & 0x3F;

        match order {
            0 => self.ord_0_bitmap[bm_idx] = self.ord_0_bitmap[bm_idx].set(bit_idx, state),
            1 => self.ord_1_bitmap[bm_idx] = self.ord_1_bitmap[bm_idx].set(bit_idx, state),
            2 => self.ord_2_bitmap = self.ord_2_bitmap.set(bit_idx, state),
            3..=8 => {
                let n_positions = 1u64 << (8 - order);
                let bit = n_positions + ((index as u64) & (n_positions - 1));
                self.hi_ord_bitmap = self.hi_ord_bitmap.set(bit as usize, state);
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

    fn allocate(&mut self, order: u64) -> Option<usize> {
        if order > 8 {
            return None;
        }

        let ret = self
            .allocate_block(order)
            .map(|idx| self.get_addr_for_block(order, idx));

        ret
    }

    fn allocate_at(&mut self, addr: usize, order: u64) -> Option<usize> {
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

    fn deallocate(&mut self, addr: usize, order: u64) {
        if order > 8 {
            panic!("invalid order {} for deallocation", order);
        }

        let block_idx = self.get_block_for_addr(addr, order);
        self.free_block(order, block_idx);
    }

    fn has_order_available(&self, order: u64) -> bool {
        for i in (order as usize)..=8 {
            if self.n_blocks[i] > 0 {
                return true;
            }
        }

        false
    }

    fn region_end(&self) -> usize {
        self.region_end
    }

    fn region_start(&self) -> usize {
        self.mem_addr
    }
}

struct PhysicalMemoryAllocator {
    allocators: AVLTree<usize, Rc<RefCell<BuddyAllocator>>>, // indexed by address
    free: Vec<Rc<RefCell<BuddyAllocator>>>,
}

impl PhysicalMemoryAllocator {
    fn new() -> PhysicalMemoryAllocator {
        PhysicalMemoryAllocator {
            allocators: AVLTree::new(),
            free: Vec::new(),
        }
    }

    fn free_list_cmp(a: &Rc<RefCell<BuddyAllocator>>, b: &Rc<RefCell<BuddyAllocator>>) -> Ordering {
        a.borrow().free_bytes.cmp(&b.borrow().free_bytes).reverse()
    }

    fn sort_free_list(&mut self) {
        self.free.sort_unstable_by(Self::free_list_cmp);
    }

    fn new_allocator(&mut self, addr: usize, len: usize) {
        debug_assert!(len <= (0x1000 * 256));

        let rc = Rc::new(RefCell::new(
            BuddyAllocator::new(addr, len).expect("could not create buddy allocator"),
        ));

        self.allocators
            .insert(addr, rc.clone())
            .expect("allocator already present");
        self.free.push(rc);
    }

    fn register_range(&mut self, addr: usize, len: usize) {
        let mut cur_len = len;
        let mut cur_addr = addr;

        while cur_len >= (0x1000 * 256) {
            self.new_allocator(cur_addr, 0x1000 * 256);
            cur_addr += 0x1000 * 256;
            cur_len -= 0x1000 * 256;
        }

        if cur_len >= 0x1000 {
            self.new_allocator(cur_addr, cur_len);
        }

        self.sort_free_list();
    }

    fn allocate_block(&mut self, order: u64) -> Result<usize, AllocationError> {
        debug_assert!(order <= 8);

        for allocator in self.free.iter() {
            let mut m = allocator.borrow_mut();
            if m.has_order_available(order) {
                let addr = m
                    .allocate(order)
                    .expect("inconsistent buddy allocator state");

                drop(m);
                drop(allocator);

                self.sort_free_list();
                return Ok(addr);
            }
        }

        Err(AllocationError::NoFreePhysicalMemory)
    }

    fn deallocate_block(&mut self, addr: usize, order: u64) {
        let (_, allocator) = self
            .allocators
            .upper_bound(Bound::Included(&addr))
            .expect("could not find originating allocator for deallocation request");

        let mut m = allocator.borrow_mut();
        debug_assert!(m.region_start() <= addr);
        debug_assert!(m.region_end() > addr);

        m.deallocate(addr, order);
        drop(m);

        self.sort_free_list();
    }

    fn allocate_block_at(&mut self, addr: usize, order: u64) -> Result<usize, AllocationError> {
        let (_, allocator) = self
            .allocators
            .upper_bound(Bound::Included(&addr))
            .ok_or(AllocationError::ReservedMemory)?;

        let mut m = allocator.borrow_mut();
        if m.region_end() < addr {
            return Err(AllocationError::ReservedMemory);
        }

        if let Some(addr) = m.allocate_at(addr, order) {
            drop(m);

            self.sort_free_list();
            Ok(addr)
        } else {
            Err(AllocationError::AlreadyAllocated)
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

fn pfn_range(addr: usize, order: u64) -> Range<usize> {
    let pfn_count: usize = 1 << (order as usize);
    let pfn_start = addr >> 12;
    pfn_start..(pfn_start + pfn_count)
}

/// Allocate a block of physical memory pages.
///
/// The order is a buddy allocator order; the number of memory pages actually
/// allocated is (1 << order).
pub fn allocate(order: u64) -> Result<usize, AllocationError> {
    if order > 8 {
        return Err(AllocationError::InvalidAllocation);
    }

    KERNEL_PMA.lock().allocate_block(order)
}

/// Allocate a block of physical memory pages at a specific address.
///
/// The order is a buddy allocator order; the number of memory pages actually
/// allocated is (1 << order).
pub fn allocate_at(addr: usize, order: u64) -> Result<usize, AllocationError> {
    if order > 8 {
        return Err(AllocationError::InvalidAllocation);
    }

    KERNEL_PMA.lock().allocate_block_at(addr, order)
}

/// Mark a block of physical memory pages as being free.
pub unsafe fn deallocate(addr: usize, order: u64) {
    if let Some(page_data) = paging::page_metadata() {
        for pfn in pfn_range(addr, order) {
            page_data[pfn].clear_refs();
        }
    }

    KERNEL_PMA.lock().deallocate_block(addr, order);
}

/// Deallocates a specific page frame by its number.
pub unsafe fn deallocate_pfn(pfn: usize) {
    KERNEL_PMA.lock().deallocate_block(pfn << 12, 0);
}

/// Represents an owned, allocated block of contiguous physical memory.
///
/// This can be used as a safer interface to the physical memory allocator;
/// deallocation is handled automatically via Drop.
#[derive(Debug, Ord, PartialOrd, Eq, PartialEq)]
pub struct PhysicalMemory {
    addr: usize,
    order: u64,
}

impl PhysicalMemory {
    /// Allocate a new block of physical memory.
    ///
    /// The order is a buddy allocator order; the number of memory pages
    /// actually allocated is (1 << order).
    pub fn new(order: u64) -> Result<PhysicalMemory, AllocationError> {
        let addr = allocate(order)?;

        if let Some(page_data) = paging::page_metadata() {
            for pfn in pfn_range(addr, order) {
                unsafe { page_data[pfn].increment_refs() };
            }
        }

        Ok(PhysicalMemory { addr, order })
    }

    /// Allocate a new block of physical memory at a specific address.
    ///
    /// The order is a buddy allocator order; the number of memory pages
    /// actually allocated is (1 << order).
    pub fn new_at(addr: usize, order: u64) -> Result<PhysicalMemory, AllocationError> {
        allocate_at(addr, order)?;
        Ok(PhysicalMemory { addr, order })
    }

    /// Allocate an arbitrary number of (non-contiguous) pages by splitting
    /// the allocation into chunks.
    pub fn allocate_many(n_pages: usize) -> Result<Vec<PhysicalMemory>, AllocationError> {
        let mut pmem: Vec<PhysicalMemory> = Vec::new();
        let mut cur_order: usize = 8;
        let mut cur_page_ct = n_pages;

        while cur_page_ct > 0 {
            if cur_page_ct >= (1 << cur_order) {
                pmem.push(PhysicalMemory::new(cur_order as u64)?);
                cur_page_ct -= 1 << cur_order;
            } else {
                cur_order -= 1;
            }
        }

        Ok(pmem)
    }

    /// Get the address of this physical memory block.
    pub fn address(&self) -> usize {
        self.addr
    }

    /// Get the budy allocator order of this physical memory block.
    pub fn order(&self) -> u64 {
        self.order
    }

    /// Get the number of pages owned by this physical memory block.
    pub fn n_pages(&self) -> usize {
        1 << (self.order as u64)
    }

    /// Get a PhysicalPointer to the start of this memory block.
    pub fn as_ptr<T>(&self) -> PhysicalPointer<T> {
        unsafe { PhysicalPointer::new_unchecked(self.addr) }
    }

    /// Get the range of pageframe numbers owned by this block.
    pub fn pfns(&self) -> impl Iterator<Item = usize> {
        pfn_range(self.addr, self.order)
    }

    /// Map this block of physical memory to contiguous virtual memory, starting
    /// at the virtual address `start`.
    ///
    /// If any page fails to be mapped, the entire target virtual address range
    /// will be unmapped.
    ///
    /// ## Safety
    /// The caller must ensure that the virtual memory range from `start` to
    /// `start + (self.n_pages() * 0x1000)` can be safely mapped or remapped.
    pub unsafe fn map_to(&self, start: usize) -> bool {
        for (i, pfn) in self.pfns().enumerate() {
            let paddr = pfn << 12;
            let vaddr = start + (i << 12);

            if !paging::map_virtual_address(vaddr, paddr) {
                paging::unmap_pages(start, (vaddr - start) >> 12).expect("could not unmap pages");
                return false;
            }
        }

        true
    }

    pub fn into_raw(self) -> (usize, u64) {
        let addr = self.addr;
        let order = self.order;
        mem::forget(self);

        (addr, order)
    }

    pub fn into_address(self) -> usize {
        self.into_raw().0
    }

    pub fn leak(self) {
        mem::forget(self);
    }
}

impl Drop for PhysicalMemory {
    fn drop(&mut self) {
        if let Some(page_data) = paging::page_metadata() {
            for pfn in self.pfns() {
                unsafe { page_data[pfn].decrement_refs() };
            }
        } else {
            unsafe { deallocate(self.addr, self.order) };
        }
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::malloc::tests::TestAlloc;
    use crate::paging;
    use crate::rng::MersenneTwister64;
    use crate::test::TEST_SEED;

    use alloc_crate::vec::Vec;
    use kernel_test_macro::kernel_test;

    const PMA_TEST_ALLOCS: usize = 100;

    #[kernel_test]
    fn test_pma() {
        let mut rng = MersenneTwister64::new(TEST_SEED);
        let mut allocs: Vec<TestAlloc> = Vec::with_capacity(PMA_TEST_ALLOCS);

        for i in 0..PMA_TEST_ALLOCS {
            let order = rng.generate() % 6;

            let addr = match allocate(order) {
                Ok(a) => a,
                Err(e) => panic!(
                    "alloc {} failed (seed: {:#x}, order {}) - {:?}",
                    i, TEST_SEED, order, e
                ),
            };

            allocs.push(TestAlloc {
                addr,
                size: order as usize,
            });
        }

        allocs.sort();
        for i in 0..(allocs.len() - 1) {
            // ensure this alloc does not overlap the next one
            let this_end = allocs[i].addr + (0x1000 << allocs[i].size);
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
                deallocate(alloc.addr, alloc.size as u64);
            }
        }
    }

    #[kernel_test]
    fn test_refcount() {
        let pmem = PhysicalMemory::new(0).unwrap();
        let paddr = pmem.address();
        let pfn = paddr >> 12;

        unsafe {
            // Ensure that the allocator is keeping track of things correctly
            // and that the refcount was properly incremented by the PhysicalMemory
            // constructor:
            let page_data = paging::page_metadata().unwrap();
            assert_eq!(page_data[pfn].refcount(), 1, "incorrect refcount for page");

            let alloc_test = allocate_at(paddr, 0);
            assert_eq!(
                alloc_test,
                Err(AllocationError::AlreadyAllocated),
                "incorrectly overwrote test allocation"
            );

            // Test refcount >1:
            page_data[pfn].increment_refs();
            assert_eq!(page_data[pfn].refcount(), 2, "incorrect refcount for page");

            // Ensure that PhysicalMemory's drop implementation decrements the
            // refcount:
            drop(pmem);
            assert_eq!(page_data[pfn].refcount(), 1, "incorrect refcount for page");

            // Ensure that the drop implementation does _not_ fully deallocate
            // the page:
            let alloc_test = allocate_at(paddr, 0);
            assert_eq!(
                alloc_test,
                Err(AllocationError::AlreadyAllocated),
                "incorrectly overwrote test allocation"
            );

            // Now drop the last ref to the page:
            page_data[pfn].decrement_refs();
            assert_eq!(page_data[pfn].refcount(), 0, "incorrect refcount for page");

            // Ensure that the page was freed:
            let alloc_test = allocate_at(paddr, 0);
            assert_eq!(
                alloc_test,
                Ok(paddr),
                "could not re-allocate test allocation"
            );

            // Clean up:
            deallocate(paddr, 0);
            assert_eq!(page_data[pfn].refcount(), 0, "incorrect refcount for page");
        }
    }

    #[kernel_test]
    fn test_into_address() {
        let pmem = PhysicalMemory::new(0).unwrap();
        let paddr = pmem.address();
        let pfn = paddr >> 12;

        unsafe {
            // Ensure that the allocator is keeping track of things correctly
            // and that the refcount was properly incremented by the PhysicalMemory
            // constructor:
            let page_data = paging::page_metadata().unwrap();
            assert_eq!(page_data[pfn].refcount(), 1, "incorrect refcount for page");

            // Should consume the PhysicalMemory object without messing with
            // the refcount:
            let paddr = pmem.into_address();
            assert_eq!(page_data[pfn].refcount(), 1, "incorrect refcount for page");

            // Clean up:
            deallocate(paddr, 0);
            assert_eq!(page_data[pfn].refcount(), 0, "incorrect refcount for page");
        }
    }
}
