use alloc::alloc::{GlobalAlloc, Layout};

pub mod physical_mem;
pub mod small_zone_alloc;
pub mod virtual_mem;

use small_zone_alloc::SmallZoneAllocator;
use small_zone_alloc::KERNEL_SMA;

pub use crate::paging::KERNEL_HEAP_BASE;
pub use physical_mem::PhysicalMemory;

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

#[alloc_error_handler]
pub fn kernel_alloc_failed(layout: core::alloc::Layout) -> ! {
    panic!(
        "could not satisfy kernel heap allocation request for {} bytes",
        layout.size()
    );
}

pub unsafe fn initialize_small_heap(init_addr: usize, n_pages: usize) {
    let mut l = KERNEL_SMA.lock();
    *l = SmallZoneAllocator::new(init_addr, n_pages);

    KERNEL_ALLOCATOR.sma_ready = true;
}
