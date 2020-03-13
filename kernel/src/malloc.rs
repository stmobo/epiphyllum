use alloc::alloc::{GlobalAlloc, Layout};
use core::ptr;

pub mod large_zone_alloc;
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
        } else if layout.size() <= 7160 {
            /* Redirect to large-zone allocator. */
            large_zone_alloc::allocate(layout).map_or(ptr::null_mut(), |addr| addr as *mut u8)
        } else {
            /* Redirect to page allocator. */
            if layout.align() > 0x1000 {
                return ptr::null_mut();
            }

            heap_pages::allocate(layout.size()).map_or(ptr::null_mut(), |addr| addr as *mut u8)
        }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        let min_block_sz: usize = KernelHeapAllocator::get_layout_alloc_size(layout);
        let addr = ptr as usize;

        if min_block_sz <= 512 {
            /* Block was from the small-zone allocator. */
            if !self.sma_ready {
                panic!("attempted to deallocate memory prior to small-object heap init");
            }

            let mut l = KERNEL_SMA.lock();
            l.deallocate(ptr as usize);
        } else if layout.size() <= 7160 {
            large_zone_alloc::deallocate(addr, layout);
        } else {
            heap_pages::deallocate(addr, layout.size());
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

pub mod heap_pages {
    use super::physical_mem;
    use super::virtual_mem;
    use crate::paging;

    /// Allocates virtual memory pages from the kernel heap and maps them to
    /// a same-sized physical memory allocation.
    /// This is intended to be more-or-less equivalent to anonymous mmap(2).
    ///
    /// The size of the memory request is in bytes; if the size is not already a
    /// multiple of the page size, it will be rounded up accordingly.
    pub unsafe fn allocate(size: usize) -> Option<usize> {
        let alloc_sz = paging::round_to_next_page(size);
        let n_pages = alloc_sz / 0x1000;

        let vaddr = virtual_mem::allocate(alloc_sz);
        let paddr = physical_mem::allocate(alloc_sz);

        if vaddr.is_some() && paddr.is_some() {
            let mut success = true;
            let vaddr = vaddr.unwrap();
            let paddr = paddr.unwrap();

            for i in 0..n_pages {
                if !paging::map_virtual_address(vaddr + (0x1000 * i), paddr + (0x1000 * i)) {
                    success = false;
                    break;
                }
            }

            if success {
                return Some(vaddr);
            } else {
                /* Clean up mappings. */
                for i in 0..n_pages {
                    paging::unmap_virtual_address(vaddr + (0x1000 * i));
                }
            }
        }

        /* Something was unsuccessful. Deallocate everything. */
        if vaddr.is_some() {
            virtual_mem::deallocate(vaddr.unwrap(), alloc_sz);
        }

        if paddr.is_some() {
            physical_mem::deallocate(paddr.unwrap(), alloc_sz);
        }

        None
    }

    /// Deallocates virtual and physical memory previously acquired by a call to
    /// `allocate`.
    ///
    /// As usual, the address and size passed here must correspond to a previous
    /// `allocate` call!
    pub unsafe fn deallocate(vaddr: usize, size: usize) {
        use paging::PageTableEntry;

        let alloc_sz = paging::round_to_next_page(size);
        let entry: PageTableEntry =
            paging::get_mapping(vaddr).expect("attempted to free unallocated memory");

        let paddr = entry.physical_address();
        let n_pages = alloc_sz / 0x1000;

        for i in 0..n_pages {
            paging::unmap_virtual_address(vaddr + (i * 0x1000));
        }

        virtual_mem::deallocate(vaddr, alloc_sz);
        physical_mem::deallocate(paddr, alloc_sz);
    }
}
