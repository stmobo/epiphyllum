use alloc_crate::alloc::{GlobalAlloc, Layout};
use core::ptr;

pub mod large_zone_alloc;
pub mod physical_mem;
pub mod small_zone_alloc;
pub mod virtual_mem;

pub use crate::paging::KERNEL_HEAP_BASE;
pub use physical_mem::PhysicalMemory;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum AllocationError {
    ReservedMemory,
    NoFreeVirtualMemory,
    NoFreePhysicalMemory,
    InvalidAllocation,
    CouldNotMapAddress,
}

#[cfg(not(test))]
pub mod global_allocator {
    use super::*;

    pub struct KernelHeapAllocator {}

    #[cfg_attr(not(test), global_allocator)]
    pub static mut KERNEL_ALLOCATOR: KernelHeapAllocator = KernelHeapAllocator {};

    fn enforce_min_layout_size(layout: Layout) -> Layout {
        if layout.size() < 8 {
            if layout.align() < 8 {
                return Layout::from_size_align(8, 8).unwrap();
            } else {
                return Layout::from_size_align(8, layout.align()).unwrap();
            }
        }

        layout
    }

    unsafe impl GlobalAlloc for KernelHeapAllocator {
        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            let layout = enforce_min_layout_size(layout);

            let res: Result<usize, AllocationError>;
            if small_zone_alloc::is_valid_sma_block(layout) {
                /* Use small-zone allocator. */
                res = small_zone_alloc::allocate(layout);
            } else if layout.size() < 7160 {
                /* Redirect to large-zone allocator. */
                res = large_zone_alloc::allocate(layout);
            } else if layout.size() > 7160 {
                /* Redirect to page allocator. */
                if layout.align() > 0x1000 {
                    return ptr::null_mut();
                }
                res = heap_pages::allocate(layout.size());
            } else {
                return ptr::null_mut();
            }

            res.map_or(ptr::null_mut(), |addr| addr as *mut u8)
        }

        unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
            let layout = enforce_min_layout_size(layout);
            let addr = ptr as usize;

            if small_zone_alloc::is_valid_sma_block(layout) {
                /* Block was from the small-zone allocator. */
                small_zone_alloc::deallocate(addr);
            } else if layout.size() < 7160 {
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
}

pub mod heap_pages {
    use super::physical_mem;
    use super::virtual_mem;
    use super::AllocationError;
    use crate::paging;

    /// Allocates virtual memory pages from the kernel heap and maps them to
    /// a same-sized physical memory allocation.
    /// This is intended to be more-or-less equivalent to anonymous mmap(2).
    ///
    /// The size of the memory request is in bytes; if the size is not already a
    /// multiple of the page size, it will be rounded up accordingly.
    pub unsafe fn allocate(size: usize) -> Result<usize, AllocationError> {
        let alloc_sz = paging::round_to_next_page(size);
        let n_pages = alloc_sz / 0x1000;

        let paddr = physical_mem::allocate(alloc_sz)?;
        let vaddr = virtual_mem::allocate(alloc_sz);

        if vaddr.is_err() {
            physical_mem::deallocate(paddr, alloc_sz);
            return vaddr;
        }

        let vaddr = vaddr.unwrap();
        let mut status = Ok(vaddr);

        for i in 0..n_pages {
            if !paging::map_virtual_address(vaddr + (0x1000 * i), paddr + (0x1000 * i)) {
                status = Err(AllocationError::CouldNotMapAddress);
                break;
            }
        }

        if status.is_err() {
            /* Something was unsuccessful. Clean up everything. */
            for i in 0..n_pages {
                paging::unmap_virtual_address(vaddr + (0x1000 * i));
            }
            virtual_mem::deallocate(vaddr, alloc_sz);
            physical_mem::deallocate(paddr, alloc_sz);
        }

        status
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
