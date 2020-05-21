use alloc_crate::alloc::{GlobalAlloc, Layout};
use core::ptr;

pub mod large_zone_alloc;
pub mod physical_mem;
pub mod small_zone_alloc;
pub mod virtual_mem;

pub use crate::paging::KERNEL_HEAP_BASE;
pub use physical_mem::PhysicalMemory;
pub use virtual_mem::VirtualMemory;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum AllocationError {
    ReservedMemory,
    AlreadyAllocated,
    NoFreeVirtualMemory,
    NoFreePhysicalMemory,
    InvalidAllocation,
    CouldNotMapAddress,
}

pub mod global_allocator {
    use super::*;

    pub struct KernelHeapAllocator {}

    #[global_allocator]
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

            if let Err(e) = res {
                direct_println!(
                    "malloc: errored allocating {} bytes ({:?})",
                    layout.size(),
                    e
                );
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
    use super::virtual_mem;
    use super::AllocationError;
    use super::{PhysicalMemory, VirtualMemory};
    use crate::paging;

    /// Allocates virtual memory pages from the kernel heap and maps them to
    /// a same-sized physical memory allocation.
    /// This is intended to be more-or-less equivalent to anonymous mmap(2).
    ///
    /// The size of the memory request is in bytes; if the size is not already a
    /// multiple of the page size, it will be rounded up accordingly.
    pub unsafe fn allocate(size: usize) -> Result<usize, AllocationError> {
        let alloc_sz = paging::round_to_next_page(size);
        let n_pages = alloc_sz >> 12;

        let pmem = PhysicalMemory::allocate_many(n_pages)?;
        let vmem = VirtualMemory::new(alloc_sz)?;
        let mut vaddr = vmem.address();
        let mut vspace = paging::AddressSpace::current();

        for phys_block in pmem.iter() {
            if vspace
                .map_page_range(vaddr, phys_block.address(), phys_block.n_pages())
                .is_err()
            {
                let start_addr = vmem.address();
                drop(pmem);
                drop(vmem);
                vspace.unmap_page_range(start_addr, vaddr).unwrap();
                direct_println!("could not map address for {:#018x}", vaddr);

                return Err(AllocationError::CouldNotMapAddress);
            }

            vaddr += phys_block.n_pages() << 12;
        }

        Ok(vmem.into_address())
    }

    /// Deallocates virtual and physical memory previously acquired by a call to
    /// `allocate`.
    ///
    /// As usual, the address and size passed here must correspond to a previous
    /// `allocate` call!
    pub unsafe fn deallocate(vaddr: usize, size: usize) {
        let alloc_sz = paging::round_to_next_page(size);
        let start_addr = paging::round_to_prev_page(vaddr);

        let mut vspace = paging::AddressSpace::current();
        vspace
            .unmap_page_range(start_addr, alloc_sz >> 12)
            .expect("could not unmap pages");
        virtual_mem::deallocate(vaddr, alloc_sz);
    }
}

#[cfg(test)]
mod tests {
    use core::cmp::Ordering;
    use core::fmt;

    #[derive(Debug, Copy, Clone)]
    pub struct TestAlloc {
        pub addr: usize,
        pub size: usize,
    }

    impl PartialEq for TestAlloc {
        fn eq(&self, other: &TestAlloc) -> bool {
            self.addr.eq(&other.addr)
        }
    }

    impl Eq for TestAlloc {}

    impl PartialOrd for TestAlloc {
        fn partial_cmp(&self, other: &TestAlloc) -> Option<Ordering> {
            self.addr.partial_cmp(&other.addr)
        }
    }

    impl Ord for TestAlloc {
        fn cmp(&self, other: &Self) -> Ordering {
            self.addr.cmp(&other.addr)
        }
    }

    impl fmt::Display for TestAlloc {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{:#018x} (size {})", self.addr, self.size)
        }
    }
}
