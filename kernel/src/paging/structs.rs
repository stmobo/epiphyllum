use alloc_crate::alloc::Layout;
use core::slice;
use core::sync::atomic::{AtomicU32, Ordering};

use super::PhysicalPointer;
use crate::lock::OnceCell;
use crate::malloc::physical_mem;
use crate::malloc::{PhysicalMemory, VirtualMemory};
use crate::multiboot::MultibootInfo;

static PAGE_DATA: OnceCell<&'static [PageData]> = OnceCell::new();

#[derive(Debug)]
pub struct PageData {
    pfn: usize,
    refcount: AtomicU32,
}

impl PageData {
    /// Get a reference to the PageData for a page frame via its page frame number.
    pub fn get(pfn: usize) -> &'static PageData {
        &PAGE_DATA.get().expect("Paging metadata not initialized")[pfn]
    }

    pub fn get_by_address(physical_address: usize) -> &'static PageData {
        PageData::get(physical_address >> 12)
    }

    /// Increment the reference count for this page frame.
    ///
    /// Returns the new reference count.
    pub unsafe fn increment_refs(&self) -> u32 {
        if self.refcount() > 50000 {
            panic!(
                "corrupted structure at {:#018x} (value = {:#010x})",
                ((&self.refcount) as *const AtomicU32) as usize,
                self.refcount(),
            );
        }

        self.refcount.fetch_add(1, Ordering::SeqCst) + 1
    }

    /// Decrement the reference count for this page frame, saturating at 0.
    ///
    /// Returns the new reference count.
    pub unsafe fn decrement_refs(&self) -> u32 {
        // use a CAS loop here so we can use saturating_sub
        let new: u32 = loop {
            let cur = self.refcount.load(Ordering::SeqCst);
            if cur == 0 {
                return 0;
            }

            let new = cur.saturating_sub(1);
            if self.refcount.compare_and_swap(cur, new, Ordering::SeqCst) == cur {
                break new;
            }
        };

        if new == 0 {
            physical_mem::deallocate_pfn(self.pfn);
        }

        new
    }

    /// Completely clear the reference count for this page frame.
    pub unsafe fn clear_refs(&self) {
        self.refcount.store(0, Ordering::SeqCst);
    }

    /// Get the current reference count for this page frame atomically.
    pub fn refcount(&self) -> u32 {
        self.refcount.load(Ordering::SeqCst)
    }

    /// Get the page frame number to which this struct refers.
    pub fn pfn(&self) -> usize {
        self.pfn
    }

    /// Get the physical address of this page frame.
    pub fn physical_address(&self) -> usize {
        self.pfn << 12
    }

    /// Get a PhysicalPointer to the start of the page described by this struct,
    /// or None if this struct happens to refer to the zero page.
    pub fn as_ptr<T>(&self) -> Option<PhysicalPointer<T>> {
        PhysicalPointer::new(self.physical_address())
    }
}

pub fn initialize<'a>(mb: &'a MultibootInfo) {
    let mut pfn_count: usize = 0;
    if let Some(mem_info) = mb.get_memory_info() {
        for range in mem_info {
            let pfns = (range.length as usize) >> 12;
            pfn_count += pfns;
        }
    }

    let layout = Layout::array::<PageData>(pfn_count).unwrap();
    let alloc_sz = super::round_to_next_page(layout.size());

    // Allocate physical and virtual memory manually to avoid going through the
    // heap_data API:
    let pmem =
        PhysicalMemory::allocate_many(alloc_sz >> 12).expect("could not allocate physical memory");
    let vmem = VirtualMemory::new(alloc_sz).expect("could not allocate virtual memory");

    let array_addr = vmem.address();
    let mut vaddr = vmem.into_address();
    for phys_mem in pmem {
        let n_pages = phys_mem.n_pages();
        let paddr = phys_mem.into_address();

        for i in 0..n_pages {
            if !super::map_virtual_address(vaddr + (i << 12), paddr + (i << 12)) {
                panic!(
                    "could not map virtual address {:#018x} => {:#018x}",
                    vaddr + (i << 12),
                    paddr + (i << 12)
                );
            }
        }

        vaddr += n_pages << 12;
    }

    unsafe {
        let uninit = array_addr as *mut PageData;
        for pfn in 0..pfn_count {
            uninit.offset(pfn as isize).write(PageData {
                pfn,
                refcount: AtomicU32::new(0),
            });
        }

        drop(uninit);
        let data = array_addr as *const PageData;
        let page_data: &'static [PageData] = slice::from_raw_parts(data, pfn_count);

        PAGE_DATA
            .set(page_data)
            .expect("Paging metadata already initialized");
    }

    println!("paging: initialized metadata for {} pageframes", pfn_count);
}

pub fn metadata_initialized() -> bool {
    PAGE_DATA.get().is_some()
}

pub unsafe fn add_page_ref(addr: usize) {
    if let Some(data) = PAGE_DATA.get() {
        data[addr >> 12].increment_refs();
    }
}

pub unsafe fn remove_page_ref(addr: usize) {
    if let Some(data) = PAGE_DATA.get() {
        data[addr >> 12].decrement_refs();
    }
}

pub fn page_metadata() -> Option<&'static [PageData]> {
    PAGE_DATA.get().map(|x| *x)
}
