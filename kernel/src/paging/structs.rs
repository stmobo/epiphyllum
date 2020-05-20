use alloc_crate::boxed::Box;
use core::mem::MaybeUninit;
use core::sync::atomic::{AtomicU32, Ordering};

use super::round_to_prev_page;
use super::PhysicalPointer;
use crate::lock::OnceCell;
use crate::multiboot::MultibootInfo;

static PAGE_DATA: OnceCell<Box<[PageData]>> = OnceCell::new();

#[derive(Debug)]
pub struct PageData {
    pfn: usize,
    refcount: AtomicU32,
}

impl PageData {
    pub fn get(phys_addr: usize) -> &'static PageData {
        let pfn = round_to_prev_page(phys_addr) >> 12;
        &PAGE_DATA.get().expect("Paging metadata not initialized")[pfn]
    }

    pub fn increment_refs(&self) -> u32 {
        self.refcount.fetch_add(1, Ordering::SeqCst) + 1
    }

    pub fn decrement_refs(&self) -> u32 {
        // use a CAS loop here so we can use saturating_sub
        loop {
            let cur = self.refcount.load(Ordering::SeqCst);
            let new = cur.saturating_sub(1);
            if self.refcount.compare_and_swap(cur, new, Ordering::SeqCst) == cur {
                return new;
            }
        }
    }

    pub fn refcount(&self) -> u32 {
        self.refcount.load(Ordering::SeqCst)
    }

    pub fn physical_address(&self) -> usize {
        self.pfn << 12
    }

    pub fn as_ptr<T>(&self) -> Option<PhysicalPointer<T>> {
        PhysicalPointer::new(self.physical_address())
    }
}

pub fn initialize<'a>(mb: &'a MultibootInfo) {
    let mut pfn_count: usize = 0;
    if let Some(mem_info) = mb.get_memory_info() {
        for range in mem_info {
            let pfns = round_to_prev_page(range.length as usize) >> 12;
            pfn_count += pfns;
        }
    }

    let mut data: Box<[MaybeUninit<PageData>]> = Box::new_uninit_slice(pfn_count);
    unsafe {
        for pfn in 0..pfn_count {
            data[pfn].as_mut_ptr().write(PageData {
                pfn,
                refcount: AtomicU32::new(0),
            });
        }

        PAGE_DATA
            .set(data.assume_init())
            .expect("Paging metadata already initialized");
    }

    println!("paging: initialized pageframe metadata");
}
