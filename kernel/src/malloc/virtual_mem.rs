use crate::avl_tree::AVLTree;
use crate::paging::{is_page_aligned, round_to_next_page, round_to_prev_page};

use alloc::rc::Rc;
use alloc::vec::Vec;
use core::cell::{Ref, RefCell, RefMut};
use core::cmp::Ordering;

#[derive(Debug, Clone)]
struct VirtualMemoryRange {
    start: usize,
    end: usize,
    free_list_index: Option<usize>,
}

impl VirtualMemoryRange {
    fn new(start: usize, end: usize) -> VirtualMemoryRange {
        if !is_page_aligned(start) || !is_page_aligned(end) {
            panic!(
                "attempted to create non-aligned virtual memory range at {:#016x} - {:#016x}",
                start, end
            );
        }

        VirtualMemoryRange {
            start: start,
            end: end,
            free_list_index: None,
        }
    }

    fn size(&self) -> usize {
        return self.end - self.start;
    }

    fn is_free(&self) -> bool {
        self.free_list_index.is_some()
    }
}

#[derive(Debug, Clone)]
#[repr(transparent)]
struct RangeWrapper {
    range: Rc<RefCell<VirtualMemoryRange>>,
}

impl RangeWrapper {
    fn borrow(&self) -> Ref<'_, VirtualMemoryRange> {
        self.range.borrow()
    }

    fn borrow_mut(&self) -> RefMut<'_, VirtualMemoryRange> {
        self.range.borrow_mut()
    }

    fn new(range: VirtualMemoryRange) -> RangeWrapper {
        RangeWrapper {
            range: Rc::new(RefCell::new(range)),
        }
    }

    fn start(&self) -> usize {
        let b = self.range.borrow();
        b.start
    }
}

impl PartialEq for RangeWrapper {
    fn eq(&self, rhs: &RangeWrapper) -> bool {
        let r = rhs.borrow();
        let s = self.borrow();

        r.size() == s.size()
    }
}

impl Eq for RangeWrapper {}

impl PartialOrd for RangeWrapper {
    fn partial_cmp(&self, rhs: &RangeWrapper) -> Option<Ordering> {
        let r = rhs.borrow();
        let s = self.borrow();

        let s1 = r.size();
        let s2 = s.size();

        Some(s1.cmp(&s2))
    }
}

impl Ord for RangeWrapper {
    fn cmp(&self, rhs: &RangeWrapper) -> Ordering {
        let r = rhs.borrow();
        let s = self.borrow();

        let s1 = r.size();
        let s2 = s.size();

        s1.cmp(&s2)
    }
}

struct VirtualMemoryAllocator {
    regions: AVLTree<RangeWrapper, usize>, /* indexed by address */
    free: Vec<RangeWrapper>,
}

impl VirtualMemoryAllocator {
    fn add_range(&mut self, range: RangeWrapper, free: bool) {
        self.regions.insert(range.start(), range.clone());
        if free {
            let mut b = range.borrow_mut();
            b.free_list_index = Some(self.free.len());
            drop(b);

            self.free.push(range);
            self.free_list_sift_up(self.free.len() - 1);
        }
    }

    fn remove_free_list_entry(&mut self, idx: usize) -> RangeWrapper {
        let range = self.free.swap_remove(idx);
        for ent in self.free.iter_mut().skip(idx) {
            let mut b = ent.borrow_mut();
            let list_idx = b.free_list_index.as_mut().unwrap();
            *list_idx -= 1;
        }
        self.free_list_sift_down(idx);

        range
    }

    fn free_list_sift_up(&mut self, idx: usize) {
        use core::mem::swap;
        if idx == 0 {
            return;
        }

        let parent_idx = (idx - 1) >> 1;
        let parent = &self.free[parent_idx];
        let child = &self.free[idx];

        if *child > *parent {
            swap(
                &mut child.borrow_mut().free_list_index,
                &mut parent.borrow_mut().free_list_index,
            );

            drop(child);
            drop(parent);

            self.free.swap(parent_idx, idx);

            return self.free_list_sift_up(parent_idx);
        }
    }

    fn free_list_sift_down(&mut self, idx: usize) {
        use core::mem::swap;
        if idx >= self.free.len() {
            return;
        }

        let mut swap_idx = idx;

        if let Some(c1) = self.free.get((idx << 1) + 1) {
            if (*c1) > self.free[swap_idx] {
                swap_idx = (idx << 1) + 1;
            }
        }

        if let Some(c2) = self.free.get((idx << 1) + 2) {
            if (*c2) > self.free[swap_idx] {
                swap_idx = (idx << 1) + 2;
            }
        }

        if swap_idx != idx {
            self.free.swap(idx, swap_idx);

            let mut cur = self.free[idx].borrow_mut();
            let mut larger = self.free[swap_idx].borrow_mut();

            swap(&mut cur.free_list_index, &mut larger.free_list_index);
            drop(cur);
            drop(larger);

            return self.free_list_sift_down(swap_idx);
        }
    }

    pub fn register_memory(&mut self, start: usize, end: usize) {
        let start = round_to_next_page(start);
        let end = round_to_prev_page(end);
        self.add_range(RangeWrapper::new(VirtualMemoryRange::new(start, end)), true);
    }

    pub fn allocate(&mut self, size: usize) -> Option<usize> {
        let alloc_sz = round_to_next_page(size);

        if let Some(wrapper) = self.free.get(0) {
            let range = wrapper.borrow();
            if range.size() < alloc_sz {
                return None;
            }
        } else {
            return None;
        }

        /* Pull the free region with the largest size off the list. */
        let wrapper = self.remove_free_list_entry(0);
        let mut range = wrapper.borrow_mut();

        /* We're going to be updating this range's key, so remove it from the tree. */
        self.regions.delete(range.start);

        /* Add a new region for the allocation. */
        let alloc_start = range.start;
        let alloc_end = alloc_start + alloc_sz;
        self.add_range(
            RangeWrapper::new(VirtualMemoryRange::new(alloc_start, alloc_end)),
            false,
        );

        /* If some of the free region still remains, add it back. */
        if range.end > alloc_end && range.end - alloc_end >= 0x1000 {
            range.start = alloc_end;
            drop(range);

            self.add_range(wrapper, true);
        }

        Some(alloc_start)
    }

    pub fn allocate_at(&mut self, start: usize, end: usize) -> Option<usize> {
        let start = round_to_prev_page(start);
        let end = round_to_next_page(end);

        let alloc_sz = end - start;
        if alloc_sz < 0x1000 {
            return None;
        }

        /* Do preliminary checks. */
        let key: usize;
        let free_list_index: usize;
        {
            let opt = self.regions.search_interval(start, |r| {
                let b = r.borrow();
                (b.start, b.end)
            });

            if opt.is_none() {
                return None;
            }

            let wrapper = opt.unwrap();
            let b = wrapper.borrow();
            if !b.is_free() || b.end < end {
                return None;
            }

            key = b.start;
            free_list_index = b.free_list_index.unwrap();
        }

        /* Remove the region from the tree and free list, since we're modifying all of its addresses */
        let wrapper = self.regions.delete(key).unwrap();
        self.remove_free_list_entry(free_list_index);
        let mut range = wrapper.borrow_mut();

        if range.start < start && start - range.start >= 0x1000 {
            /* There's extra free space at the start of the region; re-add it */
            self.add_range(
                RangeWrapper::new(VirtualMemoryRange::new(range.start, start)),
                true,
            );

            range.start = start;
        }

        if range.end > end && end - range.end >= 0x1000 {
            /* Same thing, but with extra space at the end of the region */
            self.add_range(
                RangeWrapper::new(VirtualMemoryRange::new(end, range.end)),
                true,
            );

            range.end = end;
        }

        /* Add the allocated region itself. */
        drop(range);
        self.add_range(wrapper, false);

        Some(start)
    }

    pub fn deallocate(&mut self, start: usize, size: usize) {
        let alloc_sz = round_to_next_page(size);
        let end = start + alloc_sz;

        let opt = self.regions.delete(start);
        if opt.is_none() {
            panic!(
                "Attempt to free unallocated virtual memory range {:#016} - {:#016}",
                start, end
            );
        }

        let wrapper: RangeWrapper = opt.unwrap();
        if wrapper.borrow().is_free() {
            panic!(
                "Attempt to double-free virtual memory range {:#016} - {:#016}",
                start, end
            );
        }
        let mut freed_region = wrapper.borrow_mut();

        /* Determine if adjacent regions are free; if so, we can merge them. */
        let merge_prev: Option<usize>;
        if let Some((_, prev)) = self.regions.predecessor(start) {
            let b = prev.borrow();
            if b.is_free() && b.end == start {
                merge_prev = b.free_list_index;
            } else {
                merge_prev = None;
            }
        } else {
            merge_prev = None;
        }

        let mut merge_next: Option<usize>;
        if let Some((_, next)) = self.regions.successor(start) {
            let b = next.borrow();
            if b.is_free() && b.start == end {
                merge_next = b.free_list_index;
            } else {
                merge_next = None;
            }
        } else {
            merge_next = None;
        }

        if let Some(idx) = merge_prev {
            /* Take the entry off the free list first. */
            let merge_wrapper = self.remove_free_list_entry(idx);
            let prev_range = merge_wrapper.borrow().clone();

            /* Merge the region boundaries. */
            freed_region.start = prev_range.start;
            self.regions.delete(prev_range.start);

            /* Taking this entry off the free list decremented all deeper indices by 1. */
            if merge_next.is_some() {
                let r = merge_next.as_mut().unwrap();
                if *r >= idx {
                    *r -= 1;
                }
            }
        }

        if let Some(idx) = merge_next {
            /* Same deal as before. */
            let merge_wrapper = self.remove_free_list_entry(idx);
            let next_range = merge_wrapper.borrow().clone();

            freed_region.end = next_range.end;
            self.regions.delete(next_range.start);
        }

        /* Add the new range back into the list. */
        drop(freed_region);
        self.add_range(wrapper, true);
    }
}
