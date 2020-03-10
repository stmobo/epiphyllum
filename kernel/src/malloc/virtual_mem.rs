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
    fn new(start: usize, end: usize, free: bool) -> VirtualMemoryRange {
        if !is_page_aligned(start) || !is_page_aligned(end) {
            panic!(
                "attempted to create non-aligned virtual memory range at {:#016x} - {:#016x}",
                start, end
            );
        }

        let free_list_index: Option<usize>;
        if free {
            free_list_index = Some(0);
        } else {
            free_list_index = None;
        }

        VirtualMemoryRange {
            start: start,
            end: end,
            free_list_index,
        }
    }

    fn size(&self) -> usize {
        return self.end - self.start;
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

    fn borrow_mut(&mut self) -> RefMut<'_, VirtualMemoryRange> {
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
    fn add_range(&mut self, start: usize, end: usize, free: bool) {
        let range = RangeWrapper::new(VirtualMemoryRange::new(start, end, free));

        self.regions.insert(range.start(), range.clone());
        if free {
            self.free.push(range.clone());
        }
    }

    fn free_list_sift_up(&mut self, idx: usize) {
        use core::mem::swap;
        if idx == 0 {
            return;
        }

        let parent_idx = (idx - 1) >> 1;
        let parent = &mut self.free[parent_idx];
        let child = &mut self.free[idx];

        if *child > *parent {
            swap(
                &mut child.borrow_mut().free_list_index,
                &mut parent.borrow_mut().free_list_index,
            );

            drop(child);
            drop(parent);

            swap(
                self.free.get_mut(parent_idx).unwrap(),
                self.free.get_mut(idx).unwrap(),
            );

            return self.free_list_sift_up(parent_idx);
        }
    }

    fn free_list_sift_down(&mut self, idx: usize) {
        use core::mem::swap;
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
            let cur = self.free[idx].borrow_mut();
            let larger = self.free[swap_idx].borrow_mut();

            let t = self.free[swap_idx];
            self.free[swap_idx] = self.free[idx];
            self.free[idx] = t;

            swap(&mut cur.free_list_index, &mut larger.free_list_index);
            return self.free_list_sift_down(swap_idx);
        }
    }

    pub fn register_memory(&mut self, start: usize, end: usize) {
        let start = round_to_next_page(start);
        let end = round_to_prev_page(end);
        self.add_range(start, end, true);
    }

    pub fn allocate(&mut self, size: usize) -> Option<usize> {
        let alloc_sz = round_to_next_page(size);
        if let Some(wrapper) = self.free.get_mut(0) {
            let mut range = wrapper.borrow_mut();

            if range.size() >= alloc_sz {
                let alloc_start = range.start;
                let alloc_end = alloc_start + alloc_sz;
                self.add_range(alloc_start, alloc_end, false);

                if range.end > alloc_end && range.end - alloc_end >= 0x1000 {
                    range.start = alloc_end;
                    drop(range);
                    drop(wrapper);
                } else {
                    drop(range);
                    drop(wrapper);
                    self.free.swap_remove(0);
                }

                self.free_list_sift_down(0);

                return Some(alloc_start);
            }
        }

        None
    }
}
