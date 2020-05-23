use core::convert::TryInto;
use core::mem;
use core::ops::{Deref, DerefMut, Index, IndexMut};
use core::ptr;
use core::ptr::NonNull;
use core::slice;
use core::slice::SliceIndex;

use alloc_crate::alloc;
use alloc_crate::alloc::Layout;
use alloc_crate::vec::Vec;

const MAX_ARENA_SIZE: usize = 6144; // 1.5 pages
const MAX_NODE_SIZE: usize = 1024;

#[derive(Debug)]
#[repr(transparent)]
pub struct Arena<T> {
    data: NonNull<T>,
}

impl<T> Arena<T> {
    fn new() -> Arena<T> {
        let layout = Arena::<T>::layout();

        unsafe {
            let p = alloc::alloc(layout);
            if let Some(p) = NonNull::new(p) {
                Arena { data: p.cast() }
            } else {
                alloc::handle_alloc_error(layout);
            }
        }
    }

    const fn layout() -> Layout {
        let elem_sz = Arena::<T>::padded_elem_sz();
        let n_elems = Arena::<T>::capacity();
        let alloc_sz = elem_sz * n_elems;

        // This is safe:
        // - The alignment returned by mem::align_of::<T>() presumably meets
        //     the invariants required by Layout.
        // - alloc_sz is already rounded up to a multiple of the alignment
        //     (by padded_elem_sz) and is bounded by MAX_ARENA_SIZE.
        // We also deliberately don't support ZSTs.
        unsafe { Layout::from_size_align_unchecked(alloc_sz, mem::align_of::<T>()) }
    }

    /// Round up the size of T to the nearest multiple of its alignment.
    const fn padded_elem_sz() -> usize {
        let align = mem::align_of::<T>();
        let sz = mem::size_of::<T>();
        sz.wrapping_add(align).wrapping_sub(1) & !align.wrapping_sub(1)
    }

    /// Get the number of elements within this arena type.
    const fn capacity() -> usize {
        let sz = Arena::<T>::padded_elem_sz();
        MAX_ARENA_SIZE / sz
    }
}

impl<T> Drop for Arena<T> {
    fn drop(&mut self) {
        unsafe {
            // Deallocate our memory block.
            let p = self.data.as_ptr() as *mut u8;
            alloc::dealloc(p, Arena::<T>::layout());
        }
    }
}

impl<T> Deref for Arena<T> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        unsafe { slice::from_raw_parts(self.data.as_ptr() as *const T, Self::capacity()) }
    }
}

impl<T> DerefMut for Arena<T> {
    fn deref_mut(&mut self) -> &mut [T] {
        unsafe { slice::from_raw_parts_mut(self.data.as_ptr(), Self::capacity()) }
    }
}

impl<T, I: SliceIndex<[T]>> Index<I> for Arena<T> {
    type Output = I::Output;

    fn index(&self, index: I) -> &Self::Output {
        Index::index(&**self, index)
    }
}

impl<T, I: SliceIndex<[T]>> IndexMut<I> for Arena<T> {
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        IndexMut::index_mut(&mut **self, index)
    }
}

#[derive(Debug)]
pub struct ArenaList<T> {
    arenas: Vec<Arena<T>>,
    len: usize,
}

impl<T> ArenaList<T> {
    pub fn new() -> ArenaList<T> {
        debug_assert!(
            Arena::<T>::padded_elem_sz() <= MAX_NODE_SIZE,
            "Arena elements too large ({} > {})",
            Arena::<T>::padded_elem_sz(),
            MAX_NODE_SIZE
        );

        ArenaList {
            arenas: Vec::new(),
            len: 0,
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn capacity(&self) -> usize {
        Arena::<T>::capacity() * self.arenas.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Get the index of the arena, and the offset within that arena, that
    /// should be used to access the given element.
    const fn arena_index(element_index: usize) -> (usize, usize) {
        let offset = element_index % Arena::<T>::capacity();
        let arena = element_index / Arena::<T>::capacity();
        (arena, offset)
    }

    pub fn get<I: Into<usize>>(&self, index: I) -> Option<&T> {
        let index: usize = index.into();
        if index >= self.len {
            return None;
        }

        let (arena, offset) = Self::arena_index(index);
        self.arenas.get(arena).and_then(|a| a.get(offset))
    }

    pub fn get_mut<I: Into<usize>>(&mut self, index: I) -> Option<&mut T> {
        let index: usize = index.into();
        if index >= self.len {
            return None;
        }

        let (arena, offset) = Self::arena_index(index);
        self.arenas.get_mut(arena).and_then(|a| a.get_mut(offset))
    }

    pub fn element_pointer(&mut self, index: usize) -> *mut T {
        if index >= self.len {
            panic!(
                "index out of bounds (the len is {} but the index is {})",
                self.len, index
            );
        }

        let (arena, offset) = Self::arena_index(index);
        unsafe {
            let p = self.arenas[arena].data.as_ptr();
            p.add(offset)
        }
    }

    pub fn push(&mut self, value: T) {
        let (arena, offset) = Self::arena_index(self.len);
        debug_assert!(arena <= self.arenas.len(), "list length corrupted");

        if arena == self.arenas.len() {
            /* Need to add a new arena. */
            self.arenas.push(Arena::new());
        }

        let insert_arena = &mut self.arenas[arena];
        unsafe {
            let p = insert_arena.data.as_ptr();
            ptr::write(p.add(offset), value);
        }

        self.len += 1;
    }

    pub fn swap_remove<I: Into<usize>>(&mut self, index: I) -> T {
        if self.len == 0 {
            panic!("attempt to swap_remove from empty list");
        }

        let index: usize = index.into();
        let swap_to = self.element_pointer(index);
        let last_elem = self.element_pointer(self.len - 1);
        self.len -= 1;

        unsafe {
            let removed = ptr::read(swap_to);
            if swap_to != last_elem {
                ptr::write(swap_to, ptr::read(last_elem));
            }

            removed
        }
    }
}

impl<T> Drop for ArenaList<T> {
    fn drop(&mut self) {
        if self.arenas.is_empty() {
            // don't need to drop anything
            return;
        }

        for arena in 0..(self.arenas.len() - 1) {
            // Drop everything inside these arenas:
            let p = self.arenas[arena].data.as_ptr();
            for j in 0..Arena::<T>::capacity() {
                unsafe {
                    ptr::drop_in_place(p.add(j));
                }
            }
        }

        // Drop the remaining items in the last (non-full) arena
        let rem = self.len % Arena::<T>::capacity();
        let p = self.arenas[self.arenas.len() - 1].data.as_ptr();
        for i in 0..rem {
            unsafe {
                ptr::drop_in_place(p.add(i));
            }
        }

        // each Arena's drop impl will handle deallocating memory
    }
}

impl<T, I: TryInto<usize>> Index<I> for ArenaList<T> {
    type Output = T;

    fn index(&self, index: I) -> &T {
        let index: usize = match index.try_into() {
            Ok(x) => x,
            Err(_) => panic!("could not convert index to usize"),
        };

        if index >= self.len {
            panic!(
                "index out of bounds (the len is {} but the index is {})",
                self.len, index
            );
        }

        let (arena, offset) = Self::arena_index(index);
        &self.arenas[arena][offset]
    }
}

impl<T, I: TryInto<usize>> IndexMut<I> for ArenaList<T> {
    fn index_mut(&mut self, index: I) -> &mut T {
        let index: usize = match index.try_into() {
            Ok(x) => x,
            Err(_) => panic!("could not convert index to usize"),
        };

        if index >= self.len {
            panic!(
                "index out of bounds (the len is {} but the index is {})",
                self.len, index
            );
        }

        let (arena, offset) = Self::arena_index(index);
        &mut self.arenas[arena][offset]
    }
}

unsafe impl<T> Sync for ArenaList<T> {}
unsafe impl<T> Send for ArenaList<T> {}
