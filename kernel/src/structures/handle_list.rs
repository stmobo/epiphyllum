use alloc_crate::alloc::{Allocator, Global, Layout, handle_alloc_error};
use core::marker::PhantomData;
use core::ops::{Deref, DerefMut};
use core::pin::Pin;
use core::ptr::NonNull;

use crate::lock::{NoIRQSpinlock, NoIRQSpinlockGuard};

#[derive(Debug)]
#[repr(transparent)]
pub struct LinkWrapper<T>(NonNull<ListNode<T>>);

impl<T> Clone for LinkWrapper<T> {
    fn clone(&self) -> Self {
        LinkWrapper(self.0.clone())
    }
}

impl<T> Copy for LinkWrapper<T> {}

impl<T> Deref for LinkWrapper<T> {
    type Target = ListNode<T>;

    fn deref(&self) -> &Self::Target {
        unsafe { self.0.as_ref() }
    }
}

impl<T> PartialEq for LinkWrapper<T> {
    fn eq(&self, other: &LinkWrapper<T>) -> bool {
        self.0.as_ptr() == other.0.as_ptr()
    }
}

impl<'a, T> From<&'a mut ListNode<T>> for LinkWrapper<T> {
    fn from(val: &'a mut ListNode<T>) -> Self {
        LinkWrapper(val.into())
    }
}

/// An intrusive doubly-linked list node.
///
/// No synchronization is implemented for this type; all operations assume
/// that only one thread is accessing the list at any given moment.
pub struct ListNode<T> {
    data: T,
    prev: Option<Pin<LinkWrapper<T>>>,
    next: Option<Pin<LinkWrapper<T>>>,
}

impl<T> ListNode<T> {
    fn new_in<A: Allocator>(data: T, alloc: &A) -> Pin<LinkWrapper<T>> {
        let layout = Layout::new::<ListNode<T>>();
        if let Ok(p) = alloc.allocate(layout) {
            unsafe {
                let mut p: NonNull<ListNode<T>> = p.cast();

                // Safety: this should be a valid pointer, since we just
                // allocated it with the correct Layout.
                p.as_ptr().write(ListNode {
                    data,
                    prev: None,
                    next: None,
                });

                // Safety:
                // - We just initialized `p`.
                // - LinkWrapper's Deref implementation does not move out of `self`.
                // - There's no way for code to get a &mut ListNode (or a *mut ListNode)
                //   without reaching into the (private) internals of the LinkWrapper.
                Pin::new_unchecked(p.as_mut().into())
            }
        } else {
            handle_alloc_error(layout);
        }
    }

    unsafe fn cleanup<A: Allocator>(ptr: NonNull<ListNode<T>>, alloc: &A) {
        let layout = Layout::new::<ListNode<T>>();

        // Safety: assuming that `ptr` and `alloc` match a previous call to
        // new_in, `ptr` should point to a valid ListNode (so drop_in_place is
        // sound), and the allocator and layout should both match as well
        // (so deallocate is sound).
        ptr.as_ptr().drop_in_place();
        alloc.deallocate(ptr.cast(), layout);
    }

    unsafe fn data_mut<'a>(self: Pin<LinkWrapper<T>>) -> &'a mut T {
        // None of the fields of a ListNode are structurally pinned, so this
        // should be safe.
        let p: LinkWrapper<T> = Pin::into_inner_unchecked(self);
        &mut (*p.0.as_ptr()).data
    }

    unsafe fn prev_mut<'a>(self: Pin<LinkWrapper<T>>) -> &'a mut Option<Pin<LinkWrapper<T>>> {
        let p: LinkWrapper<T> = Pin::into_inner_unchecked(self);
        &mut (*p.0.as_ptr()).prev
    }

    unsafe fn next_mut<'a>(self: Pin<LinkWrapper<T>>) -> &'a mut Option<Pin<LinkWrapper<T>>> {
        let p: LinkWrapper<T> = Pin::into_inner_unchecked(self);
        &mut (*p.0.as_ptr()).next
    }

    unsafe fn unlink(self: Pin<LinkWrapper<T>>) {
        let next = self.next;
        let prev = self.prev;

        if let Some(prev) = self.prev_mut().take() {
            *prev.next_mut() = next;
        }

        if let Some(next) = self.next_mut().take() {
            *next.prev_mut() = prev;
        }
    }

    unsafe fn append(self: Pin<LinkWrapper<T>>, next: Pin<LinkWrapper<T>>) {
        *self.next_mut() = Some(next);
        *next.prev_mut() = Some(self);
    }
}

pub struct ListInternals<T, A: Allocator> {
    head: Option<Pin<LinkWrapper<T>>>,
    tail: Option<Pin<LinkWrapper<T>>>,
    len: usize,
    alloc: A,
}

impl<T, A: Allocator> ListInternals<T, A> {
    fn new_in(alloc: A) -> ListInternals<T, A> {
        ListInternals {
            head: None,
            tail: None,
            len: 0,
            alloc
        }
    }

    fn push_front(&mut self, data: T) -> Pin<LinkWrapper<T>> {
        let node = ListNode::new_in(data, &self.alloc);

        if let Some(head) = self.head.take() {
            // Safety: we should be the only thread accessing this list, since
            // we take &mut self.
            unsafe { node.append(head) };
        }

        if self.tail.is_none() {
            self.tail = Some(node);
        }

        self.head = Some(node);
        self.len += 1;

        node
    }

    fn push_back(&mut self, data: T) -> Pin<LinkWrapper<T>> {
        let node = ListNode::new_in(data, &self.alloc);

        if let Some(tail) = self.tail {
            // Safety: same as push_front.
            unsafe { tail.append(node) };
        }

        if self.head.is_none() {
            self.head = Some(node);
        }

        self.tail = Some(node);
        self.len += 1;

        node
    }

    fn _pop_ptr_front(&mut self) -> Option<Pin<LinkWrapper<T>>> {
        if let Some(head) = self.head.take() {
            unsafe {
                // Safety: we never write into or move the ListNode pointed to
                // here, so we uphold the pinning API contracts.
                let head_ptr = Pin::into_inner_unchecked(head);

                if let Some(tail) = self.tail {
                    let tail_ptr = Pin::into_inner_unchecked(tail);
                    if head_ptr == tail_ptr {
                        self.tail = None;
                    }
                }

                self.head = head_ptr.next;
                drop(head_ptr);

                // Safety: We should have exclusive access to this list via
                // our &mut self reference.
                head.unlink();
                self.len -= 1;

                Some(head)
            }
        } else {
            None
        }
    }

    fn _pop_ptr_back(&mut self) -> Option<Pin<LinkWrapper<T>>> {
        if let Some(tail) = self.tail.take() {
            // Safety: see _pop_ptr_front.
            unsafe {
                let tail_ptr = Pin::into_inner_unchecked(tail);

                if let Some(head) = self.head {
                    let head_ptr = Pin::into_inner_unchecked(head);
                    if tail_ptr == head_ptr {
                        self.head = None;
                    }
                }

                self.tail = tail_ptr.prev;
                drop(tail_ptr);
                tail.unlink();
                self.len -= 1;

                Some(tail)
            }
        } else {
            None
        }
    }

    /// Pops an element off the front of this list.
    ///
    /// Since this interface already requires exclusive access to this list
    /// (via `&mut self`), it directly returns an `Option<&mut T>` instead of
    /// an `AccessGuard`.
    pub fn pop_front(&mut self) -> Option<&mut T> {
        if let Some(p) = self._pop_ptr_front() {
            // Safety: we should be the only thread accessing this list, since
            // we take &mut self.
            Some(unsafe { p.data_mut() })
        } else {
            None
        }
    }

    /// Pops an element off the back of this list.
    ///
    /// Since this interface already requires exclusive access to this list
    /// (via `&mut self`), it directly returns an `Option<&mut T>` instead of
    /// an `AccessGuard`.
    pub fn pop_back(&mut self) -> Option<&mut T> {
        if let Some(p) = self._pop_ptr_back() {
            // Safety: same as pop_front.
            Some(unsafe { p.data_mut() })
        } else {
            None
        }
    }

    /// Immutably iterates over the elements in this list.
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            head: self.head,
            _marker: PhantomData,
        }
    }

    /// Mutably iterates over the elements in this list.
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut {
            node: self.head,
            _marker: PhantomData,
        }
    }

    /// Creates a draining iterator over the elements in this list.
    ///
    /// Using the returned iterator is conceptually similar to repeatedly
    /// calling `pop_front` and/or `pop_back`: elements are popped off the ends
    /// of the list, one at a time, until iteration stops.
    ///
    /// If the iterator is only partially consumed, any unconsumed elements
    /// will remain linked into the list.
    pub fn drain(&mut self) -> Drain<'_, T, A> {
        Drain(self)
    }

    /// Gets the length of this list.
    pub fn len(&self) -> usize {
        self.len
    }
}

impl<T> ListInternals<T, Global> {
    const fn new() -> ListInternals<T, Global> {
        ListInternals {
            head: None,
            tail: None,
            len: 0,
            alloc: Global
        }
    }
}

/// An non-owning, doubly-linked list that provides handles to pushed elements.
///
/// Unlike a regular linked list, elements in this list aren't (fully) owned by
/// the list itself; the list instead shares ownership over stored elements
/// with its clients.
///
/// Pushing an element onto a HandleList returns a handle to that element,
/// allowing for fast access to that element in the future if necessary.
/// In addition, dropping the handle will automatically unlink the element from
/// the list if it hasn't already been popped.
///
/// This type of list is mostly useful for event queues and such.
/// (for example: `WaitQueue`.)
pub struct HandleList<T, A: Allocator = Global> {
    internals: NoIRQSpinlock<ListInternals<T, A>>,
}

impl<T, A: Allocator> HandleList<T, A> {
    /// Creates a new HandleList.
    pub fn new_in(alloc: A) -> HandleList<T, A> {
        HandleList {
            internals: NoIRQSpinlock::new(ListInternals::new_in(alloc)),
        }
    }

    /// Pushes an element onto the front of this list.
    ///
    /// Returns a handle to the pushed node.
    pub fn push_front(&self, data: T) -> NodeHandle<'_, T, A> {
        let mut lock = self.internals.lock();
        let node = lock.push_front(data);
        drop(lock);

        NodeHandle {
            list: self,
            node,
            _marker: PhantomData,
        }
    }

    /// Pushes an element onto the back of this list.
    ///
    /// Returns a handle to the pushed node.
    pub fn push_back(&self, data: T) -> NodeHandle<'_, T, A> {
        let mut lock = self.internals.lock();
        let node = lock.push_back(data);
        drop(lock);

        NodeHandle {
            list: self,
            node,
            _marker: PhantomData,
        }
    }

    /// Pops an element from the front of this list.
    ///
    /// Returns a locked access guard to the popped element, if any.
    pub fn pop_front(&self) -> Option<AccessGuard<'_, T, A>> {
        let mut lock = self.internals.lock();
        lock._pop_ptr_front().map(move |node| AccessGuard {
            lock,
            node,
            _marker: PhantomData,
        })
    }

    /// Pops an element from the back of this list.
    ///
    /// Returns a locked access guard to the popped element, if any.
    pub fn pop_back(&self) -> Option<AccessGuard<'_, T, A>> {
        let mut lock = self.internals.lock();
        lock._pop_ptr_back().map(move |node| AccessGuard {
            lock,
            node,
            _marker: PhantomData,
        })
    }

    /// Acquires an exclusive lock on this list.
    ///
    /// Locking a list is required in order to iterate over it, and also allows
    /// for more efficient popping (without the overhead of repeatedly locking
    /// and unlocking the same spinlock).
    pub fn lock(&self) -> NoIRQSpinlockGuard<'_, ListInternals<T, A>> {
        self.internals.lock()
    }

    /// Gets the number of elements in this list.
    pub fn len(&self) -> usize {
        self.internals.lock().len()
    }
}

impl<T> HandleList<T, Global> {
    pub const fn new() -> HandleList<T, Global> {
        HandleList {
            internals: NoIRQSpinlock::new(ListInternals::new()),
        }
    }
}

// NOTE: implementing Sync for T: Send should be sound due to the internal locks.
unsafe impl<T: Send, A: Allocator + Send> Send for HandleList<T, A> {}
unsafe impl<T: Send, A: Allocator + Sync> Sync for HandleList<T, A> {}

// Note: We don't need to implement Drop, since an HandleList cannot be
// dropped until all NodeHandles pointing into the list are themselves dropped
// (or forgotten), in which case there's nothing we need to explicitly clean up.

/// An owning handle to a node that has been pushed onto a `HandleList`.
///
/// This handle can be used to quickly access the pushed element again.
/// Dropping this handle will automatically unlink the node if it hasn't been
/// popped, then deallocate the node's storage.
pub struct NodeHandle<'a, T, A: Allocator = Global> {
    list: &'a HandleList<T, A>,
    node: Pin<LinkWrapper<T>>,
    _marker: PhantomData<T>,
}

impl<'a, T, A: Allocator> NodeHandle<'a, T, A> {
    /// Gets access to the data in this node by locking its corresponding list.
    ///
    /// This returns an 'access guard' to the node referenced by this handle,
    /// which can be used as a reference to the node's data (via `Deref` and
    /// `DerefMut`.)
    pub fn lock(&self) -> AccessGuard<'_, T, A> {
        AccessGuard {
            lock: self.list.internals.lock(),
            node: self.node,
            _marker: PhantomData,
        }
    }
}

// Safety note: We don't access the actual value contained within the node
// during drop, so we can apply #[may_dangle] to T.
unsafe impl<'a, #[may_dangle] T, A: Allocator> Drop for NodeHandle<'a, T, A> {
    fn drop(&mut self) {
        let mut lock = self.list.internals.lock();
        unsafe {
            // Remove the node from the list entirely:
            let node_ptr = Pin::into_inner_unchecked(self.node);

            let mut at_list_end = false;

            // Safety: these unwrapped pointers are only used for equality
            // comparisons; we don't actually use them to access memory in any
            // way.
            if let Some(head) = lock.head {
                let p = Pin::into_inner_unchecked(head);
                if p == node_ptr {
                    lock.head = node_ptr.next;
                    at_list_end = true;
                }
            }

            if let Some(tail) = lock.tail {
                let p = Pin::into_inner_unchecked(tail);
                if p == node_ptr {
                    lock.tail = node_ptr.prev;
                    at_list_end = true;
                }
            }

            if at_list_end || node_ptr.prev.is_some() || node_ptr.next.is_some() {
                // this node was linked in before, decrement the length
                lock.len -= 1;
            }

            // Safety: We have a lock on the list containing this node
            // (self.list.internals).
            self.node.unlink();

            // Now deallocate the node storage.
            // At this point, we don't care whether or not the node is pinned,
            // because no one should point to it anymore.
            ListNode::cleanup(node_ptr.0, &lock.alloc);
        }
    }
}

// Implementing Sync for T: Send is sound because dereferencing through the
// handle requires locking the list.
unsafe impl<'a, T: Send, A: Allocator + Send> Send for NodeHandle<'a, T, A> {}
unsafe impl<'a, T: Send, A: Allocator + Sync> Sync for NodeHandle<'a, T, A> {}

pub struct AccessGuard<'a, T, A: Allocator = Global> {
    lock: NoIRQSpinlockGuard<'a, ListInternals<T, A>>,
    node: Pin<LinkWrapper<T>>,
    _marker: PhantomData<&'a mut T>,
}

impl<'a, T, A: Allocator> Deref for AccessGuard<'a, T, A> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // Safety:
        // - We own a lock on the list that the node belongs to.
        // - The `data` field on list nodes isn't considered to be pinned.
        unsafe { self.node.data_mut() }
    }
}

impl<'a, T, A: Allocator> DerefMut for AccessGuard<'a, T, A> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // Safety: see Deref.
        unsafe { self.node.data_mut() }
    }
}

// AccessGuard is effectively a smart-reference type, so implement Send/Sync
// only for T: Send + Sync to match &T.
unsafe impl<'a, T: Send + Sync, A: Allocator + Send> Send for AccessGuard<'a, T, A> {}
unsafe impl<'a, T: Send + Sync, A: Allocator + Sync> Sync for AccessGuard<'a, T, A> {}

pub struct Iter<'a, T> {
    head: Option<Pin<LinkWrapper<T>>>,
    _marker: PhantomData<&'a ListNode<T>>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(p) = self.head.take() {
            self.head = p.next;

            // Safety: The returned references have lifetime equal to the list
            // we're iterating over, which should prevent said list from being
            // mutated while we hold any live references from here.
            Some(unsafe { p.data_mut() })
        } else {
            None
        }
    }
}

pub struct IterMut<'a, T> {
    node: Option<Pin<LinkWrapper<T>>>,
    _marker: PhantomData<&'a mut ListNode<T>>,
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(p) = self.node.take() {
            self.node = p.next;

            // Safety: see ListIter.
            Some(unsafe { p.data_mut() })
        } else {
            None
        }
    }
}

pub struct Drain<'a, T, A: Allocator = Global>(&'a mut ListInternals<T, A>);

impl<'a, T, A: Allocator> Iterator for Drain<'a, T, A> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(p) = self.0._pop_ptr_front() {
            // Safety: see ListInternals::pop_front.
            Some(unsafe { p.data_mut() })
        } else {
            None
        }
    }
}

impl<'a, T, A: Allocator> DoubleEndedIterator for Drain<'a, T, A> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if let Some(p) = self.0._pop_ptr_back() {
            // Safety: see ListInternals::pop_back.
            Some(unsafe { p.data_mut() })
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc_crate::vec::Vec;
    use core::sync::atomic::{AtomicBool, Ordering};
    use kernel_test_macro::kernel_test;

    // Sets a boolean flag when it gets dropped.
    struct DropFlagged<'a> {
        flag: &'a AtomicBool,
    }

    impl<'a> DropFlagged<'a> {
        fn new(flag: &'a AtomicBool) -> DropFlagged<'a> {
            DropFlagged { flag }
        }
    }

    impl<'a> Drop for DropFlagged<'a> {
        fn drop(&mut self) {
            self.flag.store(true, Ordering::SeqCst);
        }
    }

    #[kernel_test]
    fn test_pushes() {
        let list: HandleList<u64> = HandleList::new();
        let _h1 = list.push_front(5);
        let _h2 = list.push_back(10);
        let h3 = list.push_front(15);
        let h4 = list.push_back(20);

        assert_eq!(list.len(), 4, "incorrect list length");

        // Test immutable iteration:
        {
            let lock = list.lock();
            let v: Vec<u64> = lock.iter().copied().collect();
            assert_eq!(v, vec![15, 5, 10, 20]);
        }

        // Test mutable access to stored data through a node handle:
        {
            let mut lock = h3.lock();
            *lock = 40;
        }

        {
            let lock = list.lock();
            let v: Vec<u64> = lock.iter().copied().collect();
            assert_eq!(v, vec![40, 5, 10, 20]);
        }

        // Test mutable iteration:
        {
            let mut lock = list.lock();
            let mut v: Vec<&mut u64> = lock.iter_mut().collect();
            *v[3] = 100;
        }

        // Test immutable access to stored data through a node handle:
        {
            let lock = h4.lock();
            assert_eq!(*lock, 100);
        }
    }

    #[kernel_test]
    fn test_pop() {
        let list: HandleList<u64> = HandleList::new();
        let h1 = list.push_front(5);
        let h2 = list.push_back(10);

        assert_eq!(list.len(), 2, "incorrect list length");

        // Test write access via a popped handle:
        {
            let mut p1 = list.pop_front().unwrap();
            assert_eq!(*p1, 5);

            *p1 = 20;
        }

        {
            let lock = h1.lock();
            assert_eq!(*lock, 20);
        }

        assert_eq!(list.len(), 1, "incorrect list length");

        // Ensure that dropping the original handle works properly
        drop(h1);

        // Test read access via a popped handle:
        {
            let mut lock = h2.lock();
            *lock = 100;
        }

        {
            let p2 = list.pop_back().unwrap();
            assert_eq!(*p2, 100);
        }

        drop(h2);

        // List should be empty afterwards
        assert!(list.pop_back().is_none());
        assert!(list.pop_front().is_none());
        assert_eq!(list.len(), 0, "incorrect list length");
    }

    #[kernel_test]
    fn test_drop() {
        let list = HandleList::new();
        let flag_1 = AtomicBool::new(false);
        let flag_2 = AtomicBool::new(false);

        let h1 = list.push_front(DropFlagged::new(&flag_1));
        let h2 = list.push_back(DropFlagged::new(&flag_2));

        // Make sure the data in the nodes isn't dropped too early:
        assert!(!flag_1.load(Ordering::SeqCst));
        assert!(!flag_2.load(Ordering::SeqCst));
        assert_eq!(list.len(), 2, "incorrect list length");

        // Drop each handle and make sure that the data inside the corresponding
        // nodes actually gets dropped:
        drop(h1);
        assert!(flag_1.load(Ordering::SeqCst));
        assert!(!flag_2.load(Ordering::SeqCst));
        assert_eq!(list.len(), 1, "incorrect list length");

        drop(h2);
        assert!(flag_1.load(Ordering::SeqCst));
        assert!(flag_2.load(Ordering::SeqCst));
        assert_eq!(list.len(), 0, "incorrect list length");
    }

    #[kernel_test]
    fn test_drain() {
        let list: HandleList<u64> = HandleList::new();
        let _h1 = list.push_back(5);
        let _h2 = list.push_back(10);
        let _h3 = list.push_back(15);
        let _h4 = list.push_back(20);

        assert_eq!(list.len(), 4, "incorrect list length");

        let mut lock = list.lock();
        let mut drain = lock.drain();

        let d1 = drain.next().unwrap();
        assert_eq!(*d1, 5);

        let d4 = drain.next_back().unwrap();
        assert_eq!(*d4, 20);

        let v: Vec<&mut u64> = drain.collect();
        assert_eq!(v.len(), 2);
        assert_eq!(*v[0], 10);
        assert_eq!(*v[1], 15);
    }
}
