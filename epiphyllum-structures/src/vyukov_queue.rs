//! Non-intrusive Vyukov MPSC queue.
//! See also:
//! http://www.1024cores.net/home/lock-free-algorithms/queues/non-intrusive-mpsc-node-based-queue
//! https://int08h.com/post/ode-to-a-vyukov-queue/
//!
//! This is also a nearly identical reimplementation of the same queue type as:
//! https://github.com/rust-lang/rust/blob/master/src/libstd/sync/mpsc/mpsc_queue.rs

use alloc::alloc::{Allocator, Global, Layout, handle_alloc_error};
use alloc::sync::Arc;
use core::cell::UnsafeCell;
use core::marker::PhantomData;
use core::ptr;
use core::sync::atomic::{AtomicPtr, Ordering};
use core::ptr::NonNull;

/// Possible results of a pop() operation on a Queue.
pub enum PopResult<T> {
    Success(T),
    Empty,
    Inconsistent
}

impl<T> From<PopResult<T>> for Option<T> {
    fn from(val: PopResult<T>) -> Self {
        if let PopResult::Success(data) = val {
            Some(data)
        } else {
            None
        }
    }
}


/// A node within a (Vyukov) Queue.
pub struct QueueNode<T, A: Allocator> {
    data: Option<T>,
    next: AtomicPtr<QueueNode<T, A>>,
}

impl<T, A: Allocator> QueueNode<T, A> {
    unsafe fn new(v: Option<T>, alloc: &A) -> *mut QueueNode<T, A> {
        let layout = Layout::new::<QueueNode<T, A>>();
        if let Ok(p) = alloc.allocate(layout) {
            let p: *mut QueueNode<T, A> = p.cast().as_ptr();
            
            p.write(QueueNode {
                data: v,
                next: AtomicPtr::new(ptr::null_mut()),
            });
            
            p
        } else {
            handle_alloc_error(layout)
        }
    }

    unsafe fn free(ptr: *mut QueueNode<T, A>, alloc: &A) {
        let layout = Layout::new::<QueueNode<T, A>>();
        ptr.drop_in_place();
        alloc.deallocate(NonNull::new_unchecked(ptr.cast()), layout);
    }
}

/// A multi-producer, single-consumer queue.
///
/// This type implements a basic Vyukov queue, allowing multiple tasks to
/// concurrently enqueue data, while a single task dequeues data.
///
/// These queues can be used in two ways:
/// - Directly, with push() and pop() methods called on the Queue itself, or
/// - via linked _writer_ and _reader_ objects.
///
/// Linked writers and readers offer a safer interface, at the cost of some
/// overhead; internally, they rely on sharing a Queue object via an Arc.
///
/// Queue objects can also be used directly to remove this overhead, at the
/// cost of making pop operations unsafe: it is up to the programmer to ensure
/// that only a single task calls pop() at a time.
#[derive(Debug)]
pub struct Queue<T, A: Allocator = Global> {
    head: AtomicPtr<QueueNode<T, A>>,
    tail: UnsafeCell<*mut QueueNode<T, A>>,
    allocator: A
}

impl<T, A: Allocator> Queue<T, A> {
    /// Directly create a new Queue with the given memory allocator.
    pub fn new_direct_in(alloc: A) -> Queue<T, A> {
        let stub = unsafe { QueueNode::new(None, &alloc) };
        Queue {
            head: AtomicPtr::new(stub),
            tail: UnsafeCell::new(stub),
            allocator: alloc
        }
    }

    /// Push a value onto this queue.
    pub fn push(&self, data: T) {
        unsafe {
            let node = QueueNode::new(Some(data), &self.allocator);
            let prev = self.head.swap(node, Ordering::AcqRel);

            (*prev).next.store(node, Ordering::Release);
        }
    }

    /// Pop a value from this queue.
    ///
    /// A `Success` result indicates that an element was successfully popped
    /// off the queue.
    /// 
    /// An `Empty` result indicates that there were no elements to pop off the
    /// queue to begin with.
    ///
    /// An `Inconsistent` result indicates that, while there is data in the
    /// queue, some writers are in the middle of pushing, and so no data can
    /// be read for the moment. (In this case, the caller should retry the
    /// pop in the near future, after allowing some time for writers to progress.)
    ///
    /// ## Safety
    /// The caller must ensure that `pop` is only called by one task at a time.
    pub unsafe fn pop(&self) -> PopResult<T> {
        let tail = *self.tail.get();
        let next = (*tail).next.load(Ordering::Acquire);

        if !next.is_null() {
            *self.tail.get() = next;
            let val = (*next).data.take().unwrap();
            QueueNode::free(tail, &self.allocator);

            return PopResult::Success(val);
        }

        if self.head.load(Ordering::Acquire) == tail {
            PopResult::Empty
        } else {
            PopResult::Inconsistent
        }
    }

    /// Get an iterator that sequentially reads values from this queue.
    ///
    /// ## Safety
    /// Iterating over the object returned from this method is equivalent to
    /// calling `pop` in a loop, and the same safety requirements apply: no
    /// two tasks may pop from the same queue concurrently.
    pub unsafe fn try_iter(&self) -> TryIter<'_, T, A> {
        TryIter(self)
    }
}

impl<T> Queue<T, Global> {
    /// Directly create a new Queue with the global memory allocator.
    pub fn new_direct() -> Queue<T, Global> {
        Queue::new_direct_in(Global)
    }

    /// Create a linked pair of `QueueWriter` and `QueueReader` objects, using
    /// the global memory allocator.
    pub fn new() -> (QueueWriter<T>, QueueReader<T>) {
        let queue = Arc::new(Queue::new_direct());
        (QueueWriter::new(queue.clone()), QueueReader::new(queue))
    }
}

unsafe impl<T: Send, A: Allocator + Send> Send for Queue<T, A> {}
unsafe impl<T: Send, A: Allocator + Sync> Sync for Queue<T, A> {}

/// The writer / sender end of a linked queue pair.
///
/// Writers can be freely cloned or shared between threads, provided that the
/// data within the queue itself is `Send`.
#[derive(Clone)]
#[repr(transparent)]
pub struct QueueWriter<T> {
    queue: Arc<Queue<T, Global>>,
}

impl<T> QueueWriter<T> {
    fn new(queue: Arc<Queue<T, Global>>) -> QueueWriter<T> {
        QueueWriter { queue }
    }

    /// Push a value onto the queue associated with this writer.
    pub fn push(&self, data: T) {
        self.queue.push(data)
    }
}

/// The reader / receiver end of a linked queue pair.
///
/// Unlike writers, readers can only be passed between threads, not shared.
#[repr(transparent)]
pub struct QueueReader<T> {
    queue: Arc<Queue<T, Global>>,
    _marker: PhantomData<*mut ()>, // for !Sync
}

impl<T> QueueReader<T> {
    fn new(queue: Arc<Queue<T, Global>>) -> QueueReader<T> {
        QueueReader {
            queue,
            _marker: PhantomData,
        }
    }

    /// Pop a value off this queue.
    ///
    /// See `Queue::pop` for descriptions of possible results from this method.
    pub fn pop(&self) -> PopResult<T> {
        unsafe { self.queue.pop() }
    }

    /// Iteratively pop values off this queue, until either the queue is empty
    /// or an `Inconsistent` pop result is returned.
    ///
    /// This is a convenience method for calling `pop` in loops.
    pub fn try_iter(&self) -> TryIter<'_, T, Global> {
        TryIter(self.queue.as_ref())
    }
}

unsafe impl<T: Send> Send for QueueReader<T> {}

pub struct TryIter<'a, T, A: Allocator>(&'a Queue<T, A>);

impl<'a, T, A: Allocator> Iterator for TryIter<'a, T, A> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            self.0.pop().into()
        }
    }
}

/// Create a multi-producer, single-consumer (MPSC) queue.
///
/// This is the same as `Queue::<T>::new()`.
pub fn queue<T>() -> (QueueWriter<T>, QueueReader<T>) {
    Queue::new()
}
