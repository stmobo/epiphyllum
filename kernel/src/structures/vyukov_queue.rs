//! Non-intrusive Vyukov MPSC queue.
//! See also:
//! http://www.1024cores.net/home/lock-free-algorithms/queues/non-intrusive-mpsc-node-based-queue
//! https://int08h.com/post/ode-to-a-vyukov-queue/
//!
//! This is also a nearly identical reimplementation of the same queue type as:
//! https://github.com/rust-lang/rust/blob/master/src/libstd/sync/mpsc/mpsc_queue.rs

use alloc_crate::alloc::{Allocator, Global, Layout, handle_alloc_error};
use alloc_crate::sync::Arc;
use core::cell::UnsafeCell;
use core::marker::PhantomData;
use core::ptr;
use core::sync::atomic::{AtomicPtr, Ordering};
use core::future::Future;
use core::ptr::NonNull;

use crate::task::{WaitMode, WaitQueue};

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

/// An MPSC queue with integrated sleep / wakeup capability.
///
/// Channels provide an extremely similar interface to regular Queues, however
/// they also allow consumers to sleep while waiting for data to be enqueued.
///
/// As with regular Queues, sending on a Channel is safe, while directly 
/// receiving from a Channel (in any way) is unsafe: the programmer must ensure
/// that only a single task receives from a Channel at a time.
///
/// Linked pairs of Senders and Receivers can be used to provide a safe interface
/// for Channels, at the cost of some overhead.
pub struct Channel<T> {
    data_queue: Queue<T>,
    wait_queue: WaitQueue,
}

// TODO: make Channel accept an Allocator type parameter
// (requires WaitQueue to also accept an allocator parameter)

impl<T> Channel<T> {
    /// Directly create a new Channel.
    pub fn new_direct() -> Channel<T> {
        Channel {
            data_queue: Queue::new_direct(),
            wait_queue: WaitQueue::new(),
        }
    }

    /// Create a linked pair of `Sender` and `Receiver` objects.
    pub fn new() -> (Sender<T>, Receiver<T>) {
        let ch = Arc::new(Channel::new_direct());
        (Sender(ch.clone()), Receiver(ch, PhantomData))
    }

    /// Push a value onto the queue, and wake up any waiting task.
    pub fn send(&self, data: T) {
        self.data_queue.push(data);
        self.wait_queue.wake();
    }

    /// Directly attempt to pop data off the queue, returning immediately if
    /// the queue is empty or if an inconsistent queue state is encountered.
    pub unsafe fn try_recv(&self) -> PopResult<T> {
        self.data_queue.pop()
    }

    /// Pop data off the queue, waiting until the first successful pop operation.
    pub unsafe fn recv(&self) -> T {
        let mut ret: Option<T> = None;

        // note: if an inconsistent queue state is encountered, then it is safe
        // to go to sleep, since there must be a pushing task (which will
        // eventually wake us up once it progresses).
        self.wait_queue.wait(|| {
            ret = self.data_queue.pop().into();
            ret.is_some()
        }, WaitMode::Default);

        ret.expect("wait returned without any data")
    }

    /// Returns a future that, when `await`ed, pops data off the queue, waiting
    /// asynchronously until the first successful pop operation.
    pub async unsafe fn async_recv(&self) -> T {
        let mut ret: Option<T> = None;

        self.wait_queue
            .wait_async(|| {
                ret = self.data_queue.pop().into();
                ret.is_some()
            }, WaitMode::Default)
            .await;

        ret.expect("wait returned without any data")
    }

    /// Iteratively pop values off the queue until either it is empty or an
    /// `Inconsistent` result is returned.
    ///
    /// This is the same as `Queue::try_iter`.
    pub unsafe fn try_iter(&self) -> TryIter<'_, T, Global> {
        self.data_queue.try_iter()
    }

    /// Continuously pop values off the queue forever, blocking when no data
    /// is available.
    pub unsafe fn wait_iter(&self) -> WaitIter<'_, T> {
        WaitIter(self)
    }
}

unsafe impl<T: Send> Send for Channel<T> {}
unsafe impl<T: Send> Sync for Channel<T> {}

pub struct WaitIter<'a, T>(&'a Channel<T>);

impl<'a, T> Iterator for WaitIter<'a, T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        unsafe { Some(self.0.recv()) }
    }
}

/// The sender half of a linked channel pair.
///
/// Like `QueueWriter`s, `Sender`s are both `Send` and `Sync` for `T: Send`.
#[derive(Clone)]
#[repr(transparent)]
pub struct Sender<T>(Arc<Channel<T>>);

impl<T> Sender<T> {
    /// Send a value to this sender's linked Receiver, and wake up any task
    /// waiting on it.
    pub fn send(&self, data: T) {
        self.0.send(data)
    }
}

/// The receiver half of a linked channel pair.
///
/// Like `QueueReader`s, `Receiver`s are only `Send` for `T: Send`, and are
/// never `Sync`.
#[repr(transparent)]
pub struct Receiver<T>(Arc<Channel<T>>, PhantomData<*mut ()>);

impl<T> Receiver<T> {
    /// Directly attempt to pop data off the queue, returning immediately if
    /// the queue is empty or if an inconsistent queue state is encountered.
    pub fn try_recv(&self) -> PopResult<T> {
        unsafe { self.0.try_recv() }
    }

    /// Pop data off the queue, waiting until the first successful pop operation.
    pub fn recv(&self) -> T {
        unsafe { self.0.recv() }
    }

    /// Returns a future that, when `await`ed, pops data off the queue, waiting
    /// asynchronously until the first successful pop operation.
    pub fn async_recv(&self) -> impl Future<Output = T> + '_ {
        unsafe { self.0.async_recv() }
    }

    /// Iteratively pop values off the queue until either it is empty or an
    /// `Inconsistent` result is returned.
    ///
    /// This is the same as `Queue::try_iter` and `Channel::try_iter`.
    pub fn try_iter(&self) -> TryIter<'_, T, Global> {
        unsafe { self.0.data_queue.try_iter() }
    }

    /// Continuously pop values off the queue forever, blocking when no data
    /// is available.
    pub fn wait_iter(&self) -> WaitIter<'_, T> {
        unsafe { self.0.wait_iter() }
    }
}

unsafe impl<T: Send> Send for Receiver<T> {}

/// Create a multi-producer, single-consumer (MPSC) channel.
///
/// This is the same as `Channel::<T>::new()`.
pub fn channel<T>() -> (Sender<T>, Receiver<T>) {
    Channel::new()
}

/// Create a multi-producer, single-consumer (MPSC) queue.
///
/// This is the same as `Queue::<T>::new()`.
pub fn queue<T>() -> (QueueWriter<T>, QueueReader<T>) {
    Queue::new()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rng::MersenneTwister64;
    use crate::task::{run_future, Task};
    use crate::test::TEST_SEED;
    use kernel_test_macro::kernel_test;

    async fn channel_tester() {
        let (s1, r1) = channel();
        let (s2, r2) = channel();

        let task_1 = Task::from_closure(false, move || {
            let mut rng = MersenneTwister64::new(TEST_SEED);

            for _ in 0..100 {
                s1.send(rng.generate());
                assert_eq!(r2.recv(), rng.generate(), "RNG states out of sync");
            }

            0
        })
        .expect("could not spawn task");

        let task_2 = Task::from_closure(false, move || {
            let mut rng = MersenneTwister64::new(TEST_SEED);

            for _ in 0..100 {
                assert_eq!(r1.recv(), rng.generate(), "RNG states out of sync");
                s2.send(rng.generate());
            }

            0
        })
        .expect("could not spawn task");

        task_1.schedule();
        task_2.schedule();

        task_1.exit_future().await;
        task_2.exit_future().await;
    }

    #[kernel_test]
    fn test_channels() {
        run_future(channel_tester());
    }
}
