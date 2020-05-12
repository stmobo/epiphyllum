//! Non-intrusive Vyukov MPSC queue.
//! See also:
//! http://www.1024cores.net/home/lock-free-algorithms/queues/non-intrusive-mpsc-node-based-queue
//! https://int08h.com/post/ode-to-a-vyukov-queue/
//!
//! This is also a nearly identical reimplementation of the same queue type as:
//! https://github.com/rust-lang/rust/blob/master/src/libstd/sync/mpsc/mpsc_queue.rs

use alloc_crate::boxed::Box;
use alloc_crate::sync::Arc;
use core::cell::UnsafeCell;
use core::marker::PhantomData;
use core::ptr;
use core::sync::atomic::{AtomicPtr, Ordering};

pub struct QueueNode<T> {
    data: Option<T>,
    next: AtomicPtr<QueueNode<T>>,
}

impl<T> QueueNode<T> {
    unsafe fn new(v: Option<T>) -> *mut QueueNode<T> {
        Box::into_raw(Box::new(QueueNode {
            data: v,
            next: AtomicPtr::new(ptr::null_mut()),
        }))
    }
}

#[derive(Debug)]
pub struct Queue<T> {
    head: AtomicPtr<QueueNode<T>>,
    tail: UnsafeCell<*mut QueueNode<T>>,
}

impl<T> Queue<T> {
    pub fn new() -> (QueueReader<T>, QueueWriter<T>) {
        let stub = unsafe { QueueNode::new(None) };
        let queue = Arc::new(Queue {
            head: AtomicPtr::new(stub),
            tail: UnsafeCell::new(stub),
        });

        (QueueReader::new(queue.clone()), QueueWriter::new(queue))
    }

    pub fn new_direct() -> Queue<T> {
        let stub = unsafe { QueueNode::new(None) };
        Queue {
            head: AtomicPtr::new(stub),
            tail: UnsafeCell::new(stub),
        }
    }

    pub fn push(&self, data: T) {
        unsafe {
            let node = QueueNode::new(Some(data));
            let prev = self.head.swap(node, Ordering::AcqRel);

            (*prev).next.store(node, Ordering::Release);
        }
    }

    pub unsafe fn pop(&self) -> Option<T> {
        let tail = *self.tail.get();
        let next = (*tail).next.load(Ordering::Acquire);

        if next != ptr::null_mut() {
            *self.tail.get() = next;
            let val = (*next).data.take().unwrap();
            drop(Box::from_raw(tail));

            return Some(val);
        }

        None
    }

    pub unsafe fn try_iter(&self) -> TryIter<'_, T> {
        TryIter(self)
    }
}

unsafe impl<T> Send for Queue<T> {}
unsafe impl<T> Sync for Queue<T> {}

#[derive(Clone)]
#[repr(transparent)]
pub struct QueueWriter<T> {
    queue: Arc<Queue<T>>,
}

impl<T> QueueWriter<T> {
    fn new(queue: Arc<Queue<T>>) -> QueueWriter<T> {
        QueueWriter { queue }
    }

    pub fn push(&self, data: T) {
        self.queue.push(data)
    }
}

unsafe impl<T> Send for QueueWriter<T> {}
unsafe impl<T> Sync for QueueWriter<T> {}

#[repr(transparent)]
pub struct QueueReader<T> {
    queue: Arc<Queue<T>>,
    _marker: PhantomData<UnsafeCell<T>>, // for !Sync
}

impl<T> QueueReader<T> {
    fn new(queue: Arc<Queue<T>>) -> QueueReader<T> {
        QueueReader {
            queue,
            _marker: PhantomData,
        }
    }

    pub fn pop(&self) -> Option<T> {
        unsafe { self.queue.pop() }
    }

    pub fn try_iter(&self) -> TryIter<'_, T> {
        TryIter(self.queue.as_ref())
    }
}

unsafe impl<T> Send for QueueReader<T> {}

pub struct TryIter<'a, T>(&'a Queue<T>);

impl<'a, T> Iterator for TryIter<'a, T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        unsafe { self.0.pop() }
    }
}
