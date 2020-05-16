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
use core::sync::atomic::{AtomicPtr, AtomicUsize, Ordering};

use crate::task::{WaitMode, WaitQueue};

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
    len: AtomicUsize,
}

impl<T> Queue<T> {
    pub fn new() -> (QueueReader<T>, QueueWriter<T>) {
        let stub = unsafe { QueueNode::new(None) };
        let queue = Arc::new(Queue {
            head: AtomicPtr::new(stub),
            tail: UnsafeCell::new(stub),
            len: AtomicUsize::new(0),
        });

        (QueueReader::new(queue.clone()), QueueWriter::new(queue))
    }

    pub fn new_direct() -> Queue<T> {
        let stub = unsafe { QueueNode::new(None) };
        Queue {
            head: AtomicPtr::new(stub),
            tail: UnsafeCell::new(stub),
            len: AtomicUsize::new(0),
        }
    }

    pub fn push(&self, data: T) {
        unsafe {
            let node = QueueNode::new(Some(data));
            let prev = self.head.swap(node, Ordering::AcqRel);

            (*prev).next.store(node, Ordering::Release);
            self.len.fetch_add(1, Ordering::SeqCst);
        }
    }

    pub unsafe fn pop(&self) -> Option<T> {
        let tail = *self.tail.get();
        let next = (*tail).next.load(Ordering::Acquire);

        if next != ptr::null_mut() {
            *self.tail.get() = next;
            let val = (*next).data.take().unwrap();
            drop(Box::from_raw(tail));
            self.len.fetch_sub(1, Ordering::SeqCst);

            return Some(val);
        }

        None
    }

    pub unsafe fn try_iter(&self) -> TryIter<'_, T> {
        TryIter(self)
    }

    pub fn len(&self) -> usize {
        self.len.load(Ordering::SeqCst)
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

    pub fn len(&self) -> usize {
        self.queue.len()
    }
}

unsafe impl<T> Send for QueueWriter<T> {}
unsafe impl<T> Sync for QueueWriter<T> {}

#[repr(transparent)]
pub struct QueueReader<T> {
    queue: Arc<Queue<T>>,
    _marker: PhantomData<*mut ()>, // for !Sync
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

    pub fn len(&self) -> usize {
        self.queue.len()
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

pub struct Channel<T> {
    data_queue: Queue<T>,
    wait_queue: WaitQueue,
}

impl<T> Channel<T> {
    pub fn new() -> (Receiver<T>, Sender<T>) {
        let ch = Arc::new(Channel {
            data_queue: Queue::new_direct(),
            wait_queue: WaitQueue::new(),
        });

        (
            Receiver {
                channel: ch.clone(),
                _marker: PhantomData,
            },
            Sender(ch),
        )
    }
}

#[derive(Clone)]
#[repr(transparent)]
pub struct Sender<T>(Arc<Channel<T>>);

impl<T> Sender<T> {
    pub fn send(&self, data: T) {
        self.0.data_queue.push(data);
        self.0.wait_queue.wake();
    }

    pub fn len(&self) -> usize {
        self.0.data_queue.len()
    }
}

unsafe impl<T> Send for Sender<T> {}
unsafe impl<T> Sync for Sender<T> {}

#[repr(transparent)]
pub struct Receiver<T> {
    channel: Arc<Channel<T>>,
    _marker: PhantomData<*mut ()>,
}

impl<T> Receiver<T> {
    pub fn try_recv(&self) -> Option<T> {
        unsafe { self.channel.data_queue.pop() }
    }

    pub fn recv(&self) -> T {
        loop {
            self.channel
                .wait_queue
                .wait(|| self.channel.data_queue.len() > 0, WaitMode::Default);

            unsafe {
                if let Some(data) = self.channel.data_queue.pop() {
                    return data;
                }
            }
        }
    }

    pub async fn async_recv(&self) -> T {
        loop {
            self.channel
                .wait_queue
                .wait_async(|| self.channel.data_queue.len() > 0, WaitMode::Default)
                .await;

            unsafe {
                if let Some(data) = self.channel.data_queue.pop() {
                    return data;
                }
            }
        }
    }

    pub fn try_iter(&self) -> TryIter<'_, T> {
        unsafe { self.channel.data_queue.try_iter() }
    }

    pub fn wait_iter(&self) -> WaitIter<'_, T> {
        WaitIter(self)
    }

    pub fn len(&self) -> usize {
        self.channel.data_queue.len()
    }
}

unsafe impl<T> Send for Receiver<T> {}

pub struct WaitIter<'a, T>(&'a Receiver<T>);

impl<'a, T> Iterator for WaitIter<'a, T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.0.recv())
    }
}
