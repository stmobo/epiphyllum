use alloc_crate::alloc::{Allocator, Global};
use alloc_crate::sync::Arc;
use core::marker::PhantomData;
use core::future::Future;

use epiphyllum_structures::Queue;
use epiphyllum_structures::vyukov_queue::{PopResult, TryIter};
use crate::task::{WaitMode, WaitQueue};

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
pub struct Channel<T, A: Allocator = Global> {
    data_queue: Queue<T, A>,
    wait_queue: WaitQueue<A>,
}

// TODO: make Channel accept an Allocator type parameter
// (requires WaitQueue to also accept an allocator parameter)

impl<T, A: Allocator> Channel<T, A> {
    /// Directly create a new Channel with the specified memory allocator.
    pub fn new_direct_in(alloc: A) -> Channel<T, A>
    where
        A: Clone
    {
        Channel {
            data_queue: Queue::new_direct_in(alloc.clone()),
            wait_queue: WaitQueue::new_in(alloc),
        }
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
    pub unsafe fn try_iter(&self) -> TryIter<'_, T, A> {
        self.data_queue.try_iter()
    }

    /// Continuously pop values off the queue forever, blocking when no data
    /// is available.
    pub unsafe fn wait_iter(&self) -> WaitIter<'_, T, A> {
        WaitIter(self)
    }
}

impl<T> Channel<T, Global> {
    /// Directly create a new Channel with the global memory allocator.
    pub fn new_direct() -> Channel<T, Global> {
        Channel {
            data_queue: Queue::new_direct_in(Global),
            wait_queue: WaitQueue::new_in(Global),
        }
    }

    /// Create a linked pair of `Sender` and `Receiver` objects.
    pub fn new() -> (Sender<T>, Receiver<T>) {
        let ch = Arc::new(Channel::new_direct_in(Global));
        (Sender(ch.clone()), Receiver(ch, PhantomData))
    }
}

unsafe impl<T: Send, A: Allocator + Send> Send for Channel<T, A> {}
unsafe impl<T: Send, A: Allocator + Sync> Sync for Channel<T, A> {}

pub struct WaitIter<'a, T, A: Allocator>(&'a Channel<T, A>);

impl<'a, T, A: Allocator> Iterator for WaitIter<'a, T, A> {
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
pub struct Sender<T>(Arc<Channel<T, Global>>);

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
pub struct Receiver<T>(Arc<Channel<T, Global>>, PhantomData<*mut ()>);

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
    pub fn wait_iter(&self) -> WaitIter<'_, T, Global> {
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
