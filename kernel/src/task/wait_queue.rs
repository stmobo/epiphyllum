use core::future::Future;
use core::pin::Pin;
use core::task::{Context, Poll, Waker};

use super::structs::TaskStatus;
use crate::structures::handle_list::NodeHandle;
use crate::structures::HandleList;

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum WaitMode {
    Default,
    Exclusive,
}

#[derive(Clone)]
pub struct WaitData {
    waker: Option<Waker>,
    mode: WaitMode,
}

pub struct WaitHandle<'a>(NodeHandle<'a, WaitData>);

#[repr(transparent)]
pub struct WaitQueue {
    tasks: HandleList<WaitData>,
}

impl WaitQueue {
    /// Create a new WaitQueue.
    pub const fn new() -> WaitQueue {
        WaitQueue {
            tasks: HandleList::new(),
        }
    }

    /// Add a Waker to this WaitQueue.
    ///
    /// The waker will be removed from the queue when the following happens:
    ///  - The returned WaitHandle is dropped, or
    ///  - A call to wake() awakens the added Waker.
    ///
    /// Either way, the storage for the node will only be deallocated once the
    /// returned WaitHandle is dropped.
    pub fn add_waiter(&self, waker: Option<Waker>, mode: WaitMode) -> WaitHandle<'_> {
        let data = WaitData { waker, mode };
        let handle = match mode {
            WaitMode::Default => self.tasks.push_front(data),
            WaitMode::Exclusive => self.tasks.push_back(data),
        };

        WaitHandle(handle)
    }

    /// Wake up waiters on this queue.
    ///
    /// All pending WaitMode::Default waiters will be awakened, as well as
    /// at most 1 WaitMode::Exclusive waiter.
    pub fn wake(&self) {
        let mut queue = self.tasks.lock();
        for waiter in queue.drain() {
            if let Some(waker) = waiter.waker.take() {
                waker.wake();
            }

            if waiter.mode == WaitMode::Exclusive {
                break;
            }
        }
    }

    /// Wait for a condition to become true, sleeping on this queue in the
    /// meanwhile.
    pub fn wait<F: FnMut() -> bool>(&self, mut condition: F, mode: WaitMode) {
        let p = super::current_task();

        loop {
            p.set_wakeup_pending(false);
            let _h = self.add_waiter(Some(super::current_task().waker()), mode);

            if condition() {
                break;
            }

            p.set_status(TaskStatus::Sleeping);
            //direct_println!("task {} sleeping", p.id());
            super::scheduler().update();
        }

        p.set_wakeup_pending(false);
        p.set_status(TaskStatus::Running);
    }

    /// Creates a Future that sleeps on this queue until the given condition
    /// becomes true.
    pub fn wait_async<F: FnMut() -> bool + Unpin>(
        &self,
        condition: F,
        mode: WaitMode,
    ) -> WaitQueueFuture<'_, F> {
        WaitQueueFuture {
            handle: None,
            queue: self,
            condition,
            mode,
        }
    }
}

pub struct WaitQueueFuture<'a, F: FnMut() -> bool + Unpin> {
    handle: Option<WaitHandle<'a>>,
    queue: &'a WaitQueue,
    condition: F,
    mode: WaitMode,
}

impl<'a, F: FnMut() -> bool + Unpin> Future for WaitQueueFuture<'a, F> {
    type Output = ();

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let m = self.get_mut();

        m.handle = Some(m.queue.add_waiter(Some(cx.waker().clone()), m.mode));
        if (m.condition)() {
            m.handle.take();
            Poll::Ready(())
        } else {
            Poll::Pending
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::task;
    use crate::task::Task;
    use crate::timer::{sleep, sleep_async, TimerDeadline};
    use kernel_test_macro::kernel_test;

    use alloc_crate::sync::Arc;
    use core::sync::atomic::{AtomicU64, Ordering};

    // TODO: test for lost-wakeup problems?
    // How would you do that?

    #[kernel_test]
    fn basic_sync_test() {
        let queue = Arc::new(WaitQueue::new());
        let shared = Arc::new(AtomicU64::new(0));

        let child_queue = queue.clone();
        let child_shared = shared.clone();

        let child = Task::from_closure(true, move || {
            let s = child_shared.clone();
            child_queue.wait(|| s.load(Ordering::SeqCst) > 5, WaitMode::Default);
            child_shared.fetch_add(1, Ordering::SeqCst);

            0
        })
        .expect("could not spawn subtask");
        child.schedule();

        sleep(TimerDeadline::Relative(512)).unwrap();
        assert_eq!(shared.load(Ordering::SeqCst), 0);

        shared.store(3, Ordering::SeqCst);
        queue.wake();

        sleep(TimerDeadline::Relative(512)).unwrap();
        assert_eq!(shared.load(Ordering::SeqCst), 3);

        shared.store(10, Ordering::SeqCst);
        queue.wake();

        sleep(TimerDeadline::Relative(512)).unwrap();
        assert_eq!(shared.load(Ordering::SeqCst), 11);

        drop(child);
    }

    async fn basic_async_test_child(
        child_queue: Arc<WaitQueue>,
        child_shared: Arc<AtomicU64>,
    ) -> u64 {
        let s = child_shared.clone();
        child_queue
            .wait_async(|| s.load(Ordering::SeqCst) > 5, WaitMode::Default)
            .await;

        child_shared.fetch_add(1, Ordering::SeqCst);
        0
    }

    #[kernel_test]
    fn basic_async_test() {
        let queue = Arc::new(WaitQueue::new());
        let shared = Arc::new(AtomicU64::new(0));

        let child_queue = queue.clone();
        let child_shared = shared.clone();

        let child = task::spawn_async(true, basic_async_test_child(child_queue, child_shared))
            .expect("could not spawn subtask");
        child.schedule();

        task::run_future(async {
            sleep_async(TimerDeadline::Relative(512)).unwrap().await;
            assert_eq!(shared.load(Ordering::SeqCst), 0);

            shared.store(3, Ordering::SeqCst);
            queue.wake();

            sleep_async(TimerDeadline::Relative(512)).unwrap().await;
            assert_eq!(shared.load(Ordering::SeqCst), 3);

            shared.store(10, Ordering::SeqCst);
            queue.wake();

            sleep_async(TimerDeadline::Relative(512)).unwrap().await;
            assert_eq!(shared.load(Ordering::SeqCst), 11);
        });
    }
}
