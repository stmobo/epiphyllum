use alloc_crate::boxed::Box;
use core::future::Future;
use core::marker::PhantomData;
use core::pin::Pin;
use core::ptr::NonNull;
use core::task::{Context, Poll, Waker};

use super::scheduler;
use super::scheduling::{current_task, yield_cpu};
use super::structs::TaskStatus;
use crate::lock::NoIRQSpinlock;

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum WaitMode {
    Default,
    Exclusive,
}

#[derive(Clone)]
pub struct ListNode {
    waker: Option<Waker>,
    mode: WaitMode,
    prev: Option<NonNull<ListNode>>,
    next: Option<NonNull<ListNode>>,
}

impl ListNode {
    fn new(waker: Option<Waker>, mode: WaitMode) -> NonNull<ListNode> {
        Box::leak(Box::new(ListNode {
            waker,
            mode,
            prev: None,
            next: None,
        }))
        .into()
    }

    unsafe fn unlink(&mut self) {
        if let Some(mut prev) = self.prev {
            prev.as_mut().next = self.next;
        }

        if let Some(mut next) = self.next {
            next.as_mut().prev = self.prev;
        }

        self.prev = None;
        self.next = None;
    }

    unsafe fn append(&mut self, mut node: NonNull<ListNode>) {
        {
            let mut r = node.as_mut();
            r.next = self.next;
            r.prev = Some(NonNull::new_unchecked(self as *mut ListNode));
        }

        if let Some(mut next) = self.next {
            next.as_mut().prev = Some(node);
        }

        self.next = Some(node);
    }
}

pub struct WaitList {
    head: Option<NonNull<ListNode>>,
    tail: Option<NonNull<ListNode>>,
}

impl WaitList {
    const fn new() -> WaitList {
        WaitList {
            head: None,
            tail: None,
        }
    }

    // SAFETY: The caller must not do anything with the returned ListNode
    // without first acquiring a lock on this list.
    unsafe fn push_front(&mut self, mut node: NonNull<ListNode>) {
        if let Some(head) = self.head {
            node.as_mut().append(head);
        }
        self.head = Some(node);
    }

    // SAFETY: See push_front.
    unsafe fn push_back(&mut self, node: NonNull<ListNode>) {
        if let Some(mut tail) = self.tail {
            tail.as_mut().append(node);
        }
        self.tail = Some(node);
    }

    // This is safe, since users of WaitListIter can't get rid of their mut
    // reference to / lock on this list while they hold returned references
    // from the iterator.
    fn iter_mut(&mut self) -> WaitListIter<'_> {
        WaitListIter(self.head, PhantomData)
    }
}

struct WaitListIter<'a>(Option<NonNull<ListNode>>, PhantomData<&'a mut ListNode>);

impl<'a> Iterator for WaitListIter<'a> {
    type Item = &'a mut ListNode;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.take().map(|p| {
            let r: &'a mut ListNode = unsafe { &mut *p.as_ptr() };
            if r.mode != WaitMode::Exclusive {
                self.0 = r.next;
            }

            r
        })
    }
}

#[repr(transparent)]
pub struct WaitQueue {
    tasks: NoIRQSpinlock<WaitList>,
}

impl WaitQueue {
    /// Create a new WaitQueue.
    pub const fn new() -> WaitQueue {
        WaitQueue {
            tasks: NoIRQSpinlock::new(WaitList::new()),
        }
    }

    /// Add a Waker to this WaitQueue.
    ///
    /// The waker will be removed from the queue when the following happens:
    ///  - The returned WaiterHandle is dropped, or
    ///  - A call to wake() awakens the added Waker.
    ///
    /// Either way, the storage for the node will only be deallocated once the
    /// returned WaiterHandle is dropped.
    pub fn add_waiter(&self, waker: Option<Waker>, mode: WaitMode) -> WaiterHandle<'_> {
        let node = ListNode::new(waker, mode);

        let mut queue = self.tasks.lock();
        unsafe {
            match mode {
                WaitMode::Default => queue.push_front(node),
                WaitMode::Exclusive => queue.push_back(node),
            };
        }
        drop(queue);

        WaiterHandle(self, node)
    }

    /// Wake up waiters on this queue.
    ///
    /// All pending WaitMode::Default waiters will be awakened, as well as
    /// at most 1 WaitMode::Exclusive waiter.
    pub fn wake(&self) {
        let mut queue = self.tasks.lock();

        for node in queue.iter_mut() {
            if node.waker.is_some() {
                node.waker.as_ref().unwrap().wake_by_ref();
            }
        }

        drop(queue);
    }

    /// Wait for a condition to become true, sleeping on this queue in the
    /// meanwhile.
    pub fn wait<F: FnMut() -> bool>(&self, mut condition: F, mode: WaitMode) {
        let h = self.add_waiter(Some(current_task().waker()), mode);
        let p = scheduler().running_task_ptr();

        loop {
            unsafe {
                (*p).set_wakeup_pending(false);
            }

            if condition() {
                break;
            }

            unsafe {
                (*p).set_status(TaskStatus::Sleeping);
            }

            yield_cpu();
        }

        unsafe {
            (*p).set_wakeup_pending(false);
            (*p).set_status(TaskStatus::Running);
        }

        drop(h);
    }

    pub fn wait_async<F: Fn() -> bool>(
        &self,
        condition: F,
        mode: WaitMode,
    ) -> WaitQueueFuture<'_, F> {
        let waiter = self.add_waiter(None, mode);
        WaitQueueFuture { waiter, condition }
    }
}

unsafe impl Send for WaitQueue {}
unsafe impl Sync for WaitQueue {}

pub struct WaiterHandle<'a>(&'a WaitQueue, NonNull<ListNode>);

impl<'a> WaiterHandle<'a> {
    fn set_waker(&self, waker: Waker) {
        let lock = self.0.tasks.lock();
        unsafe {
            let p = self.1.as_ptr();
            (*p).waker = Some(waker);
        }
        drop(lock);
    }
}

impl<'a> Drop for WaiterHandle<'a> {
    fn drop(&mut self) {
        let lock = self.0.tasks.lock();
        unsafe {
            self.1.as_mut().unlink();
            drop(Box::from_raw(self.1.as_ptr()));
        }
        drop(lock);
    }
}

unsafe impl<'a> Send for WaiterHandle<'a> {}
unsafe impl<'a> Sync for WaiterHandle<'a> {}

pub struct WaitQueueFuture<'a, F: Fn() -> bool> {
    waiter: WaiterHandle<'a>,
    condition: F,
}

impl<'a, F: Fn() -> bool> Future for WaitQueueFuture<'a, F> {
    type Output = ();

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        self.waiter.set_waker(cx.waker().clone());
        if (self.condition)() {
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
    use core::sync::atomic::{spin_loop_hint, AtomicBool, AtomicU64, Ordering};

    // TODO: test for lost-wakeup problems?
    // How would you do that?

    #[kernel_test]
    fn basic_sync_test() {
        let queue = Arc::new(WaitQueue::new());
        let shared = Arc::new(AtomicU64::new(0));

        let child_queue = queue.clone();
        let child_shared = shared.clone();

        let child = Task::from_closure(move || {
            let s = child_shared.clone();
            child_queue.wait(|| s.load(Ordering::SeqCst) > 5, WaitMode::Default);
            child_shared.fetch_add(1, Ordering::SeqCst);

            0
        })
        .expect("could not spawn subtask");
        child.schedule();

        sleep(TimerDeadline::Relative(1024)).unwrap();
        assert_eq!(shared.load(Ordering::SeqCst), 0);

        shared.store(3, Ordering::SeqCst);
        queue.wake();

        sleep(TimerDeadline::Relative(1024)).unwrap();
        assert_eq!(shared.load(Ordering::SeqCst), 3);

        shared.store(10, Ordering::SeqCst);
        queue.wake();

        sleep(TimerDeadline::Relative(1024)).unwrap();
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

        let child = task::spawn_async(basic_async_test_child(child_queue, child_shared))
            .expect("could not spawn subtask");
        child.schedule();

        task::run_future(async {
            sleep_async(TimerDeadline::Relative(1024)).unwrap().await;
            assert_eq!(shared.load(Ordering::SeqCst), 0);

            shared.store(3, Ordering::SeqCst);
            queue.wake();

            sleep_async(TimerDeadline::Relative(1024)).unwrap().await;
            assert_eq!(shared.load(Ordering::SeqCst), 3);

            shared.store(10, Ordering::SeqCst);
            queue.wake();

            sleep_async(TimerDeadline::Relative(1024)).unwrap().await;
            assert_eq!(shared.load(Ordering::SeqCst), 11);
        });
    }
}
