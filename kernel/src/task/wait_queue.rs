use alloc_crate::boxed::Box;
use core::future::Future;
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

    // SAFETY: The caller must not deallocate the pushed ListNode without first
    // acquiring a lock on this list.
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

    // returns &ListNode since we don't actually own the node; the push_*
    // callers do
    //
    // SAFETY: The returned &ListNode must not be accessed after releasing
    // the lock on this list.
    unsafe fn pop_front(&mut self) -> Option<&mut ListNode> {
        if let Some(mut head) = self.head {
            let m = head.as_mut();
            self.head = m.next;
            m.unlink();

            drop(m);
            Some(&mut *head.as_ptr())
        } else {
            None
        }
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

        unsafe {
            let mut cur = queue.pop_front();
            while cur.is_some() {
                let node = cur.unwrap();
                if let Some(waker) = node.waker.take() {
                    waker.wake();
                }

                if node.mode == WaitMode::Exclusive {
                    break;
                }

                cur = queue.pop_front();
            }
        }

        drop(queue);
    }

    pub fn wait<F: FnMut() -> bool>(&self, mut condition: F, mode: WaitMode) {
        let h = self.add_waiter(Some(current_task().waker()), mode);

        loop {
            unsafe {
                (*scheduler().running_task_ptr()).set_status(TaskStatus::Sleeping);
            }

            if condition() {
                break;
            }

            yield_cpu();
        }

        unsafe {
            (*scheduler().running_task_ptr()).set_status(TaskStatus::Running);
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
