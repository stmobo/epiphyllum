//! Async task infrastructure.
use alloc_crate::boxed::Box;
use alloc_crate::sync::Arc;
use core::future::Future;
use core::pin::Pin;
use core::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};

use super::scheduling;
use super::{ExitStatus, Task, TaskHandle, TaskSpawnError, TaskStatus};
use crate::lock::NoIRQSpinlock;
use crate::paging::AddressSpace;

const TASK_WAKER_VTABLE: RawWakerVTable =
    RawWakerVTable::new(clone_task, wake_task, wake_task_ref, drop_task);

unsafe fn wake_task(task: *const ()) {
    let handle = TaskHandle::from_raw(task as *const Task).unwrap();
    handle.schedule();
}

unsafe fn wake_task_ref(task: *const ()) {
    let p = task as *const Task;
    (*p).schedule();
}

unsafe fn drop_task(task: *const ()) {
    TaskHandle::from_raw(task as *const Task);
}

unsafe fn clone_task(task: *const ()) -> RawWaker {
    let p = task as *const Task;
    (*p).inc_refcount();
    RawWaker::new(task, &TASK_WAKER_VTABLE)
}

/// Make a Waker from a TaskHandle.
pub fn make_task_waker(task: TaskHandle) -> Waker {
    let handle = task.as_raw() as *const ();
    let raw = RawWaker::new(handle, &TASK_WAKER_VTABLE);

    unsafe { Waker::from_raw(raw) }
}

/// Execute a Future, putting the Task to sleep whenever it would block
/// (_i.e._ whenever the future's poll method returns Pending).
pub fn run_future<T>(mut future: impl Future<Output = T>) -> T {
    let waker = super::current_task().waker();
    let mut context = Context::from_waker(&waker);

    loop {
        // this should be safe since nothing else gets its hands on the future
        // anyway (it's moved into this function)
        let future = unsafe { Pin::new_unchecked(&mut future) };
        let p = super::current_task();
        p.set_wakeup_pending(false);

        match future.poll(&mut context) {
            Poll::Ready(retval) => return retval,
            Poll::Pending => {
                p.set_status(TaskStatus::Sleeping);
                scheduling::yield_cpu();
            }
        };
    }
}

/// Spawn a new Task that runs a Future with run_future().
///
/// Like Task::from_closure, the Future must be both Send and 'static so that
/// it can be safely sent to the created Task.
///
/// shared_address_space means the same thing as it does in Task::new.
pub fn spawn_async<T: Future<Output = u64> + Send + 'static>(
    shared_address_space: bool,
    future: T,
) -> Result<TaskHandle, TaskSpawnError> {
    let address_space = if shared_address_space {
        super::current_task().clone_address_space()
    } else {
        Arc::new(NoIRQSpinlock::new(
            AddressSpace::new().map_err(TaskSpawnError::AllocationError)?
        ))
    };

    let data = Box::into_raw(Box::new(future)) as usize;
    let res = unsafe { Task::new_raw(async_task_runner::<T> as usize, data as u64, address_space) };

    match res {
        Ok(h) => Ok(h),
        Err(v) => {
            drop(unsafe { Box::from_raw(data as *mut T) });
            Err(v)
        }
    }
}

fn async_task_runner<T: Future<Output = u64> + Send + 'static>(ctx: *mut T) -> u64 {
    let boxed = unsafe { Box::from_raw(ctx) };
    let pinned: Pin<Box<T>> = boxed.into();
    run_future(pinned)
}

/// The shared state underlying a TaskExitFuture.
///
/// Each instance of TaskExitFuture is associated with an instance of this
/// struct. References to it are held by the TaskExitFuture itself and by
/// the exit callback registered on the Task we're interested in.
pub struct TaskExitState {
    task: TaskHandle,
    waker: Option<Waker>,
}

/// A Future that waits for a Task to exit, then returns its exit status.
pub struct TaskExitFuture(Arc<NoIRQSpinlock<TaskExitState>>);

impl TaskExitFuture {
    /// Create a new TaskExitFuture that waits for the given Task.
    pub fn new(task: TaskHandle) -> TaskExitFuture {
        let state = Arc::new(NoIRQSpinlock::new(TaskExitState { task, waker: None }));
        let cb_state = state.clone();

        let s = state.lock();
        s.task.register_exit_callback(move || {
            let mut lock = cb_state.lock();
            if let Some(waker) = lock.waker.take() {
                waker.wake();
            }
        });
        drop(s);

        TaskExitFuture(state)
    }
}

impl Drop for TaskExitFuture {
    fn drop(&mut self) {
        // Make sure no wakeups are delivered after this Future is dropped.
        // This turns the exit callback into a no-op (except for locking and
        // unlocking the underlying shared state).
        self.0.lock().waker.take();
    }
}

impl Future for TaskExitFuture {
    type Output = ExitStatus;

    fn poll(self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Self::Output> {
        let mut lock = self.0.lock();
        if let Some(status) = lock.task.exit_status() {
            Poll::Ready(status)
        } else {
            lock.waker = Some(ctx.waker().clone());
            Poll::Pending
        }
    }
}
