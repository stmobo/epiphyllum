//! Async task infrastructure.
use alloc_crate::sync::Arc;
use core::future::Future;
use core::pin::Pin;
use core::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};

use super::scheduling;
use super::{ExitStatus, Task, TaskHandle, TaskSpawnError, TaskStatus};
use crate::lock::NoIRQSpinlock;

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
/// Note that the future to run is not passed directly to this function.
/// Rather, you need to pass a _closure_ that (synchronously) returns the
/// future to run.
/// 
/// This is to allow non-Send futures to be safely used with this function:
/// the creating closure must be Send (since it is being passed to the new
/// Task); the future itself, however, remains strictly within the spawned
/// Task for its entire lifetime, and so is free to be non-Send.
///
/// shared_address_space means the same thing as it does in Task::new.
pub fn spawn_async<F: Future<Output = u64>, C: FnOnce() -> F + Send + 'static>(
    shared_address_space: bool,
    closure: C,
) -> Result<TaskHandle, TaskSpawnError>
{
    Task::from_closure(shared_address_space, move || {
        run_future(closure())
    })
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
