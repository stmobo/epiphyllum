//! Async task infrastructure.
use alloc_crate::boxed::Box;
use alloc_crate::sync::Arc;
use core::future::Future;
use core::mem;
use core::pin::Pin;
use core::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};

use super::scheduling;
use super::{ExitStatus, Task, TaskHandle, TaskSpawnError, TaskStatus};
use crate::lock::NoIRQSpinlock;

const TASK_WAKER_VTABLE: RawWakerVTable =
    RawWakerVTable::new(clone_task, wake_task, wake_task_ref, drop_task);

unsafe fn wake_task(task: *const ()) {
    let handle = Arc::from_raw(task as *const Task);
    handle.schedule();
}

unsafe fn wake_task_ref(task: *const ()) {
    let handle = Arc::from_raw(task as *const Task);
    handle.schedule();

    // avoid decreasing refcount
    mem::forget(handle);
}

unsafe fn drop_task(task: *const ()) {
    Arc::from_raw(task as *const Task);
}

unsafe fn clone_task(task: *const ()) -> RawWaker {
    let handle = Arc::from_raw(task as *const Task);
    let new_handle = Arc::into_raw(handle.clone());

    mem::forget(handle);
    RawWaker::new(new_handle as *const (), &TASK_WAKER_VTABLE)
}

pub fn make_task_waker(task: TaskHandle) -> Waker {
    let handle = Arc::into_raw(task) as *const ();
    let raw = RawWaker::new(handle, &TASK_WAKER_VTABLE);

    unsafe { Waker::from_raw(raw) }
}

pub fn run_future<T>(mut future: impl Future<Output = T>) -> T {
    let waker = scheduling::current_task().waker();
    let mut context = Context::from_waker(&waker);

    loop {
        // this should be safe since nothing else gets its hands on the future
        // anyway (it's moved into this function)
        let future = unsafe { Pin::new_unchecked(&mut future) };

        // TODO: this might suffer from the lost-wakeup problem.
        // Unfortunately, we can't set ourselves as 'sleeping' prior to
        // entering `future.poll()`, since if we got preempted while running
        // in poll() we'd never wake up again.
        //
        // Maybe we could add a special Async task state to cover this case
        // within the scheduler?
        let p = scheduling::scheduler().running_task_ptr();
        match future.poll(&mut context) {
            Poll::Ready(retval) => return retval,
            Poll::Pending => {
                unsafe {
                    (*p).set_status(TaskStatus::Sleeping);
                }
                scheduling::yield_cpu()
            }
        };
    }
}

pub fn spawn_async<T: Future<Output = u64> + Send + 'static>(
    future: T,
) -> Result<TaskHandle, TaskSpawnError> {
    let data = Box::into_raw(Box::new(future)) as usize;
    let res = unsafe { Task::new_raw(async_task_runner::<T> as usize, data as u64) };

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

pub struct TaskExitState {
    task: TaskHandle,
    waker: Option<Waker>,
}

pub struct TaskExitFuture(Arc<NoIRQSpinlock<TaskExitState>>);

impl TaskExitFuture {
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

// TODO: impl Drop for TaskExitFuture?
// (unregister callback somehow?)

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
