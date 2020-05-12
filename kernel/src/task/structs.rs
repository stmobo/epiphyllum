use alloc_crate::boxed::Box;
use alloc_crate::sync::{Arc, Weak};
use core::mem;
use core::ptr;
use core::sync::atomic::{AtomicPtr, Ordering};
use core::task::Waker;

use super::async_task;
use super::scheduling;
use super::scheduling::SchedulerData;
use crate::interrupts::InterruptFrame;
use crate::lock::{LockedGlobal, OnceCell};
use crate::malloc::{heap_pages, AllocationError};
use crate::structures::{AVLTree, Queue};

use crossbeam::atomic::AtomicCell;

const TASK_STACK_SIZE: usize = 4 * 0x1000;

pub static TASKS: LockedGlobal<AVLTree<u64, TaskHandle>> = LockedGlobal::new();
static CUR_PID: AtomicCell<u64> = AtomicCell::new(0);

pub type TaskHandle = Arc<Task>;

#[derive(Debug, Copy, Clone)]
pub enum TaskSpawnError {
    AllocationError(AllocationError),
    StructureError,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum TaskStatus {
    Waiting,
    Running,
    Dead,
    Sleeping,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum ExitStatus {
    ReturnCode(u64),
}

#[derive(Debug)]
pub struct Task {
    id: u64,
    kernel_stack_base: usize,
    kernel_stack_head: AtomicPtr<InterruptFrame>,
    status: AtomicCell<TaskStatus>,
    scheduler_data: SchedulerData,
    exit_status: OnceCell<ExitStatus>,
    wake_on_exit: Queue<Waker>,
}

impl Task {
    fn new_common(entry: usize, init_arg: u64) -> Result<TaskHandle, TaskSpawnError> {
        let stack_end = unsafe {
            heap_pages::allocate(TASK_STACK_SIZE).map_err(|e| TaskSpawnError::AllocationError(e))?
        };

        // Stacks grow downwards on x86-64:
        let kernel_stack_base = stack_end + TASK_STACK_SIZE;
        let head_addr = kernel_stack_base - mem::size_of::<InterruptFrame>();
        let kernel_stack_head = head_addr as *mut InterruptFrame;
        let id = CUR_PID.fetch_add(1);
        let start_addr = task_entry as usize;

        unsafe {
            ptr::write(
                kernel_stack_head,
                InterruptFrame::new(start_addr, kernel_stack_base),
            );
        }

        let task: TaskHandle = Arc::new(Task {
            id,
            kernel_stack_base,
            kernel_stack_head: AtomicPtr::new(kernel_stack_head),
            status: AtomicCell::new(TaskStatus::Sleeping),
            scheduler_data: SchedulerData::new(),
            exit_status: OnceCell::new(),
            wake_on_exit: Queue::new_direct(),
        });

        unsafe {
            let handle_ptr = Weak::into_raw(Arc::downgrade(&task));
            (*kernel_stack_head).registers.rdi = (handle_ptr as usize) as u64;
            (*kernel_stack_head).registers.rsi = entry as u64;
            (*kernel_stack_head).registers.rdx = init_arg;
        }

        TASKS
            .lock()
            .insert(id, task.clone())
            .map_err(|_| TaskSpawnError::StructureError)?;
        Ok(task)
    }

    pub fn new(entry: fn(u64) -> u64, init_arg: u64) -> Result<TaskHandle, TaskSpawnError> {
        Self::new_common(entry as usize, init_arg)
    }

    pub fn from_closure<T: FnOnce() -> u64 + Send + 'static>(
        entry: T,
    ) -> Result<TaskHandle, TaskSpawnError> {
        let p = (Box::into_raw(Box::new(entry)) as usize) as u64;
        match Self::new_common(boxed_func_task::<T> as usize, p) {
            Ok(h) => Ok(h),
            Err(e) => {
                let p = (p as usize) as *mut T;
                drop(unsafe { Box::from_raw(p) });
                Err(e)
            }
        }
    }

    pub unsafe fn new_raw(entry: usize, init_arg: u64) -> Result<TaskHandle, TaskSpawnError> {
        Self::new_common(entry, init_arg)
    }

    pub fn get_context(&self) -> *mut InterruptFrame {
        self.kernel_stack_head.load(Ordering::Acquire)
    }

    pub fn set_context(&self, ctx: *mut InterruptFrame) {
        self.kernel_stack_head.store(ctx, Ordering::Release)
    }

    pub fn id(&self) -> u64 {
        self.id
    }

    pub fn status(&self) -> TaskStatus {
        self.status.load()
    }

    pub fn set_status(&self, status: TaskStatus) {
        self.status.store(status)
    }

    pub fn schedule(self: &Arc<Self>) {
        let status = self.status();
        if status == TaskStatus::Waiting || status == TaskStatus::Running {
            // we're already scheduled to run
            return;
        }

        scheduling::scheduler().schedule(self)
    }

    pub fn set_task_running(&self) {
        self.set_status(TaskStatus::Running);
        self.scheduler_data.start_timeslice();
    }

    pub fn scheduler_data(&self) -> &SchedulerData {
        &self.scheduler_data
    }

    /// Mark this task as dead.
    /// If this task is already dead, returns an error containing its ExitStatus.
    pub fn kill(&self, status: ExitStatus) -> Result<(), ExitStatus> {
        if let Err(_) = self.exit_status.set(status) {
            return Err(self.exit_status().unwrap());
        }

        self.set_status(TaskStatus::Dead);

        TASKS
            .lock()
            .remove(&self.id())
            .expect("task not found in tasks list");

        unsafe {
            // this is safe since this is the only place we ever read from the
            // queue, and we will never be here twice to begin with.
            // (we will return beforehand if we try)
            for waker in self.wake_on_exit.try_iter() {
                waker.wake();
            }
        }

        // if this task was scheduled, it'll be removed from the runqueue since
        // it's marked as dead.
        Ok(())
    }

    pub fn exit_status(&self) -> Option<ExitStatus> {
        self.exit_status.get().copied()
    }

    pub fn register_wake_on_exit(&self, waker: Waker) {
        self.wake_on_exit.push(waker);
    }

    pub fn waker(self: Arc<Self>) -> Waker {
        async_task::make_task_waker(self)
    }

    pub fn exit_future(self: Arc<Self>) -> async_task::TaskExitFuture {
        async_task::TaskExitFuture::new(self)
    }
}

impl Drop for Task {
    fn drop(&mut self) {
        unsafe {
            heap_pages::deallocate(self.kernel_stack_base, TASK_STACK_SIZE);
        }
    }
}

impl PartialEq for Task {
    fn eq(&self, other: &Task) -> bool {
        self.id == other.id
    }
}

impl Eq for Task {}

pub fn initialize() {
    TASKS.init(|| AVLTree::new());
}

#[allow(unused_must_use)]
fn task_entry(handle: *const Task, entrypoint: fn(u64) -> u64, init_arg: u64) {
    let handle = unsafe { Weak::from_raw(handle) };
    let retcode = entrypoint(init_arg);

    if let Some(handle) = handle.upgrade() {
        handle.kill(ExitStatus::ReturnCode(retcode));
    }

    let sched = scheduling::scheduler();
    sched.update();
    unsafe {
        sched.force_context_switch();
    }
}

fn boxed_func_task<T: FnOnce() -> u64 + Send + 'static>(ctx: *mut T) -> u64 {
    let boxed = unsafe { Box::from_raw(ctx) };
    (*boxed)()
}
