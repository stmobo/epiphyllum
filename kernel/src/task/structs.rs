use alloc_crate::sync::{Arc, Weak};
use core::mem;
use core::ptr;
use core::sync::atomic::{AtomicPtr, Ordering};

use super::scheduler;
use super::scheduler::SchedulerData;
use crate::interrupts::InterruptFrame;
use crate::lock::{LockedGlobal, NoIRQSpinlock};
use crate::malloc::{heap_pages, AllocationError};
use crate::structures::AVLTree;

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
    exit_status: NoIRQSpinlock<Option<ExitStatus>>,
}

impl Task {
    pub fn new(entry: fn(u64) -> u64, init_arg: u64) -> Result<TaskHandle, TaskSpawnError> {
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
            exit_status: NoIRQSpinlock::new(None),
        });

        unsafe {
            let handle_ptr = Weak::into_raw(Arc::downgrade(&task));
            (*kernel_stack_head).registers.rdi = (handle_ptr as usize) as u64;
            (*kernel_stack_head).registers.rsi = (entry as usize) as u64;
            (*kernel_stack_head).registers.rdx = init_arg;
        }

        TASKS
            .lock()
            .insert(id, task.clone())
            .map_err(|_| TaskSpawnError::StructureError)?;
        Ok(task)
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

    pub fn schedule(self: Arc<Self>) {
        scheduler::schedule_task(self);
    }

    pub fn set_task_running(&self) {
        self.set_status(TaskStatus::Running);
        self.scheduler_data.start_timeslice();
    }

    pub fn scheduler_data(&self) -> &SchedulerData {
        &self.scheduler_data
    }

    pub fn kill(&self, status: ExitStatus) {
        self.exit_status.lock().replace(status);
        self.set_status(TaskStatus::Dead);

        TASKS
            .lock()
            .remove(&self.id())
            .expect("task not found in tasks list");

        // if this task was scheduled, it'll be removed from the runqueue since
        // it's marked as dead.
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

fn task_entry(handle: *const Task, entrypoint: fn(u64) -> u64, init_arg: u64) {
    let handle = unsafe { Weak::from_raw(handle) };

    let retcode = entrypoint(init_arg);
    if let Some(handle) = handle.upgrade() {
        handle.kill(ExitStatus::ReturnCode(retcode));
    }

    scheduler::update();
    unsafe {
        scheduler::switch_to_task();
    }
}
