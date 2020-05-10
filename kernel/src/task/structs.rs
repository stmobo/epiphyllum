use alloc_crate::sync::Arc;
use core::mem;
use core::ptr;
use core::sync::atomic::{AtomicU64, Ordering};

use crate::interrupts::InterruptFrame;
use crate::lock::{LockedGlobal, NoIRQSpinlock, NoIRQSpinlockGuard};
use crate::malloc::{heap_pages, AllocationError};
use crate::structures::AVLTree;

use super::scheduler;

const TASK_STACK_SIZE: usize = 4 * 0x1000;

pub static TASKS: LockedGlobal<AVLTree<u64, TaskHandle>> = LockedGlobal::new();
static CUR_PID: AtomicU64 = AtomicU64::new(0);

pub type TaskHandle = Arc<Task>;

#[derive(Debug)]
pub enum TaskSpawnError {
    AllocationError(AllocationError),
    StructureError,
}

#[derive(Debug)]
pub enum TaskStatus {
    Waiting,
    Running,
    Dead,
}

pub struct Task {
    id: u64,
    kernel_stack_base: usize,
    kernel_stack_head: NoIRQSpinlock<*mut InterruptFrame>,
    status: NoIRQSpinlock<TaskStatus>,
}

impl Task {
    pub fn new(entry: fn(u64) -> !, init_arg: u64) -> Result<TaskHandle, TaskSpawnError> {
        let stack_end = unsafe {
            heap_pages::allocate(TASK_STACK_SIZE).map_err(|e| TaskSpawnError::AllocationError(e))?
        };

        let start_addr = entry as usize;

        // Stacks grow downwards on x86-64:
        let kernel_stack_base = stack_end + TASK_STACK_SIZE;
        let head_addr = kernel_stack_base - mem::size_of::<InterruptFrame>();
        let kernel_stack_head = head_addr as *mut InterruptFrame;
        let id = CUR_PID.fetch_add(1, Ordering::SeqCst);

        unsafe {
            ptr::write(
                kernel_stack_head,
                InterruptFrame::new(start_addr, kernel_stack_base, init_arg),
            );
        }

        let task: TaskHandle = Arc::new(Task {
            id,
            kernel_stack_base,
            kernel_stack_head: NoIRQSpinlock::new(kernel_stack_head),
            status: NoIRQSpinlock::new(TaskStatus::Waiting),
        });

        TASKS
            .lock()
            .insert(id, task.clone())
            .map_err(|_| TaskSpawnError::StructureError)?;
        Ok(task)
    }

    /// Set this task to be the next to run after returning from kernel space.
    pub fn make_next_task(&self) {
        scheduler::set_next_context(*self.kernel_stack_head.lock());
    }

    pub fn id(&self) -> u64 {
        self.id
    }

    pub fn status(&self) -> NoIRQSpinlockGuard<'_, TaskStatus> {
        self.status.lock()
    }
}

impl Drop for Task {
    fn drop(&mut self) {
        unsafe {
            heap_pages::deallocate(self.kernel_stack_base, TASK_STACK_SIZE);
        }
    }
}

pub fn initialize() {
    TASKS.init(|| AVLTree::new());
}
