pub mod async_task;
pub mod scheduling;
pub mod structs;
pub mod wait_queue;

pub use async_task::{make_task_waker, run_future, spawn_async, TaskExitFuture};
pub use scheduling::{scheduler, scheduler_initialized, yield_cpu};
pub use structs::{start_initial_task, ExitStatus, Task, TaskHandle, TaskSpawnError, TaskStatus, CurrentTaskRef};
pub use wait_queue::{WaitMode, WaitQueue, WaitQueueFuture};

use alloc_crate::sync::Arc;

use crate::lock::{NoIRQSpinlock, NoIRQSpinlockGuard};
use crate::paging::AddressSpace;

pub fn initialize(address_space: Arc<NoIRQSpinlock<AddressSpace>>) {
    structs::initialize();
    scheduling::initialize(address_space);
    println!("tasks: initialization complete");
}

/// Get a reference to the currently running Task.
///
/// Note that this does not require incrementing / decrementing the reference
/// count for the current Task, however in exchange the reference is non-Send
/// and non-Sync.
pub fn current_task() -> CurrentTaskRef {
    Task::get_current_task().expect("no current task")
}

/// Get a TaskHandle for the currently running Task.
///
/// This reference is Send/Sync, but also requires incrementing / decrementing
/// the current Task's reference count (similarly to Arc).
pub fn current_task_handle() -> TaskHandle {
    current_task().new_handle()
}
