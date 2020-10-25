pub mod async_task;
pub mod scheduling;
pub mod structs;
pub mod wait_queue;

pub use async_task::{make_task_waker, run_future, spawn_async, TaskExitFuture};
pub use scheduling::{scheduler, scheduler_initialized, yield_cpu};
pub use structs::{start_initial_task, ExitStatus, Task, TaskHandle, TaskSpawnError, TaskStatus};
pub use wait_queue::{WaitMode, WaitQueue, WaitQueueFuture};

use alloc_crate::sync::Arc;

use crate::lock::{NoIRQSpinlock, NoIRQSpinlockGuard};
use crate::paging::AddressSpace;

pub fn initialize(address_space: Arc<NoIRQSpinlock<AddressSpace>>) {
    structs::initialize();
    scheduling::initialize(address_space);
    println!("tasks: initialization complete");
}

pub fn current_task() -> &'static Task {
    Task::get_current_task().unwrap()
}

pub fn current_task_handle() -> TaskHandle {
    Task::get_current_task().unwrap().new_handle()
}

pub fn cur_address_space_handle() -> Arc<NoIRQSpinlock<AddressSpace>> {
    current_task().clone_address_space()
}

// probably the wrong lifetime for this, but it's close enough
pub fn current_address_space() -> NoIRQSpinlockGuard<'static, AddressSpace> {
    current_task().address_space()
}
