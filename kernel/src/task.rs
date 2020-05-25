pub mod async_task;
pub mod scheduling;
pub mod structs;
pub mod wait_queue;

pub use async_task::{make_task_waker, run_future, spawn_async, TaskExitFuture};
pub use scheduling::{
    cur_address_space_handle, current_address_space, current_context, current_task, scheduler,
    scheduler_initialized, yield_cpu,
};
pub use structs::{ExitStatus, Task, TaskHandle, TaskSpawnError, TaskStatus};
pub use wait_queue::{WaitMode, WaitQueue, WaitQueueFuture};

use alloc_crate::sync::Arc;

use crate::lock::NoIRQSpinlock;
use crate::paging::AddressSpace;

pub fn initialize(address_space: Arc<NoIRQSpinlock<AddressSpace>>) {
    structs::initialize();
    scheduling::initialize(address_space);
    println!("tasks: initialization complete");
}
