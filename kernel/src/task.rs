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

pub fn initialize() {
    structs::initialize();
    scheduling::initialize();
    println!("tasks: initialization complete");
}
