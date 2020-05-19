pub mod async_task;
pub mod scheduling;
pub mod structs;
pub mod wait_queue;

pub use async_task::{make_task_waker, run_future, spawn_async, TaskExitFuture};
pub use scheduling::{current_context, current_task, scheduler, scheduler_initialized, yield_cpu};
pub use structs::{ExitStatus, Task, TaskHandle, TaskSpawnError, TaskStatus};
pub use wait_queue::{WaitMode, WaitQueue, WaitQueueFuture};

pub fn initialize() {
    structs::initialize();
    scheduling::initialize();
}
