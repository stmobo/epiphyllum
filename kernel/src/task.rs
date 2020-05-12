pub mod scheduling;
pub mod structs;

pub use scheduling::{current_context, current_task, scheduler, yield_cpu};
pub use structs::{Task, TaskHandle, TaskSpawnError, TaskStatus};

pub fn initialize() {
    structs::initialize();
    scheduling::initialize();
}
