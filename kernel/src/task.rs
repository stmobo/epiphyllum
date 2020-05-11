pub mod scheduler;
pub mod structs;

pub use structs::{Task, TaskHandle, TaskSpawnError, TaskStatus};

pub fn initialize() {
    structs::initialize();
    scheduler::initialize();
}
