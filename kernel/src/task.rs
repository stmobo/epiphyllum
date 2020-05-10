mod scheduler;
mod structs;

pub use scheduler::{get_next_context, set_next_context, switch_to_task};
pub use structs::{Task, TaskHandle, TaskSpawnError, TaskStatus};

pub fn initialize() {
    structs::initialize();
}
