mod extension;
mod wheel;

pub use extension::{Timer, TimerError};
pub use wheel::{update_timers, TimerData, TimerHandle};

pub const TICKS_PER_SECOND: u64 = 8192;
