use core::sync::atomic::{AtomicU64, Ordering};

mod extension;
mod wheel;

pub use extension::{Timer, TimerError};
pub use wheel::{TimerData, TimerDeadline, TimerHandle};

pub const TICKS_PER_SECOND: u64 = 8192;
pub static KERNEL_TICKS: AtomicU64 = AtomicU64::new(0);

pub fn initialize() {
    wheel::init_timer_wheel();
}

pub fn update_timers(n_ticks: u64) {
    let new_time = wheel::update_timers(n_ticks);
    KERNEL_TICKS.store(new_time, Ordering::SeqCst);
}

pub fn get_kernel_ticks() -> u64 {
    KERNEL_TICKS.load(Ordering::SeqCst)
}
