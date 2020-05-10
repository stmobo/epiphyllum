use core::ptr;
use core::sync::atomic::{AtomicPtr, Ordering};

use crate::interrupts::InterruptFrame;

static NEXT_TASK: AtomicPtr<InterruptFrame> = AtomicPtr::new(ptr::null_mut());

extern "C" {
    fn switch_context(frame: *mut InterruptFrame) -> !;
}

pub fn set_next_context(ctx: *mut InterruptFrame) {
    NEXT_TASK.store(ctx, Ordering::SeqCst);
}

pub fn get_next_context() -> *mut InterruptFrame {
    NEXT_TASK.load(Ordering::SeqCst)
}

pub unsafe fn switch_to_task() -> ! {
    let next = get_next_context();
    switch_context(next);
}
