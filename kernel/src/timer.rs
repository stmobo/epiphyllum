use core::sync::atomic::{AtomicU64, Ordering};

mod wheel;

pub use sleep_funcs::{sleep, sleep_async, AsyncSleep};
pub use wheel::{TimerData, TimerDeadline, TimerHandle};

pub const TICKS_PER_SECOND: u64 = 8192;
pub static KERNEL_TICKS: AtomicU64 = AtomicU64::new(0);

pub fn update_timers(n_ticks: u64) {
    let new_time = wheel::update_timers(n_ticks);
    KERNEL_TICKS.store(new_time, Ordering::SeqCst);
}

pub fn get_kernel_ticks() -> u64 {
    KERNEL_TICKS.load(Ordering::SeqCst)
}

pub fn initialize() {
    wheel::init_timer_wheel();
    println!("timer: timer wheel initialized");
}

mod sleep_funcs {
    use alloc_crate::sync::Arc;
    use core::future::Future;
    use core::pin::Pin;
    use core::sync::atomic::{AtomicBool, Ordering};
    use core::task::{Context, Poll, Waker};

    use crate::lock::NoIRQSpinlock;
    use crate::task;
    use crate::task::TaskStatus;

    use super::wheel::{TimerData, TimerDeadline};

    pub fn sleep(deadline: TimerDeadline) -> Result<(), u64> {
        let cur_task = task::current_task_handle();
        let flag = Arc::new(AtomicBool::new(false));
        let cb_flag = flag.clone();
        let cb_handle = cur_task.clone();

        TimerData::new(
            move || {
                cb_flag.store(true, Ordering::SeqCst);
                cb_handle.schedule();
            },
            deadline,
        )
        .start()?;

        loop {
            cur_task.set_wakeup_pending(false);

            if flag.load(Ordering::SeqCst) {
                break;
            }

            cur_task.set_status(TaskStatus::Sleeping);
            task::yield_cpu();
        }

        cur_task.set_wakeup_pending(false);
        cur_task.set_status(TaskStatus::Running);

        Ok(())
    }

    pub struct AsyncSleepState {
        ready: bool,
        waker: Option<Waker>,
    }

    pub struct AsyncSleep(Arc<NoIRQSpinlock<AsyncSleepState>>);

    impl Future for AsyncSleep {
        type Output = ();

        fn poll(self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<()> {
            let mut state = self.0.lock();
            if state.ready {
                Poll::Ready(())
            } else {
                state.waker = Some(ctx.waker().clone());
                Poll::Pending
            }
        }
    }

    impl AsyncSleep {
        pub fn new(deadline: TimerDeadline) -> Result<AsyncSleep, u64> {
            let state = Arc::new(NoIRQSpinlock::new(AsyncSleepState {
                ready: false,
                waker: None,
            }));

            let cb_state = state.clone();
            TimerData::new(
                move || {
                    let mut state = cb_state.lock();
                    state.ready = true;
                    if let Some(waker) = state.waker.take() {
                        waker.wake();
                    }
                },
                deadline,
            )
            .start()?;

            Ok(AsyncSleep(state))
        }
    }

    // TODO: cancel timer on Drop?

    pub fn sleep_async(deadline: TimerDeadline) -> Result<AsyncSleep, u64> {
        AsyncSleep::new(deadline)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::task;
    use kernel_test_macro::kernel_test;

    #[kernel_test]
    fn test_timed_sleep() {
        let deadline = TimerDeadline::Relative(1024);
        let start_ticks = get_kernel_ticks();

        sleep(deadline).expect("could not start sleep");

        let end_ticks = get_kernel_ticks();
        let dt = end_ticks - start_ticks;
        assert!(
            dt >= 1024,
            "test did not sleep for long enough (slept for {} ticks, expected 1024)",
            dt
        );
    }

    #[kernel_test]
    fn test_async_sleep() {
        let deadline = TimerDeadline::Relative(1024);
        let start_ticks = get_kernel_ticks();

        task::run_future(sleep_async(deadline).expect("could not start sleep"));

        let end_ticks = get_kernel_ticks();
        let dt = end_ticks - start_ticks;
        assert!(
            dt >= 1024,
            "test did not sleep for long enough (slept for {} ticks, expected 1024)",
            dt
        );
    }
}
