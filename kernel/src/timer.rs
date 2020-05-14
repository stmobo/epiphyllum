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
}

mod sleep_funcs {
    use alloc_crate::sync::Arc;
    use core::future::Future;
    use core::pin::Pin;
    use core::sync::atomic::{AtomicBool, Ordering};
    use core::task::{Context, Poll, Waker};

    use crate::lock::NoIRQSpinlock;
    use crate::task;

    use super::wheel::{TimerData, TimerDeadline};

    pub fn sleep(deadline: TimerDeadline) -> Result<(), u64> {
        let cur_task = task::current_task();
        let flag = Arc::new(AtomicBool::new(false));
        let cb_flag = flag.clone();

        TimerData::new(
            move || {
                cb_flag.store(true, Ordering::SeqCst);
                cur_task.schedule();
            },
            deadline,
        )
        .start()?;

        while !flag.load(Ordering::SeqCst) {
            task::yield_cpu();
        }

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
