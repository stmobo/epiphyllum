use alloc::boxed::Box;
use alloc::sync::Arc;
use core::ptr;
use core::sync::atomic::{AtomicBool, AtomicPtr, AtomicU64, Ordering};

pub const TICKS_PER_SECOND: u64 = 4096;

static TIMER_LIST: TimerList = TimerList {
    head: AtomicPtr::new(ptr::null_mut()),
};

static KERNEL_TICKS: AtomicU64 = AtomicU64::new(0);
static NEXT_DEADLINE: AtomicU64 = AtomicU64::new(u64::max_value());

pub fn get_kernel_ticks() -> u64 {
    KERNEL_TICKS.load(Ordering::Relaxed)
}

#[derive(Debug)]
struct TimerList {
    head: AtomicPtr<TimerListNode>,
}

impl TimerList {
    fn insert(&self, new_node: Box<TimerListNode>) {
        let new_node = Box::into_raw(new_node);

        unsafe {
            loop {
                let cur = self.head.load(Ordering::Acquire);

                (*new_node).next.store(cur, Ordering::Relaxed);
                if self.head.compare_and_swap(cur, new_node, Ordering::Release) == cur {
                    return;
                }
            }
        }
    }

    fn sweep(&self, cur_time: u64) -> u64 {
        /* Only one thread should be running this at any time! */
        let cur_head = self.head.load(Ordering::Acquire);

        let mut next_deadline: u64 = u64::max_value();

        unsafe {
            if cur_head != ptr::null_mut() {
                /* Sweep through non-head nodes first. */
                let mut prev_ptr: &AtomicPtr<TimerListNode> = &(*cur_head).next;
                let mut prev_node: *mut TimerListNode = cur_head;
                let mut cur = prev_ptr.load(Ordering::Acquire);

                while cur != ptr::null_mut() {
                    let next_ptr = &(*cur).next;
                    let next_node = next_ptr.load(Ordering::Acquire);

                    let timer: &Timer = &(*cur).timer;
                    let mut timer_deadline = timer.deadline.load(Ordering::Relaxed);

                    let skip = timer.skip.load(Ordering::Relaxed);
                    if skip || timer_deadline <= cur_time {
                        let unlink = skip || timer.period.is_none();
                        if unlink {
                            /* This node needs to be unlinked.
                             * We don't have to use CAS here since nothing else concurrently
                             * touches the next pointers of inserted nodes.
                             */
                            prev_ptr.store(next_node, Ordering::Release);
                        }

                        if !skip {
                            (timer.callback)();
                        }
                        timer.fired.store(true, Ordering::Release);
                        if let Some(period) = timer.period {
                            timer.deadline.fetch_add(period, Ordering::Release);
                            timer_deadline = timer.deadline.load(Ordering::Relaxed);
                        }

                        drop(timer);
                        if unlink {
                            /* Clean up node storage */
                            let b: Box<TimerListNode> = Box::from_raw(cur);
                            drop(b);
                        }
                    } else {
                        prev_ptr = next_ptr;
                        prev_node = cur;
                    }

                    if timer_deadline > cur_time && timer_deadline < next_deadline {
                        next_deadline = timer_deadline;
                    }

                    cur = next_node;
                }

                /* Process cur_head. */
                let timer: &Timer = &(*cur_head).timer;
                let mut timer_deadline = timer.deadline.load(Ordering::Relaxed);
                let skip = timer.skip.load(Ordering::Relaxed);
                if skip || timer_deadline <= cur_time {
                    let unlink = skip || timer.period.is_none();

                    if unlink {
                        /* Need to unlink cur_head. */
                        let next = (*cur_head).next.load(Ordering::Relaxed);
                        if self
                            .head
                            .compare_and_swap(cur_head, next, Ordering::Release)
                            != cur_head
                        {
                            /* There are new nodes in the list.
                             * We need to traverse the list to unlink cur_head.
                             */

                            let new_head = self.head.load(Ordering::Acquire);
                            cur = new_head;
                            prev_ptr = &self.head;

                            while cur != ptr::null_mut() && cur != cur_head {
                                prev_ptr = &(*cur).next;
                                cur = prev_ptr.load(Ordering::Acquire);
                            }

                            assert_ne!(cur, ptr::null_mut());
                            prev_ptr.store(next, Ordering::Release);
                        }
                    }

                    if !skip {
                        (timer.callback)();
                    }

                    timer.fired.store(true, Ordering::Release);
                    if let Some(period) = timer.period {
                        timer.deadline.fetch_add(period, Ordering::Release);
                        timer_deadline = timer.deadline.load(Ordering::Relaxed);
                    }

                    drop(timer);
                    if unlink {
                        let b: Box<TimerListNode> = Box::from_raw(cur_head);
                        drop(b);
                    }
                }

                if timer_deadline > cur_time && timer_deadline < next_deadline {
                    next_deadline = timer_deadline;
                }
            }
        }

        next_deadline
    }
}

struct TimerListNode {
    timer: Arc<Timer>,
    next: AtomicPtr<TimerListNode>,
}

impl TimerListNode {
    fn new(timer: Arc<Timer>) -> TimerListNode {
        TimerListNode {
            timer,
            next: AtomicPtr::new(ptr::null_mut()),
        }
    }
}

pub struct Timer {
    callback: Box<dyn Fn() + Send + Sync + 'static>,
    deadline: AtomicU64,
    period: Option<u64>,
    skip: AtomicBool,
    fired: AtomicBool,
}

impl Timer {
    fn new<T>(callback: T, deadline: u64, period: Option<u64>) -> Timer
    where
        T: Fn() + Send + Sync + 'static,
    {
        Timer {
            callback: Box::new(callback),
            deadline: AtomicU64::new(deadline),
            period,
            skip: AtomicBool::new(false),
            fired: AtomicBool::new(false),
        }
    }
}

fn reschedule_timer_interrupt(ticks: Option<u64>) {
    use crate::devices;

    if let Some(deadline) = ticks {
        let cur_time = KERNEL_TICKS.load(Ordering::Relaxed);
        if deadline > cur_time {
            devices::timer::set_lapic_oneshot(deadline - cur_time);
            return;
        }
    }

    devices::timer::clear_lapic();
}

/// Runs pending timers.
pub fn update_timers() {
    let last_time = KERNEL_TICKS.load(Ordering::Acquire);
    let mut cur_time = NEXT_DEADLINE.load(Ordering::Acquire);

    if cur_time < last_time || cur_time == u64::max_value() {
        return;
    }

    KERNEL_TICKS.store(cur_time, Ordering::Release);

    // next_time == u64::max_value() indicates there is no next deadline
    let mut next_time: u64 = TIMER_LIST.sweep(cur_time);
    loop {
        if NEXT_DEADLINE.compare_and_swap(cur_time, next_time, Ordering::Release) == cur_time {
            if next_time < u64::max_value() {
                reschedule_timer_interrupt(Some(next_time));
            } else {
                reschedule_timer_interrupt(None);
            }

            break;
        }

        cur_time = NEXT_DEADLINE.load(Ordering::Acquire);
        if next_time >= cur_time {
            /* Someone else has already rescheduled the timer interrupt */
            break;
        }
    }
}

pub fn schedule_timer<T>(callback: T, deadline: u64, period: Option<u64>) -> Arc<Timer>
where
    T: Fn() + Send + Sync + 'static,
{
    let timer = Arc::new(Timer::new(callback, deadline, period));
    let cur_time = KERNEL_TICKS.load(Ordering::Relaxed);
    if deadline < cur_time {
        (timer.callback)();
        timer.fired.store(true, Ordering::Relaxed);

        return timer;
    }

    TIMER_LIST.insert(Box::new(TimerListNode::new(timer.clone())));
    loop {
        let next_deadline = NEXT_DEADLINE.load(Ordering::Acquire);
        if deadline >= next_deadline {
            break;
        }

        if NEXT_DEADLINE.compare_and_swap(next_deadline, deadline, Ordering::Release)
            == next_deadline
        {
            reschedule_timer_interrupt(Some(deadline));
            break;
        }
    }

    timer
}

pub fn schedule_timer_relative<T>(callback: T, deadline: u64, period: Option<u64>) -> Arc<Timer>
where
    T: Fn() + Send + Sync + 'static,
{
    let cur_time = KERNEL_TICKS.load(Ordering::Relaxed);
    schedule_timer(callback, cur_time + deadline, period)
}
