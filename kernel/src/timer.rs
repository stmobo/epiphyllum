use alloc::boxed::Box;
use alloc::sync::Arc;
use core::ptr;
use core::sync::atomic::{AtomicBool, AtomicPtr, AtomicU64, Ordering};

use crate::devices::timer::max_timer_deadline;

pub const TICKS_PER_SECOND: u64 = 4096;

static TIMER_LIST: TimerList = TimerList {
    head: AtomicPtr::new(ptr::null_mut()),
    cleanup: AtomicPtr::new(ptr::null_mut()),
};

static KERNEL_TICKS: AtomicU64 = AtomicU64::new(0);
static NEXT_DEADLINE: AtomicU64 = AtomicU64::new(u64::max_value());

pub fn get_kernel_ticks() -> u64 {
    KERNEL_TICKS.load(Ordering::Relaxed)
}

#[derive(Debug)]
struct TimerList {
    head: AtomicPtr<TimerListNode>,
    cleanup: AtomicPtr<TimerListNode>,
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

    /// Free all memory used by cleanup list nodes.
    ///
    /// This needs to run *outside* interrupt context!
    fn free_cleanup_list(&self) {
        let mut cur: *mut TimerListNode = self.cleanup.load(Ordering::Acquire);
        while cur != ptr::null_mut() {
            unsafe {
                let b: Box<TimerListNode> = Box::from_raw(cur);
                cur = b.next.load(Ordering::Acquire);

                drop(b);
            }
        }
    }

    /// Moves a timer list node into the "cleanup" list.
    fn move_to_cleanup(&self, node: *mut TimerListNode) {
        /* Should only be called from sweep() */
        unsafe {
            let prev_cleanup_head = self.cleanup.load(Ordering::Acquire);

            (*node).next.store(prev_cleanup_head, Ordering::Relaxed);
            (*node).timer.dead.store(true, Ordering::Release);

            self.cleanup.store(node, Ordering::Release);
        }
    }

    /// Update all timers in this list, running their callbacks if necessary.
    ///
    /// dt: ticks since last sweep
    fn sweep(&self, dt: u64) -> u64 {
        /* Only one thread should be running this at any time! */
        let cur_head = self.head.load(Ordering::Acquire);

        let mut next_deadline: u64 = u64::max_value();

        unsafe {
            if cur_head != ptr::null_mut() {
                /* Sweep through non-head nodes first. */
                let mut prev_ptr: &AtomicPtr<TimerListNode> = &(*cur_head).next;
                let mut cur = prev_ptr.load(Ordering::Acquire);

                while cur != ptr::null_mut() {
                    let next_ptr = &(*cur).next;
                    let next_node = next_ptr.load(Ordering::Acquire);

                    let timer: &Timer = &(*cur).timer;
                    let mut cur_deadline = timer.deadline.fetch_sub(dt, Ordering::AcqRel);
                    let period = timer.period.load(Ordering::Relaxed);
                    let mut timer_unlinked = false;

                    let skip = timer.skip.load(Ordering::Relaxed);
                    if skip || cur_deadline <= dt {
                        let unlink = skip || period == 0;
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

                        timer.fire_count.fetch_add(1, Ordering::Release);
                        if period > 0 {
                            timer.deadline.store(period, Ordering::Release);
                            cur_deadline = period;
                        }

                        drop(timer);
                        if unlink {
                            /* Clean up node storage */
                            self.move_to_cleanup(cur);
                            timer_unlinked = true;
                        }
                    } else {
                        prev_ptr = next_ptr;
                    }

                    if !timer_unlinked && cur_deadline < next_deadline {
                        next_deadline = cur_deadline;
                    }

                    cur = next_node;
                }

                /* Process cur_head. */
                let timer: &Timer = &(*cur_head).timer;
                let period = timer.period.load(Ordering::Relaxed);
                let mut cur_deadline = timer.deadline.fetch_sub(dt, Ordering::AcqRel);
                let mut timer_unlinked = false;
                let skip = timer.skip.load(Ordering::Relaxed);

                if skip || cur_deadline <= dt {
                    let unlink = skip || period == 0;

                    if unlink {
                        /* Need to unlink cur_head. */
                        let next = (*cur_head).next.load(Ordering::Relaxed);
                        let prev_head =
                            self.head.compare_and_swap(cur_head, next, Ordering::AcqRel);
                        if prev_head != cur_head {
                            /* There are new nodes in the list.
                             * We need to traverse the list to unlink cur_head.
                             */
                            cur = prev_head;
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

                    timer.fire_count.fetch_add(1, Ordering::Release);
                    if period > 0 {
                        timer.deadline.store(period, Ordering::Release);
                        cur_deadline = period;
                    }

                    drop(timer);
                    if unlink {
                        self.move_to_cleanup(cur_head);
                        timer_unlinked = true;
                    }
                }

                if !timer_unlinked && cur_deadline < next_deadline {
                    next_deadline = cur_deadline;
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
    period: AtomicU64,
    fire_count: AtomicU64,
    skip: AtomicBool,
    dead: AtomicBool,
}

impl Timer {
    fn new<T>(callback: T, deadline: u64, period: Option<u64>) -> Timer
    where
        T: Fn() + Send + Sync + 'static,
    {
        Timer {
            callback: Box::new(callback),
            deadline: AtomicU64::new(deadline),
            period: AtomicU64::new(period.unwrap_or(0)),
            fire_count: AtomicU64::new(0),
            skip: AtomicBool::new(false),
            dead: AtomicBool::new(false),
        }
    }

    /// Prevent this timer from firing in the future.
    pub fn cancel(&self) {
        self.skip.store(true, Ordering::Relaxed);
    }

    /// Get the number of times this timer has been triggered.
    pub fn times_fired(&self) -> u64 {
        self.fire_count.load(Ordering::Relaxed)
    }

    /// Returns `true` if this timer has fired at least once before.
    pub fn triggered(&self) -> bool {
        self.fire_count.load(Ordering::Relaxed) > 0
    }

    pub fn is_dead(&self) -> bool {
        self.dead.load(Ordering::Acquire)
    }
}

fn reschedule_timer_interrupt(dt: Option<u64>) {
    use crate::devices;

    if let Some(deadline) = dt {
        assert!(deadline <= max_timer_deadline());
        devices::timer::set_lapic_oneshot(deadline);
    } else {
        devices::timer::clear_lapic();
    }
}

/// Runs pending timers.
pub fn update_timers() {
    let mut dt = NEXT_DEADLINE.load(Ordering::Acquire);
    if dt == u64::max_value() {
        return;
    }

    KERNEL_TICKS.fetch_add(dt, Ordering::Release);

    // new_dt == u64::max_value() indicates there is no next deadline
    let mut new_dt: u64 = TIMER_LIST.sweep(dt);
    if new_dt != u64::max_value() && new_dt >= max_timer_deadline() {
        new_dt = max_timer_deadline();
    }

    loop {
        if NEXT_DEADLINE.compare_and_swap(dt, new_dt, Ordering::Release) == dt {
            /* Successfully CAS'd new DT value */
            if new_dt < u64::max_value() {
                reschedule_timer_interrupt(Some(new_dt));
            } else {
                reschedule_timer_interrupt(None);
            }

            break;
        }

        dt = NEXT_DEADLINE.load(Ordering::Acquire);
        if new_dt >= dt {
            /* Someone else has already rescheduled the timer interrupt */
            break;
        }
    }
}

/// Schedules a new timer that will fire in the future.
pub fn schedule_timer<T>(callback: T, deadline: u64, period: Option<u64>) -> Arc<Timer>
where
    T: Fn() + Send + Sync + 'static,
{
    let timer = Arc::new(Timer::new(callback, deadline, period));
    let effective_deadline: u64;

    if deadline > max_timer_deadline() {
        effective_deadline = max_timer_deadline();
    } else {
        effective_deadline = deadline;
    }

    TIMER_LIST.insert(Box::new(TimerListNode::new(timer.clone())));
    loop {
        let next_deadline = NEXT_DEADLINE.load(Ordering::Acquire);
        if effective_deadline >= next_deadline {
            break;
        }

        if NEXT_DEADLINE.compare_and_swap(next_deadline, effective_deadline, Ordering::Release)
            == next_deadline
        {
            reschedule_timer_interrupt(Some(effective_deadline));
            break;
        }
    }

    timer
}
