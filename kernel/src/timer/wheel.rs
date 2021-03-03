use alloc_crate::boxed::Box;
use core::mem::MaybeUninit;

use super::get_kernel_ticks;
use crate::lock::LockedGlobal;

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum TimerDeadline {
    Absolute(u64),
    Relative(u64),
}

impl TimerDeadline {
    /// Get the absolute time associated with this deadline.
    pub fn absolute(self) -> u64 {
        match self {
            TimerDeadline::Absolute(t) => t,
            TimerDeadline::Relative(t) => get_kernel_ticks() + t,
        }
    }

    /// Get the relative time associated with this deadline, if this deadline
    /// refers to a time in the future.
    ///
    /// Otherwise, returns None.
    pub fn relative(self) -> Option<u64> {
        match self {
            TimerDeadline::Relative(t) => Some(t),
            TimerDeadline::Absolute(t) => {
                let cur = get_kernel_ticks();
                if t >= cur {
                    Some(t - cur)
                } else {
                    None
                }
            }
        }
    }
}

/// A timer primitive.
///
/// Internally, this is nothing more than a boxed callback closure and an
/// associated deadline.
///
/// Note that the callback is called in the context of the timer IRQ.
pub struct TimerData {
    pub callback: Box<dyn FnOnce() + Sync + Send + 'static>,
    deadline: u64,
}

pub struct WheelNode {
    timer: TimerData,
    id: u64,
    next: Option<Box<WheelNode>>,
}

pub struct NodeIterator(Option<Box<WheelNode>>);

impl NodeIterator {
    pub fn new(start: Option<Box<WheelNode>>) -> NodeIterator {
        NodeIterator(start)
    }
}

impl Iterator for NodeIterator {
    type Item = Box<WheelNode>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(mut node) = self.0.take() {
            self.0 = node.next.take();
            Some(node)
        } else {
            None
        }
    }
}

/// A handle to a started timer.
pub struct TimerHandle {
    id: u64,
    deadline: u64,
}

impl TimerHandle {
    /// Stop the associated timer.
    pub fn stop(&self) -> Result<TimerData, ()> {
        TIMER_WHEEL.lock().remove(self)
    }

    /// Get the absolute deadline associated with this timer.
    pub fn deadline(&self) -> TimerDeadline {
        TimerDeadline::Absolute(self.deadline)
    }

    /// Get the associated timer's ID.
    pub fn id(&self) -> u64 {
        self.id
    }
}

pub struct TimerWheel {
    wheels: [Box<[Option<Box<WheelNode>>]>; 8], // each inner slice has fixed size of 256 elements
    indices: [u8; 8],
    next_id: u64,
}

impl TimerWheel {
    fn create_wheel_slice() -> Box<[Option<Box<WheelNode>>]> {
        let mut b: Box<[MaybeUninit<Option<Box<WheelNode>>>]> = Box::new_uninit_slice(256);

        unsafe {
            for i in b.iter_mut() {
                i.write(None);
            }

            b.assume_init()
        }
    }

    fn new() -> TimerWheel {
        TimerWheel {
            wheels: [
                TimerWheel::create_wheel_slice(),
                TimerWheel::create_wheel_slice(),
                TimerWheel::create_wheel_slice(),
                TimerWheel::create_wheel_slice(),
                TimerWheel::create_wheel_slice(),
                TimerWheel::create_wheel_slice(),
                TimerWheel::create_wheel_slice(),
                TimerWheel::create_wheel_slice(),
            ],
            indices: [0; 8],
            next_id: 0,
        }
    }

    fn nodes(&mut self, level: usize, index: u8) -> NodeIterator {
        NodeIterator::new(self.wheels[level][index as usize].take())
    }

    fn tick(&mut self, level: usize) -> NodeIterator {
        if self.indices[level] == 255 {
            self.cascade(level);
            self.indices[level] = 0;
        } else {
            self.indices[level] += 1;
        }

        self.nodes(level, self.indices[level])
    }

    fn cascade(&mut self, level: usize) {
        if level == 7 {
            return;
        }

        for mut node in self.tick(level + 1) {
            let deadline = node.timer.deadline;
            let index = ((deadline >> (8 * level)) & 0xFF) as usize;

            node.next = self.wheels[level][index].take();
            self.wheels[level][index] = Some(node);
        }
    }

    fn insert(&mut self, timer: TimerData) -> Result<TimerHandle, u64> {
        let id = self.next_id;

        /* Find first wheel where timer is at least 1 unit into the future. */
        let deadline_idx = timer.deadline.to_le_bytes();
        for level in (0..=7usize).rev() {
            if deadline_idx[level] > self.indices[level] {
                let insert_at = deadline_idx[level] as usize;
                let deadline = timer.deadline;
                let node = Box::new(WheelNode {
                    timer,
                    id,
                    next: self.wheels[level][insert_at].take(),
                });

                self.wheels[level][insert_at] = Some(node);
                self.next_id += 1;

                return Ok(TimerHandle { id, deadline });
            }
        }

        Err(u64::from_le_bytes(self.indices))
    }

    fn remove(&mut self, timer: &TimerHandle) -> Result<TimerData, ()> {
        /* As with insert, the timer will be stored in the first wheel where
         * the timer's index lies in the future.
         */
        let deadline_idx = timer.deadline.to_le_bytes();
        for level in (0..=7usize).rev() {
            if deadline_idx[level] > self.indices[level] {
                let idx = deadline_idx[level];
                let mut removed_node: Option<WheelNode> = None;
                let mut cur_head: Option<Box<WheelNode>> = None;

                for mut node in self.nodes(level, idx) {
                    if node.id == timer.id {
                        removed_node = Some(*node);
                    } else {
                        node.next = cur_head.take();
                        cur_head = Some(node);
                    }
                }

                self.wheels[level][idx as usize] = cur_head;
                if let Some(node) = removed_node {
                    return Ok(node.timer);
                } else {
                    return Err(());
                }
            }
        }

        Err(())
    }

    fn update(&mut self) -> NodeIterator {
        self.tick(0)
    }

    fn get_time(&self) -> u64 {
        u64::from_le_bytes(self.indices)
    }
}

static TIMER_WHEEL: LockedGlobal<TimerWheel> = LockedGlobal::new();

pub fn init_timer_wheel() {
    TIMER_WHEEL.init(TimerWheel::new);
}

/// Update all registered timers, running their callbacks as necessary.
pub fn update_timers(n_ticks: u64) -> u64 {
    for _ in 0..n_ticks {
        // NOTE: unlock wheel ASAP so that we don't deadlock, if timer callbacks
        // try to start new timers of their own.
        let nodes = TIMER_WHEEL.lock().update();
        for node in nodes {
            let node = *node;
            (node.timer.callback)();
        }
    }

    TIMER_WHEEL.lock().get_time()
}

impl TimerData {
    /// Create a new timer.
    /// 
    /// The timer will not be started until its start method is called.
    ///
    /// Note that the timer callback will be called in the context of the
    /// timer IRQ.
    pub fn new<F>(callback: F, deadline: TimerDeadline) -> TimerData
    where
        F: FnOnce() + Sync + Send + 'static,
    {
        TimerData {
            callback: Box::new(callback),
            deadline: deadline.absolute(),
        }
    }

    /// Set the deadline for this timer.
    pub fn set_deadline(&mut self, deadline: TimerDeadline) {
        self.deadline = deadline.absolute();
    }

    /// Get the (absolute) deadline associated with this timer.
    pub fn deadline(&self) -> TimerDeadline {
        TimerDeadline::Absolute(self.deadline)
    }

    /// Start this timer.
    /// 
    /// Returns a handle to the started timer, if successful.
    /// Returns the current kernel time if the timer could not be started
    /// (because its deadline has already passed).
    pub fn start(self) -> Result<TimerHandle, u64> {
        TIMER_WHEEL.lock().insert(self)
    }
}
