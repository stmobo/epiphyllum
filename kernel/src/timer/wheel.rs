use alloc_crate::boxed::Box;
use core::mem::MaybeUninit;

use super::get_kernel_ticks;
use crate::lock::LockedGlobal;

pub struct TimerData {
    pub callback: Box<dyn FnOnce() + Sync + Send + 'static>,
    deadline: u64,
}

pub struct WheelNode {
    timer: TimerData,
    id: u64,
    next: Option<Box<WheelNode>>,
}

pub struct TimerHandle {
    id: u64,
    deadline: u64,
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum TimerDeadline {
    Absolute(u64),
    Relative(u64),
}

impl TimerDeadline {
    pub fn absolute(self) -> u64 {
        match self {
            TimerDeadline::Absolute(t) => t,
            TimerDeadline::Relative(t) => get_kernel_ticks() + t,
        }
    }

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

    fn tick(&mut self, level: usize) -> Option<Box<WheelNode>> {
        if self.indices[level] == 255 {
            self.cascade(level);
            self.indices[level] = 0;
        } else {
            self.indices[level] += 1;
        }

        let idx = self.indices[level];
        self.wheels[level][idx as usize].take()
    }

    fn cascade(&mut self, level: usize) {
        if level == 7 {
            return;
        }

        let mut cur = self.tick(level + 1);
        while cur.is_some() {
            let mut node = cur.unwrap();
            cur = node.next.take();

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
                let idx = self.indices[level] as usize;
                let mut cur = self.wheels[level][idx].take();
                let mut head: Option<Box<WheelNode>> = None;
                let mut search_node: Option<Box<WheelNode>> = None;

                while cur.is_some() {
                    let mut node = cur.unwrap();

                    if node.id != timer.id {
                        // go to next node
                        if let Some(b) = head {
                            cur = node.next.replace(b);
                        } else {
                            cur = node.next.take();
                        }

                        head = Some(node);
                    } else {
                        // found the node
                        // save it for later and unlink it from the rest
                        cur = node.next.take();
                        search_node = Some(node);
                    }
                }

                if let Some(node) = head {
                    self.wheels[level][idx].replace(node);
                }

                if let Some(node) = search_node {
                    let node = *node;
                    return Ok(node.timer);
                } else {
                    return Err(());
                }
            }
        }

        Err(())
    }

    fn update(&mut self) -> Option<Box<WheelNode>> {
        self.tick(0)
    }

    fn get_time(&self) -> u64 {
        u64::from_le_bytes(self.indices)
    }
}

static TIMER_WHEEL: LockedGlobal<TimerWheel> = LockedGlobal::new();

pub fn init_timer_wheel() {
    TIMER_WHEEL.init(|| TimerWheel::new());
}

pub fn update_timers(n_ticks: u64) -> u64 {
    for _ in 0..n_ticks {
        let mut cur = TIMER_WHEEL.lock().update();
        while cur.is_some() {
            let mut node = *cur.unwrap();
            cur = node.next.take();
            (node.timer.callback)();
        }
    }

    TIMER_WHEEL.lock().get_time()
}

impl TimerData {
    pub fn new<F>(callback: F, deadline: TimerDeadline) -> TimerData
    where
        F: FnOnce() + Sync + Send + 'static,
    {
        TimerData {
            callback: Box::new(callback),
            deadline: deadline.absolute(),
        }
    }

    pub fn set_deadline(&mut self, deadline: TimerDeadline) {
        self.deadline = deadline.absolute();
    }

    pub fn deadline(&self) -> TimerDeadline {
        TimerDeadline::Absolute(self.deadline)
    }

    pub fn start(self) -> Result<TimerHandle, u64> {
        TIMER_WHEEL.lock().insert(self)
    }
}

impl TimerHandle {
    pub fn stop(&self) -> Result<TimerData, ()> {
        TIMER_WHEEL.lock().remove(self)
    }

    pub fn deadline(&self) -> TimerDeadline {
        TimerDeadline::Absolute(self.deadline)
    }

    pub fn id(&self) -> u64 {
        self.id
    }
}
