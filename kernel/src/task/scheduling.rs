use alloc_crate::sync::Arc;
use core::sync::atomic::{AtomicU64, Ordering};
use epiphyllum_structures::RBTree;

use super::structs::{AtomicTaskHandle, Task, TaskHandle, TaskStatus};
use crate::lock::{NoIRQSpinlock, OnceCell};
use crate::paging::AddressSpace;
use crate::timer::{get_kernel_ticks, TICKS_PER_SECOND};

static SCHEDULER: OnceCell<Scheduler> = OnceCell::new();
const NS_PER_TICK: u64 = 1_000_000_000 / TICKS_PER_SECOND;
const GRANULARITY: u64 = 7; // in ms

#[derive(Debug)]
pub struct SchedulerData {
    /// The absolute time at which this process last executed.
    exec_start: AtomicU64,

    /// The virtual runtime of this process, in nanoseconds.
    virtual_runtime: AtomicU64,

    scheduler_key: NoIRQSpinlock<Option<TimelineKey>>,
}

impl SchedulerData {
    pub fn new() -> SchedulerData {
        SchedulerData {
            exec_start: AtomicU64::new(0),
            virtual_runtime: AtomicU64::new(0),
            scheduler_key: NoIRQSpinlock::new(None),
        }
    }

    pub fn start_running(&self) {
        self.exec_start.store(get_kernel_ticks(), Ordering::SeqCst);
    }

    pub fn update_runtime(&self, n_tasks: u64) {
        let start_time = self.exec_start.load(Ordering::SeqCst);
        let abs_ns = (get_kernel_ticks() - start_time) * NS_PER_TICK;
        let virt_time = abs_ns / n_tasks;

        self.virtual_runtime.fetch_add(virt_time, Ordering::SeqCst);
    }

    fn set_runtime(&self, time: u64) {
        self.virtual_runtime.store(time, Ordering::SeqCst);
    }

    pub fn virtual_runtime(&self) -> u64 {
        self.virtual_runtime.load(Ordering::SeqCst)
    }
}

#[derive(Debug, Ord, PartialOrd, Eq, PartialEq, Clone)]
pub struct TimelineKey {
    virtual_runtime: u64,
    task_id: u64,
}

impl TimelineKey {
    fn new(task: &Task) -> TimelineKey {
        TimelineKey {
            virtual_runtime: task.scheduler_data().virtual_runtime(),
            task_id: task.id(),
        }
    }
}

pub struct SchedulerTimeline {
    tree: RBTree<TimelineKey, TaskHandle>,
    min_virt_runtime: u64,
}

impl SchedulerTimeline {
    fn new() -> SchedulerTimeline {
        SchedulerTimeline {
            tree: RBTree::new(),
            min_virt_runtime: 0,
        }
    }
}

pub struct Scheduler {
    timeline: NoIRQSpinlock<SchedulerTimeline>,
    default_task: TaskHandle,
    running_task: AtomicTaskHandle,
}

impl Scheduler {
    fn new(address_space: Arc<NoIRQSpinlock<AddressSpace>>) -> Scheduler {
        let default_task = unsafe {
            Task::new_raw(idle_task as usize, 0, address_space).expect("could not create idle task")
        };

        default_task.set_status(TaskStatus::Waiting);
        Scheduler {
            default_task: default_task.clone(),
            running_task: AtomicTaskHandle::new(default_task),
            timeline: NoIRQSpinlock::new(SchedulerTimeline::new()),
        }
    }

    /// Get a TaskHandle to the currently running Task.
    pub fn running_task_handle(&self) -> TaskHandle {
        self.running_task.load()
    }

    fn running_task_ref(&self) -> &Task {
        self.running_task.load_ref()
    }

    fn run_task(&self, next_task: TaskHandle) -> Option<TaskHandle> {
        let cur_task = self.running_task_handle();
        unsafe { cur_task.switch_context(&next_task) }
    }

    /// Wake up a Task, and schedule it for execution.
    /// Can be called from both regular and IRQ contexts.
    ///
    /// Returns true if the task was successfully added to the runqueue, and
    /// false if the task was already queued.
    pub fn schedule(&self, task: &Task) -> bool {
        let mut timeline = self.timeline.lock();
        let scheduler_data = task.scheduler_data();

        let n_tasks = (timeline.tree.len() as u64) + 1;
        let margin = (2 * GRANULARITY * 1_000_000) / n_tasks;

        if scheduler_data.virtual_runtime() < timeline.min_virt_runtime {
            scheduler_data.set_runtime(timeline.min_virt_runtime + margin);
        }

        let mut prev_key = scheduler_data.scheduler_key.lock();
        if prev_key.is_none() {
            let key = TimelineKey::new(task);
            if timeline.tree.insert(key.clone(), task.new_handle()).is_none() {
                *prev_key = Some(key);
                //direct_println!("scheduled task {}", task.id());
                return true;
            }
        }

        false
    }

    /// Remove a Task from the run queue.
    /// Can be called from both regular and IRQ contexts.
    ///
    /// Returns true if the task was successfully removed from the queue, and
    /// false if it wasn't queued to begin with.
    pub fn deschedule(&self, task: &Task) -> bool {
        let mut timeline = self.timeline.lock();
        let mut prev_key = task.scheduler_data().scheduler_key.lock();
        if let Some(key) = prev_key.take() {
            timeline
                .tree
                .remove(&key)
                .expect("inconsistent timeline key state");
            true
        } else {
            false
        }
    }

    fn swap_task(&self, new_task: &Task) {
        let prev_task = self.running_task.swap(new_task.new_handle());

        new_task.set_status(TaskStatus::Running);
        if prev_task.status() == TaskStatus::Running {
            prev_task.set_status(TaskStatus::Waiting);
        }

        unsafe {
            prev_task.switch_context(new_task);
        }
    }

    /// Run a scheduler update, swapping out the current Task for other tasks
    /// that are scheduled to run if necessary.
    pub fn update(&self) {
        let mut timeline = self.timeline.lock();
        let n_tasks = (timeline.tree.len() as u64) + 1;

        let cur_task = self.running_task_handle();
        let sched_data = cur_task.scheduler_data();
        let mut timeline_key_lock = sched_data.scheduler_key.lock();

        if cur_task.id() != self.default_task.id() {
            if let Some(old_key) = timeline_key_lock.take() {
                timeline
                    .tree
                    .remove(&old_key)
                    .expect("could not find old timeline key in tree");
            }
        }

        cur_task.scheduler_data().update_runtime(n_tasks);
        let new_key = TimelineKey::new(&cur_task);

        if cur_task.should_run() && cur_task.id() != self.default_task.id() {
            timeline
                .tree
                .insert(new_key.clone(), cur_task.clone());
            *timeline_key_lock = Some(new_key.clone());
        }

        let mut new_task = None;
        if let Some((key, task)) = timeline.tree.get_first() {
            let should_swap =
                (cur_task.id() == self.default_task.id()) || !cur_task.should_run() || {
                    let threshold = (GRANULARITY * 1_000_000) / n_tasks;
                    let diff = new_key.virtual_runtime.saturating_sub(key.virtual_runtime);

                    diff >= threshold
                };

            if should_swap {
                new_task = Some(task.clone());
            }

            timeline.min_virt_runtime = key.virtual_runtime;
        } else {
            // Run the default task
            new_task = Some(self.default_task.clone());
        }

        drop(timeline_key_lock);
        drop(timeline);

        if let Some(task) = new_task {
            self.swap_task(&task);
        }
    }

    /// Forcibly set the current running task.
    pub unsafe fn force_set_running_task(&self, task: TaskHandle) {
        task.set_status(TaskStatus::Running);
        self.schedule(&task);
        self.running_task.store(task);
    }
}

unsafe impl Sync for Scheduler {}

pub fn initialize(address_space: Arc<NoIRQSpinlock<AddressSpace>>) {
    if SCHEDULER.set(Scheduler::new(address_space)).is_err() {
        panic!("attempted to initialize scheduler twice");
    }
}

pub fn scheduler_initialized() -> bool {
    SCHEDULER.get().is_some()
}

pub fn scheduler() -> &'static Scheduler {
    SCHEDULER.get().expect("Scheduler not initialized")
}

pub fn yield_cpu() {
    scheduler().update();
}

fn idle_task(_: u64) -> u64 {
    loop {
        unsafe {
            llvm_asm!("hlt" :::: "volatile");
        }
    }
}
