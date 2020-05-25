use alloc_crate::sync::Arc;
use core::mem;
use core::ops::Bound;
use core::sync::atomic::{AtomicPtr, AtomicU64, Ordering};

use super::structs::{Task, TaskHandle, TaskStatus};
use crate::asm::interrupts;
use crate::interrupts::InterruptFrame;
use crate::lock::{NoIRQSpinlock, NoIRQSpinlockGuard, OnceCell};
use crate::paging::AddressSpace;
use crate::structures::AVLTree;
use crate::timer::{get_kernel_ticks, TICKS_PER_SECOND};

static SCHEDULER: OnceCell<Scheduler> = OnceCell::new();
const NS_PER_TICK: u64 = 1_000_000_000 / TICKS_PER_SECOND;
const GRANULARITY: u64 = 7; // in ms

extern "C" {
    fn switch_context(frame: *mut InterruptFrame) -> !;
    fn yield_cpu_1();
}

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
    tree: AVLTree<TimelineKey, TaskHandle>,
    min_virt_runtime: u64,
}

impl SchedulerTimeline {
    fn new() -> SchedulerTimeline {
        SchedulerTimeline {
            tree: AVLTree::new(),
            min_virt_runtime: 0,
        }
    }
}

pub struct Scheduler {
    timeline: NoIRQSpinlock<SchedulerTimeline>,
    default_task: TaskHandle,
    running_task: AtomicPtr<Task>, // this is actually an Arc<Task>
}

impl Scheduler {
    fn new(address_space: Arc<NoIRQSpinlock<AddressSpace>>) -> Scheduler {
        let default_task = unsafe {
            Task::new_raw(idle_task as usize, 0, address_space).expect("could not create idle task")
        };

        let p = Arc::into_raw(default_task.clone());
        let running_task = AtomicPtr::new(p as *mut Task);
        default_task.set_status(TaskStatus::Waiting);

        Scheduler {
            default_task,
            running_task,
            timeline: NoIRQSpinlock::new(SchedulerTimeline::new()),
        }
    }

    /// Get a TaskHandle to the currently running Task.
    pub fn running_task_handle(&self) -> TaskHandle {
        let p = self.running_task.load(Ordering::SeqCst);
        let handle = unsafe { Arc::from_raw(p as *const Task) };

        // Make sure the refcount for the handle is properly incremented.
        mem::forget(handle.clone());

        handle
    }

    /// Get a raw pointer to the currently running Task.
    pub fn running_task_ptr(&self) -> *const Task {
        self.running_task.load(Ordering::SeqCst) as *const Task
    }

    /// Get the stored context for the currently running Task.
    pub fn cur_context(&self) -> *mut InterruptFrame {
        unsafe { (*self.running_task_ptr()).get_context() }
    }

    /// Update the stored context for the currently-running Task.
    pub fn update_cur_context(&self, ctx: *mut InterruptFrame) {
        unsafe {
            (*self.running_task_ptr()).set_context(ctx);
        }
    }

    unsafe fn prepare_context_switch(&self) {
        use crate::paging::{KERNEL_BASE, KERNEL_HEAP_BASE};

        let task = self.running_task_ptr();

        let ctx = (*task).get_context();
        assert!(
            (*ctx).rip >= (KERNEL_BASE as u64),
            "attempt to context switch to task {} with invalid address {:#018x}",
            (*task).id(),
            (*ctx).rip
        );

        assert!(
            (*ctx).rsp >= (KERNEL_HEAP_BASE as u64),
            "attempt to context switch to task {} with invalid RSP {:#018x}",
            (*task).id(),
            (*ctx).rsp
        );

        (*task).scheduler_data().start_running();
        (*task).load_address_space();
    }

    /// Perform an immediate context switch to the current task's stored context.
    ///
    /// ## Safety
    /// The caller must ensure that the current task to run actually has a
    /// valid context to switch to, otherwise _very_ undefined behavior will
    /// happen.
    pub unsafe fn force_context_switch(&self) -> ! {
        self.prepare_context_switch();
        let ctx = self.cur_context();
        switch_context(ctx)
    }

    /// Wake up a Task, and schedule it for execution.
    /// Can be called from both regular and IRQ contexts.
    ///
    /// Returns true if the task was successfully added to the runqueue, and
    /// false if the task was already queued.
    pub fn schedule(&self, task: &TaskHandle) -> bool {
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
            if timeline.tree.insert(key.clone(), task.clone()).is_ok() {
                *prev_key = Some(key);
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

    fn swap_task(&self, new_task: &TaskHandle) {
        let new = Arc::into_raw(new_task.clone());
        let prev = unsafe {
            Arc::from_raw(self.running_task.swap(new as *mut Task, Ordering::SeqCst) as *const Task)
        };

        new_task.set_status(TaskStatus::Running);
        if prev.status() == TaskStatus::Running {
            prev.set_status(TaskStatus::Waiting);
        }
    }

    /// Run a scheduler update, swapping out the current Task for other tasks
    /// that are scheduled to run if necessary.
    pub fn update(&self) {
        let mut timeline = self.timeline.lock();
        let n_tasks = (timeline.tree.len() as u64) + 1;

        let cur_task = unsafe { &*self.running_task_ptr() };
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
        let new_key = TimelineKey::new(cur_task);

        if cur_task.should_run() && cur_task.id() != self.default_task.id() {
            if timeline
                .tree
                .insert(new_key.clone(), self.running_task_handle())
                .is_err()
            {
                panic!(
                    "could not re-insert task {} into timeline tree",
                    cur_task.id()
                );
            }

            *timeline_key_lock = Some(new_key.clone());
        }

        if let Some((key, task)) = timeline.tree.lower_bound(Bound::Unbounded) {
            let should_swap =
                (cur_task.id() == self.default_task.id()) || !cur_task.should_run() || {
                    let threshold = (GRANULARITY * 1_000_000) / n_tasks;
                    let diff = new_key.virtual_runtime.saturating_sub(key.virtual_runtime);

                    diff >= threshold
                };

            if should_swap {
                self.swap_task(task);
            }

            timeline.min_virt_runtime = key.virtual_runtime;
        } else {
            // Run the default task
            self.swap_task(&self.default_task);
        }
    }

    /// Forcibly set the current running task.
    pub unsafe fn force_set_running_task(&self, task: TaskHandle) {
        task.set_status(TaskStatus::Running);
        self.schedule(&task);

        let task = Arc::into_raw(task);
        Arc::from_raw(self.running_task.swap(task as *mut Task, Ordering::SeqCst) as *const Task);
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

pub fn current_context() -> Option<*mut InterruptFrame> {
    SCHEDULER.get().map(|s| s.cur_context())
}

pub fn cur_address_space_handle() -> Arc<NoIRQSpinlock<AddressSpace>> {
    unsafe { (*scheduler().running_task_ptr()).clone_address_space() }
}

// probably the wrong lifetime for this, but it's close enough
pub fn current_address_space() -> NoIRQSpinlockGuard<'static, AddressSpace> {
    unsafe { (*scheduler().running_task_ptr()).address_space() }
}

pub unsafe fn prepare_context_switch() {
    if let Some(sched) = SCHEDULER.get() {
        sched.prepare_context_switch();
    }
}

pub fn current_task() -> TaskHandle {
    scheduler().running_task_handle()
}

/// Put the currently-running Task to sleep until awoken by another Task.
pub fn yield_cpu() {
    unsafe {
        yield_cpu_1();
    }
}

#[no_mangle]
extern "C" fn yield_cpu_2(return_ctx: *mut InterruptFrame) {
    let sched = scheduler(); // this is safe to not drop

    {
        unsafe {
            // If an interrupt comes in between task.set_context() and switch_to_task(),
            // the context for the current task could end up corrupted.
            // (the interrupt flag will be restored as part of the context)

            interrupts::set_if(false);

            let task = sched.running_task_ptr();
            if (*task).should_run() {
                // Abort the yield and restore our context from yield_cpu_1.
                (*task).set_status(TaskStatus::Running);
                (*task).set_wakeup_pending(false);
                return;
            }

            (*task).set_context(return_ctx);
            sched.deschedule(&*task);
        }
    }

    sched.update();
    unsafe {
        sched.force_context_switch();
    }
}

fn idle_task(_: u64) -> u64 {
    loop {
        unsafe {
            llvm_asm!("hlt" :::: "volatile");
        }
    }
}
