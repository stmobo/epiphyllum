use alloc_crate::collections::VecDeque;

use super::structs::{Task, TaskHandle, TaskStatus};
use crate::asm::interrupts;
use crate::interrupts::InterruptFrame;
use crate::lock::{LockedGlobal, NoIRQSpinlock};
use crate::timer::get_kernel_ticks;

use crossbeam::atomic::AtomicCell;
use spin::Once;

static RUN_QUEUE: LockedGlobal<VecDeque<TaskHandle>> = LockedGlobal::new();
static RUNNING_TASK: NoIRQSpinlock<Option<TaskHandle>> = NoIRQSpinlock::new(None);
static DEFAULT_TASK: Once<TaskHandle> = Once::new();
const TIMESLICE_TICKS: u64 = 41; // corresponds to roughly 5 ms

extern "C" {
    fn switch_context(frame: *mut InterruptFrame) -> !;
    fn yield_cpu_1();
}

#[derive(Debug)]
pub struct SchedulerData {
    slice_start: AtomicCell<u64>,
}

impl SchedulerData {
    pub fn new() -> SchedulerData {
        SchedulerData {
            slice_start: AtomicCell::new(get_kernel_ticks()),
        }
    }

    pub fn start_timeslice(&self) {
        self.slice_start.store(get_kernel_ticks());
    }

    pub fn cur_exec_time(&self) -> Option<u64> {
        get_kernel_ticks().checked_sub(self.slice_start.load())
    }
}

pub fn initialize() {
    let default_task = Task::new(idle_task, 0).expect("could not create idle task");
    default_task.set_status(TaskStatus::Waiting);
    RUNNING_TASK.lock().replace(default_task.clone());

    RUN_QUEUE.init(|| VecDeque::new());
    DEFAULT_TASK.call_once(move || default_task);
}

pub fn get_running_task() -> TaskHandle {
    RUNNING_TASK.lock().clone().expect("no running task")
}

pub fn update_task_context(new_ctx: *mut InterruptFrame) {
    let lock = RUNNING_TASK.lock();
    if let Some(handle) = lock.as_ref() {
        handle.set_context(new_ctx);
    }
}

pub fn current_context() -> Option<*mut InterruptFrame> {
    RUNNING_TASK.lock().as_ref().map(|t| t.get_context())
}

pub unsafe fn switch_to_task() -> ! {
    let next = current_context().expect("no running task");
    switch_context(next);
}

pub fn set_running_task(task: TaskHandle) -> TaskHandle {
    task.set_task_running();
    RUNNING_TASK.lock().replace(task).expect("no running task")
}

pub fn schedule_task(task: TaskHandle) {
    let default_task = DEFAULT_TASK.wait().expect("default task not initialized");
    let mut task_lock = RUNNING_TASK.lock();

    if task_lock
        .as_ref()
        .expect("no running task")
        .eq(default_task)
    {
        // we're idle right now, go ahead and schedule this task immediately
        task.set_task_running();
        task_lock.replace(task);
    } else {
        // something else is running, add this task to the run queue
        drop(task_lock);
        task.set_status(TaskStatus::Waiting);
        RUN_QUEUE.lock().push_back(task);
    }
}

pub fn update() {
    let default_task = DEFAULT_TASK.wait().expect("default task not initialized");
    let mut task_lock = RUNNING_TASK.lock();
    let cur_task = task_lock.as_ref().expect("no running task");

    let mut should_switch = false;

    // Check to see if we need to switch to a new task:
    if !cur_task.eq(default_task) {
        if cur_task.status() != TaskStatus::Running {
            should_switch = true;
        } else {
            let elapsed = cur_task
                .scheduler_data()
                .cur_exec_time()
                .expect("invalid timeslice start time for running task");
            should_switch = elapsed >= TIMESLICE_TICKS;
        }
    } // if we're idle, we rely on schedule_task() to break us out

    if should_switch {
        let mut queue = RUN_QUEUE.lock();

        // look for a runnable task
        while queue.len() > 0 {
            let next_task = queue.pop_front().unwrap();
            if next_task.status() != TaskStatus::Waiting {
                continue;
            }

            drop(cur_task);

            // set this task as running
            next_task.set_task_running();
            let prev_task = task_lock.replace(next_task).expect("no previous task?");
            let prev_status = prev_task.status();

            if prev_status == TaskStatus::Running {
                // prev_task is still runnable
                prev_task.set_status(TaskStatus::Waiting);
                if !prev_task.eq(default_task) {
                    queue.push_back(prev_task);
                }
            } // else prev_task is now blocked or dead

            return;
        }

        let cur_task = task_lock.as_ref().expect("no running task");

        // no other tasks are runnable
        if cur_task.status() == TaskStatus::Running {
            // set up this task for another timeslice
            cur_task.set_task_running();
        } else {
            // set the idle task to run
            default_task.set_task_running();
            task_lock.replace(default_task.clone());
        }
    }
}

/// Put the currently-running Task to sleep until awoken by another Task.
pub fn yield_cpu() {
    unsafe {
        yield_cpu_1();
    }
}

#[no_mangle]
extern "C" fn yield_cpu_2(return_ctx: *mut InterruptFrame) -> ! {
    // If an interrupt comes in between task.set_context() and switch_to_task(),
    // the context for the current task could end up corrupted.
    // (the interrupt flag will be restored as part of the context)
    unsafe {
        interrupts::set_if(false);
    }

    {
        let lock = RUNNING_TASK.lock();
        let task = lock.as_ref().expect("no running task");

        task.set_status(TaskStatus::Sleeping);
        task.set_context(return_ctx);
    }

    update();
    unsafe {
        switch_to_task();
    }
}

fn idle_task(_: u64) -> u64 {
    loop {
        unsafe {
            llvm_asm!("hlt" :::: "volatile");
        }
    }
}
