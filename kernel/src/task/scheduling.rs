use alloc_crate::sync::Arc;
use core::mem;
use core::sync::atomic::{AtomicPtr, Ordering};

use super::structs::{Task, TaskHandle, TaskStatus};
use crate::asm::interrupts;
use crate::interrupts::InterruptFrame;
use crate::lock::{NoIRQSpinlock, NoIRQSpinlockGuard, OnceCell};
use crate::paging::AddressSpace;
use crate::structures::{Queue, QueueReader, QueueWriter};
use crate::timer::get_kernel_ticks;

use crossbeam::atomic::AtomicCell;

static SCHEDULER: OnceCell<Scheduler> = OnceCell::new();
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

pub struct Scheduler {
    run_queue_writer: QueueWriter<TaskHandle>,
    run_queue_reader: NoIRQSpinlock<QueueReader<TaskHandle>>,
    default_task: TaskHandle,
    running_task: AtomicPtr<Task>, // this is actually an Arc<Task>
}

impl Scheduler {
    fn new() -> Scheduler {
        let default_task = Task::new(idle_task, 0, false).expect("could not create idle task");
        let p = Arc::into_raw(default_task.clone());
        let running_task = AtomicPtr::new(p as *mut Task);
        let (reader, writer) = Queue::new();
        default_task.set_status(TaskStatus::Waiting);

        Scheduler {
            default_task,
            running_task,
            run_queue_reader: NoIRQSpinlock::new(reader),
            run_queue_writer: writer,
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

    /// Perform an immediate context switch to the current task's stored context.
    ///
    /// ## Safety
    /// The caller must ensure that the current task to run actually has a
    /// valid context to switch to, otherwise _very_ undefined behavior will
    /// happen.
    pub unsafe fn force_context_switch(&self) -> ! {
        (*self.running_task_ptr()).load_address_space();
        let ctx = self.cur_context();
        switch_context(ctx)
    }

    fn cas_running_task(&self, cur: *const Task, new: *const Task) -> bool {
        self.running_task
            .compare_and_swap(cur as *mut Task, new as *mut Task, Ordering::SeqCst)
            == cur as *mut Task
    }

    /// Wake up a Task, and schedule it for execution.
    /// Can be called from both regular and IRQ contexts.
    pub fn schedule(&self, task: &TaskHandle) {
        let task_ptr = Arc::into_raw(task.clone());

        loop {
            let cur_task = self.running_task_ptr();

            if self.default_task.as_ref().eq(unsafe { &*cur_task }) {
                // we're idle right now, go ahead and schedule this task immediately
                if self.cas_running_task(cur_task, task_ptr) {
                    unsafe {
                        (*task_ptr).set_task_running();
                        Arc::from_raw(cur_task);
                        return;
                    }
                } else {
                    continue;
                }
            } else {
                // something else is running, add this task to the run queue
                let handle = unsafe { Arc::from_raw(task_ptr) };
                task.set_status(TaskStatus::Waiting);
                self.run_queue_writer.push(handle);
                return;
            }
        }
    }

    /// Run a scheduler update, swapping out the current Task for other tasks
    /// that are scheduled to run if necessary.
    pub fn update(&self) {
        let queue_lock = self.run_queue_reader.lock();
        let cur_task = unsafe { &*self.running_task_ptr() };
        let mut should_switch = false;

        // Check to see if we need to switch to a new task:
        if !cur_task.eq(&self.default_task) {
            if cur_task.status() != TaskStatus::Running {
                should_switch = true;
            } else {
                let elapsed = cur_task
                    .scheduler_data()
                    .cur_exec_time()
                    .expect("invalid timeslice start time for running task");
                should_switch = elapsed >= TIMESLICE_TICKS;
            }
        } // if we're idle, we rely on schedule() to break us out

        if should_switch {
            for handle in queue_lock.try_iter() {
                if handle.status() != TaskStatus::Waiting {
                    continue;
                }

                drop(cur_task);

                // set this task as running
                handle.set_task_running();
                let prev_task = unsafe {
                    Arc::from_raw(
                        self.running_task
                            .swap(Arc::into_raw(handle) as *mut Task, Ordering::Relaxed),
                    )
                };

                if prev_task.should_run() {
                    // prev_task is still runnable
                    prev_task.set_status(TaskStatus::Waiting);
                    prev_task.set_wakeup_pending(false);
                    if !prev_task.eq(&self.default_task) {
                        self.run_queue_writer.push(prev_task);
                    }
                } // else prev_task is now blocked or dead

                return;
            }

            // no other tasks are runnable
            if cur_task.should_run() {
                // set up this task for another timeslice
                cur_task.set_task_running();
            } else {
                // set the idle task to run
                self.default_task.set_task_running();
                unsafe {
                    drop(Arc::from_raw(self.running_task.swap(
                        Arc::into_raw(self.default_task.clone()) as *mut Task,
                        Ordering::SeqCst,
                    )));
                }
            }
        }
    }
}

unsafe impl Sync for Scheduler {}

pub fn initialize() {
    if SCHEDULER.set(Scheduler::new()).is_err() {
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
        let task = sched.running_task_ptr();
        (*task).load_address_space();
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
