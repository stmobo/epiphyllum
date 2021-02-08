use alloc_crate::boxed::Box;
use alloc_crate::sync::Arc;
use core::cell::UnsafeCell;
use core::mem;
use core::ops::Deref;
use core::ptr;
use core::ptr::NonNull;
use core::sync::atomic::{AtomicBool, AtomicPtr, AtomicU64, Ordering};
use core::task::Waker;

use super::async_task;
use super::scheduling;
use super::scheduling::SchedulerData;
use crate::lock::{LockedGlobal, NoIRQSpinlock, NoIRQSpinlockGuard, OnceCell};
use crate::malloc::{virtual_mem, AllocationError, PhysicalMemory, VirtualMemory};
use crate::paging;
use crate::paging::AddressSpace;
use crate::structures::{AVLTree, Queue, Sender};

use crossbeam::atomic::AtomicCell;

const TASK_STACK_ORDER: u64 = 5;
const TASK_STACK_PAGES: usize = (1 << (TASK_STACK_ORDER as usize)) - 2;
const TASK_STACK_SIZE: usize = TASK_STACK_PAGES * 0x1000;

pub static TASKS: LockedGlobal<AVLTree<u64, TaskHandle>> = LockedGlobal::new();
static CUR_PID: AtomicU64 = AtomicU64::new(0);
static REAPER_CH: OnceCell<Sender<TaskHandle>> = OnceCell::new();

extern "C" {
    #[allow(improper_ctypes)]
    fn do_context_switch(
        prev_rsp: *mut *mut TaskSwitchFrame,
        next_rsp: *mut *mut TaskSwitchFrame,
        prev: *const Task,
        next: *const Task,
    ) -> *const Task;

    fn initialize_task();
}

#[derive(Debug, Copy, Clone)]
pub enum TaskSpawnError {
    AllocationError(AllocationError),
    StructureError,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum TaskStatus {
    Waiting,
    Running,
    Dead,
    Sleeping,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum ExitStatus {
    ReturnCode(u64),
}

#[repr(C)]
pub struct TaskSwitchFrame {
    r15: u64,
    r14: u64,
    r13: u64,
    r12: u64,
    rbx: u64,
    rbp: u64,
    rip: u64,
}

impl TaskSwitchFrame {
    fn new(rip: u64) -> TaskSwitchFrame {
        TaskSwitchFrame {
            r15: 0,
            r14: 0,
            r13: 0,
            r12: 0,
            rbx: 0,
            rbp: 0,
            rip,
        }
    }
}

#[derive(Debug)]
#[repr(transparent)]
pub struct TaskHandle {
    inner: NonNull<Task>,
}

impl TaskHandle {
    pub unsafe fn from_ref(task: &Task) -> TaskHandle {
        task.inc_refcount();
        TaskHandle { inner: task.into() }
    }

    pub unsafe fn from_raw(task: *const Task) -> Option<TaskHandle> {
        TaskHandle::from_mut(mem::transmute(task))
    }

    unsafe fn from_mut(task: *mut Task) -> Option<TaskHandle> {
        NonNull::new(task).map(|inner| TaskHandle { inner })
    }

    pub const fn as_raw(self) -> *const Task {
        let ret = self.inner.as_ptr() as *const Task;
        mem::forget(self);
        ret
    }
}

impl Drop for TaskHandle {
    fn drop(&mut self) {
        unsafe {
            let prev_rc = self.inner.as_ref().dec_refcount();
            assert!(prev_rc > 0, "task refcount dropped below 0");

            if prev_rc != 1 {
                return;
            }

            // Do an "acquire" load of refcount for synchronization
            self.inner.as_ref().refcount.load();

            // Actually drop the task
            ptr::drop_in_place(self.inner.as_ptr())
        }
    }
}

impl Clone for TaskHandle {
    fn clone(&self) -> Self {
        unsafe { self.inner.as_ref().inc_refcount() };
        TaskHandle { inner: self.inner }
    }
}

impl Deref for TaskHandle {
    type Target = Task;

    fn deref(&self) -> &Self::Target {
        unsafe { self.inner.as_ref() }
    }
}

impl From<TaskHandle> for *const Task {
    fn from(handle: TaskHandle) -> Self {
        handle.as_raw()
    }
}

// Safe because TaskHandle only allows shared access (&Task), and because refcounts
// are synchronized
unsafe impl Sync for TaskHandle {}
unsafe impl Send for TaskHandle {}

#[derive(Debug, Default)]
#[repr(transparent)]
pub struct AtomicTaskHandle {
    inner: AtomicPtr<Task>,
}

impl AtomicTaskHandle {
    pub fn new(handle: TaskHandle) -> AtomicTaskHandle {
        let p = handle.inner.as_ptr();
        mem::forget(handle);
        AtomicTaskHandle {
            inner: AtomicPtr::new(p),
        }
    }

    pub fn load(&self) -> TaskHandle {
        let p = self.inner.load(Ordering::Acquire);
        unsafe {
            let handle = TaskHandle::from_mut(p).unwrap();
            handle.inc_refcount();
            handle
        }
    }

    pub fn load_ref(&self) -> &Task {
        let p = self.inner.load(Ordering::Acquire);
        unsafe { &*p }
    }

    pub fn swap(&self, handle: TaskHandle) -> TaskHandle {
        let new = handle.inner.as_ptr();
        mem::forget(handle);

        let old = self.inner.swap(new, Ordering::AcqRel);
        NonNull::new(old).map(|inner| TaskHandle { inner }).unwrap()
    }

    pub fn store(&self, handle: TaskHandle) {
        // immediately drop the swapped-out handle
        self.swap(handle);
    }
}

#[derive(Debug)]
#[repr(transparent)]
pub struct SwitchFrameHead {
    inner: UnsafeCell<*mut TaskSwitchFrame>,
}

impl SwitchFrameHead {
    const fn new(addr: *mut TaskSwitchFrame) -> SwitchFrameHead {
        SwitchFrameHead {
            inner: UnsafeCell::new(addr),
        }
    }

    const fn get(&self) -> *mut *mut TaskSwitchFrame {
        self.inner.get()
    }
}

unsafe impl Sync for SwitchFrameHead {}
unsafe impl Send for SwitchFrameHead {}

pub struct Task {
    id: u64,
    kernel_stack_base: usize,
    kernel_stack_head: SwitchFrameHead,
    status: AtomicCell<TaskStatus>,
    wakeup_pending: AtomicBool,
    scheduler_data: SchedulerData,
    exit_status: OnceCell<ExitStatus>,
    exit_callbacks: Queue<Box<dyn FnOnce() + Send + 'static>>,
    address_space: Arc<NoIRQSpinlock<AddressSpace>>,
    refcount: AtomicCell<isize>,
}

impl Task {
    fn new_common(
        entry: usize,
        init_arg: u64,
        address_space: Arc<NoIRQSpinlock<AddressSpace>>,
    ) -> Result<TaskHandle, TaskSpawnError> {
        let stack_end = Self::allocate_stack_pages().map_err(TaskSpawnError::AllocationError)?;

        // Stacks grow downwards on x86-64:
        let kernel_stack_base = stack_end + TASK_STACK_SIZE;
        let head_addr = kernel_stack_base - mem::size_of::<TaskSwitchFrame>();
        let task_ptr = stack_end as *mut Task;
        let kernel_stack_head = head_addr as *mut TaskSwitchFrame;
        let id = CUR_PID.fetch_add(1, Ordering::SeqCst);
        let start_addr = task_entry as usize;

        println!("task[{}], stack base = {:#018x}", id, kernel_stack_base);
        println!("task[{}], task ptr = {:#018x}", id, task_ptr as usize);

        let task: TaskHandle = unsafe {
            ptr::write(
                kernel_stack_head,
                TaskSwitchFrame {
                    rbp: kernel_stack_base as u64,
                    rbx: (task_ptr as usize) as u64,
                    r12: entry as u64,
                    r13: init_arg,
                    r14: 0,
                    r15: start_addr as u64,
                    rip: (initialize_task as usize) as u64,
                },
            );
            ptr::write(
                task_ptr,
                Task {
                    id,
                    kernel_stack_base,
                    kernel_stack_head: SwitchFrameHead::new(kernel_stack_head),
                    status: AtomicCell::new(TaskStatus::Sleeping),
                    wakeup_pending: AtomicBool::new(false),
                    scheduler_data: SchedulerData::new(),
                    exit_status: OnceCell::new(),
                    exit_callbacks: Queue::new_direct(),
                    address_space,
                    refcount: AtomicCell::new(0),
                },
            );

            TaskHandle::from_ref(&*task_ptr)
        };

        TASKS
            .lock()
            .insert(id, task.clone())
            .map_err(|_| TaskSpawnError::StructureError)?;
        Ok(task)
    }

    pub fn new(
        entry: fn(u64) -> u64,
        init_arg: u64,
        shared_address_space: bool,
    ) -> Result<TaskHandle, TaskSpawnError> {
        let address_space: Arc<NoIRQSpinlock<AddressSpace>>;
        if shared_address_space {
            address_space = super::cur_address_space_handle();
        } else {
            let space = AddressSpace::new().map_err(TaskSpawnError::AllocationError)?;
            address_space = Arc::new(NoIRQSpinlock::new(space));
        }

        Self::new_common(entry as usize, init_arg, address_space)
    }

    pub fn from_closure<T: FnOnce() -> u64 + Send + 'static>(
        shared_address_space: bool,
        entry: T,
    ) -> Result<TaskHandle, TaskSpawnError> {
        let address_space: Arc<NoIRQSpinlock<AddressSpace>>;
        if shared_address_space {
            address_space = super::cur_address_space_handle();
        } else {
            let space = AddressSpace::new().map_err(TaskSpawnError::AllocationError)?;
            address_space = Arc::new(NoIRQSpinlock::new(space));
        }

        let p = (Box::into_raw(Box::new(entry)) as usize) as u64;
        match Self::new_common(boxed_func_task::<T> as usize, p, address_space) {
            Ok(h) => Ok(h),
            Err(e) => {
                let p = (p as usize) as *mut T;
                drop(unsafe { Box::from_raw(p) });
                Err(e)
            }
        }
    }

    pub unsafe fn new_raw(
        entry: usize,
        init_arg: u64,
        address_space: Arc<NoIRQSpinlock<AddressSpace>>,
    ) -> Result<TaskHandle, TaskSpawnError> {
        Self::new_common(entry, init_arg, address_space)
    }

    fn allocate_stack_pages() -> Result<usize, AllocationError> {
        // Allocate one page on both sides of the task stack.
        let virt_sz = TASK_STACK_SIZE + 0x2000;

        let pmem = PhysicalMemory::new(TASK_STACK_ORDER)?;
        let vmem = VirtualMemory::new(virt_sz)?;
        let mut vspace = unsafe { paging::AddressSpace::current() };

        vspace.unmap_page_range(vmem.address(), TASK_STACK_PAGES + 2);
        vspace.map_page_range(vmem.address() + 0x1000, pmem.address(), TASK_STACK_PAGES);

        Ok(vmem.into_address() + 0x1000)
    }

    pub fn get_current_task() -> Option<&'static Task> {
        unsafe {
            let mut rsp: usize;
            llvm_asm!("mov %rsp, $0" : "=r"(rsp));

            if rsp >= paging::KERNEL_HEAP_BASE && rsp <= paging::KERNEL_BASE {
                rsp = (rsp & !(TASK_STACK_SIZE + 0x2000 - 1)) + 0x1000;
                Some(&*(rsp as *const Task))
            } else {
                None
            }
        }
    }

    pub fn in_stack_bounds(&self, addr: usize) -> bool {
        let base_addr = (self as *const Task) as usize;
        let stack_end = base_addr + mem::size_of::<Task>();
        let stack_start = base_addr + TASK_STACK_SIZE;

        return (addr >= stack_end) && (addr < stack_start);
    }

    pub unsafe fn inc_refcount(&self) -> isize {
        self.refcount.fetch_add(1)
    }

    pub unsafe fn dec_refcount(&self) -> isize {
        self.refcount.fetch_sub(1)
    }

    /// Perform a context switch from this task to another task.
    ///
    /// This function will then return once another task has context-switched
    /// back to this task, returning a handle to that task.
    ///
    /// ## Safety
    /// This function must be called from the kernel stack associated with this Task.
    /// Passing self == next will also result in UB.
    pub unsafe fn switch_context(&self, next: &Task) -> Option<TaskHandle> {
        let prev_rsp = self.kernel_stack_head.get();
        let next_rsp = (*next).kernel_stack_head.get();
        let handle = TaskHandle::from_raw(do_context_switch(
            prev_rsp,
            next_rsp,
            self as *const Task,
            next as *const Task,
        ))
        .expect("do_context_switch returned a null Task pointer?");

        handle.inc_refcount();
        Some(handle)
    }

    pub fn new_handle(&self) -> TaskHandle {
        unsafe { TaskHandle::from_ref(self) }
    }

    pub unsafe fn load_address_space(&self) {
        self.address_space.lock().load();
    }

    pub fn address_space(&self) -> NoIRQSpinlockGuard<'_, AddressSpace> {
        self.address_space.lock()
    }

    pub fn clone_address_space(&self) -> Arc<NoIRQSpinlock<AddressSpace>> {
        self.address_space.clone()
    }

    pub fn id(&self) -> u64 {
        self.id
    }

    pub fn status(&self) -> TaskStatus {
        self.status.load()
    }

    pub fn set_status(&self, status: TaskStatus) {
        self.status.store(status)
    }

    pub fn wakeup_pending(&self) -> bool {
        self.wakeup_pending.load(Ordering::SeqCst)
    }

    pub fn set_wakeup_pending(&self, val: bool) {
        self.wakeup_pending.store(val, Ordering::SeqCst);
    }

    pub fn schedule(&self) {
        self.set_wakeup_pending(true);

        let status = self.status();
        if status == TaskStatus::Waiting || status == TaskStatus::Running {
            // we're already scheduled to run
            return;
        }

        scheduling::scheduler().schedule(&self);
    }

    pub fn should_run(&self) -> bool {
        if self.status() == TaskStatus::Dead {
            return false;
        }

        self.status() == TaskStatus::Running || self.wakeup_pending()
    }

    pub fn scheduler_data(&self) -> &SchedulerData {
        &self.scheduler_data
    }

    /// Mark this task as dead.
    /// If this task is already dead, returns an error containing its ExitStatus.
    pub fn kill(&self, status: ExitStatus) -> Result<(), ExitStatus> {
        if self.exit_status.set(status).is_err() {
            return Err(self.exit_status().unwrap());
        }

        self.set_status(TaskStatus::Dead);

        /*
        TASKS
            .lock()
            .remove(&self.id())
            .expect("task not found in tasks list");
        */

        unsafe {
            // this is safe since this is the only place we ever read from the
            // queue, and we will never be here twice to begin with.
            // (we will return beforehand if we try)
            for callback in self.exit_callbacks.try_iter() {
                callback();
            }
        }

        // if this task was scheduled, it'll be removed from the runqueue since
        // it's marked as dead.
        Ok(())
    }

    pub fn exit_status(&self) -> Option<ExitStatus> {
        self.exit_status.get().copied()
    }

    pub fn register_exit_callback<F: FnOnce() + Send + 'static>(&self, callback: F) {
        self.exit_callbacks.push(Box::new(callback));
    }

    pub fn waker(&self) -> Waker {
        async_task::make_task_waker(self.new_handle())
    }

    pub fn exit_future(&self) -> async_task::TaskExitFuture {
        async_task::TaskExitFuture::new(self.new_handle())
    }
}

impl Drop for Task {
    fn drop(&mut self) {
        direct_println!("dropping task {}", self.id());

        assert_eq!(
            self.refcount.load(),
            0,
            "attempted to drop task with nonzero refcount"
        );

        if super::current_task().id() == self.id() {
            panic!("attempted to drop running task ({})", self.id());
        }

        unsafe {
            let vaddr = self.kernel_stack_base - TASK_STACK_SIZE;
            let mut vspace = paging::AddressSpace::current();
            vspace.unmap_page_range(vaddr, TASK_STACK_PAGES);
            virtual_mem::deallocate(vaddr - 0x1000, TASK_STACK_SIZE + 0x2000);
        }
    }
}

impl PartialEq for Task {
    fn eq(&self, other: &Task) -> bool {
        self.id == other.id
    }
}

impl Eq for Task {}

pub fn initialize() {
    TASKS.init(AVLTree::new);
}

#[allow(unused_must_use)]
fn task_entry(handle: *const Task, entrypoint: fn(u64) -> u64, init_arg: u64) {
    let handle = unsafe {
        (*handle).inc_refcount();
        TaskHandle::from_raw(handle).unwrap()
    };
    let retcode = entrypoint(init_arg);

    handle.kill(ExitStatus::ReturnCode(retcode));
    loop {
        scheduling::yield_cpu();
    }
}

fn boxed_func_task<T: FnOnce() -> u64 + Send + 'static>(ctx: *mut T) -> u64 {
    let boxed = unsafe { Box::from_raw(ctx) };
    (*boxed)()
}

pub unsafe fn start_initial_task(task: &Task) -> ! {
    let mut prev_rsp: *mut TaskSwitchFrame = ptr::null_mut();
    let next_rsp = (*task).kernel_stack_head.get();
    do_context_switch(
        &mut prev_rsp,
        next_rsp,
        ptr::null_mut(),
        task as *const Task,
    );
    panic!("start_initial_task returned");
}

#[no_mangle]
extern "C" fn finalize_context_switch(prev: *const Task, next: *const Task) -> *const Task {
    unsafe {
        let next = &*next;
        next.scheduler_data().start_running();
        next.load_address_space();
        next.set_status(TaskStatus::Running);
    }

    prev
}
