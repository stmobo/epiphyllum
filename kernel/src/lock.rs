use crate::asm::interrupts;
use core::mem::ManuallyDrop;
use core::ops::{Deref, DerefMut};
use spin::{Mutex, MutexGuard, Once};

/// A spinlock / mutex that also disables interrupts when taken.
#[derive(Debug)]
#[repr(transparent)]
pub struct NoIRQSpinlock<T: ?Sized> {
    lock: Mutex<T>,
}

impl<T> NoIRQSpinlock<T> {
    pub const fn new(data: T) -> NoIRQSpinlock<T> {
        NoIRQSpinlock {
            lock: Mutex::new(data),
        }
    }

    pub fn into_inner(self) -> T {
        self.lock.into_inner()
    }
}

impl<T: ?Sized> NoIRQSpinlock<T> {
    pub fn lock(&self) -> NoIRQSpinlockGuard<'_, T> {
        let interrupt_flag = interrupts::enabled();
        unsafe {
            interrupts::set_if(false);
        }

        let guard = self.lock.lock();
        NoIRQSpinlockGuard::new(guard, interrupt_flag)
    }

    pub fn try_lock(&self) -> Option<NoIRQSpinlockGuard<'_, T>> {
        let interrupt_flag = interrupts::enabled();
        unsafe {
            interrupts::set_if(false);
        }

        if let Some(guard) = self.lock.try_lock() {
            Some(NoIRQSpinlockGuard::new(guard, interrupt_flag))
        } else {
            unsafe {
                interrupts::set_if(interrupt_flag);
            }

            None
        }
    }

    pub unsafe fn force_unlock(&self) {
        self.lock.force_unlock();
    }
}

#[derive(Debug)]
pub struct NoIRQSpinlockGuard<'a, T: ?Sized> {
    guard: ManuallyDrop<MutexGuard<'a, T>>,
    interrupt_flag: bool,
}

impl<'a, T: ?Sized> NoIRQSpinlockGuard<'a, T> {
    fn new(guard: MutexGuard<'a, T>, iflag: bool) -> NoIRQSpinlockGuard<'a, T> {
        NoIRQSpinlockGuard {
            guard: ManuallyDrop::new(guard),
            interrupt_flag: iflag,
        }
    }
}

impl<'a, T: ?Sized> Drop for NoIRQSpinlockGuard<'a, T> {
    fn drop(&mut self) {
        unsafe {
            ManuallyDrop::drop(&mut self.guard);
            interrupts::set_if(self.interrupt_flag);
        }
    }
}

impl<'a, T: ?Sized> Deref for NoIRQSpinlockGuard<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        (*self.guard).deref()
    }
}

impl<'a, T: ?Sized> DerefMut for NoIRQSpinlockGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        (*self.guard).deref_mut()
    }
}

/// A wrapper around the common Once<NoIRQSpinlock<T>> pattern.
#[derive(Debug)]
#[repr(transparent)]
pub struct LockedGlobal<T> {
    data: Once<NoIRQSpinlock<T>>,
}

impl<T> LockedGlobal<T> {
    pub const fn new() -> LockedGlobal<T> {
        LockedGlobal { data: Once::new() }
    }

    pub fn init<'a, F>(&'a self, init: F) -> &'a NoIRQSpinlock<T>
    where
        F: FnOnce() -> T,
    {
        self.data.call_once(|| NoIRQSpinlock::new(init()))
    }

    pub fn is_initialized(&self) -> bool {
        self.data.wait().is_some()
    }

    fn get(&self) -> &NoIRQSpinlock<T> {
        // panic if data is not initialized yet
        if let Some(lock) = self.data.wait() {
            lock
        } else {
            panic!("attempted to access global before initialization");
        }
    }

    pub fn lock(&self) -> NoIRQSpinlockGuard<'_, T> {
        self.get().lock()
    }

    pub fn try_lock(&self) -> Option<NoIRQSpinlockGuard<'_, T>> {
        self.get().try_lock()
    }

    pub unsafe fn force_unlock(&self) {
        self.get().force_unlock()
    }
}
