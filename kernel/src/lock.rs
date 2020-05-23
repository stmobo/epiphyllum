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

/// A Cell-like container that can only be filled once.
/// Meant to be identical to the once_cell crate, but based on `spin` instead.
#[derive(Debug)]
#[repr(transparent)]
pub struct OnceCell<T> {
    data: Once<T>,
}

impl<T> OnceCell<T> {
    pub const fn new() -> OnceCell<T> {
        OnceCell { data: Once::new() }
    }

    pub fn get(&self) -> Option<&T> {
        self.data.r#try()
    }

    pub fn wait(&self) -> Option<&T> {
        self.data.wait()
    }

    pub fn set(&self, value: T) -> Result<(), T> {
        let mut v = Some(value);
        self.data.call_once(|| v.take().unwrap());
        match v {
            Some(x) => Err(x),
            None => Ok(()),
        }
    }
}

impl<T> Default for OnceCell<T> {
    fn default() -> Self {
        OnceCell::new()
    }
}

impl<T: PartialEq> PartialEq for OnceCell<T> {
    fn eq(&self, other: &OnceCell<T>) -> bool {
        self.get() == other.get()
    }
}

impl<T: Eq> Eq for OnceCell<T> {}

impl<T: PartialEq> PartialEq<T> for OnceCell<T> {
    fn eq(&self, other: &T) -> bool {
        self.get().map_or(false, |r| r.eq(other))
    }
}

impl<T> From<T> for OnceCell<T> {
    fn from(v: T) -> OnceCell<T> {
        let cell = OnceCell::new();
        if cell.set(v).is_err() {
            panic!("could not set newly-initialized OnceCell");
        }

        cell
    }
}

impl<T: Clone> Clone for OnceCell<T> {
    fn clone(&self) -> OnceCell<T> {
        if let Some(v) = self.get() {
            v.clone().into()
        } else {
            OnceCell::new()
        }
    }
}
