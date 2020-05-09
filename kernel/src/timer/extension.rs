use alloc_crate::boxed::Box;
use alloc_crate::sync::{Arc, Weak};

use super::wheel::{TimerData, TimerHandle};
use crate::lock::NoIRQSpinlock;
use core::mem;

type CallbackBox = Box<dyn Fn() + Sync + Send + 'static>;

pub enum TimerError {
    InvalidDeadline(u64),
    IncorrectState,
}

pub enum TimerState {
    Stopped(TimerData),
    Started(TimerHandle),
    Complete,
}

pub struct Timer {
    event_count: u64,
    state: TimerState,
    self_ref: Weak<NoIRQSpinlock<Timer>>,
    callback: Option<CallbackBox>,
}

impl Timer {
    fn callback_wrapper(lock: &Arc<NoIRQSpinlock<Timer>>) {
        let mut timer = lock.lock();

        timer.event_count += 1;
        timer.state = TimerState::Complete;
        if let Some(callback) = &timer.callback {
            callback();
        }
    }

    fn new_internal(callback: Option<CallbackBox>, deadline: u64) -> Arc<NoIRQSpinlock<Timer>> {
        let timer = NoIRQSpinlock::new(Timer {
            event_count: 0,
            state: TimerState::Complete,
            callback,
            self_ref: Weak::new(),
        });

        let timer = Arc::new(timer);
        let cb_timer = timer.clone();
        let cb_wrapper = move || {
            Timer::callback_wrapper(&cb_timer);
        };

        let mut d = timer.lock();
        d.state = TimerState::Stopped(TimerData::new(cb_wrapper, deadline));
        d.self_ref = Arc::downgrade(&timer);
        drop(d);

        timer
    }

    pub fn new_empty(deadline: u64) -> Arc<NoIRQSpinlock<Timer>> {
        Timer::new_internal(None, deadline)
    }

    pub fn new<F>(callback: F, deadline: u64) -> Arc<NoIRQSpinlock<Timer>>
    where
        F: Fn() + Sync + Send + 'static,
    {
        Timer::new_internal(Some(Box::new(callback)), deadline)
    }

    pub fn restart(&mut self, deadline: u64) -> Result<(), TimerError> {
        if !self.is_complete() {
            return Err(TimerError::IncorrectState);
        }

        let cb_timer = self.self_ref.upgrade().unwrap();
        let cb_wrapper = move || {
            Timer::callback_wrapper(&cb_timer);
        };

        self.state = TimerState::Stopped(TimerData::new(cb_wrapper, deadline));
        Ok(())
    }

    pub fn is_running(&self) -> bool {
        match &self.state {
            TimerState::Started(_) => true,
            _ => false,
        }
    }

    pub fn is_stopped_state(&self) -> bool {
        match &self.state {
            TimerState::Stopped(_) => true,
            _ => false,
        }
    }

    pub fn is_complete(&self) -> bool {
        match &self.state {
            TimerState::Complete => true,
            _ => false,
        }
    }

    pub fn start(&mut self) -> Result<&TimerHandle, TimerError> {
        if !self.is_stopped_state() {
            return Err(TimerError::IncorrectState);
        }

        let mut t = TimerState::Complete;
        mem::swap(&mut t, &mut self.state);

        if let TimerState::Stopped(data) = t {
            let handle = data.start().map_err(|x| TimerError::InvalidDeadline(x))?;
            self.state = TimerState::Started(handle);
            match &self.state {
                TimerState::Started(r) => Ok(r),
                _ => unreachable!(),
            }
        } else {
            unreachable!();
        }
    }

    pub fn stop(&mut self) -> Result<(), TimerError> {
        if let TimerState::Started(handle) = &self.state {
            let data = handle.stop().map_err(|_| TimerError::IncorrectState)?;
            self.state = TimerState::Stopped(data);
            Ok(())
        } else {
            Err(TimerError::IncorrectState)
        }
    }

    pub fn set_deadline(&mut self, deadline: u64) -> Result<(), TimerError> {
        match &mut self.state {
            TimerState::Stopped(data) => {
                data.deadline = deadline;
                Ok(())
            }
            TimerState::Complete => self.restart(deadline),
            _ => Err(TimerError::IncorrectState),
        }
    }

    pub fn deadline(&self) -> Result<u64, TimerError> {
        match &self.state {
            TimerState::Complete => Err(TimerError::IncorrectState),
            TimerState::Started(h) => Ok(h.deadline()),
            TimerState::Stopped(d) => Ok(d.deadline),
        }
    }

    pub fn set_callback<F>(&mut self, callback: F) -> Result<Option<CallbackBox>, TimerError>
    where
        F: Fn() + Sync + Send + 'static,
    {
        if self.is_stopped_state() {
            Ok(self.callback.replace(Box::new(callback)))
        } else {
            Err(TimerError::IncorrectState)
        }
    }

    pub fn clear_callback(&mut self) -> Result<Option<CallbackBox>, TimerError> {
        if self.is_stopped_state() {
            Ok(self.callback.take())
        } else {
            Err(TimerError::IncorrectState)
        }
    }
}
