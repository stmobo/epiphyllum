//! Intel PIT support.

use super::pic::local_apic;
use super::pic::local_apic::LocalAPIC;
use crate::asm::ports;
use crate::interrupts;
use crate::interrupts::InterruptHandlerStatus;
use crate::lock::NoIRQSpinlock;
use crate::timer::{update_timers, TICKS_PER_SECOND};

use alloc_crate::sync::Arc;
use core::sync::atomic::{spin_loop_hint, AtomicU64, Ordering};

const CH0_ADDR: u16 = 0x40;
const COMMAND_ADDR: u16 = 0x43;

const LAPIC_TIMER_DIVISOR: u8 = 8;
const CALIBRATION_TRIALS: i64 = 512;

#[derive(Debug)]
struct CalibrationData {
    cur_avg: i64,
    cur_trial: i64,
    apic_timer_active: bool,
    lapic_isr_id: u64,
    pit_isr_id: u64,
}

impl CalibrationData {
    fn handle_pit_event(&mut self) {
        if self.done() {
            return;
        }
        let lapic = LocalAPIC::new();

        if self.apic_timer_active {
            lapic.disable_timer();
            let ticks = lapic.get_timer_ticks() as i64;

            if ticks > 500 {
                /* We should have valid data for this trial. */
                let elapsed = 0xFFFF_FFFF - ticks;

                let avg_term = (elapsed - self.cur_avg) / (self.cur_trial + 1);
                self.cur_avg += avg_term;
                self.cur_trial += 1;

                if self.done() {
                    /* All trials completed.
                     * Disable the PIT and the LAPIC timers:
                     */
                    unsafe {
                        ports::outb(COMMAND_ADDR, 0b00_11_000_0);
                    }
                    return;
                }
            }
        }

        /* The LAPIC timer needs to be (re)started for another trial. */
        lapic
            .configure_timer(local_apic::TimerMode::OneShot, LAPIC_TIMER_DIVISOR, 0x30)
            .unwrap();
        lapic.set_timer_ticks(0xFFFF_FFFF);
        self.apic_timer_active = true;
    }

    fn pit_isr(isr_data: &Arc<NoIRQSpinlock<CalibrationData>>) -> InterruptHandlerStatus {
        let mut d = isr_data.lock();
        d.handle_pit_event();

        InterruptHandlerStatus::Handled
    }

    fn new() -> Arc<NoIRQSpinlock<CalibrationData>> {
        /* Set up the LAPIC timer ISR first since it doesn't depend on
         * anything else.
         */
        let lapic_isr_id = interrupts::register_handler(0x30, || -> InterruptHandlerStatus {
            InterruptHandlerStatus::Handled
        })
        .expect("could not register LAPIC timer interrupt handler");

        let d = CalibrationData {
            cur_avg: 0,
            cur_trial: 0,
            apic_timer_active: false,
            lapic_isr_id,
            pit_isr_id: 0,
        };

        let isr_data = Arc::new(NoIRQSpinlock::new(d));
        let ret = isr_data.clone();
        let isr = move || -> InterruptHandlerStatus { CalibrationData::pit_isr(&isr_data) };

        let lapic = LocalAPIC::new();
        lapic
            .configure_timer(local_apic::TimerMode::OneShot, LAPIC_TIMER_DIVISOR, 0x30)
            .unwrap();

        let mut d = ret.lock();
        d.pit_isr_id = interrupts::register_handler(0x20, isr)
            .expect("could not register PIT interrupt handler");
        drop(d);

        /* Set up the PIT timer in mode 2 (rate generator). */
        unsafe {
            let count = (1193182 / TICKS_PER_SECOND) as u16;
            println!("timer: PIT divisor = {}", count);

            ports::outb(COMMAND_ADDR, 0b00_11_010_0);
            ports::outb(CH0_ADDR, (count & 0xFF) as u8);
            ports::outb(CH0_ADDR, ((count >> 8) & 0xFF) as u8);
        }

        ret
    }

    fn done(&self) -> bool {
        self.cur_trial >= CALIBRATION_TRIALS
    }

    fn average(&self) -> i64 {
        self.cur_avg
    }

    /*
     * This is necessary because the ISR registered in new() hangs on to an
     * Arc pointing to the calibration data.
     * We need to unregister the ISRs in order to get them to drop their refs.
     */
    fn unregister_handlers(&self) {
        interrupts::unregister_handler(0x20, self.pit_isr_id);
        interrupts::unregister_handler(0x30, self.lapic_isr_id);
    }
}

/* Number of APIC timer ticks per kernel tick. */
static APIC_RATE_CONSTANT: AtomicU64 = AtomicU64::new(0);

pub fn get_apic_rate_constant() -> u64 {
    APIC_RATE_CONSTANT.load(Ordering::Relaxed)
}

pub fn max_timer_deadline() -> u64 {
    0xFFFF_FFFFu64 / get_apic_rate_constant()
}

pub fn calibrate_apic_timer() {
    println!("timer: calibrating APIC timer against PIT...");
    let calibrator = CalibrationData::new();

    loop {
        // loop some number of times
        let mut i = 0;
        while i < 1000 {
            i += 1;
            spin_loop_hint();
        }

        // check the calibrator:
        {
            let d = calibrator.lock();
            if d.done() {
                break;
            }
        }
    }

    let data = calibrator.lock();
    data.unregister_handlers();
    let avg = data.average() as u64;
    APIC_RATE_CONSTANT.store(avg, Ordering::SeqCst);

    println!(
        "timer: APIC timer constant is {} ticks per kernel tick",
        avg
    );
}

pub fn start_ticks() {
    let rate = APIC_RATE_CONSTANT.load(Ordering::SeqCst);
    if rate == 0 {
        panic!("APIC rate constant not set");
    }

    let lapic = LocalAPIC::new();
    lapic
        .configure_timer(local_apic::TimerMode::Periodic, LAPIC_TIMER_DIVISOR, 0x30)
        .unwrap();

    interrupts::register_handler(0x30, || {
        update_timers(1);
        InterruptHandlerStatus::Handled
    })
    .expect("could not register kernel tick handler");

    lapic.set_timer_ticks(rate as u32);
}
