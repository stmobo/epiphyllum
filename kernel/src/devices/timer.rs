//! Intel PIT support.

use super::pic::io_apic::IOAPIC;
use super::pic::local_apic;
use super::pic::local_apic::LocalAPIC;
use crate::asm::ports;
use crate::interrupts;
use crate::interrupts::{IRQHandler, InterruptHandlerStatus};
use crate::lock::OnceCell;
use crate::task::scheduler;
use crate::timer::{update_timers, TICKS_PER_SECOND};

use alloc_crate::sync::Arc;
use core::sync::atomic::{spin_loop_hint, AtomicBool, AtomicU64, Ordering};

const CH0_ADDR: u16 = 0x40;
const COMMAND_ADDR: u16 = 0x43;

const LAPIC_TIMER_DIVISOR: u8 = 8;
const CALIBRATION_TRIALS: u64 = 512;

static LAPIC_TIMER: OnceCell<LAPICTimer> = OnceCell::new();

// Atomic calibration state
struct CalibrationData {
    accumulated_ticks: AtomicU64,
    cur_trial: AtomicU64,
    done: AtomicBool,
    lapic_fired: AtomicBool,
    lapic_active: AtomicBool,
    pit_vector: OnceCell<u8>,
    apic_vector: OnceCell<u8>,
}

impl CalibrationData {
    fn new() -> CalibrationData {
        CalibrationData {
            done: AtomicBool::new(false),
            lapic_fired: AtomicBool::new(false),
            lapic_active: AtomicBool::new(false),
            accumulated_ticks: AtomicU64::new(0),
            cur_trial: AtomicU64::new(0),
            pit_vector: OnceCell::new(),
            apic_vector: OnceCell::new(),
        }
    }

    fn add_trial(&self, ticks: u64) {
        if ticks < 500 {
            return;
        }

        let elapsed = 0xFFFF_FFFF - ticks;
        self.accumulated_ticks.fetch_add(elapsed, Ordering::SeqCst);
        self.cur_trial.fetch_add(1, Ordering::SeqCst);

        if self.cur_trial.load(Ordering::SeqCst) >= CALIBRATION_TRIALS {
            self.done.store(true, Ordering::SeqCst);
        }
    }
}

struct CalibratingTimer {
    data: Arc<CalibrationData>,
    lapic_isr: IRQHandler,
    pit_isr: IRQHandler,
}

impl CalibratingTimer {
    fn new() -> CalibratingTimer {
        let data = Arc::new(CalibrationData::new());
        let data_pit = data.clone();
        let data_lapic = data.clone();

        let pit_isr = interrupts::register_handler(None, true, move || {
            let lapic = LocalAPIC::new();

            if data_pit.lapic_active.load(Ordering::SeqCst) {
                lapic.disable_timer();

                if !data_pit.lapic_fired.load(Ordering::SeqCst) {
                    // PIT fired before LAPIC
                    data_pit.add_trial(lapic.get_timer_ticks() as u64);
                }
            }

            data_pit.lapic_fired.store(false, Ordering::SeqCst);
            data_pit.lapic_active.store(true, Ordering::SeqCst);

            let vector = *data_pit.apic_vector.get().unwrap();

            lapic
                .configure_timer(local_apic::TimerMode::OneShot, LAPIC_TIMER_DIVISOR, vector)
                .unwrap();
            lapic.set_timer_ticks(0xFFFF_FFFF);

            InterruptHandlerStatus::Handled
        })
        .expect("could not register PIT interrupt");

        let pit_gsi = IOAPIC::isa_irq_to_gsi(0).expect("could not PIT timer GSI");
        unsafe {
            IOAPIC::set_gsi_vector(pit_gsi, pit_isr.interrupt_vector())
                .expect("could not configure PIT timer vector");
        }

        data.pit_vector.set(pit_isr.interrupt_vector()).unwrap();

        let lapic_isr = interrupts::register_handler(None, true, move || {
            data_lapic.lapic_fired.store(true, Ordering::SeqCst);
            InterruptHandlerStatus::Handled
        })
        .expect("could not register APIC timer interrupt");

        data.apic_vector.set(lapic_isr.interrupt_vector()).unwrap();

        let lapic = LocalAPIC::new();
        lapic
            .configure_timer(
                local_apic::TimerMode::OneShot,
                LAPIC_TIMER_DIVISOR,
                lapic_isr.interrupt_vector(),
            )
            .unwrap();

        /* Set up the PIT timer in mode 2 (rate generator). */
        unsafe {
            let count = (1193182 / TICKS_PER_SECOND) as u16;
            println!("timer: PIT divisor = {}", count);

            ports::outb(COMMAND_ADDR, 0b0011_0100);
            ports::outb(CH0_ADDR, (count & 0xFF) as u8);
            ports::outb(CH0_ADDR, ((count >> 8) & 0xFF) as u8);
        }

        CalibratingTimer {
            data,
            lapic_isr,
            pit_isr,
        }
    }

    fn wait(&self) {
        while !self.data.done.load(Ordering::SeqCst) {
            spin_loop_hint();
        }
    }

    fn accumulated_ticks(&self) -> u64 {
        self.data.accumulated_ticks.load(Ordering::SeqCst)
    }
}

struct LAPICTimer {
    isr: IRQHandler,
    rate: u64,
}

impl LAPICTimer {
    fn new() -> LAPICTimer {
        let calibrating = CalibratingTimer::new();

        println!("timer: now calibrating APIC timer against PIT...");
        calibrating.wait();

        let rate = calibrating.accumulated_ticks() / CALIBRATION_TRIALS;
        println!("timer: APIC timer rate is {} ticks per kernel tick", rate);

        let pit_vector = *calibrating.data.pit_vector.get().unwrap();

        interrupts::mask_irq(pit_vector, true).expect("could not mask PIT interrupt");
        drop(calibrating);

        let isr = interrupts::register_handler(None, true, timer_interrupt)
            .expect("could not register LAPIC timer ISR");
        let lapic = LocalAPIC::new();
        lapic
            .configure_timer(
                local_apic::TimerMode::Periodic,
                LAPIC_TIMER_DIVISOR,
                isr.interrupt_vector(),
            )
            .unwrap();

        lapic.set_timer_ticks(rate as u32);

        LAPICTimer { isr, rate }
    }
}

fn timer_interrupt() -> InterruptHandlerStatus {
    update_timers(1);
    scheduler().update();

    InterruptHandlerStatus::Handled
}

pub fn initialize() {
    if LAPIC_TIMER.set(LAPICTimer::new()).is_err() {
        panic!("already initialized");
    }
    println!("timer: LAPIC timer initialized");
}
