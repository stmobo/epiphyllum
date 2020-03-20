//! Intel PIT support.

use super::pic::local_apic;
use super::pic::local_apic::LocalAPIC;
use crate::asm::ports;
use crate::interrupts;

use crate::timer;
use crate::timer::TICKS_PER_SECOND;

use core::sync::atomic::{compiler_fence, spin_loop_hint, AtomicU64, Ordering};

const CH0_ADDR: u16 = 0x40;
const COMMAND_ADDR: u16 = 0x43;

const LAPIC_TIMER_DIVISOR: u8 = 8;

/* Number of APIC timer ticks per kernel tick. */
static APIC_RATE_CONSTANT: AtomicU64 = AtomicU64::new(0);

pub fn get_apic_rate_constant() -> u64 {
    APIC_RATE_CONSTANT.load(Ordering::Relaxed)
}

pub fn max_timer_deadline() -> u64 {
    0xFFFF_FFFFu64 / get_apic_rate_constant()
}

fn pit_set_oneshot(count: u16) {
    unsafe {
        ports::outb(COMMAND_ADDR, 0b00_11_000_0);
        ports::outb(CH0_ADDR, (count & 0xFF) as u8);
        ports::outb(CH0_ADDR, ((count >> 8) & 0xFF) as u8);
    }
}

fn start_lapic_calibration(lapic: LocalAPIC) {
    pit_set_oneshot((1193182 / TICKS_PER_SECOND) as u16);
    lapic.set_timer_ticks(0xFFFF_FFFF);
}

pub fn calibrate_apic_timer() {
    let lapic = LocalAPIC::new();

    println!("timer: calibrating APIC timer against PIT...");

    lapic
        .configure_timer(local_apic::TimerMode::OneShot, LAPIC_TIMER_DIVISOR, 0x30)
        .unwrap();

    let pit_isr_id =
        interrupts::register_handler(0x20, || -> interrupts::InterruptHandlerStatus {
            let lapic = LocalAPIC::new();
            let ticks = lapic.get_timer_ticks() as u64;
            let rc = APIC_RATE_CONSTANT.load(Ordering::Relaxed);

            if rc == 0 {
                if ticks != 0 {
                    /* This calibration attempt appears to have succeeded. */
                    let c = (0xFFFF_FFFF - ticks) / (LAPIC_TIMER_DIVISOR as u64);
                    APIC_RATE_CONSTANT.store(c, Ordering::Relaxed);
                } else if ticks == 0 {
                    /* The LAPIC timer fired before the PIT timer, retry calibration. */
                    start_lapic_calibration(lapic);
                }
            }
            /* if RC != 0 then a concurrent calibration attempt must have somehow gone
             * through before we unregistered the PIT ISR. Ignore it.
             */

            interrupts::InterruptHandlerStatus::Handled
        })
        .unwrap();

    let lapic_isr_id =
        interrupts::register_handler(0x30, || -> interrupts::InterruptHandlerStatus {
            if APIC_RATE_CONSTANT.load(Ordering::Relaxed) == 0 {
                /* Retry calibration. */
                start_lapic_calibration(LocalAPIC::new());
            }

            interrupts::InterruptHandlerStatus::Handled
        })
        .unwrap();

    compiler_fence(Ordering::Release);

    /* 1193182 Hz / 145 = 8192 Hz */
    start_lapic_calibration(lapic);

    compiler_fence(Ordering::Acquire);

    while get_apic_rate_constant() == 0 {
        spin_loop_hint();
    }

    lapic.disable_timer();
    interrupts::unregister_handler(0x30, lapic_isr_id);
    interrupts::unregister_handler(0x20, pit_isr_id);

    println!(
        "timer: APIC timer constant is {} ticks per kernel tick",
        get_apic_rate_constant()
    );

    interrupts::register_handler(0x30, timer_interrupt)
        .expect("could not register LAPIC timer interrupt");
}

pub fn set_lapic_oneshot(kernel_ticks: u64) {
    use core::convert::TryInto;
    let lapic = LocalAPIC::new();

    lapic
        .configure_timer(local_apic::TimerMode::OneShot, LAPIC_TIMER_DIVISOR, 0x30)
        .unwrap();

    let lapic_ticks = kernel_ticks * get_apic_rate_constant();
    lapic.set_timer_ticks(lapic_ticks.try_into().unwrap());
}

pub fn clear_lapic() {
    let lapic = LocalAPIC::new();
    lapic.disable_timer();
}

fn timer_interrupt() -> interrupts::InterruptHandlerStatus {
    timer::update_timers();

    interrupts::InterruptHandlerStatus::Handled
}
