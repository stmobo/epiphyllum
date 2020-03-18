//! Intel PIT support.

use super::pic::local_apic;
use super::pic::local_apic::LocalAPIC;
use crate::asm::ports;
use crate::interrupts;

use core::ptr;
use alloc::boxed::Box;
use core::sync::atomic::{AtomicU64, AtomicPtr, AtomicBool, Ordering};

const CH0_ADDR: u16 = 0x40;
const COMMAND_ADDR: u16 = 0x43;

static mut PIT_ISR_ID: u64 = 0; // Used only during initialization

/* Number of APIC timer ticks in (1/8192) of a second. */
static mut APIC_RATE_CONSTANT: u64 = 0;
static CUR_TICK_COUNT = AtomicU64::new(0);

pub fn get_apic_rate_constant() -> u64 {
    unsafe { APIC_RATE_CONSTANT }
}

unsafe fn pit_set_oneshot(count: u16) {
    ports::outb(COMMAND_ADDR, 0b00_11_000_0);
    ports::outb(CH0_ADDR, (count & 0xFF) as u8);
    ports::outb(CH0_ADDR, ((count >> 8) & 0xFF) as u8);
}

pub fn calibrate_apic_timer() {
    let lapic = LocalAPIC::new();

    println!("timer: calibrating APIC timer against PIT...");

    lapic
        .configure_timer(local_apic::TimerMode::OneShot, 1, 0x30)
        .unwrap();

    let pit_isr_id =
        interrupts::register_handler(0x20, || -> interrupts::InterruptHandlerStatus {
            let lapic = LocalAPIC::new();
            let ticks = lapic.get_timer_ticks() as u64;

            unsafe {
                APIC_RATE_CONSTANT = 0xFFFF_FFFF - ticks;
            }

            interrupts::InterruptHandlerStatus::Handled
        })
        .unwrap();

    unsafe {
        /* 1193182 Hz / 145 = 8192 Hz */
        pit_set_oneshot(145);
        lapic.set_timer_ticks(0xFFFF_FFFF);
    }

    while get_apic_rate_constant() == 0 {
        unsafe {
            asm!("hlt");
        }
    }

    lapic.disable_timer();
    interrupts::unregister_handler(0x20, pit_isr_id);

    println!(
        "timer: APIC timer constant is {} ticks per 0.00012207 sec",
        get_apic_rate_constant()
    );
}
