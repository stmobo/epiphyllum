use crate::asm::ports;
use crate::lock::{NoIRQSpinlock, OnceCell};

use super::PCISegmentConfigSpace;

static LEGACY_CFG: OnceCell<LegacyPCIConfig> = OnceCell::new();

pub struct LegacyPCIConfig(NoIRQSpinlock<()>);

fn construct_config_address(bus: u8, device: u8, function: u8, offset: u16) -> u32 {
    assert!(device < 32, "invalid device number {}", device);
    assert!(function < 8, "invalid function number {}", function);
    assert!((offset & 0x03) == 0, "offset {:#06x} not aligned", offset);

    ((bus as u32) << 16)
        | (((device & 0x1F) as u32) << 11)
        | (((function & 0x07) as u32) << 8)
        | ((offset & 0xFC) as u32)
        | 0x8000_0000
}

impl PCISegmentConfigSpace for LegacyPCIConfig {
    fn segment_number(&self) -> u16 {
        0
    }

    unsafe fn read(&self, bus: u8, device: u8, function: u8, offset: u16) -> u32 {
        let address = construct_config_address(bus, device, function, offset);
        let _lock = self.0.lock();

        ports::outd(0xCF8, address);
        ports::ind(0xCFC)
    }

    unsafe fn write(&self, bus: u8, device: u8, function: u8, offset: u16, value: u32) {
        let address = construct_config_address(bus, device, function, offset);
        let _lock = self.0.lock();

        ports::outd(0xCF8, address);
        ports::outd(0xCFC, value);
    }
}

pub fn initialize() {
    if LEGACY_CFG
        .set(LegacyPCIConfig(NoIRQSpinlock::new(())))
        .is_err()
    {
        panic!("already initialized");
    }

    println!("pci: initialized legacy configuration access mechanism");
}

pub fn get() -> &'static LegacyPCIConfig {
    LEGACY_CFG.get().expect("not initialized")
}
