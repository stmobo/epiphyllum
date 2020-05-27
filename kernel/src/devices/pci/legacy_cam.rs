use crate::asm::ports;
use crate::lock::{NoIRQSpinlock, OnceCell};

use super::{PCIAddress, PCISegmentConfigSpace};

static LEGACY_CFG: OnceCell<LegacyPCIConfig> = OnceCell::new();

pub struct LegacyPCIConfig(NoIRQSpinlock<()>);

impl PCISegmentConfigSpace for LegacyPCIConfig {
    fn segment_number(&self) -> u16 {
        0
    }

    unsafe fn read(&self, address: PCIAddress, offset: u16) -> u32 {
        assert_eq!(offset & 0x03, 0, "offset {:#06x} not aligned", offset);
        assert!(
            offset < 0x100,
            "offset {:#06x} too large (limit 0x100)",
            offset
        );

        let _lock = self.0.lock();
        ports::outd(0xCF8, address.legacy_cam_address(offset));
        ports::ind(0xCFC)
    }

    unsafe fn write(&self, address: PCIAddress, offset: u16, value: u32) {
        assert_eq!(offset & 0x03, 0, "offset {:#06x} not aligned", offset);
        assert!(
            offset < 0x100,
            "offset {:#06x} too large (limit 0x100)",
            offset
        );

        let _lock = self.0.lock();
        ports::outd(0xCF8, address.legacy_cam_address(offset));
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
