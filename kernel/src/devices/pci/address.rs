use core::fmt;
use core::fmt::Display;
use core::ops::Deref;

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct PCIAddress(u32);

impl PCIAddress {
    pub fn new(segment: u16, bus: u8, device: u8, function: u8) -> PCIAddress {
        assert!(device < 32, "invalid device number {}", device);
        assert!(function < 8, "invalid function number {}", function);

        let addr: u32 = ((segment as u32) << 16)
            | ((bus as u32) << 8)
            | (((device & 0x1F) as u32) << 3)
            | ((function & 0x07) as u32);

        PCIAddress(addr)
    }

    pub fn legacy_cam_address(self, offset: u16) -> u32 {
        debug_assert_eq!(
            self.0 & !0xFFFF,
            0,
            "cannot access devices outside of segment 0 with legacy configuration mechanism"
        );

        0x8000_0000 | ((self.0 & 0xFFFF) << 8) | ((offset as u32) & 0xFF)
    }

    pub fn extended_cam_shift(self) -> u64 {
        (self.0 << 12) as u64
    }

    #[inline]
    pub fn segment(self) -> u16 {
        ((self.0 >> 16) & 0xFFFF) as u16
    }

    #[inline]
    pub fn bus(self) -> u8 {
        ((self.0 >> 8) & 0xFF) as u8
    }

    #[inline]
    pub fn device(self) -> u8 {
        ((self.0 >> 3) & 0x1F) as u8
    }

    #[inline]
    pub fn function(self) -> u8 {
        (self.0 & 0x07) as u8
    }
}

impl Deref for PCIAddress {
    type Target = u32;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Display for PCIAddress {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.segment() != 0 {
            write!(
                f,
                "{:04x}:{:02x}:{:02x}.{:01x}",
                self.segment(),
                self.bus(),
                self.device(),
                self.function()
            )
        } else {
            write!(
                f,
                "{:02x}:{:02x}.{:01x}",
                self.bus(),
                self.device(),
                self.function()
            )
        }
    }
}
