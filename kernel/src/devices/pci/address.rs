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

    pub fn segment(self) -> u16 {
        ((self.0 >> 16) & 0xFFFF) as u16
    }

    pub fn bus(self) -> u8 {
        ((self.0 >> 8) & 0xFF) as u8
    }

    pub fn device(self) -> u8 {
        ((self.0 >> 3) & 0x1F) as u8
    }

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
