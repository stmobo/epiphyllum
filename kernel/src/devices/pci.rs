mod address;
mod config_space;
mod device;
mod enhanced_cam;
mod legacy_cam;

pub use address::PCIAddress;
use config_space::PCISegmentConfigSpace;
pub use device::{PCIDevice, PCIInterruptPin};

pub fn initialize() {
    config_space::initialize();
    device::enumerate_acpi();
    device::enumerate_devices();
}
