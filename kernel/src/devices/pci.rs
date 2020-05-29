mod acpi;
mod address;
mod config_space;
mod device;
mod enhanced_cam;
mod enumeration;
mod host_bridge;
mod legacy_cam;

pub use address::PCIAddress;
use config_space::PCISegmentConfigSpace;
pub use device::{PCIDevice, PCIInterruptPin};

pub fn initialize() {
    config_space::initialize();
    acpi::initialize();
    device::enumerate_devices();
}
