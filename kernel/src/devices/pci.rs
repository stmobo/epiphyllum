mod acpi;
mod address;
mod config_space;
mod device;
mod enhanced_cam;
mod enumeration;
mod interrupts;
mod legacy_cam;

pub use address::PCIAddress;
use config_space::PCISegmentConfigSpace;
pub use device::{PCIBus, PCIDevice};
pub use interrupts::PCIInterruptPin;

pub fn initialize() {
    config_space::initialize();
    acpi::initialize();
    device::enumerate_devices();
    interrupts::enumerate_device_interrupts();

    println!("pci: initialization complete");
}
