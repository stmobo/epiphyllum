use crate::lock::{NoIRQSpinlock, OnceCell};
use crate::structures::HashMap;

mod address;
mod config_space;
mod device;
mod enhanced_cam;
mod legacy_cam;

use address::PCIAddress;
use config_space::PCISegmentConfigSpace;
use device::PCIDevice;

static DEVICES: OnceCell<HashMap<PCIAddress, NoIRQSpinlock<PCIDevice>>> = OnceCell::new();

pub fn initialize() {
    config_space::initialize();
    device::enumerate_acpi();

    let devices = device::enumerate_devices();

    let mut map: HashMap<PCIAddress, NoIRQSpinlock<PCIDevice>> = HashMap::new();
    for device in devices {
        let address = device.address();
        if map.insert(address, NoIRQSpinlock::new(device)).is_some() {
            panic!(
                "PCI address conflict: address {} enumerated twice?",
                address
            );
        }
    }

    if DEVICES.set(map).is_err() {
        panic!("already initialized");
    }
}
