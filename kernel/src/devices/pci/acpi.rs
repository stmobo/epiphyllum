use crate::acpica;
use crate::acpica::AcpiDevice;
use crate::lock::OnceCell;
use crate::structures::HashMap;

use super::enumeration;
use super::PCIAddress;

static ROOT_BRIDGE_DEVICE: OnceCell<&'static AcpiDevice> = OnceCell::new();
static ACPI_MAP: OnceCell<HashMap<PCIAddress, &'static AcpiDevice>> = OnceCell::new();

fn get_root_acpi_device() -> Option<&'static AcpiDevice> {
    for (_, device) in acpica::get_device_map().iter() {
        if device.is_pci_root() {
            return Some(device);
        }
    }

    None
}

fn enumerate_bus_acpi_devices(
    bus: u8,
    device: &'static AcpiDevice,
    dev_map: &mut HashMap<PCIAddress, &'static AcpiDevice>,
) {
    for child in device.children() {
        if let Some(addr) = child.address() {
            let function = (addr & 0x07) as u8;
            let dev_id = ((addr >> 16) & 0x1F) as u8;

            let pci_addr = PCIAddress::new(0, bus, dev_id, function);
            if dev_map.insert(pci_addr, child).is_some() {
                panic!("PCI address collision in dev map");
            }

            let (major_class, minor_class, _) = enumeration::read_class(0, bus, dev_id, function);
            if (major_class != 0x06) || (minor_class != 0x04) {
                // not a PCI-PCI bridge
                continue;
            }

            let child_bus = enumeration::get_secondary_bus(0, bus, dev_id, function);
            enumerate_bus_acpi_devices(child_bus, child, dev_map);
        }
    }
}

// Enumerate all PCI devices in the ACPI namespace.
pub fn initialize() {
    let root = get_root_acpi_device().expect("could not find ACPI device for PCI root bridge");

    if ROOT_BRIDGE_DEVICE.set(root).is_err() {
        panic!("already initialized");
    }

    let mut dev_map: HashMap<PCIAddress, &'static AcpiDevice> = HashMap::new();

    // Assume that the root bridge is bus 0.
    enumerate_bus_acpi_devices(0, root, &mut dev_map);

    if ACPI_MAP.set(dev_map).is_err() {
        panic!("already initialized");
    }
}

pub fn get_root_bridge_device() -> &'static AcpiDevice {
    *ROOT_BRIDGE_DEVICE.get().expect("not initialized")
}

pub fn get_acpi_device(address: PCIAddress) -> Option<&'static AcpiDevice> {
    let map = ACPI_MAP.get().expect("not initialized");
    map.get(&address).copied()
}
