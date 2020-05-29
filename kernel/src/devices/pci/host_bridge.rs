use alloc_crate::sync::Arc;
use alloc_crate::vec::Vec;

use super::PCIDevice;
use crate::acpica::{AcpiDevice, PCIRoutingEntry};

pub struct HostBridgeBus {
    bus: u8,
    acpi_device: &'static AcpiDevice,
    interrupts: Vec<PCIRoutingEntry>,
    devices: Vec<Arc<PCIDevice>>,
}
