mod acpi;
mod address;
mod config_space;
mod device;
mod enhanced_cam;
mod enumeration;
mod legacy_cam;

pub use address::PCIAddress;
use config_space::PCISegmentConfigSpace;
pub use device::{PCIDevice, PCIInterruptPin};

use crate::acpica::resource::ExtendedIrq;
use crate::acpica::{AcpiDevice, PCIInterruptSource};
use alloc_crate::vec::Vec;

pub fn initialize() {
    config_space::initialize();
    acpi::initialize();
    device::enumerate_devices();

    // (experimental code)
    // find all interrupt link devices:
    let root_bridge_acpi = acpi::get_root_bridge_device();
    let prt = root_bridge_acpi
        .pci_irq_routing()
        .expect("could not get IRQ routing table for PCI root device");

    let mut link_devices: Vec<&'static AcpiDevice> = Vec::new();

    for entry in prt {
        match entry.interrupt_source() {
            PCIInterruptSource::Hardwired(_) => println!("pci: {}", entry),
            PCIInterruptSource::Device(device) => {
                if !link_devices.contains(&device) {
                    link_devices.push(device);
                }
            }
        }
    }

    println!(
        "pci: enumerated {} interrupt link devices:",
        link_devices.len()
    );
    for device in link_devices {
        let prs = match device.possible_resources::<ExtendedIrq>() {
            Ok(r) => r,
            Err(e) => panic!(
                "could not get possible resource settings for device {}: {:?}",
                device, e
            ),
        };

        let crs = match device.current_resources::<ExtendedIrq>() {
            Ok(r) => r,
            Err(e) => panic!(
                "could not get current resource settings for device {}: {:?}",
                device, e
            ),
        };

        assert_eq!(
            crs.len(),
            1,
            "multiple/no current extended IRQ settings for device {}",
            device
        );

        assert_eq!(
            crs[0].interrupts.len(),
            1,
            "multiple/no current IRQs for device {}",
            device
        );

        let cur_irq: u32 = crs[0].interrupts[0];
        print!("pci:     {} mapped to IRQ {}", device, cur_irq);

        if prs.len() > 0 {
            print!(" (available: ");

            for possible in prs {
                print!("{}", possible.interrupts[0]);

                for irq in possible.interrupts.iter().skip(1) {
                    print!(", {}", *irq);
                }
            }

            print!(")");
        }

        print!("\n");
    }

    println!("pci: initialization complete");
}
