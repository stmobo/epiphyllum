use alloc_crate::sync::Arc;
use alloc_crate::vec::Vec;
use core::fmt;
use core::fmt::Display;

use super::device;
use super::{PCIAddress, PCIDevice};
use crate::acpica::resource::ExtendedIrq;
use crate::acpica::{AcpiDevice, PCIInterruptSource};
use crate::lock::OnceCell;
use crate::structures::HashMap;

static INT_LINKS: OnceCell<Vec<InterruptLinkDevice>> = OnceCell::new();
static INT_ASSIGNMENTS: OnceCell<HashMap<PCIAddress, Vec<InterruptAssignment>>> = OnceCell::new();

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
#[repr(u8)]
pub enum PCIInterruptPin {
    LNKA = 0x00,
    LNKB = 0x01,
    LNKC = 0x02,
    LNKD = 0x03,
}

impl PCIInterruptPin {
    /// Maps an interrupt pin on a device downstream of a PCI-PCI bridge to the
    /// corresponding upstream interrupt pin.
    ///
    /// # Examples
    /// For device 0, this is simply an identity map: LNKA on the child maps to
    /// LNKA on the parent bus, and so on.
    ///
    /// For device 1, all interrupt pins shift 1 over to the right: LNKA on the
    /// child maps to LNK_B_ on the parent bus, etc.
    ///
    /// This should also carry over to nested busses as well.
    /// Consider the following (contrived) PCI topology:
    /// ```text
    /// [0000:00]-+-00:00.0                                (Host Bridge)
    ///           \-00:02.0-[01]-+-01:00.0                 (PCI-PCI bridge from bus 00 -> 01)
    ///                          +-01:03.0-[02]-+-02:00.0  (PCI-PCI bridge from bus 01 -> 02)
    ///                          |              \-02:02.0  (Device)
    ///                          \-01:05.0                 (Device)
    /// ```
    ///
    /// The routing of pin `LNKA` from device `02:02.0` would look like:
    /// ```text
    /// LNKA      -> LNKC      -> LNKB
    /// (02:02.0)    (01:03.0)    (00:02.0)
    /// [0]          [0+2 = 2]    [2+3 = 5 mod 4 = 1]
    /// ```
    ///
    /// The routing of pin `LNKC` from device `01:05.0` is:
    /// ```text
    /// LNKC      -> LNKD
    /// (01:05.0)    (00:02.0)
    /// [2]          [2+5 = 7 mod 4 = 3]
    /// ```
    ///
    /// For devices on the root bridge, the ACPI `_PRT` table specifies what
    /// PCI interrupt link devices correspond to each interrupt pin.
    pub fn bridge_swizzle(self, device_no: u8) -> PCIInterruptPin {
        debug_assert!(device_no < 0x1F, "invalid device number {:02x}", device_no);

        let new_pin = ((self as u8) + device_no) & 0x03;
        match new_pin {
            0 => PCIInterruptPin::LNKA,
            1 => PCIInterruptPin::LNKB,
            2 => PCIInterruptPin::LNKC,
            3 => PCIInterruptPin::LNKD,
            _ => unreachable!(),
        }
    }

    fn next_pin(self) -> PCIInterruptPin {
        match self {
            PCIInterruptPin::LNKA => PCIInterruptPin::LNKB,
            PCIInterruptPin::LNKB => PCIInterruptPin::LNKC,
            PCIInterruptPin::LNKC => PCIInterruptPin::LNKD,
            PCIInterruptPin::LNKD => PCIInterruptPin::LNKA,
        }
    }

    fn prev_pin(self) -> PCIInterruptPin {
        match self {
            PCIInterruptPin::LNKA => PCIInterruptPin::LNKD,
            PCIInterruptPin::LNKB => PCIInterruptPin::LNKA,
            PCIInterruptPin::LNKC => PCIInterruptPin::LNKB,
            PCIInterruptPin::LNKD => PCIInterruptPin::LNKC,
        }
    }

    fn extend(self) -> [PCIInterruptPin; 4] {
        [
            self,
            self.next_pin(),
            self.next_pin().next_pin(),
            self.prev_pin(),
        ]
    }
}

impl Display for PCIInterruptPin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            PCIInterruptPin::LNKA => write!(f, "LNKA"),
            PCIInterruptPin::LNKB => write!(f, "LNKB"),
            PCIInterruptPin::LNKC => write!(f, "LNKC"),
            PCIInterruptPin::LNKD => write!(f, "LNKD"),
        }
    }
}

fn get_root_pin_map(device: Arc<PCIDevice>) -> (PCIInterruptPin, PCIAddress) {
    let mut cur_pin = PCIInterruptPin::LNKA;
    let mut cur_device = device;

    loop {
        let bus = cur_device.parent_bus();
        if let Some(bridge) = bus.bridge() {
            cur_pin = cur_pin.bridge_swizzle(cur_device.address().device());
            cur_device = bridge;
        } else {
            // we have reached the root node
            break;
        }
    }

    (cur_pin, cur_device.address())
}

pub struct InterruptLinkDevice {
    segment_id: u16,
    bus_id: u8,
    acpi_device: &'static AcpiDevice,
    current_irq: ExtendedIrq,
    possible_irqs: Vec<ExtendedIrq>,
    assignments: Vec<(PCIInterruptPin, Arc<PCIDevice>)>,
    link_device_number: usize,
}

#[derive(Debug)]
pub enum InterruptAssignment {
    Device(usize),
    Hardwired(u8),
}

pub fn enumerate_device_interrupts() {
    let mut link_devices: Vec<InterruptLinkDevice> = Vec::new();
    let mut prts = Vec::new();

    // Get interrupt routing tables for all root busses
    for bus in device::get_root_busses().iter() {
        let acpi_device = bus.acpi_device();
        let prt = match acpi_device.pci_irq_routing() {
            Ok(prt) => prt,
            Err(e) => panic!(
                "could not get PCI IRQ routing table for bus {:04x}:{:02x} - {:?}",
                bus.segment_id(),
                bus.bus_id(),
                e
            ),
        };

        // Build a list of all interrupt link devices
        for entry in prt.iter() {
            if let PCIInterruptSource::Device(link_device) = entry.interrupt_source() {
                if link_devices
                    .iter()
                    .find(|link| {
                        (link.segment_id == bus.segment_id())
                            && (link.bus_id == bus.bus_id())
                            && (link.acpi_device == link_device)
                    })
                    .is_none()
                {
                    let prs = match link_device.possible_resources::<ExtendedIrq>() {
                        Ok(r) => r,
                        Err(e) => panic!(
                            "could not get possible resource settings for device {}: {:?}",
                            link_device, e
                        ),
                    };

                    let crs = match link_device.current_resources::<ExtendedIrq>() {
                        Ok(r) => r,
                        Err(e) => panic!(
                            "could not get current resource settings for device {}: {:?}",
                            link_device, e
                        ),
                    };

                    assert_eq!(
                        crs.len(),
                        1,
                        "multiple/no current extended IRQ settings for device {}",
                        link_device
                    );

                    assert_eq!(
                        crs[0].interrupts.len(),
                        1,
                        "multiple/no current IRQs for device {}",
                        link_device
                    );

                    let link_dev = InterruptLinkDevice {
                        segment_id: bus.segment_id(),
                        bus_id: bus.bus_id(),
                        acpi_device: link_device,
                        current_irq: crs[0].clone(),
                        possible_irqs: prs,
                        assignments: Vec::new(),
                        link_device_number: link_devices.len(),
                    };

                    link_devices.push(link_dev);
                }
            }
        }

        prts.push((bus.segment_id(), bus.bus_id(), prt));
    }

    let mut int_map: HashMap<PCIAddress, Vec<InterruptAssignment>> = HashMap::new();

    // Now go through all devices and map interrupt numbers:
    for (address, device) in device::get_device_map().iter() {
        let address = *address;
        let (root_pin, bridge_address) = get_root_pin_map(device.clone());

        // Find the PRT for this device:
        let prt = prts
            .iter()
            .find(|t| (t.0 == bridge_address.segment()) && (t.1 == bridge_address.bus()));

        assert!(
            prt.is_some(),
            "could not find PRT for PCI device {} (bridge address {})",
            address,
            bridge_address
        );
        let prt = prt.unwrap();

        // Get the PRT entries for each of the four interrupt pins...
        let pins = root_pin.extend();
        let routing_entries = pins.iter().map(|pin| {
            let bridge_pin = *pin;
            let entry = prt
                .2
                .iter()
                .find(|e| (e.pin() == bridge_pin) && (e.device_id() == bridge_address.device()));

            assert!(
                entry.is_some(),
                "could not find PRT entry for PCI device {}, pin {}",
                bridge_address,
                bridge_pin
            );

            entry.unwrap().clone()
        });

        //println!("pci:     device {}:", address);

        // Convert those PRT entries into InterruptAssignments...
        let assignments: Vec<InterruptAssignment> = routing_entries
            .enumerate()
            .map(|(i, entry)| {
                let device_pin = match i {
                    0 => PCIInterruptPin::LNKA,
                    1 => PCIInterruptPin::LNKB,
                    2 => PCIInterruptPin::LNKC,
                    3 => PCIInterruptPin::LNKD,
                    _ => unreachable!(),
                };

                match entry.interrupt_source() {
                    PCIInterruptSource::Hardwired(gsi) => {
                        //println!("pci:         {} => GSI {} (hardwired)", device_pin, gsi);
                        InterruptAssignment::Hardwired(gsi)
                    }
                    PCIInterruptSource::Device(d) => {
                        // Find the given interrupt link device
                        let linked = link_devices.iter_mut().find(|l| {
                            l.acpi_device == d
                        });
                        assert!(
                            linked.is_some(),
                            "could not find interrupt link device for PCI device {} (bridge address {}), device pin {}",
                            address,
                            bridge_address,
                            device_pin
                        );

                        let linked = linked.unwrap();

                        //let irq_no = linked.current_irq.interrupts[0];
                        //println!("pci:         {} => {} (IRQ {})", device_pin, d, irq_no);

                        // Add this PCI device / interrupt pin combo to the int
                        // device's list of mapped devices
                        linked.assignments.push((device_pin, device.clone()));

                        // Get its number, and use that for the interrupt asssignment
                        InterruptAssignment::Device(linked.link_device_number)
                    }
                }
            })
            .collect();

        int_map.insert(address, assignments);
    }

    println!("pci: found {} interrupt link devices:", link_devices.len());
    for link in link_devices.iter() {
        println!(
            "pci:     {} ({} interrupts)",
            link.acpi_device,
            link.assignments.len()
        );
    }

    if INT_LINKS.set(link_devices).is_err() {
        panic!("already initialized");
    }

    if INT_ASSIGNMENTS.set(int_map).is_err() {
        panic!("already initialized");
    }
}
