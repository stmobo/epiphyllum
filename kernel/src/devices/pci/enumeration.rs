use super::config_space;

pub fn read_dev_vendor_id(segment: u16, bus: u8, device: u8, function: u8) -> (u16, u16) {
    let data = unsafe { config_space::read_config_split(segment, bus, device, function, 0) };
    let vendor_id = (data & 0xFFFF) as u16;
    let device_id = ((data >> 16) & 0xFFFF) as u16;
    (vendor_id, device_id)
}

pub fn device_present(segment: u16, bus: u8, device: u8, function: u8) -> bool {
    let (vendor_id, _) = read_dev_vendor_id(segment, bus, device, function);
    vendor_id != 0xFFFF
}

pub fn is_multi_function(segment: u16, bus: u8, device: u8, function: u8) -> bool {
    let data = unsafe { config_space::read_config_split(segment, bus, device, function, 12) };
    let raw_header_type = ((data >> 16) & 0xFF) as u8;

    (raw_header_type & 0x80) != 0
}

pub fn read_class(segment: u16, bus: u8, device: u8, function: u8) -> (u8, u8, u8) {
    let data = unsafe { config_space::read_config_split(segment, bus, device, function, 8) };
    let major_class = ((data >> 24) & 0xFF) as u8;
    let minor_class = ((data >> 16) & 0xFF) as u8;
    let prog_if = ((data >> 8) & 0xFF) as u8;

    (major_class, minor_class, prog_if)
}

pub fn get_secondary_bus(segment: u16, bus: u8, device: u8, function: u8) -> u8 {
    let t = unsafe { config_space::read_config_split(segment, bus, device, function, 0x18) };
    ((t >> 8) & 0xFF) as u8
}
