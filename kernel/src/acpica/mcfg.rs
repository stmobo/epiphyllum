use alloc_crate::vec::Vec;
use core::mem;
use core::ops::Deref;
use core::ptr;

use spin::Once;

static MCFG_DATA: Once<Option<MCFG>> = Once::new();

#[repr(C)]
pub struct HostBridgeSpace {
    pub address: usize,
    pub segment_group: u16,
    pub start_bus: u8,
    pub end_bus: u8,
    _pad: u32,
}

#[repr(transparent)]
pub struct MCFG {
    pub bridges: Vec<HostBridgeSpace>,
}

impl MCFG {
    fn parse() -> Option<MCFG> {
        debug_assert_eq!(mem::size_of::<HostBridgeSpace>(), 16);

        let table_addr: usize = super::get_table(b"MCFG", 0).ok()?;
        unsafe {
            let len = ptr::read((table_addr + 4) as *const u32);

            // address of cfg data start, and length of cfg data
            let cfg_start = table_addr + 44;
            let cfg_len = (len - 44) as usize;

            assert_eq!(
                cfg_len % 16,
                0,
                "MCFG configuration data length not divisible by 16?"
            );

            let n_bridges = cfg_len / 16;
            let mut bridges = Vec::with_capacity(n_bridges as usize);
            let p = cfg_start as *const HostBridgeSpace;

            for i in 0..n_bridges {
                let bridge = p.add(i).read_unaligned();
                println!("acpi: host bridge {}:", i);
                println!("acpi:    segment group {}", bridge.segment_group);
                println!("acpi:    busses {} - {}", bridge.start_bus, bridge.end_bus);
                println!("acpi:    address: {:#018x}", bridge.address);

                bridges.push(bridge);
            }

            Some(MCFG { bridges })
        }
    }

    pub fn get() -> Option<&'static MCFG> {
        MCFG_DATA.call_once(MCFG::parse).as_ref()
    }
}

impl Deref for MCFG {
    type Target = Vec<HostBridgeSpace>;

    fn deref(&self) -> &Self::Target {
        &self.bridges
    }
}
