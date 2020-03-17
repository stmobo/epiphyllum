pub mod bindings {
    #![allow(non_upper_case_globals)]
    #![allow(non_camel_case_types)]
    #![allow(non_snake_case)]
    include!(concat!(env!("OUT_DIR"), "/bindings.rs"));
}

pub mod os_services {
    use super::bindings;

    #[no_mangle]
    pub extern "C" fn AcpiOsInitialize() -> bindings::ACPI_STATUS {
        0
    }

    #[no_mangle]
    pub extern "C" fn AcpiOsTerminate() -> bindings::ACPI_STATUS {
        0
    }

    #[no_mangle]
    pub extern "C" fn AcpiOsPrintf() {}
}

pub fn initialize() {
    let status = unsafe { bindings::AcpiInitializeSubsystem() };
}
