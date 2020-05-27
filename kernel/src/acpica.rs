use core::mem;
use core::ptr;

pub mod bindings {
    #![allow(dead_code)]
    #![allow(non_upper_case_globals)]
    #![allow(non_camel_case_types)]
    #![allow(non_snake_case)]
    #![allow(clippy::all)]
    use core::convert::TryFrom;
    use core::ops::{Deref, DerefMut, Try};
    use num_enum::{IntoPrimitive, TryFromPrimitive};

    include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

    pub const AE_OK: ACPI_STATUS = 0;

    #[derive(Debug, Copy, Clone, PartialEq, Eq, IntoPrimitive, TryFromPrimitive)]
    #[repr(u32)]
    pub enum AcpiError {
        /* Environmental errors */
        AE_ERROR = 0x0001,
        AE_NO_ACPI_TABLES = 0x0002,
        AE_NO_NAMESPACE = 0x0003,
        AE_NO_MEMORY = 0x0004,
        AE_NOT_FOUND = 0x0005,
        AE_NOT_EXIST = 0x0006,
        AE_ALREADY_EXISTS = 0x0007,
        AE_TYPE = 0x0008,
        AE_NULL_OBJECT = 0x0009,
        AE_NULL_ENTRY = 0x000A,
        AE_BUFFER_OVERFLOW = 0x000B,
        AE_STACK_OVERFLOW = 0x000C,
        AE_STACK_UNDERFLOW = 0x000D,
        AE_NOT_IMPLEMENTED = 0x000E,
        AE_SUPPORT = 0x000F,
        AE_LIMIT = 0x0010,
        AE_TIME = 0x0011,
        AE_ACQUIRE_DEADLOCK = 0x0012,
        AE_RELEASE_DEADLOCK = 0x0013,
        AE_NOT_ACQUIRED = 0x0014,
        AE_ALREADY_ACQUIRED = 0x0015,
        AE_NO_HARDWARE_RESPONSE = 0x0016,
        AE_NO_GLOBAL_LOCK = 0x0017,
        AE_ABORT_METHOD = 0x0018,
        AE_SAME_HANDLER = 0x0019,
        AE_NO_HANDLER = 0x001A,
        AE_OWNER_ID_LIMIT = 0x001B,
        AE_NOT_CONFIGURED = 0x001C,
        AE_ACCESS = 0x001D,
        AE_IO_ERROR = 0x001E,
        AE_NUMERIC_OVERFLOW = 0x001F,
        AE_HEX_OVERFLOW = 0x0020,
        AE_DECIMAL_OVERFLOW = 0x0021,
        AE_OCTAL_OVERFLOW = 0x0022,
        AE_END_OF_TABLE = 0x0023,

        /* Programmer errors */
        AE_BAD_PARAMETER = 0x1001,
        AE_BAD_CHARACTER = 0x1002,
        AE_BAD_PATHNAME = 0x1003,
        AE_BAD_DATA = 0x1004,
        AE_BAD_HEX_CONSTANT = 0x1005,
        AE_BAD_OCTAL_CONSTANT = 0x1006,
        AE_BAD_DECIMAL_CONSTANT = 0x1007,
        AE_MISSING_ARGUMENTS = 0x1008,
        AE_BAD_ADDRESS = 0x1009,

        /* Table errors */
        AE_BAD_SIGNATURE = 0x2001,
        AE_BAD_HEADER = 0x2002,
        AE_BAD_CHECKSUM = 0x2003,
        AE_BAD_VALUE = 0x2004,
        AE_INVALID_TABLE_LENGTH = 0x2005,

        /* AML errors */
        AE_AML_BAD_OPCODE = 0x3001,
        AE_AML_NO_OPERAND = 0x3002,
        AE_AML_OPERAND_TYPE = 0x3003,
        AE_AML_OPERAND_VALUE = 0x3004,
        AE_AML_UNINITIALIZED_LOCAL = 0x3005,
        AE_AML_UNINITIALIZED_ARG = 0x3006,
        AE_AML_UNINITIALIZED_ELEMENT = 0x3007,
        AE_AML_NUMERIC_OVERFLOW = 0x3008,
        AE_AML_REGION_LIMIT = 0x3009,
        AE_AML_BUFFER_LIMIT = 0x300A,
        AE_AML_PACKAGE_LIMIT = 0x300B,
        AE_AML_DIVIDE_BY_ZERO = 0x300C,
        AE_AML_BAD_NAME = 0x300D,
        AE_AML_NAME_NOT_FOUND = 0x300E,
        AE_AML_INTERNAL = 0x300F,
        AE_AML_INVALID_SPACE_ID = 0x3010,
        AE_AML_STRING_LIMIT = 0x3011,
        AE_AML_NO_RETURN_VALUE = 0x3012,
        AE_AML_METHOD_LIMIT = 0x3013,
        AE_AML_NOT_OWNER = 0x3014,
        AE_AML_MUTEX_ORDER = 0x3015,
        AE_AML_MUTEX_NOT_ACQUIRED = 0x3016,
        AE_AML_INVALID_RESOURCE_TYPE = 0x3017,
        AE_AML_INVALID_INDEX = 0x3018,
        AE_AML_REGISTER_LIMIT = 0x3019,
        AE_AML_NO_WHILE = 0x301A,
        AE_AML_ALIGNMENT = 0x301B,
        AE_AML_NO_RESOURCE_END_TAG = 0x301C,
        AE_AML_BAD_RESOURCE_VALUE = 0x301D,
        AE_AML_CIRCULAR_REFERENCE = 0x301E,
        AE_AML_BAD_RESOURCE_LENGTH = 0x301F,
        AE_AML_ILLEGAL_ADDRESS = 0x3020,
        AE_AML_LOOP_TIMEOUT = 0x3021,
        AE_AML_UNINITIALIZED_NODE = 0x3022,
        AE_AML_TARGET_TYPE = 0x3023,
        AE_AML_PROTOCOL = 0x3024,
        AE_AML_BUFFER_LENGTH = 0x3025,

        /* Internal control errors */
        AE_CTRL_RETURN_VALUE = 0x4001,
        AE_CTRL_PENDING = 0x4002,
        AE_CTRL_TERMINATE = 0x4003,
        AE_CTRL_TRUE = 0x4004,
        AE_CTRL_FALSE = 0x4005,
        AE_CTRL_DEPTH = 0x4006,
        AE_CTRL_END = 0x4007,
        AE_CTRL_TRANSFER = 0x4008,
        AE_CTRL_BREAK = 0x4009,
        AE_CTRL_CONTINUE = 0x400A,
        AE_CTRL_PARSE_CONTINUE = 0x400B,
        AE_CTRL_PARSE_PENDING = 0x400C,
    }

    #[derive(Debug, Copy, Clone, PartialEq, Eq)]
    #[repr(transparent)]
    pub struct AcpiStatus(Result<(), AcpiError>);

    impl AcpiStatus {
        pub const fn ok() -> AcpiStatus {
            AcpiStatus(Ok(()))
        }

        pub fn err(v: AcpiError) -> AcpiStatus {
            AcpiStatus(Err(v))
        }
    }

    impl Deref for AcpiStatus {
        type Target = Result<(), AcpiError>;

        fn deref(&self) -> &Self::Target {
            &self.0
        }
    }

    impl DerefMut for AcpiStatus {
        fn deref_mut(&mut self) -> &mut Self::Target {
            &mut self.0
        }
    }

    impl From<ACPI_STATUS> for AcpiStatus {
        fn from(val: ACPI_STATUS) -> AcpiStatus {
            if val == 0 {
                AcpiStatus(Ok(()))
            } else {
                AcpiStatus(Err(AcpiError::try_from(val).unwrap_or(AcpiError::AE_ERROR)))
            }
        }
    }

    impl From<AcpiStatus> for ACPI_STATUS {
        fn from(val: AcpiStatus) -> ACPI_STATUS {
            if let Err(err_code) = val.0 {
                err_code.into()
            } else {
                AE_OK
            }
        }
    }

    impl From<AcpiStatus> for Result<(), AcpiError> {
        fn from(val: AcpiStatus) -> Result<(), AcpiError> {
            val.0
        }
    }

    impl Try for AcpiStatus {
        type Ok = ();
        type Error = AcpiError;

        fn into_result(self) -> Result<(), AcpiError> {
            self.0
        }

        fn from_ok(_: ()) -> AcpiStatus {
            AcpiStatus(Ok(()))
        }

        fn from_error(v: AcpiError) -> AcpiStatus {
            AcpiStatus(Err(v))
        }
    }
}

pub mod madt;
pub mod mcfg;

#[allow(non_snake_case)]
pub mod os_services;

use bindings::*;

type AcpiResult<T> = Result<T, AcpiError>;

pub fn initialize() -> AcpiResult<()> {
    println!("acpica: initializing ACPI...");

    os_services::init_alloc_map();
    os_services::init_isr_map();

    unsafe {
        AcpiStatus::from(AcpiInitializeSubsystem()).expect("AcpiInitializeSubsystem");

        AcpiStatus::from(AcpiInitializeTables(ptr::null_mut(), 16, 0))
            .expect("AcpiInitializeTables");

        AcpiStatus::from(AcpiLoadTables()).expect("AcpiLoadTables");

        AcpiStatus::from(AcpiEnableSubsystem(ACPI_FULL_INITIALIZATION))
            .expect("AcpiEnableSubsystem");

        AcpiStatus::from(AcpiInitializeObjects(ACPI_FULL_INITIALIZATION))
            .expect("AcpiInitializeObjects");
    }

    println!("acpica: initialization complete");

    Ok(())
}

fn get_table(signature: &[u8], instance: u32) -> AcpiResult<usize> {
    if signature.len() != 4 {
        return Err(AcpiError::AE_BAD_PARAMETER);
    }

    unsafe {
        let mut raw_header: *mut ACPI_TABLE_HEADER = ptr::null_mut();
        let sig_ptr: *const u8 = signature.as_ptr();

        AcpiStatus::from(AcpiGetTable(
            mem::transmute(sig_ptr),
            instance,
            &mut raw_header,
        ))?;

        if raw_header.is_null() {
            return Err(AcpiError::AE_NOT_FOUND);
        }

        Ok(raw_header as usize)
    }
}
