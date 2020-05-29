use alloc_crate::alloc;
use alloc_crate::alloc::Layout;
use alloc_crate::boxed::Box;
use alloc_crate::string::String;
use alloc_crate::vec::Vec;
use core::convert::TryFrom;
use core::fmt;
use core::fmt::Debug;
use core::mem;
use core::ops::Deref;
use core::ptr;
use core::slice;
use core::str;

use num_enum::{TryFromPrimitive, TryFromPrimitiveError};

use super::bindings::*;
use super::{AcpiResult, AcpiStatus, AE_OK};

#[derive(Debug, Copy, Clone)]
pub enum ParseFailure {
    InvalidResourceType(TryFromPrimitiveError<AcpiResourceType>),
    InvalidIOAddressDecode(TryFromPrimitiveError<IOAddressDecode>),
    InvalidTriggerMode(TryFromPrimitiveError<TriggerMode>),
    InvalidPolarity(TryFromPrimitiveError<Polarity>),
    InvalidMemoryCacheMode(TryFromPrimitiveError<MemoryCacheMode>),
    InvalidAcceptableIORange(TryFromPrimitiveError<AcceptableIORange>),
    InvalidDMAType(TryFromPrimitiveError<DMAType>),
    InvalidDMATransferType(TryFromPrimitiveError<DMATransferType>),
    InvalidSDFPriority(TryFromPrimitiveError<SDFPriority>),
    InvalidAddressType(TryFromPrimitiveError<AddressType>),
    InvalidAddressDecode(TryFromPrimitiveError<AddressDecode>),
    InvalidMemoryRangeType(TryFromPrimitiveError<MemoryRangeType>),
    InvalidResourceMode(TryFromPrimitiveError<ResourceMode>),
    InvalidDMATransferWidth(TryFromPrimitiveError<FixedDMATransferWidth>),
    InvalidAddressSpaceID(TryFromPrimitiveError<AddressSpaceID>),
    InvalidRegisterAccessSize(TryFromPrimitiveError<RegisterAccessSize>),
    InvalidBooleanFlag((&'static str, u8)),
    InvalidStringLength(usize),
    InvalidStringEncoding(str::Utf8Error),
    InvalidDMAChannel(u8),
    WrongResourceType(AcpiResourceType),
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, TryFromPrimitive)]
#[repr(u32)]
pub enum AcpiResourceType {
    Irq = 0,
    Dma = 1,
    StartDependent = 2,
    EndDependent = 3,
    Io = 4,
    FixedIo = 5,
    Vendor = 6,
    EndTag = 7,
    Memory24 = 8,
    Memory32 = 9,
    FixedMemory32 = 10,
    Address16 = 11,
    Address32 = 12,
    Address64 = 13,
    ExtendedAddress64 = 14,
    ExtendedIrq = 15,
    GenericRegister = 16,
    Gpio = 17,             // TODO: implement
    FixedDma = 18,         //
    SerialBus = 19,        // TODO: implement
    PinFunction = 20,      // TODO: implement
    PinConfig = 21,        // TODO: implement
    PinGroup = 22,         // TODO: implement
    PinGroupFunction = 23, // TODO: implement
    PinGroupConfig = 24,   // TODO: implement
}

impl AcpiResourceType {
    fn parse(value: u32) -> Result<AcpiResourceType, ParseFailure> {
        AcpiResourceType::try_from(value).map_err(ParseFailure::InvalidResourceType)
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, TryFromPrimitive)]
#[repr(u8)]
/// I/O port descriptor decode mode
pub enum IOAddressDecode {
    TenBit = 0x00,
    SixteenBit = 0x01,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, TryFromPrimitive)]
#[repr(u8)]
/// Interrupt triggering mode.
pub enum TriggerMode {
    LevelSensitive = 0x00,
    EdgeSensitive = 0x01,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, TryFromPrimitive)]
#[repr(u8)]
/// Interrupt triggering polarity.
pub enum Polarity {
    High = 0x00,
    Low = 0x01,
    Both = 0x02,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, TryFromPrimitive)]
#[repr(u8)]
/// Memory caching attributes.
pub enum MemoryCacheMode {
    Uncacheable = 0x00,
    Cacheable = 0x01,
    WriteCombining = 0x02,
    Prefetchable = 0x03,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, TryFromPrimitive)]
#[repr(u8)]
/// Acceptable ranges for IO ports.
pub enum AcceptableIORange {
    NonISA = 0x01,
    ISA = 0x02,
    Any = 0x03,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, TryFromPrimitive)]
#[repr(u8)]
pub enum DMAType {
    Compatibility = 0x00,
    A = 0x01,
    B = 0x02,
    F = 0x03,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, TryFromPrimitive)]
#[repr(u8)]
pub enum DMATransferType {
    Eight = 0x00,
    Both = 0x01,
    Sixteen = 0x02,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, TryFromPrimitive)]
#[repr(u8)]
pub enum FixedDMATransferWidth {
    Width8 = 0,
    Width16 = 1,
    Width32 = 2,
    Width64 = 3,
    Width128 = 4,
    Width256 = 5,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, TryFromPrimitive)]
#[repr(u8)]
pub enum SDFPriority {
    Good = 0x00,
    Acceptable = 0x01,
    SubOptimal = 0x02,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, TryFromPrimitive)]
#[repr(u8)]
pub enum AddressType {
    Memory = 0x00,
    IO = 0x01,
    BusNumber = 0x02,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, TryFromPrimitive)]
#[repr(u8)]
pub enum MemoryRangeType {
    Default = 0,
    Reserved = 1,
    ACPI = 2,
    NVS = 3,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, TryFromPrimitive)]
#[repr(u8)]
pub enum AddressDecode {
    Positive = 0x00,
    Subtractive = 0x01,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, TryFromPrimitive)]
#[repr(u8)]
pub enum AddressSpaceID {
    Memory = 0x00,
    IO = 0x01,
    PCIConfig = 0x02,
    Embedded = 0x03,
    SMBus = 0x04,
    SystemCMOS = 0x05,
    PCIBarTarget = 0x06,
    IPMI = 0x07,
    GPIO = 0x08,
    GenericSerialBus = 0x09,
    PCC = 0x0A,
    FunctionalFixedHardware = 0x7F,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, TryFromPrimitive)]
#[repr(u8)]
pub enum RegisterAccessSize {
    Undefined = 0x00,
    Byte = 0x01,
    Word = 0x02,
    Dword = 0x03,
    QWord = 0x04,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, TryFromPrimitive)]
#[repr(u8)]
pub enum ResourceMode {
    Producer = 0x00,
    Consumer = 0x01,
}

macro_rules! parse_func {
    ($parse_type:ty, $failure_type:path) => {
        impl $parse_type {
            fn parse(value: u8) -> Result<$parse_type, ParseFailure> {
                <$parse_type>::try_from(value).map_err($failure_type)
            }
        }
    };
}

parse_func!(IOAddressDecode, ParseFailure::InvalidIOAddressDecode);
parse_func!(TriggerMode, ParseFailure::InvalidTriggerMode);
parse_func!(Polarity, ParseFailure::InvalidPolarity);
parse_func!(MemoryCacheMode, ParseFailure::InvalidMemoryCacheMode);
parse_func!(AcceptableIORange, ParseFailure::InvalidAcceptableIORange);
parse_func!(DMAType, ParseFailure::InvalidDMAType);
parse_func!(DMATransferType, ParseFailure::InvalidDMATransferType);
parse_func!(FixedDMATransferWidth, ParseFailure::InvalidDMATransferWidth);
parse_func!(SDFPriority, ParseFailure::InvalidSDFPriority);
parse_func!(AddressType, ParseFailure::InvalidAddressType);
parse_func!(MemoryRangeType, ParseFailure::InvalidMemoryRangeType);
parse_func!(AddressDecode, ParseFailure::InvalidAddressDecode);
parse_func!(AddressSpaceID, ParseFailure::InvalidAddressSpaceID);
parse_func!(RegisterAccessSize, ParseFailure::InvalidRegisterAccessSize);
parse_func!(ResourceMode, ParseFailure::InvalidResourceMode);

fn parse_bool(value: u8, field_name: &'static str) -> Result<bool, ParseFailure> {
    match value {
        0 => Ok(false),
        1 => Ok(true),
        _ => Err(ParseFailure::InvalidBooleanFlag((field_name, value))),
    }
}

pub trait AcpiResource: Sized {
    fn parse(data: &ResourceBox) -> Result<Self, ParseFailure>;
    fn resource_type() -> AcpiResourceType;
}

#[derive(Debug, Clone)]
pub struct Irq {
    pub triggering: TriggerMode,
    pub polarity: Polarity,
    pub sharable: bool,
    pub wake_capable: bool,
    pub interrupts: Vec<u8>,
}

impl AcpiResource for Irq {
    fn parse(data: &ResourceBox) -> Result<Irq, ParseFailure> {
        let irq_field = unsafe { &data.Irq };
        let triggering = TriggerMode::parse(irq_field.Triggering)?;
        let polarity = Polarity::parse(irq_field.Polarity)?;
        let sharable = parse_bool(irq_field.Shareable, "sharable")?;
        let wake_capable = parse_bool(irq_field.WakeCapable, "wake_capable")?;
        let count = irq_field.InterruptCount as usize;
        let ints: &[u8] = data.fix_slice(count, &irq_field.Interrupts);

        Ok(Irq {
            triggering,
            polarity,
            sharable,
            wake_capable,
            interrupts: ints.iter().copied().collect(),
        })
    }

    fn resource_type() -> AcpiResourceType {
        AcpiResourceType::Irq
    }
}

#[derive(Debug, Clone)]
pub struct Dma {
    pub dma_type: DMAType,
    pub bus_master: bool,
    pub transfer_type: DMATransferType,
    pub channels: Vec<u8>,
}

impl AcpiResource for Dma {
    fn parse(data: &ResourceBox) -> Result<Dma, ParseFailure> {
        let field = unsafe { &data.Dma };
        let dma_type = DMAType::parse(field.Type)?;
        let transfer_type = DMATransferType::parse(field.Transfer)?;
        let bus_master = parse_bool(field.BusMaster, "bus_master")?;
        let count = field.ChannelCount as usize;
        let chs: &[u8] = data.fix_slice(count, &field.Channels);

        Ok(Dma {
            dma_type,
            bus_master,
            transfer_type,
            channels: chs.iter().copied().collect(),
        })
    }

    fn resource_type() -> AcpiResourceType {
        AcpiResourceType::Dma
    }
}

#[derive(Debug, Copy, Clone)]
pub struct StartDependentFunctions {
    pub compatibility: SDFPriority,
    pub perf_robustness: SDFPriority,
}

impl AcpiResource for StartDependentFunctions {
    fn parse(data: &ResourceBox) -> Result<StartDependentFunctions, ParseFailure> {
        let field = unsafe { &data.StartDpf };

        Ok(StartDependentFunctions {
            compatibility: SDFPriority::parse(field.CompatibilityPriority)?,
            perf_robustness: SDFPriority::parse(field.PerformanceRobustness)?,
        })
    }

    fn resource_type() -> AcpiResourceType {
        AcpiResourceType::StartDependent
    }
}

#[derive(Debug, Copy, Clone)]
pub struct EndDependentFunctions();

impl AcpiResource for EndDependentFunctions {
    fn parse(_: &ResourceBox) -> Result<EndDependentFunctions, ParseFailure> {
        Ok(EndDependentFunctions())
    }

    fn resource_type() -> AcpiResourceType {
        AcpiResourceType::EndDependent
    }
}

#[derive(Debug, Copy, Clone)]
pub struct Io {
    pub decode: IOAddressDecode,
    pub alignment: u8,
    pub length: u8,
    pub min: u16,
    pub max: u16,
}

impl AcpiResource for Io {
    fn parse(data: &ResourceBox) -> Result<Io, ParseFailure> {
        let field = unsafe { &data.Io };

        Ok(Io {
            decode: IOAddressDecode::parse(field.IoDecode)?,
            alignment: field.Alignment,
            length: field.AddressLength,
            min: field.Minimum,
            max: field.Maximum,
        })
    }

    fn resource_type() -> AcpiResourceType {
        AcpiResourceType::Io
    }
}

#[derive(Debug, Copy, Clone)]
pub struct FixedIo {
    address: u16,
    length: u8,
}

impl AcpiResource for FixedIo {
    fn parse(data: &ResourceBox) -> Result<FixedIo, ParseFailure> {
        let field = unsafe { &data.FixedIo };

        Ok(FixedIo {
            address: field.Address,
            length: field.AddressLength,
        })
    }

    fn resource_type() -> AcpiResourceType {
        AcpiResourceType::FixedIo
    }
}

#[derive(Debug, Copy, Clone)]
pub struct FixedDma {
    request_lines: u16,
    channels: u16,
    width: FixedDMATransferWidth,
}

impl AcpiResource for FixedDma {
    fn parse(data: &ResourceBox) -> Result<FixedDma, ParseFailure> {
        let field = unsafe { &data.FixedDma };

        Ok(FixedDma {
            request_lines: field.RequestLines,
            channels: field.Channels,
            width: FixedDMATransferWidth::parse(field.Width)?,
        })
    }

    fn resource_type() -> AcpiResourceType {
        AcpiResourceType::FixedDma
    }
}

#[derive(Debug, Clone)]
pub struct Vendor {
    data: Box<[u8]>,
}

impl AcpiResource for Vendor {
    fn parse(data: &ResourceBox) -> Result<Vendor, ParseFailure> {
        let field = unsafe { &data.Vendor };
        let data: &[u8] = data.fix_slice(field.ByteLength as usize, &field.ByteData);

        Ok(Vendor {
            data: Box::from(data.iter().copied().collect::<Vec<u8>>()),
        })
    }

    fn resource_type() -> AcpiResourceType {
        AcpiResourceType::Vendor
    }
}

#[derive(Debug, Copy, Clone)]
pub struct EndTag {
    pub checksum: u8,
}

impl AcpiResource for EndTag {
    fn parse(data: &ResourceBox) -> Result<EndTag, ParseFailure> {
        let field = unsafe { &data.EndTag };

        Ok(EndTag {
            checksum: field.Checksum,
        })
    }

    fn resource_type() -> AcpiResourceType {
        AcpiResourceType::EndTag
    }
}

#[derive(Debug, Copy, Clone)]
pub struct Memory24 {
    pub writeable: bool,
    pub min: u16,
    pub max: u16,
    pub alignment: u16,
    pub length: usize,
}

impl AcpiResource for Memory24 {
    fn parse(data: &ResourceBox) -> Result<Memory24, ParseFailure> {
        let field = unsafe { &data.Memory24 };

        Ok(Memory24 {
            writeable: parse_bool(field.WriteProtect, "writeable")?,
            min: field.Minimum,
            max: field.Maximum,
            alignment: field.Alignment,
            length: (field.AddressLength as usize) * 256,
        })
    }

    fn resource_type() -> AcpiResourceType {
        AcpiResourceType::Memory24
    }
}

#[derive(Debug, Copy, Clone)]
pub struct Memory32 {
    pub writeable: bool,
    pub min: u32,
    pub max: u32,
    pub alignment: u32,
    pub length: usize,
}

impl AcpiResource for Memory32 {
    fn parse(data: &ResourceBox) -> Result<Memory32, ParseFailure> {
        let field = unsafe { &data.Memory32 };

        Ok(Memory32 {
            writeable: parse_bool(field.WriteProtect, "writeable")?,
            min: field.Minimum,
            max: field.Maximum,
            alignment: field.Alignment,
            length: field.AddressLength as usize,
        })
    }

    fn resource_type() -> AcpiResourceType {
        AcpiResourceType::Memory32
    }
}

#[derive(Debug, Copy, Clone)]
pub struct FixedMemory32 {
    pub writeable: bool,
    pub address: u32,
    pub length: usize,
}

impl AcpiResource for FixedMemory32 {
    fn parse(data: &ResourceBox) -> Result<FixedMemory32, ParseFailure> {
        let field = unsafe { &data.FixedMemory32 };

        Ok(FixedMemory32 {
            writeable: parse_bool(field.WriteProtect, "writeable")?,
            address: field.Address,
            length: field.AddressLength as usize,
        })
    }

    fn resource_type() -> AcpiResourceType {
        AcpiResourceType::FixedMemory32
    }
}

fn convert_string_ptr(len: u16, raw_ptr: *mut cty::c_char) -> Result<String, ParseFailure> {
    let len = len as usize;
    if len == 0 {
        return Err(ParseFailure::InvalidStringLength(len));
    }

    unsafe {
        let data = raw_ptr as *const u8;
        let byte_slice = slice::from_raw_parts(data, len);
        let str_slice = match str::from_utf8(byte_slice) {
            Ok(s) => s,
            Err(e) => return Err(ParseFailure::InvalidStringEncoding(e)),
        };

        Ok(String::from(str_slice))
    }
}

fn parse_label(label: &ACPI_RESOURCE_LABEL) -> Result<String, ParseFailure> {
    convert_string_ptr(label.StringLength, label.StringPtr)
}

#[derive(Debug, Clone)]
pub struct ResourceSource {
    pub index: Option<u8>,
    pub string: String,
}

impl ResourceSource {
    fn parse(data: &ACPI_RESOURCE_SOURCE) -> Result<ResourceSource, ParseFailure> {
        if data.StringLength == 0 {
            Ok(ResourceSource {
                index: None,
                string: String::new(),
            })
        } else {
            Ok(ResourceSource {
                index: Some(data.Index),
                string: convert_string_ptr(data.StringLength, data.StringPtr)?,
            })
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct MemoryAttributes {
    pub writeable: bool,
    pub caching: MemoryCacheMode,
    pub range_type: MemoryRangeType,
    pub translated: bool,
}

#[derive(Debug, Copy, Clone)]
pub struct IOAttributes {
    pub sparse_translation: bool,
    pub translated: bool,
    pub range: AcceptableIORange,
}

#[derive(Debug, Copy, Clone)]
pub enum AddressAttributes {
    Memory(MemoryAttributes),
    IO(IOAttributes),
    BusNumber,
}

#[derive(Debug, Copy, Clone)]
pub struct AddressData<T> {
    pub granularity: T,
    pub min: T,
    pub max: T,
    pub offset: T,
    pub length: T,
}

macro_rules! parse_address_attrs {
    ($src:expr) => {{
        let rsc_type = AddressType::parse($src.ResourceType)?;
        match rsc_type {
            AddressType::BusNumber => AddressAttributes::BusNumber,
            AddressType::Memory => {
                let subfield = unsafe { &$src.Info.Mem };
                AddressAttributes::Memory(MemoryAttributes {
                    writeable: parse_bool(subfield.WriteProtect, "writeable")?,
                    caching: MemoryCacheMode::parse(subfield.Caching)?,
                    range_type: MemoryRangeType::parse(subfield.RangeType)?,
                    translated: parse_bool(subfield.Translation, "translated")?,
                })
            }
            AddressType::IO => {
                let subfield = unsafe { &$src.Info.Io };
                AddressAttributes::IO(IOAttributes {
                    range: AcceptableIORange::parse(subfield.RangeType)?,
                    translated: parse_bool(subfield.Translation, "translated")?,
                    sparse_translation: parse_bool(subfield.TranslationType, "sparse_translation")?,
                })
            }
        }
    }};
}

macro_rules! parse_address_data {
    ($src:expr) => {
        AddressData {
            granularity: $src.Address.Granularity,
            min: $src.Address.Minimum,
            max: $src.Address.Maximum,
            offset: $src.Address.TranslationOffset,
            length: $src.Address.AddressLength,
        }
    };
}

macro_rules! parse_address_resource {
    ($out_type:ident, $src:expr) => {
        $out_type {
            producer_consumer: ResourceMode::parse($src.ProducerConsumer)?,
            decode: AddressDecode::parse($src.Decode)?,
            min_fixed: parse_bool($src.MinAddressFixed, "min_fixed")?,
            max_fixed: parse_bool($src.MaxAddressFixed, "nax_fixed")?,
            source: ResourceSource::parse(&$src.ResourceSource)?,
            attributes: parse_address_attrs!($src),
            address: parse_address_data!($src),
        }
    };
}

#[derive(Debug, Clone)]
pub struct Address16 {
    pub decode: AddressDecode,
    pub min_fixed: bool,
    pub max_fixed: bool,
    pub producer_consumer: ResourceMode,
    pub attributes: AddressAttributes,
    pub address: AddressData<u16>,
    pub source: ResourceSource,
}

impl AcpiResource for Address16 {
    fn parse(data: &ResourceBox) -> Result<Address16, ParseFailure> {
        let field = unsafe { &data.Address16 };
        Ok(parse_address_resource!(Address16, field))
    }

    fn resource_type() -> AcpiResourceType {
        AcpiResourceType::Address16
    }
}

#[derive(Debug, Clone)]
pub struct Address32 {
    pub decode: AddressDecode,
    pub min_fixed: bool,
    pub max_fixed: bool,
    pub producer_consumer: ResourceMode,
    pub attributes: AddressAttributes,
    pub address: AddressData<u32>,
    pub source: ResourceSource,
}

impl AcpiResource for Address32 {
    fn parse(data: &ResourceBox) -> Result<Address32, ParseFailure> {
        let field = unsafe { &data.Address32 };
        Ok(parse_address_resource!(Address32, field))
    }

    fn resource_type() -> AcpiResourceType {
        AcpiResourceType::Address32
    }
}

#[derive(Debug, Clone)]
pub struct Address64 {
    pub decode: AddressDecode,
    pub min_fixed: bool,
    pub max_fixed: bool,
    pub producer_consumer: ResourceMode,
    pub attributes: AddressAttributes,
    pub address: AddressData<u64>,
    pub source: ResourceSource,
}

impl AcpiResource for Address64 {
    fn parse(data: &ResourceBox) -> Result<Address64, ParseFailure> {
        let field = unsafe { &data.Address64 };
        Ok(parse_address_resource!(Address64, field))
    }

    fn resource_type() -> AcpiResourceType {
        AcpiResourceType::Address64
    }
}

#[derive(Debug, Clone)]
pub struct ExtendedAddress64 {
    pub decode: AddressDecode,
    pub min_fixed: bool,
    pub max_fixed: bool,
    pub producer_consumer: ResourceMode,
    pub attributes: AddressAttributes,
    pub address: AddressData<u64>,
    pub rev_id: u8,
    pub type_specific: u64,
}

impl AcpiResource for ExtendedAddress64 {
    fn parse(data: &ResourceBox) -> Result<ExtendedAddress64, ParseFailure> {
        let field = unsafe { &data.ExtAddress64 };

        Ok(ExtendedAddress64 {
            producer_consumer: ResourceMode::parse(field.ProducerConsumer)?,
            decode: AddressDecode::parse(field.Decode)?,
            min_fixed: parse_bool(field.MinAddressFixed, "min_fixed")?,
            max_fixed: parse_bool(field.MaxAddressFixed, "nax_fixed")?,
            attributes: parse_address_attrs!(field),
            address: parse_address_data!(field),
            rev_id: field.RevisionID,
            type_specific: field.TypeSpecific,
        })
    }

    fn resource_type() -> AcpiResourceType {
        AcpiResourceType::ExtendedAddress64
    }
}

#[derive(Debug, Clone)]
pub struct ExtendedIrq {
    pub producer_consumer: ResourceMode,
    pub triggering: TriggerMode,
    pub polarity: Polarity,
    pub sharable: bool,
    pub wake_capable: bool,
    pub source: ResourceSource,
    pub interrupts: Vec<u32>,
}

impl AcpiResource for ExtendedIrq {
    fn parse(data: &ResourceBox) -> Result<ExtendedIrq, ParseFailure> {
        let field = unsafe { &data.ExtendedIrq };
        let source: ACPI_RESOURCE_SOURCE = unsafe {
            let p = &field.ResourceSource as *const ACPI_RESOURCE_SOURCE;
            p.read_unaligned()
        };

        let count = field.InterruptCount as usize;
        let interrupts: Vec<u32> = unsafe {
            let base_ptr = field as *const ACPI_RESOURCE_EXTENDED_IRQ;
            let base_addr = base_ptr as usize;
            let unaligned_addr = base_addr + 6 + mem::size_of::<ACPI_RESOURCE_SOURCE>();
            let unaligned_ptr = unaligned_addr as *const u32;

            let mut v = Vec::new();
            for i in 0..count {
                v.push(unaligned_ptr.add(i).read_unaligned());
            }

            v
        };

        Ok(ExtendedIrq {
            producer_consumer: ResourceMode::parse(field.ProducerConsumer)?,
            triggering: TriggerMode::parse(field.Triggering)?,
            polarity: Polarity::parse(field.Polarity)?,
            sharable: parse_bool(field.Shareable, "sharable")?,
            wake_capable: parse_bool(field.WakeCapable, "wake_capable")?,
            source: ResourceSource::parse(&source)?,
            interrupts,
        })
    }

    fn resource_type() -> AcpiResourceType {
        AcpiResourceType::ExtendedIrq
    }
}

#[derive(Debug, Copy, Clone)]
pub struct GenericRegister {
    pub address_space: AddressSpaceID,
    pub bit_width: u8,
    pub bit_offset: u8,
    pub access_size: RegisterAccessSize,
    pub address: u64,
}

impl AcpiResource for GenericRegister {
    fn parse(data: &ResourceBox) -> Result<GenericRegister, ParseFailure> {
        let field = unsafe { &data.GenericReg };

        Ok(GenericRegister {
            address_space: AddressSpaceID::parse(field.SpaceId)?,
            bit_width: field.BitWidth,
            bit_offset: field.BitOffset,
            access_size: RegisterAccessSize::parse(field.AccessSize)?,
            address: field.Address,
        })
    }

    fn resource_type() -> AcpiResourceType {
        AcpiResourceType::GenericRegister
    }
}

#[derive(Debug)]
pub struct ResourceBox {
    resource_type: AcpiResourceType,
    data: *const ACPI_RESOURCE_DATA,
    layout: Layout,
}

impl ResourceBox {
    fn new(rsc: *const ACPI_RESOURCE) -> Result<ResourceBox, ParseFailure> {
        let align = mem::align_of::<ACPI_RESOURCE_DATA>();
        let min_sz = mem::size_of::<ACPI_RESOURCE_DATA>();

        unsafe {
            let u32_ptr = rsc as *const u32;
            let raw_type: u32 = u32_ptr.read_unaligned();
            let resource_type = AcpiResourceType::parse(raw_type)?;

            let data_len = u32_ptr.add(1).read_unaligned() as usize;
            let data_addr = (rsc as usize) + 8;
            let data_ptr = data_addr as *const u8;

            let alloc_len = if data_len < min_sz { min_sz } else { data_len };
            let layout =
                Layout::from_size_align(alloc_len, align).expect("could not create layout");

            let new_buf = alloc::alloc(layout);
            if new_buf.is_null() {
                alloc::handle_alloc_error(layout);
            }

            if alloc_len > data_len {
                // ensure all bytes of the allocation are initialized
                ptr::write_bytes(new_buf, 0, alloc_len);
            }
            // else data_len == alloc_len, so the copy will initialize everything

            // we just allocated new_buf, so it should not overlap with data_ptr
            // also, the alignment of u8 should always be 1 AFAIK
            ptr::copy_nonoverlapping(data_ptr, new_buf, data_len);
            let data = new_buf as *const ACPI_RESOURCE_DATA;

            Ok(ResourceBox {
                resource_type,
                data,
                layout,
            })
        }
    }

    fn fix_slice<'a, T>(&'a self, len: usize, broken: &'a [T]) -> &'a [T] {
        let data = broken.as_ptr();

        if cfg!(debug_assertions) {
            let len_bytes = mem::size_of::<T>() * len;
            let slice_start = data as usize;
            let slice_end = slice_start + len_bytes;

            assert!(!data.is_null());
            assert!(len_bytes <= (isize::MAX as usize));

            // check slice pointer and length alignment:
            let align = mem::align_of::<T>();

            assert_eq!(slice_start & (align - 1), 0, "slice pointer not aligned");
            assert_eq!(len_bytes & (align - 1), 0, "slice length not aligned");

            let obj_start = self.data as usize;
            let obj_end = obj_start + self.layout.size();

            // ensure slice start is in bounds:
            assert!(slice_start >= obj_start, "slice start not in bounds");
            assert!(slice_start < obj_end, "slice start not in bounds");

            // ensure slice end is in bounds:
            assert!(slice_end >= obj_start, "slice end not in bounds");
            assert!(slice_end <= obj_end, "slice end not in bounds");
        }

        unsafe { slice::from_raw_parts(data, len) }
    }

    fn expect_type(&self, rsc_type: AcpiResourceType) -> Result<(), ParseFailure> {
        if self.resource_type != rsc_type {
            Err(ParseFailure::WrongResourceType(self.resource_type))
        } else {
            Ok(())
        }
    }

    fn parse<T: AcpiResource>(&self) -> Result<T, ParseFailure> {
        self.expect_type(T::resource_type())?;
        T::parse(self)
    }
}

impl Drop for ResourceBox {
    fn drop(&mut self) {
        unsafe {
            alloc::dealloc(self.data as *mut u8, self.layout);
        }
    }
}

impl Deref for ResourceBox {
    type Target = ACPI_RESOURCE_DATA;

    fn deref(&self) -> &Self::Target {
        unsafe { &*self.data }
    }
}

pub struct Resource {
    data: ResourceBox,
}

impl Resource {
    pub fn parse<T: AcpiResource>(&self) -> Result<T, ParseFailure> {
        self.data.parse()
    }

    pub fn resource_type(&self) -> AcpiResourceType {
        self.data.resource_type
    }
}

macro_rules! debug_parse {
    ($f:expr, $src:expr, $parse_type:ident) => {
        match $src.parse::<$parse_type>() {
            Ok(parsed) => $f
                .debug_struct("Resource")
                .field("data", &parsed)
                .field("type", &$src.resource_type())
                .finish(),
            Err(e) => $f
                .debug_struct("Resource")
                .field("data", &e)
                .field("type", &$src.resource_type())
                .finish(),
        }
    };
}

impl Debug for Resource {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.data.resource_type {
            AcpiResourceType::Irq => debug_parse!(f, self, Irq),
            AcpiResourceType::Dma => debug_parse!(f, self, Dma),
            AcpiResourceType::StartDependent => debug_parse!(f, self, StartDependentFunctions),
            AcpiResourceType::EndDependent => debug_parse!(f, self, EndDependentFunctions),
            AcpiResourceType::Io => debug_parse!(f, self, Io),
            AcpiResourceType::FixedIo => debug_parse!(f, self, FixedIo),
            AcpiResourceType::Vendor => debug_parse!(f, self, Vendor),
            AcpiResourceType::EndTag => debug_parse!(f, self, EndTag),
            AcpiResourceType::Memory24 => debug_parse!(f, self, Memory24),
            AcpiResourceType::Memory32 => debug_parse!(f, self, Memory32),
            AcpiResourceType::FixedMemory32 => debug_parse!(f, self, FixedMemory32),
            AcpiResourceType::Address16 => debug_parse!(f, self, Address16),
            AcpiResourceType::Address32 => debug_parse!(f, self, Address32),
            AcpiResourceType::Address64 => debug_parse!(f, self, Address64),
            AcpiResourceType::ExtendedAddress64 => debug_parse!(f, self, ExtendedAddress64),
            AcpiResourceType::ExtendedIrq => debug_parse!(f, self, ExtendedIrq),
            AcpiResourceType::GenericRegister => debug_parse!(f, self, GenericRegister),
            AcpiResourceType::FixedDma => debug_parse!(f, self, FixedDma),
            _ => f
                .debug_struct("Resource")
                .field("data", &"<unimplemented>")
                .field("type", &self.resource_type())
                .finish(),
        }
    }
}

pub fn walk_resources(device: ACPI_HANDLE, current: bool) -> AcpiResult<Vec<Resource>> {
    let method: &'static [u8] = if current { b"_CRS\0" } else { b"_PRS\0" };

    let mut out_list: Vec<Resource> = Vec::new();
    unsafe {
        let name_ptr = method.as_ptr();
        let out_ptr = &mut out_list as *mut Vec<Resource>;

        AcpiStatus::from(AcpiWalkResources(
            device,
            mem::transmute(name_ptr),
            Some(walk_resource_callback),
            out_ptr as *mut cty::c_void,
        ))?;
    }

    Ok(out_list)
}

unsafe extern "C" fn walk_resource_callback(
    resource: *mut ACPI_RESOURCE,
    context: *mut cty::c_void,
) -> ACPI_STATUS {
    match ResourceBox::new(resource) {
        Ok(data) => {
            let out_list = &mut *(context as *mut Vec<Resource>);
            out_list.push(Resource { data });
        }
        Err(e) => {
            println!("acpi: could not parse resource ({:?})", e);
        }
    };

    AE_OK
}
