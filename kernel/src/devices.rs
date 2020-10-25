pub mod ide;
pub mod pci;
pub mod pic;
pub mod serial;
pub mod timer;
pub mod vga;

pub use pic::io_apic;
pub use pic::local_apic;
