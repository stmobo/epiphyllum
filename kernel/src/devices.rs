pub mod pic;
pub mod serial;
pub mod timer;
pub mod vga;

pub use serial::DEFAULT_SERIAL;
pub use vga::DEFAULT_DISPLAY;

pub use pic::io_apic;
pub use pic::local_apic;
