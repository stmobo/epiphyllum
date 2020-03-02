#![no_std]
#![no_main]

#[macro_use]
extern crate kernel;

#[no_mangle]
pub extern "C" fn _rust_start(boot_info: *const kernel::KernelLoaderInfo) -> ! {
    kernel::kernel_main(boot_info);
}
