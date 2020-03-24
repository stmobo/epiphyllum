#![cfg_attr(not(test), no_std)]
#![cfg_attr(not(test), no_main)]

#[cfg(not(test))]
extern crate kernel;

#[cfg(not(test))]
#[no_mangle]
pub extern "C" fn _rust_start(boot_info: *const kernel::KernelLoaderInfo) -> ! {
    kernel::kernel_main(boot_info);
}

#[cfg(test)]
fn main() {}
