use crate::asm;

use core::mem;
pub const TEST_SEED: u64 = 0x4B616E6174614368;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum TestExitStatus {
    Success = 40 >> 1,
    Failure = 42 >> 1,
}

pub fn test_exit(status: TestExitStatus) -> ! {
    unsafe {
        asm::ports::outd(0xf4, status as u32);
    }

    unreachable!();
}

pub fn test_runner(tests: &[&(&'static str, &'static str, fn())]) {
    println!("Running {} tests:", tests.len());

    for (module, name, test) in tests {
        print!("    {}::{} ...", *module, *name);
        test();
        println!(" ok");
    }

    test_exit(TestExitStatus::Success)
}

pub fn test_panic() -> ! {
    test_exit(TestExitStatus::Failure)
}
