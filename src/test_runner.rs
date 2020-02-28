use x86_64::instructions::port::Port;

const EXIT_DEVICE_IOBASE: u16 = 0xF4;

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
#[repr(u32)]
pub enum TestExitCode {
    Success = 0x10,
    Failure = 0x11,
}

pub fn exit_qemu(status: TestExitCode) {
    unsafe {
        let mut port = Port::new(EXIT_DEVICE_IOBASE);
        port.write(status as u32);
    }
}

pub fn test_runner(tests: &[&dyn Fn()]) {
    println!("Running {} tests...", tests.len());
    for test in tests {
        test();
        println!("[ok]");
    }

    exit_qemu(TestExitCode::Success);
    panic!("test runner failed to exit");
}
