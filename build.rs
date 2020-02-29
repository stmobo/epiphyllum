use std::env;
use std::path::Path;

fn main() {
    println!("cargo:rerun-if-changed=src/boot/protected_mode.S");
    println!("cargo:rerun-if-changed=src/boot/long_mode.S");
    println!("cargo:rerun-if-changed=src/boot/");
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=linker.ld");

    cc::Build::new()
        .files(vec![
            "src/boot/protected_mode.S",
            "src/boot/long_mode.S",
        ])
        .pic(false)
        .debug(true)
        .flag("-g")
        .compile("boot");
}