extern crate bindgen;

use std::env;
use std::fs;
use std::path::PathBuf;
use std::process::Command;

fn main() {
    println!("cargo:rerun-if-changed=src/acpica/wrapper.h");

    println!("cargo:rerun-if-changed=src/asm/interrupt_entry.S");
    println!("cargo:rerun-if-changed=src/asm/");
    println!("cargo:rerun-if-changed=acpica/");
    println!("cargo:rerun-if-changed=build.rs");

    let mut files: Vec<PathBuf> = Vec::new();
    for entry in fs::read_dir("src/acpica/acpi").unwrap() {
        let entry: fs::DirEntry = entry.unwrap();
        let path = entry.path();

        if path.is_file() {
            println!("cargo:rerun-if-changed={}", path.to_str().unwrap());
            files.push(path);
        }
    }

    for entry in fs::read_dir("src/acpica/include/platform").unwrap() {
        let entry: fs::DirEntry = entry.unwrap();
        let path = entry.path();

        if path.is_file() {
            println!("cargo:rerun-if-changed={}", path.to_str().unwrap());
        }
    }

    let bindings = bindgen::Builder::default()
        .header("src/acpica/wrapper.h")
        .ctypes_prefix("cty")
        .use_core()
        .parse_callbacks(Box::new(bindgen::CargoCallbacks))
        .generate()
        .expect("unable to generate ACPICA bindings");

    cc::Build::new()
        .files(files)
        .pic(false)
        .debug(false)
        .include("src/acpica/include")
        .flag("-g")
        .flag("-Wno-unused-parameter")
        .flag("-ffreestanding")
        .compile("acpica");

    cc::Build::new()
        .files(vec!["src/asm/interrupt_entry.S"])
        .pic(false)
        .debug(true)
        .flag("-g")
        .compile("kernel_asm");

    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings
        .write_to_file(out_path.join("bindings.rs"))
        .expect("Couldn't write bindings!");
}
