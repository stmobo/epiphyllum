fn main() {
    println!("cargo:rerun-if-changed=src/asm/interrupt_entry.S");
    println!("cargo:rerun-if-changed=src/asm/");
    println!("cargo:rerun-if-changed=build.rs");

    cc::Build::new()
        .files(vec!["src/asm/interrupt_entry.S"])
        .pic(false)
        .debug(true)
        .flag("-g")
        .compile("kernel_asm");
}
