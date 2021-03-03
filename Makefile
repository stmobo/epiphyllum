.PHONY: clean bootloader run test structures-test clippy clippy-fix

BOOTLOADER_CARGO_FLAGS := -Z build-std=core,compiler_builtins -Z build-std-features=compiler-builtins-mem
KERNEL_CARGO_FLAGS := -Z build-std=core,compiler_builtins,alloc -Z build-std-features=compiler-builtins-mem

run: bootloader grub.cfg
	cargo run --bin epiphyllum $(KERNEL_CARGO_FLAGS) --target ./x86_64-epiphyllum.json

build:
	cargo build -p epiphyllum $(KERNEL_CARGO_FLAGS) --target ./x86_64-epiphyllum.json

bootloader:
	cargo build -p epiphyllum-bootloader $(BOOTLOADER_CARGO_FLAGS) --target ./x86_64-bootloader.json

structures-test:
	cargo test -p epiphyllum-structures

test: structures-test bootloader grub.cfg
	cargo test -p epiphyllum $(KERNEL_CARGO_FLAGS) --target ./x86_64-epiphyllum.json

clippy:
	cargo clippy -p epiphyllum $(KERNEL_CARGO_FLAGS) --target ./x86_64-epiphyllum.json 2>&1 | tee clippy.log

clippy-fix:
	cargo clippy -p epiphyllum $(KERNEL_CARGO_FLAGS) --fix -Z unstable-options --target ./x86_64-epiphyllum.json 2>&1 | tee clippy.log

clean:
	rm -rf target/
	rm -rf kernel/target/
	rm -rf bootloader/target/
	xargo clean
