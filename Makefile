.PHONY: clean bootloader run test

clean:
	rm -rf target/
	rm -rf kernel/target/
	rm -rf bootloader/target/
	xargo clean

bootloader:
	cargo build -p epiphyllum-bootloader --target ./x86_64-bootloader.json

build:
	cargo build -p epiphyllum --target ./x86_64-epiphyllum.json

run: bootloader grub.cfg
	cargo run --bin epiphyllum --target ./x86_64-epiphyllum.json

test: bootloader grub.cfg
	cargo test -p epiphyllum --target x86_64-epiphyllum

clippy:
	cargo clippy -p epiphyllum --target ./x86_64-epiphyllum.json 2>&1 | tee clippy.log

clippy-fix:
	cargo clippy -p epiphyllum --fix -Z unstable-options --target ./x86_64-epiphyllum.json 2>&1 | tee clippy.log
