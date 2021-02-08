.PHONY: clean bootloader run test

run: bootloader grub.cfg
	cargo run --bin epiphyllum --target ./x86_64-epiphyllum.json

build:
	cargo build -p epiphyllum --target ./x86_64-epiphyllum.json

bootloader:
	cargo build -p epiphyllum-bootloader --target ./x86_64-bootloader.json

test: bootloader grub.cfg
	cargo test -p epiphyllum --target ./x86_64-epiphyllum.json

clippy:
	cargo clippy -p epiphyllum --target ./x86_64-epiphyllum.json 2>&1 | tee clippy.log

clippy-fix:
	cargo clippy -p epiphyllum --fix -Z unstable-options --target ./x86_64-epiphyllum.json 2>&1 | tee clippy.log

clean:
	rm -rf target/
	rm -rf kernel/target/
	rm -rf bootloader/target/
	xargo clean
