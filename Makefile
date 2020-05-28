.PHONY: clean bootloader run test

clean:
	rm -rf target/
	rm -rf kernel/target/
	rm -rf bootloader/target/
	xargo clean

bootloader:
	cd bootloader && RUST_TARGET_PATH=`pwd` xargo +nightly build --target x86_64-bootloader

run: bootloader grub.cfg
	cd kernel && RUST_TARGET_PATH=`pwd` xargo +nightly -Zfeatures=all run --target x86_64-epiphyllum

test: bootloader grub.cfg
	cd kernel && RUST_TARGET_PATH=`pwd` xargo +nightly -Zfeatures=all test --target x86_64-epiphyllum

clippy: bootloader grub.cfg
	cd kernel && RUST_TARGET_PATH=`pwd` xargo +nightly -Zfeatures=all clippy --target x86_64-epiphyllum 2>&1 | tee clippy.log

clippy-fix: bootloader grub.cfg
	cd kernel && RUST_TARGET_PATH=`pwd` xargo +nightly -Zfeatures=all clippy --fix -Z unstable-options --target x86_64-epiphyllum 2>&1 | tee clippy.log
