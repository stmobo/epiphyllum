.PHONY: clean bootloader run test

clean:
	rm -rf target/
	xargo clean

bootloader:
	cd bootloader && RUST_TARGET_PATH=`pwd` xargo +nightly build --target x86_64-bootloader

run: bootloader grub.cfg
	cd kernel && RUST_TARGET_PATH=`pwd` xargo +nightly -Zfeatures=all run --target x86_64-epiphyllum

test: bootloader grub.cfg
	cd kernel && RUST_TARGET_PATH=`pwd` xargo +nightly -Zfeatures=all test --target x86_64-epiphyllum
