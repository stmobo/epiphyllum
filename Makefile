.PHONY: clean bootloader kernel iso run

clean:
	rm -rf target/

bootloader: 
	cd bootloader && RUST_TARGET_PATH=`pwd` xargo build --target x86_64-bootloader

kernel: 
	cd kernel && RUST_TARGET_PATH=`pwd` xargo build --target x86_64-epiphyllum

iso: bootloader kernel grub.cfg
	mkdir -p target/iso/boot/grub
	cp grub.cfg target/iso/boot/grub
	cp target/x86_64-bootloader/debug/epiphyllum-bootloader target/iso/boot/epiphyllum-bootloader
	cp target/x86_64-epiphyllum/debug/epiphyllum target/iso/boot/epiphyllum
	grub-mkrescue -o target/boot.iso target/iso

run: iso
	qemu-system-x86_64 -cdrom target/boot.iso -device isa-debug-exit,iobase=0xf4,iosize=0x04 -s -no-reboot -d int,cpu_reset
