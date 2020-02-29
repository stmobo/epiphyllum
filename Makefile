.PHONY: cargo iso

cargo: 
	cargo xbuild

iso: cargo grub.cfg
	mkdir -p target/iso/boot/grub
	cp grub.cfg target/iso/boot/grub
	cp target/x86_64-epiphyllum/debug/epiphyllum target/iso/boot/
	grub-mkrescue -o target/boot.iso target/iso