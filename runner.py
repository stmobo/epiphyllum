#!/usr/bin/env python3
import sys
import os
from pathlib import Path
import shutil
import subprocess as sp

QEMU_EXPECTED_EXIT = 41
QEMU_TIMEOUT = None

ROOT = str(Path("../").resolve())
QEMU_OPTS = [
    "-cdrom",
    "target/boot.iso",
    "-device",
    "isa-debug-exit,iobase=0xf4,iosize=0x04",
    "-device",
    "pci-bridge,id=bridge0,chassis_nr=1,addr=07",
    "-device",
    "pci-bridge,id=bridge1,chassis_nr=2,addr=05",
    "-device",
    "pci-bridge,id=bridge2,bus=bridge0,chassis_nr=3,addr=02",
    "-device",
    "e1000,bus=bridge0,addr=0x3",
    "-device",
    "e1000,bus=bridge1,addr=0x4",
    "-device",
    "e1000,bus=bridge1,addr=0x5",
    "-device",
    "e1000,bus=bridge2,addr=0x1",
    "-serial",
    "stdio",
    "-cpu",
    "host",
    "-enable-kvm",
    "-s",
    "-no-reboot",
    "-no-shutdown",
    "-d",
    "cpu_reset",
]


def make_boot_iso():
    grub_cfg = Path("../grub.cfg").resolve()
    bootloader = Path(
        "../target/x86_64-bootloader/debug/epiphyllum-bootloader"
    ).resolve()
    kernel = Path(sys.argv[1]).resolve()

    target_dir = Path("../target/iso/boot").resolve()
    grub_dir = target_dir.joinpath("grub")
    grub_dir.mkdir(parents=True, exist_ok=True)

    shutil.copyfile(str(grub_cfg), str(grub_dir.joinpath("grub.cfg")))
    shutil.copyfile(str(bootloader), str(target_dir.joinpath("epiphyllum-bootloader")))
    shutil.copyfile(str(kernel), str(target_dir.joinpath("epiphyllum")))

    sp.run(["grub-mkrescue", "-o", "target/boot.iso", "target/iso"], cwd=ROOT)


def launch_qemu(is_test: bool):
    try:
        opts = QEMU_OPTS
        timeout = None

        if is_test:
            opts.extend(("-display", "none"))
            timeout = QEMU_TIMEOUT

        proc = sp.run(["qemu-system-x86_64"] + QEMU_OPTS, cwd=ROOT, timeout=timeout)
        if not is_test or proc.returncode == QEMU_EXPECTED_EXIT:
            sys.exit(0)
        else:
            sys.exit(1)
    except sp.TimeoutExpired:
        sys.exit(1)


def main():
    target_exec = Path(sys.argv[1])
    if "kernel" in target_exec.stem:
        return

    make_boot_iso()
    launch_qemu(target_exec.parts[-2] == "deps")


if __name__ == "__main__":
    main()
