#!/bin/sh
# gcc reference build: the final C search from ida.c, compiled for RV32I.
# Output: asm/gcc_ref.elf (load in Ripes as an executable) and the code sizes.
set -e
F="-O2 -march=rv32i -mabi=ilp32 -msmall-data-limit=0 -ffreestanding -fno-builtin -fno-tree-loop-distribute-patterns"
riscv64-unknown-elf-gcc $F -S asm/gcc_ref.c -o asm/gcc_ref_c.s
cat asm/gcc_ref_c.s tables.s > asm/gcc_ref_all.s
riscv64-unknown-elf-gcc -march=rv32i -mabi=ilp32 -nostdlib -nostartfiles -static \
    -Wl,--no-relax -Wl,-Ttext=0 -Wl,-Tdata=0x10000000 -e _start \
    asm/gcc_ref_all.s -lgcc -o asm/gcc_ref.elf
echo "gcc reference (asm/gcc_ref.elf):"
riscv64-unknown-elf-size -A asm/gcc_ref.elf | grep -E '^\.(text|rodata) '
echo "hand-written assembly (asm/cube_cli.s):"
riscv64-unknown-elf-as -march=rv32i -mabi=ilp32 asm/cube_cli.s -o /tmp/cube_cli.o
riscv64-unknown-elf-size -A /tmp/cube_cli.o | grep -E '^\.text '
