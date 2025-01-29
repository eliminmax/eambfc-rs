<!-- vim: cc=
SPDX-FileCopyrightText: 2025 Eli Array Minkoff

SPDX-License-Identifier: 0BSD
-->

# About these binaries

These binaries are adapted from [my tiny-clear-elf project](https://github.com/eliminmax/tiny-clear-elf)

They each consist of a 64-bit ELF header, a 56-bit Program Header Table entry, then the code to execute the exit(0) syscall, and nothing else.

The write-ups in the tiny-clear-elf repository explain how the original versions of these binaries worked.

The original versions printed a 10-byte ANSI escape sequence, and the code for the write system call that printed that has been removed, as has the escape sequence itself. The p_filesz and p_memsz program header fields have been adjusted for the new smaller size. Other than that, the original write-ups apply.

I was trying to figure out a way to check for executable support without needing to ship these, but working within the cargo build system, nothing as simple as just stripping out the `write` system call in a hex editor seemed available.
