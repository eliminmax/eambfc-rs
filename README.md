<!--
SPDX-FileCopyrightText: 2024 Eli Array Minkoff

SPDX-License-Identifier: 0BSD
-->

# Eli Array Minkoff's BFC (Rust version)\*

An optimizing compiler for brainfuck, written in Rust for Unix-like systems.

Output 64-bit ELF executables that uses Linux system calls for I/O. Currently,
it has x64_64, arm64, s390x, and riscv64 backends.

I was trying to get a better understanding of C, so I wrote
[an optimizing brainfuck compiler in C](https://github.com/eliminmax/eambfc).
While working on that project, C clicked for me in a way it hadn't previously.
I have tried to learn Rust a few times, but it never clicked. I hoped that this
rewrite in Rust does the same for the language I wanted to love. It did.

<!-- vim-markdown-toc GFM -->

* [Usage](#usage)
* [Supported platforms](#supported-platforms)
* [Building and Installing](#building-and-installing)
* [Development Process and Standards](#development-process-and-standards)
  * [Testing](#testing)
* [Dependencies](#dependencies)
* [Legal Stuff and Code Origins](#legal-stuff-and-code-origins)

<!-- vim-markdown-toc -->

## Usage

The most basic way to use `eambfc-rs` is to simply run it, passing files to
compile as command-line arguments:

```sh
eambfc-rs foo.bf
```

That will compile `foo.bf` into an ELF executable file named `foo`.

It expects brainfuck source files to use the file extension `.bf`.

If passed multiple files to compile, `eambfc-rs` will compile them in the
provided order, stopping on the first error.

Compiled files have a tape size of 8 4-KiB blocks, for a total of 32 KiB, so any
program that works with Urban Müller's original implementation's 30 KB tape
should work fine.

| option     | effect                                                   |
|------------|----------------------------------------------------------|
| `-h`       | Display basic usage information, then exit               |
| `-V`       | Display version and copyright information, then exit     |
| `-j`       | Write JSON-formatted error messages to `stdout`          |
| `-q`       | Don't write error messages to `stderr`                   |
| `-O`       | Perform basic optimizations                              |
| `-c`       | Continue to the next file instead of aborting on failure |
| `-A`       | Display info about supported targets, and exit           |
| `-k`       | Don't delete files after failed compilation              |
| `-t count` | Use `count` 4-KiB blocks instead of the default 8        |
| `-e ext`   | Use `ext` instead of `.bf` as the source extension       |
| `-a arch`  | Use the `arch` backend instead of the default            |
| `-s suf`   | Append `suf` to the ends of output filenames             |


If compiled with the `longopts` feature, the following options are the long
equivalents to the short options:

| short      | long                     |
|------------|--------------------------|
| `-h`       | `--help`                 |
| `-V`       | `--version`              |
| `-j`       | `--json`                 |
| `-q`       | `--quiet`                |
| `-O`       | `--optimize`             |
| `-c`       | `--continue`             |
| `-A`       | `--list-targets`         |
| `-k`       | `--keep-failed`          |
| `-t count` | `--tape-size=count`      |
| `-e ext`   | `--source-extension=ext` |
| `-a arch`  | `--target-arch=arch`     |
| `-s suf`   | `--output-suffix=suf`    |


## Supported platforms

Portability to non-Linux *target* platforms is outside of the scope of this
project, as Linux is unique in providing a stable syscall ABI. That said, it
should be possible to compile a properly-working build of `eambfc-rs` itself for
any fully-supported Rust target, though the test suite has non-portable
dependencies, and non-unix, non-wasm targets are not able to handle non-Unicode
arguments properly, and non-unix platforms can't mark the output binaries as
executable.

Development is done primarily on the current stable release of Rust, without any
effort to ensure compatibility with previous Rust versions, so there's no
guaranteed minimum supported Rust version beyond the stable release at the time
of the most recent commit.

## Building and Installing

```sh
# install with cargo
cargo install --path .
```

## Development Process and Standards

This rewrite was done more-or-less linearly, with no git branches other than
`main`. Originally, the function signatures from the C version's headers were
used as the basis for function declarations in Rust. As the actual
implementation began, it became clear that that would force me to fight against
Rust's semantics rather than embrace them, so a new approach was needed.

The goal was to support all of the C version's features and pass the C version's
test suite, and work on any Rust target that provides `std::os::unix`, and that
goal has been met.

Since then, I've used feature branches for large refactors or new features, and
dev branches for new versions.

### Testing

The test suite is run with `cargo test`, as is typical of Rust projects. The
tests require the `llvm_sys` crate, which has a bit of a complicated setup
process - [see its docs](https://github.com/tari/llvm-sys.rs#build-requirements)
for more info. In order for it to build properly on my system
(Debian Bookworm with `llvm-19-dev` installed), I had to create the following
`.cargo/config.toml` file:

```toml
[env]
LLVM_SYS_191_PREFIX = "/usr/lib/llvm-19"
```

(`.cargo/config.toml` is for local configuration and is not supposed to be
checked into version control, so if you need to do something similar, that's the
place to do it).

Some tests will only run if it's possible for the host system to directly run
the binaries that this compiler outputs, either because they're native, or
because there's a compaitibility layer that's automatically invoked, such as
Linux's `binfmt_misc` with QEMU binfmt support set up, or FreeBSD's
"Linuxulator" system call translation layer.

On non-`cfg(unix)` platforms, tests that use the `llvm-sys` crate to disassemble
compiled code will be skipped, as will tests that require Unix-specific
functionality. Around half of the test suite is skipped on platforms that are
both non-unix and lacking in support for the binaries compiled by `eambfc-rs`.

## Dependencies

The `longopts` feature requires the `lexopt` crate, and the

## Legal Stuff and Code Origins

`eambfc-rs` as a whole is licensed under the GNU General Public License
version 3. Some individual components of the source code, infrastructure, and
test assets are licensed under the Zero-Clause BSD license, a
public-domain-equivalent license.

Files have licensing information encoded in accordance with the REUSE
Specification, using SPDX headers to encode the copyright info in a manner that
is both human and machine readable.

Some brainfuck test programs include snippets of sample code taken from the
esolangs.org pages
[brainfuck algorithms](https://esolangs.org/wiki/Brainfuck_algorithms) and
[brainfuck constants](https://esolangs.org/wiki/Brainfuck_constants), which are
available under the CC0 public-domain-equivalent license.

One test uses a modified form of the brainfuck implementation of
[colortest](https://github.com/eliminmax/colortest), which is a different hobby
project of mine.

An algorithm to pick a RISC-V instruction sequence to set a register to an
immediate is adapted from the LLVM project.

Other than that, all content in this repository is my original work, either
created for `eambfc-rs`, or adapted from the the original `eambfc` project in C.

All licenses used in any part of this repository are in the LICENSES/ directory,
and every file has an SPDX License header identifying the license(s) it's under,
either near the top of the file, or in an associated `.license` file.
