<!--
SPDX-FileCopyrightText: 2024 Eli Array Minkoff

SPDX-License-Identifier: 0BSD
-->

# Eli Array Minkoff's BFC (Blazingly 🔥 Fast 🚀 version)\*

**Also check out the [Original version](https://github.com/eliminmax/eambfc),
written in C.**

An optimizing compiler for brainfuck, written in Rust for Unix-like systems.

Outputs x86\_64 ELF executables that uses Linux system calls for I/O.

I was trying to get a better understanding of C, so I wrote
[an optimizing brainfuck compiler in C](https://github.com/eliminmax/eambfc).
While working on that project, C clicked for me in a way it hadn't previously.
I have tried to learn Rust a few times, but it never clicked. I hoped that this
rewrite in Rust does the same for the language I wanted to love. It did.

## Usage

```
Usage: eambfc-rs [options] <program.bf> [<program2.bf> ...]

 -h        - display this help text and exit
 -V        - print version information and exit
 -j        - print errors in JSON format
 -q        - don't print errors unless -j was passed
 -O        - enable optimization*.
 -k        - keep files that failed to compile (for debugging)
 -c        - continue to the next file instead of quitting if a
             file fails to compile
 -t count  - allocate <count> 4-KiB blocks for the tape
             (defaults to 8 if not specified)**
 -e ext    - use 'ext' as the extension for source files instead of '.bf'
             (This program will remove this at the end of the input
             file to create the output file name)**
 -a arch   - compile for specified architecture**
 -A        - list supported architectures and exit

* Optimization can make error reporting less precise.
** -a, -t and -e can only be passed at most once each.

Remaining options are treated as source file names. If they don't
end with '.bf' (or the extension specified with '-e'), the program
will raise an error.
```

## Supported platforms

Portability to other *target* platforms is outside of the scope of this project,
but it should be possible to compile properly-working `eambfc-rs` itself for any
Rust `#[cfg(unix)]` targets. If that is not the case, it's a bug.

## Building and Installing

```sh
# install with cargo
cargo install --path .
# run test suite
cargo test
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

## Legal Stuff

`eambfc-rs` as a whole is licensed under the GNU General Public License version
3. Some individual components of the source code, infrastructure, and test
assets are licensed under the Zero-Clause BSD license,
a public-domain-equivalent license.

One test compiles a snipped of brainfuck code taken from the esolangs.org page
[brainfuck constants](https://esolangs.org/wiki/Brainfuck_constants). The
contents of that page are available under the public-domain-equivalent CC0
license.

Other than that one test, all content in this repository is my original work,
based on the original `eambfc`

All licenses used in any part of this repository are in the LICENSES/ directory,
and every file has an SPDX License header identifying the license(s) it's under,
either near the top of the file, or in an associated `.license` file.

### Disclaimer
\* *Blazingly 🔥 Fast 🚀 version may or may not actually run faster than the
original implementation. "Blazingly 🔥 Fast 🚀" is not intended to be
interpreted as any assertion of improved performance efficiency or ability to
set fires.*
