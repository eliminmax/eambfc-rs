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
 -e ext    - (only provide once) use 'ext' as the extension for
             source files instead of '.bf'
             (This program will remove this at the end of the input
             file to create the output file name)

* Optimization can make error reporting less precise.

Remaining options are treated as source file names. If they don't
end with '.bf' (or the extension specified with '-e'), the program
will raise an error.

```

## Supported platforms

Portability to other *target* platforms is outside of the scope of this project,
but it should be possible to compile properly-working `eambfc-rs` itself for any
Rust `#[cfg(unix)]` targets. If that is not the case, it's a bug.

## Disclaimer

\* *Blazingly 🔥 Fast 🚀 version may or may not actually run faster than the
original implementation. "Blazingly 🔥 Fast 🚀" is not intended to be
interpreted as any assertion of improved performance efficiency or ability to
set fires.*
