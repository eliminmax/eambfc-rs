<!--
SPDX-FileCopyrightText: 2024 Eli Array Minkoff

SPDX-License-Identifier: 0BSD
-->

# Eli Array Minkoff's BFC (Blazingly 🔥 Fast 🚀 version)\*

I was trying to get a better understanding of C, so I wrote
[an optimizing brainfuck compiler in C](https://github.com/eliminmax/eambfc).
While working on that project, C clicked for me in a way it hadn't previously.

I have tried to learn Rust a few times, but it never clicked. I hope that this
rewrite in Rust does the same for the language I want to love.

The plan was to first do a direct rewrite - use C standard library functions,
and write more-or-less 1-to-1 translations of the functions in the C
implementation, then go back and refactor it from there into more idiomatic
Rust.

When I was working on translating the function signatures of each function from
C to Rust, I realized that I was not going to be able to make that plan work,
so I decided to re-evaluate pretty much right away.

## Current state and goals

The first goal is feature parity with the orginal C implementation, with only
the `std` and `libc` crates.

To achieve this, the first place I started was not brainfuck at all, but rather
argument parsing with the same semantics as the POSIX `getopt(3)` function in C,
and error handling with the same semantics as the C implementation of `eambfc`.

After that, I worked on the x86_64 backend.

Currently, brainfuck instructions are all compiled properly, and all
command-line flags are implemented in the custom parser, but when passed `-O`,
it will error out with an `UNIMPLEMENTED` error message rather than compile, and
the internal functionality used to optimize it is not present.

The `-k` flag is also not working properly - it should compile as much as
possible before hitting an error if `-k` is passed, but it instead creates an
empty executable file.

I plan on making the tape-size customizable via command-line flag, rather than
with an equivalent to the `config.h` file in the C implementation, so that
different runs of `eambfc-rs` can compile with different tape sizes.

After that, I may rewrite this again in Zig, Go, or possibly Hare. Who knows.


## Disclaimer

\* *Blazingly 🔥 Fast 🚀 version may or may not actually run faster than the
original implementation. "Blazingly 🔥 Fast 🚀" is not intended to be
interpreted as any assertion of improved performance efficiency or ability to
set fires.*
