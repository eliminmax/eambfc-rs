<!--
SPDX-FileCopyrightText: 2024 Eli Array Minkoff

SPDX-License-Identifier: 0BSD
-->

# Eli Array Minkoff's BFC (Blazingly 🔥 Fast 🚀 version)\*

I was trying to get a better understanding of C, so I wrote
[an optimizing brainfuck compiler in C](https://github.com/eliminmax/eambfc).
While working on that project, C clicked for me in a way it hadn't previously.

I have tried to learn Rust a few times, but it never clicked. I hoped that this
rewrite in Rust does the same for the language I want to love. It did.

## Current state and goals

The main goal is feature parity with the orginal C implementation, with only
`std` used - no external crates. It currently passess 21/22 of the tests created
for the original C implementation, and the one that doesn't pass is not
applicable to this implementation - the C program had a hard limit on the
maximum number of supported nested loops, configurable when building eambfc,
but the Rust rewrite supports an arbitrary number of nested loops, so it never
throws the `OVERFLOW` error that's being tested for.

I plan on making the tape-size customizable via command-line flag, rather than
with an equivalent to the `config.h` file in the C implementation, so that
different runs of `eambfc-rs` can compile with different tape sizes. Currently,
it is hard-coded to 32 KiB.

After that, I may rewrite this again in Zig, Go, or possibly Hare. Who knows?

## Disclaimer

\* *Blazingly 🔥 Fast 🚀 version may or may not actually run faster than the
original implementation. "Blazingly 🔥 Fast 🚀" is not intended to be
interpreted as any assertion of improved performance efficiency or ability to
set fires.*
