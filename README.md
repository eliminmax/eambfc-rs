<!--
SPDX-FileCopyrightText: 2024 Eli Array Minkoff

SPDX-License-Identifier: 0BSD
-->

# Eli Array Minkoff's BFC (Blazingly Fast Edition)

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
