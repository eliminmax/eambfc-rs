// SPDX-FileCopyrightText: 2024 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only
use super::err::BFCompileError;
use super::run_config::RunConfig;
use std::fs::File;

pub fn bf_compile(
    in_f: &mut File,
    out_f: &mut File,
    optimize: bool,
    rc: &RunConfig,
) -> Result<(), BFCompileError> {
    todo!("bf_compile({in_f:?}, {out_f:?}, {optimize:?}, {rc:?})",);
}
