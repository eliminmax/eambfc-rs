// SPDX-FileCopyrightText: 2024 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use std::fmt::Debug;
use std::io::Read;

pub fn to_ir<T: Read + Debug>(file: T) -> Vec<u8> {
    todo!("to_ir({:?})", file);
}
