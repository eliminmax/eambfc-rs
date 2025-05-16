// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD
//
#![allow(
    clippy::cast_possible_truncation,
    reason = "This file is a more explicit approach, for intentionally-truncating casts"
)]

pub(crate) trait TruncateU32 {
    fn truncate_u32(self) -> u32;
}

pub(crate) trait TruncateU16 {
    fn truncate_u16(self) -> u16;
}

pub(crate) trait TruncateU8 {
    fn truncate_u8(self) -> u8;
}

impl TruncateU32 for u64 {
    fn truncate_u32(self) -> u32 {
        self as u32
    }
}

impl TruncateU16 for u32 {
    fn truncate_u16(self) -> u16 {
        self as u16
    }
}

impl TruncateU8 for u16 {
    fn truncate_u8(self) -> u8 {
        self as u8
    }
}

impl<T: TruncateU32> TruncateU16 for T {
    fn truncate_u16(self) -> u16 {
        self.truncate_u32() as u16
    }
}

impl<T: TruncateU16> TruncateU8 for T {
    fn truncate_u8(self) -> u8 {
        self.truncate_u16() as u8
    }
}

pub(crate) trait TruncateI32 {
    fn truncate_i32(self) -> i32;
}

pub(crate) trait TruncateI16 {
    fn truncate_i16(self) -> i16;
}

pub(crate) trait TruncateI8 {
    fn truncate_i8(self) -> i8;
}

impl TruncateI32 for i64 {
    fn truncate_i32(self) -> i32 {
        self as i32
    }
}

impl TruncateI16 for i32 {
    fn truncate_i16(self) -> i16 {
        self as i16
    }
}

impl TruncateI8 for i16 {
    fn truncate_i8(self) -> i8 {
        self as i8
    }
}

impl<T: TruncateI32> TruncateI16 for T {
    fn truncate_i16(self) -> i16 {
        self.truncate_i32() as i16
    }
}

impl<T: TruncateI16> TruncateI8 for T {
    fn truncate_i8(self) -> i8 {
        self.truncate_i16() as i8
    }
}

#[allow(clippy::unreadable_literal, reason = "0xdeadbeef and 0xbadf00d are readable")]
#[cfg(test)]
mod tests {
    const STARTING_U64: u64 = 0xbadf00d_deadbeef;
    const STARTING_I64: i64 = STARTING_U64.cast_signed();

    const STARTING_U32: u32 = 0xbadf00d;
    const STARTING_I32: i32 = STARTING_U32.cast_signed();

    const STARTING_U16: u16 = 0xdead;
    const STARTING_I16: i16 = STARTING_U16.cast_signed();
    use super::*;

    #[test]
    fn test_truncate() {

        assert_eq!(STARTING_U64.truncate_u32(), 0xdeadbeef);
        assert_eq!(STARTING_U64.truncate_u16(), 0xbeef);
        assert_eq!(STARTING_U64.truncate_u8(), 0xef);

        assert_eq!(STARTING_U32.truncate_u16(), 0xf00d);
        assert_eq!(STARTING_U32.truncate_u8(), 0x0d);

        assert_eq!(STARTING_U16.truncate_u8(), 0xad);

        assert_eq!(STARTING_I64.truncate_i32().cast_unsigned(), 0xdeadbeef);
        assert_eq!(STARTING_I64.truncate_i16().cast_unsigned(), 0xbeef);
        assert_eq!(STARTING_I64.truncate_i8().cast_unsigned(), 0xef);

        assert_eq!(STARTING_I32.truncate_i16().cast_unsigned(), 0xf00d);
        assert_eq!(STARTING_I32.truncate_i8().cast_unsigned(), 0x0d);

        assert_eq!(STARTING_I16.truncate_i8().cast_unsigned(), 0xad);
    }
}
