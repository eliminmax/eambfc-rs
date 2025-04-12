// SPDX-FileCopyrightText: 2024 - 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

//! This module provides types used for both the `i386` and `x86_64` backends, a function used in
//! all of their jump methods, and a macro to generate the code common to both implementations.

use crate::err::{BFCompileError, BFErrorID};
/// X86 register identifiers used within eambfc. The "RAX", "RCX", etc. identifiers are the 64-bit
/// equivalents, and use the same register IDs, but in 64-bit instructions that either are
/// identical to the 32-bit equivalent or have a REX.W prefix, so are not included in the enum
#[derive(Clone, Copy)]
#[repr(u8)]
pub(in super::super) enum X86Register {
    Eax = 0b000,
    Ecx = 0b001,
    Edx = 0b010,
    Ebx = 0b011,
    #[expect(dead_code, reason = "included for completeness's sake")]
    Esp = 0b100,
    #[expect(dead_code, reason = "included for completeness's sake")]
    Ebp = 0b101,
    Esi = 0b110,
    Edi = 0b111,
}

// many add/subtract instructions use these bit values for the upper five bits and the target
// register for the lower 3 bits to encode instructions.
#[derive(Clone, Copy)]
#[repr(u8)]
pub(super) enum ArithOp {
    Add = 0xc0,
    Sub = 0xe8,
}

#[derive(Clone, Copy)]
#[repr(u8)]
pub(super) enum ConditionCode {
    // according to B.1.4.7 Table B-10 in the Intel Manual, 0101 is not equal/not zero
    Zero = 0b0100,
    // according to B.1.4.7 Table B-10 in the Intel Manual, 0100 is equal/zero
    NotZero = 0b0101,
}

pub(super) fn conditional_jump(
    reg: X86Register,
    offset: i64,
    condition: ConditionCode,
) -> Result<[u8; 9], BFCompileError> {
    let offset_bytes = i32::try_from(offset)
        .map_err(|_| {
            BFCompileError::basic(
                BFErrorID::JumpTooLong,
                format!("{offset} is outside the range of possible 32-bit signed values"),
            )
        })?
        .to_le_bytes();
    let mut code_buf = [0; 9];
    // TEST byte ptr [reg], 0xff
    code_buf[..3].copy_from_slice(&[0xf6, reg as u8, 0xff]);
    // Jcc|tttn offset_bytes
    code_buf[3..5].copy_from_slice(&[0x0f, 0x80 | (condition as u8)]);
    code_buf[5..].copy_from_slice(&offset_bytes);
    Ok(code_buf)
}

/// This macro expands to the common parts of the `ArchInter` implementations for `x86_64` and
/// `i386`.
macro_rules! x86_common_impl {
    () => {
        type RegType = X86Register;
        const JUMP_SIZE: usize = 9;
        const E_FLAGS: u32 = 0;

        fn jump_open(
            code_buf: &mut [u8],
            index: usize,
            reg: X86Register,
            offset: i64,
        ) -> crate::compile::arch_inter::FailableInstrEncoding {
            code_buf[index..index + Self::JUMP_SIZE].copy_from_slice(
                &crate::compile::backends::x86_common::conditional_jump(
                    reg,
                    offset,
                    ConditionCode::Zero,
                )?,
            );
            Ok(())
        }

        fn jump_close(
            code_buf: &mut Vec<u8>,
            reg: X86Register,
            offset: i64,
        ) -> crate::compile::arch_inter::FailableInstrEncoding {
            code_buf.extend(crate::compile::backends::x86_common::conditional_jump(
                reg,
                offset,
                ConditionCode::NotZero,
            )?);
            Ok(())
        }

        fn pad_loop_open(code_buf: &mut Vec<u8>) {
            // UD2; times 7 NOP
            code_buf.extend([0x0f, 0x0b]);
            code_buf.extend([0x90; 7]);
        }
        fn inc_byte(code_buf: &mut Vec<u8>, reg: X86Register) {
            // INC byte [reg]
            code_buf.extend([0xfe, reg as u8]);
        }

        fn dec_byte(code_buf: &mut Vec<u8>, reg: X86Register) {
            // DEC byte [reg]
            code_buf.extend([0xfe, (reg as u8) | 8]);
        }

        fn add_byte(code_buf: &mut Vec<u8>, reg: X86Register, imm: u8) {
            // ADD byte [reg], imm8
            code_buf.extend([0x80, reg as u8, imm]);
        }

        fn sub_byte(code_buf: &mut Vec<u8>, reg: X86Register, imm: u8) {
            // SUB byte [reg], imm8
            code_buf.extend([0x80, 0x28 | (reg as u8), imm]);
        }

        fn zero_byte(code_buf: &mut Vec<u8>, reg: X86Register) {
            // MOV byte [reg], 0
            code_buf.extend([0xc6, reg as u8, 0x00]);
        }
    };
}

pub(super) use x86_common_impl;

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_jump_too_large_error() {
        let err = conditional_jump(
            X86Register::Edx,
            i64::from(i32::MAX) + 1,
            ConditionCode::Zero,
        )
        .unwrap_err();
        assert_eq!(err.error_id(), BFErrorID::JumpTooLong);
    }
}
