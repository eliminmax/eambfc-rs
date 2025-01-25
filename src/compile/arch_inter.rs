// SPDX-FileCopyrightText: 2024 - 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use crate::compile::elf_tools::{ByteOrdering, ElfArch};
use crate::err::BFCompileError;

pub (super) type FailableInstrEncoding = Result<(), BFCompileError>;
pub (super) trait ArchInter {
    type RegType: Copy;
    const JUMP_SIZE: usize;
    const REGISTERS: Registers<Self::RegType>;
    const SC_NUMS: SyscallNums;
    const ARCH: ElfArch;
    const E_FLAGS: u32;
    const EI_DATA: ByteOrdering;
    fn set_reg(code_buf: &mut Vec<u8>, reg: Self::RegType, imm: i64);
    fn reg_copy(code_buf: &mut Vec<u8>, dst: Self::RegType, src: Self::RegType);
    fn syscall(code_buf: &mut Vec<u8>);
    fn jump_zero(code_buf: &mut Vec<u8>, reg: Self::RegType, offset: i64) -> FailableInstrEncoding;
    fn jump_not_zero(
        code_buf: &mut Vec<u8>,
        reg: Self::RegType,
        offset: i64,
    ) -> FailableInstrEncoding;
    fn nop_loop_open(code_buf: &mut Vec<u8>);
    fn inc_reg(code_buf: &mut Vec<u8>, reg: Self::RegType);
    fn inc_byte(code_buf: &mut Vec<u8>, reg: Self::RegType);
    fn dec_reg(code_buf: &mut Vec<u8>, reg: Self::RegType);
    fn dec_byte(code_buf: &mut Vec<u8>, reg: Self::RegType);
    fn add_reg(code_buf: &mut Vec<u8>, reg: Self::RegType, imm: i64);
    fn add_byte(code_buf: &mut Vec<u8>, reg: Self::RegType, imm: i8);
    fn sub_reg(code_buf: &mut Vec<u8>, reg: Self::RegType, imm: i64);
    fn sub_byte(code_buf: &mut Vec<u8>, reg: Self::RegType, imm: i8);
    fn zero_byte(code_buf: &mut Vec<u8>, reg: Self::RegType);
}

#[derive(Debug)]
pub (super) struct Registers<R: Copy> {
    pub sc_num: R,
    pub arg1: R,
    pub arg2: R,
    pub arg3: R,
    pub bf_ptr: R,
}

#[derive(Debug)]
pub (super) struct SyscallNums {
    pub read: i64,
    pub write: i64,
    pub exit: i64,
}
