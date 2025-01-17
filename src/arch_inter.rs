// SPDX-FileCopyrightText: 2024 - 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use super::elf_tools::{EIData, ELFArch};
use super::err::BFCompileError;

pub type FailableInstrEncoding = Result<(), BFCompileError>;
pub trait ArchInter
where
    <Self as ArchInter>::RegType: Copy,
{
    type RegType;
    const JUMP_SIZE: usize;
    const REGISTERS: Registers<Self::RegType>;
    const SC_NUMS: SyscallNums;
    const ARCH: ELFArch;
    const E_FLAGS: u32;
    const EI_DATA: EIData;
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
    fn add_reg(code_buf: &mut Vec<u8>, reg: Self::RegType, imm: i64) -> FailableInstrEncoding;
    fn add_byte(code_buf: &mut Vec<u8>, reg: Self::RegType, imm: i8);
    fn sub_reg(code_buf: &mut Vec<u8>, reg: Self::RegType, imm: i64) -> FailableInstrEncoding;
    fn sub_byte(code_buf: &mut Vec<u8>, reg: Self::RegType, imm: i8);
    fn zero_byte(code_buf: &mut Vec<u8>, reg: Self::RegType);
}

#[derive(Debug)]
pub struct Registers<R: Copy + Clone> {
    pub sc_num: R,
    pub arg1: R,
    pub arg2: R,
    pub arg3: R,
    pub bf_ptr: R,
}

#[derive(Debug)]
pub struct SyscallNums {
    pub read: i64,
    pub write: i64,
    pub exit: i64,
}
