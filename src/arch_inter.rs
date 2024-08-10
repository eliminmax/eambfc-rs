// SPDX-FileCopyrightText: 2024 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use super::elf_tools::{EIData, ELFArch};
use super::err::BFCompileError;

pub trait ArchInter {
    type RegType;
    fn set_reg(reg: Self::RegType, imm: i64) -> Vec<u8>;
    fn reg_copy(dst: Self::RegType, src: Self::RegType) -> Vec<u8>;
    fn syscall() -> Vec<u8>;
    fn jump_zero(reg: Self::RegType, offset: i64) -> Result<Vec<u8>, BFCompileError>;
    fn jump_not_zero(reg: Self::RegType, offset: i64) -> Result<Vec<u8>, BFCompileError>;
    fn nop_loop_open() -> Vec<u8>;
    fn inc_reg(reg: Self::RegType) -> Vec<u8>;
    fn inc_byte(reg: Self::RegType) -> Vec<u8>;
    fn dec_reg(reg: Self::RegType) -> Vec<u8>;
    fn dec_byte(reg: Self::RegType) -> Vec<u8>;
    fn add_reg(reg: Self::RegType, imm: u64) -> Result<Vec<u8>, BFCompileError>;
    fn add_byte(reg: Self::RegType, imm: i8) -> Vec<u8>;
    fn sub_reg(reg: Self::RegType, imm: u64) -> Result<Vec<u8>, BFCompileError>;
    fn sub_byte(reg: Self::RegType, imm: i8) -> Vec<u8>;
    fn zero_byte(reg: Self::RegType) -> Vec<u8>;
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
    pub sc_read: i64,
    pub sc_write: i64,
    pub sc_exit: i64,
}

#[derive(Debug)]
pub struct ArchInfo<R: Copy + Clone, I: ArchInter> {
    pub registers: Registers<R>,
    pub sc_nums: SyscallNums,
    pub jump_size: usize,
    pub em_arch: ELFArch,
    pub elfdata_byte_order: EIData,
    pub inter: I,
}
