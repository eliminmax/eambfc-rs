// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use crate::err::{BFCompileError, BFErrorID};

use super::arch_inter::{ArchInter, FailableInstrEncoding, Registers, SyscallNums};
use super::elf_tools::{ByteOrdering, ElfArch};

#[derive(Debug, Clone, Copy, PartialEq)]
#[repr(u8)]
pub(in super::super) enum RiscVRegister {
    // read-only zero register
    X0 = 0,  // always-zero read-only register
    T0 = 5,  // X5, scratch register
    S0 = 8,  // X8, bf pointer register
    A0 = 10, // X10, arg1 register
    A1 = 11, // X11, arg2 register
    A2 = 12, // X12, arg3 register
    A7 = 17, // X17, syscall register
}

#[derive(Debug, Clone, Copy, PartialEq)]
#[repr(u8)]
/// Some RISC-V "C" extension compressed instructions use 3-bit rather than the normal 5-bit
/// encodings for the register operands, to save space, with the trade-off of not being able to
/// refer to all registers. This
enum RiscVCompressedRegister {
    S0 = 0b000,
    A0 = 0b010,
    A1 = 0b011,
    A2 = 0b100,
}

impl TryFrom<RiscVRegister> for RiscVCompressedRegister {
    type Error = ();
    fn try_from(value: RiscVRegister) -> Result<Self, Self::Error> {
        value.compressed_form().ok_or(())
    }
}

impl RiscVRegister {
    const fn compressed_form(self) -> Option<RiscVCompressedRegister> {
        match self {
            Self::S0 => Some(RiscVCompressedRegister::S0),
            Self::A0 => Some(RiscVCompressedRegister::A0),
            Self::A1 => Some(RiscVCompressedRegister::A1),
            Self::A2 => Some(RiscVCompressedRegister::A2),
            _ => None
        }
    }
}

pub(crate) struct RiscV64Inter;

impl ArchInter for RiscV64Inter {
    type RegType = RiscVRegister;
    const REGISTERS: Registers<RiscVRegister> = Registers {
        sc_num: RiscVRegister::A7,
        arg1: RiscVRegister::A0,
        arg2: RiscVRegister::A1,
        arg3: RiscVRegister::A2,
        bf_ptr: RiscVRegister::S0,
    };
    const SC_NUMS: SyscallNums = SyscallNums {
        read: 63,
        write: 64,
        exit: 93,
    };
    const JUMP_SIZE: usize = todo!();
    const ARCH: ElfArch = ElfArch::RiscV64;
    const E_FLAGS: u32 = 5; // EF_RISCV_RVC | EF_RISCV_FLOAT_ABI_DOUBLE (chosen to match Debian)
    const EI_DATA: ByteOrdering = ByteOrdering::LittleEndian;
    fn zero_byte(code_buf: &mut Vec<u8>, reg: Self::RegType) {
        todo!()
    }
    fn sub_byte(code_buf: &mut Vec<u8>, reg: Self::RegType, imm: u8) {
        todo!()
    }
    fn sub_reg(code_buf: &mut Vec<u8>, reg: Self::RegType, imm: u64) {
        todo!()
    }
    fn add_byte(code_buf: &mut Vec<u8>, reg: Self::RegType, imm: u8) {
        todo!()
    }
    fn add_reg(code_buf: &mut Vec<u8>, reg: Self::RegType, imm: u64) {
        todo!()
    }
    fn dec_byte(code_buf: &mut Vec<u8>, reg: Self::RegType) {
        todo!()
    }
    fn dec_reg(code_buf: &mut Vec<u8>, reg: Self::RegType) {
        todo!()
    }
    fn inc_byte(code_buf: &mut Vec<u8>, reg: Self::RegType) {
        todo!()
    }
    fn inc_reg(code_buf: &mut Vec<u8>, reg: Self::RegType) {
        todo!()
    }
    fn nop_loop_open(code_buf: &mut Vec<u8>) {
        todo!()
    }
    fn jump_close(
        code_buf: &mut Vec<u8>,
        reg: Self::RegType,
        offset: i64,
    ) -> FailableInstrEncoding {
        todo!()
    }
    fn jump_open(
        code_buf: &mut [u8],
        index: usize,
        reg: Self::RegType,
        offset: i64,
    ) -> FailableInstrEncoding {
        todo!()
    }
    fn syscall(code_buf: &mut Vec<u8>) {
        todo!()
    }
    fn reg_copy(code_buf: &mut Vec<u8>, dst: Self::RegType, src: Self::RegType) {
        todo!()
    }
    fn set_reg(code_buf: &mut Vec<u8>, reg: Self::RegType, imm: i64) {
        todo!()
    }
}
