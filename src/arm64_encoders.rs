// SPDX-FileCopyrightText: 2024 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use super::arch_inter::{ArchInter, Registers, SyscallNums};
use super::compile::BFCompile;
use super::elf_tools::{EIData, ELFArch};
use super::err::BFCompileError;


// 64-bit ARM systems have 31 general-purpose registers which can be addressed in 32-bit or 64-bit
// forms. w8 is the 32-bit form for register #8, and x0 is the 64-bit form for register #0.
// X19 is the first register that the ABI guarantees to be preserved across function calls, and the
// rest are used by the Linux system call interface for the platform.

#[derive(Debug, Copy, Clone)]
#[repr(u8)]
pub enum Arm64Register {
    X0 = 0,
    X1 = 1,
    X2 = 2,
    X8 = 8,
    X19 = 19,
}

pub struct Arm64Inter;
impl ArchInter for Arm64Inter {
    type RegType = Arm64Register;
    const JUMP_SIZE: usize = 16;
    const REGISTERS: Registers<Arm64Register> = Registers {
        // Linux uses w8 for system call numbers, but w8 is just the lower 32 bits of x8.
        sc_num: Arm64Register::X8,
        arg1: Arm64Register::X0,
        arg2: Arm64Register::X1,
        arg3: Arm64Register::X2,
        bf_ptr: Arm64Register::X19,
    };
    const SC_NUMS: SyscallNums = SyscallNums {
        read: 63,
        write: 64,
        exit: 93,
    };
    const ARCH: ELFArch = ELFArch::Arm64;
    const EI_DATA: EIData = EIData::ELFDATA2LSB;
    fn set_reg(reg: Arm64Register, imm: i64) -> Vec<u8> {
        todo!("Arm64Inter::set_reg({reg:?}, {imm})")
    }
    fn reg_copy(dst: Arm64Register, src: Arm64Register) -> Vec<u8> {
        todo!("Arm64Inter::reg_copy({dst:?}, {src:?})")
    }
    fn syscall() -> Vec<u8> {
        todo!("Arm64Inter::syscall()")
    }
    fn jump_not_zero(reg: Arm64Register, offset: i64) -> Result<Vec<u8>, BFCompileError> {
        todo!("Arm64Inter::jump_not_zero({reg:?}, {offset})")
    }
    fn jump_zero(reg: Arm64Register, offset: i64) -> Result<Vec<u8>, BFCompileError> {
        todo!("Arm64Inter::jump_zero({reg:?}, {offset})")
    }
    fn nop_loop_open() -> Vec<u8> {
        todo!("Arm64Inter::nop_loop_open()")
    }
    fn inc_reg(reg: Arm64Register) -> Vec<u8> {
        todo!("inc_reg({reg:?})")
    }
    fn inc_byte(reg: Arm64Register) -> Vec<u8> {
        todo!("inc_byte({reg:?})")
    }
    fn dec_reg(reg: Arm64Register) -> Vec<u8> {
        todo!("dec_reg({reg:?})")
    }
    fn dec_byte(reg: Arm64Register) -> Vec<u8> {
        todo!("dec_byte({reg:?})")
    }
    fn add_reg(reg: Arm64Register, imm: u64) -> Result<Vec<u8>, BFCompileError> {
        todo!("add_reg({reg:?}, {imm})")
    }
    fn add_byte(reg: Arm64Register, imm: i8) -> Vec<u8> {
        todo!("add_byte({reg:?}, {imm})")
    }
    fn sub_reg(reg: Arm64Register, imm: u64) -> Result<Vec<u8>, BFCompileError> {
        todo!("sub_reg({reg:?}, {imm})")
    }
    fn sub_byte(reg: Arm64Register, imm: i8) -> Vec<u8> {
        todo!("sub_byte({reg:?}, {imm})")
    }
    fn zero_byte(reg: Arm64Register) -> Vec<u8> {
        todo!("zero_byte({reg:?})")
    }
}

impl BFCompile for Arm64Inter {}
