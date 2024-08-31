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
// Other registers are not defined because they are not needed for eambfc-rs, but they go up to 31.
// 32 is a special case not relevant here.

#[derive(Debug, Copy, Clone)]
#[repr(u8)]
pub enum Arm64Register {
    X0 = 0,
    X1 = 1,
    X2 = 2,
    X8 = 8,
    X19 = 19,
}

#[derive(Debug, Copy, Clone)]
#[repr(u8)]
enum ShiftLevel {
    NoShift = 0,
    Shift16 = 1,
    Shift32 = 2,
    Shift48 = 3,
}

#[derive(Debug, PartialEq)]
#[repr(u8)]
enum MoveType {
    Keep = 0xf2,
    Zero = 0xd2,
    Invert = 0x92,
}

#[inline]
fn inject_operands(
    imm16: i16,
    shift: ShiftLevel,
    reg: Arm64Register,
    template: [u8; 4],
) -> [u8; 4] {
    [
        template[0] | reg as u8 | (imm16 << 5) as u8,
        // why does ARM's A64 not align immediate bits with byte boundries?
        template[1] | ((imm16 & 0b0000_0111_1111_1000) >> 3) as u8,
        // logic relies on unsigned bit-shifts for template[2]
        // alternatively could mask it to 0b11111 instead, but that's messier in my opinion
        template[2] | (shift as u8) << 5 | ((imm16 as u16) >> 11) as u8,
        template[3],
    ]
}

fn mov(move_type: MoveType, imm16: i16, shift: ShiftLevel, reg: Arm64Register) -> [u8; 4] {
    // depending on MoveType, it will be one of MOVK, MOVN, or MOVZ
    // bitwise not to invert imm16 if needed.
    let imm16 = if move_type == MoveType::Invert {
        !imm16
    } else {
        imm16
    };
    inject_operands(imm16, shift, reg, [0x00u8, 0x00, 0x80, move_type as u8])
}

pub struct Arm64Inter;
impl ArchInter for Arm64Inter {
    type RegType = Arm64Register;
    const JUMP_SIZE: usize = 8;

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
        // split the immediate into 4 16-bit parts - high, medium-high, medium-low, and low
        let parts: [(i16, ShiftLevel); 4] = [
            (imm as i16, ShiftLevel::NoShift),
            ((imm >> 16) as i16, ShiftLevel::Shift16),
            ((imm >> 32) as i16, ShiftLevel::Shift32),
            ((imm >> 48) as i16, ShiftLevel::Shift48),
        ];
        let mut instr_vec = Vec::<u8>::new();
        if imm < 0 {
            let mut parts = parts.iter().filter(|(imm16, _)| *imm16 != -1);
            let (lead_imm, lead_shift) = parts.next().unwrap_or(&(-1i16, ShiftLevel::NoShift));
            // MOVN reg, lead_imm << lead_shift
            instr_vec.extend(mov(MoveType::Invert, *lead_imm, *lead_shift, reg));
            parts.for_each(|(imm16, shift)| {
                // MOVK reg, imm16 << shift
                instr_vec.extend(mov(MoveType::Keep, !*imm16, *shift, reg));
            });
        } else {
            let mut parts = parts.iter().filter(|(imm16, _)| *imm16 != 0);
            let (lead_imm, lead_shift) = parts.next().unwrap_or(&(0i16, ShiftLevel::NoShift));
            // MOVZ reg, lead_imm << lead_shift
            instr_vec.extend(mov(MoveType::Zero, *lead_imm, *lead_shift, reg));
            parts.for_each(|(imm16, shift)| {
                // MOVK reg, imm16 << shift
                instr_vec.extend(mov(MoveType::Keep, *imm16, *shift, reg));
            });
        }
        instr_vec
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
        // 2 NOP instructions.
        vec![0x1fu8, 0x20, 0x03, 0xd5, 0x1f, 0x20, 0x03, 0xd5]
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

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_set_reg_simple() -> Result<(), String> {
        // the following can be set with 1 instruction each.
        assert_eq!(
            Arm64Inter::set_reg(Arm64Register::X0, 0),
            vec![0x00, 0x00, 0x80, 0xd2]
        );

        assert_eq!(
            Arm64Inter::set_reg(Arm64Register::X0, -1),
            vec![0x00, 0x00, 0x80, 0x92]
        );

        assert_eq!(
            Arm64Inter::set_reg(Arm64Register::X0, -0x100001),
            vec![0x00, 0x02, 0xa0, 0x92]
        );

        Ok(())
    }

    #[test]
    fn test_reg_multiple() -> Result<(), String> {
        assert_eq!(
            Arm64Inter::set_reg(Arm64Register::X0, 0xdeadbeef),
            vec![
                0xe0, 0xdd, 0x97, 0xd2, // MOVZ x0, 0xbeef
                0xa0, 0xd5, 0xbb, 0xf2, // MOVK x0, 0xdead, lsl #16
            ],
        );
        Ok(())
    }

    #[test]
    fn test_reg_split() -> Result<(), String> {
        assert_eq!(
            Arm64Inter::set_reg(Arm64Register::X19, 0xdead0000beef),
            vec![
                0xf3, 0xdd, 0x97, 0xd2, // MOVZ x19, 0xbeef
                0xb3, 0xd5, 0xdb, 0xf2, // MOVK x19, 0xdead, lsl #32
            ],
        );
        Ok(())
    }

    #[test]
    fn test_reg_neg() -> Result<(), String> {
        assert_eq!(
            Arm64Inter::set_reg(Arm64Register::X19, -0xdeadbeef),
            vec![
                0xf3, 0xdd, 0x97, 0x92, // MOVN x19, -0xbeef
                0xb3, 0xd5, 0xbb, 0xf2, // MOVK x19, 0xdead, lsl #16
            ],
        );
        Ok(())
    }
}
