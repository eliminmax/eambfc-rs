// SPDX-FileCopyrightText: 2024 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

// This file contains functions that return x86_64 machine code in Vec<u8> form.

// Throughout this file, "Intel® 64 and IA-32 Architectures Software Developer Manuals" or x86_64
// machine code in general may be referenced in comments.
// For context or clarification, see the manual, which is available at no cost as of 2024-07-11.
//
// https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html

// This file uses debug_assert! statements to ensure that any time an unexpected value is passed to
// certain functions, it causes the debug builds to panic, so that they are theoretically known to
// be used safely

// the Linux kernel reads system call numbers from RAX on x86_64 systems, and reads arguments from
// RDI, RSI, RDX, R10, R8, and R9.
// None of the system calls that eambfc-r compiles to use more than 3 arguments, and the R8-R15
// registers are addressed incompatibly, so only worry the first 3 argument registers.
//
// the RBX register is preserved through system calls, so it's useful as the tape pointer.
//
// Thus, for eambfc, the registers to care about are RAX, RDI, RSI, RDX, and RBX
//
// Oversimpifying a bit, in x86 assembly, when specifying a register that is not one of R8-R15, a
// 3-bit value is used to identify it.
//
// * RAX is 000b
// * RDI is 111b
// * RSI is 110b
// * RDX is 010b
// * RBX is 011b

use super::arch_inter::{ArchInfo, EAMBFCArch, Registers, SyscallNums};
use super::elf_tools::{ELFArch, ELFDataByteOrder};
use super::err::BFCompileError;

#[derive(Debug)]
pub enum Register {
    ScNum = 0b000,
    Arg1 = 0b111,
    Arg2 = 0b110,
    Arg3 = 0b010,
    BfPtr = 0b011,
}

pub mod registers {
    use super::Register;
    pub const REG_SC_NUM: Register = Register::ScNum;
    pub const REG_ARG1: Register = Register::Arg1;
    pub const REG_ARG2: Register = Register::Arg2;
    pub const REG_ARG3: Register = Register::Arg3;
    pub const REG_BF_PTR: Register = Register::BfPtr;
}

// Numbers used for the read, write, and exit system calls on linux/x86_64
pub mod syscall_nums {
    pub const SC_READ: i64 = 0;
    pub const SC_WRITE: i64 = 1;
    pub const SC_EXIT: i64 = 60;
}

pub mod arch_info {
    use super::super::elf_tools::{ELFArch,ELFDataByteOrder};
    pub const JUMP_SIZE: usize = 9; // size of the TEST + JUMP instructions
    pub const EM_ARCH: ELFArch = ELFArch::X86_64; // EM_X86_64 (i.e. amd64)
    pub const ELFDATA_BYTE_ORDER: ELFDataByteOrder = ELFDataByteOrder::ELFDATA2LSB;
}

// macro to declare a conditional jump instruction.
// Takes a function identifier, and a 4-bit condition as defined in the Manual, specifically the
// Vol. 2D B.1.4.7 Condition Test (tttn) Field table, and generates a function which takes a
// register and a signed 64-bit offset, and if the offset is within range, returns a vector of
// bytes representing a TEST instruction that runs on the byte pointed to by the register, and
// returns a BFCompileError::Basic with the identifier "JUMP_TOO_LONG" if it's out of range. The
// reason it takes an i64 instead of an i32 is so that other architectures with different maximum
// jump lenghts could have the same interface as x86_64.
macro_rules! fn_test_jcc {
    ($fn_name:ident, $tttn:literal) => {
        fn $fn_name(reg: Register, offset: i64) -> Result<Vec<u8>, BFCompileError> {
            // Ensure only lower 4 bits of tttn are used - the const _: () mess forces the check to
            // run at compile time rather than runtime.
            const _: () = assert!($tttn & 0xf0_u8 == 0);
            let offset_bytes = TryInto::<i32>::try_into(offset)
                .map_err(|_| BFCompileError::Basic {
                    id: String::from("JUMP_TOO_LONG"),
                    msg: format!("{offset} is outside the range of possible 32-bit signed values"),
                })?
                .to_le_bytes();
            #[rustfmt::skip]
            let mut v = vec![
                // TEST byte [reg], 0xff
                0xf6_u8, reg as u8, 0xff_u8,
                // Jcc|tttn (must be followed by a 32-bit immediate jump offset)
                0x0f_u8, 0x80_u8|$tttn
            ];
            v.extend(offset_bytes);
            Ok(v)
        }
    };
}

pub struct X86_64Inter();
impl EAMBFCArch for X86_64Inter {
    type RegType = Register;
    // Chooses the shortest instrution to set a register to an immediate value, from the following:
    // XOR reg, reg
    // PUSH imm8; POP reg
    // MOV reg, imm32
    // MOV reg, imm64
    fn set_reg(reg: Register, imm: i64) -> Vec<u8> {
        let reg = reg as u8;
        match imm {
            // XOR reg, reg
            0 => vec![0x31_u8, 0xc0_u8 | (reg << 3) | reg],
            // PUSH imm8; POP reg
            i if i < i8::MAX.into() => vec![0x6a, imm as u8, 0x58 + reg],
            // MOV reg, imm32
            i if i < i32::MAX.into() => {
                let mut v = vec![0xb8 + reg];
                v.extend((i as i32).to_le_bytes());
                v
            }
            // MOV reg, imm64
            i => {
                let mut v = vec![0x48, 0xb8 + reg];
                v.extend(i.to_le_bytes());
                v
            }
        }
    }
    fn reg_copy(dst: Register, src: Register) -> Vec<u8> {
        // MOV dst, src
        vec![0x89_u8, 0xc0 + ((src as u8) << 3) + dst as u8]
    }
    fn syscall() -> Vec<u8> {
        // SYSCALL
        vec![0x0f_u8, 0x05_u8]
    }
    // according to B.1.4.7 Table B-10 in the Intel Manual, 0101 is not equal/not zero
    fn_test_jcc!(jump_not_zero, 0b0101_u8);
    // according to B.1.4.7 Table B-10 in the Intel Manual, 0100 is equal/zero
    fn_test_jcc!(jump_zero, 0b0100_u8);

    fn nop_loop_open() -> Vec<u8> {
        // times JUMP_SIZE NOP
        Vec::<u8>::from([0x90; X86_64_INTER.jump_size])
    }
    fn inc_reg(reg: Register) -> Vec<u8> {
        todo!("inc_reg({reg:?}");
    }
    fn inc_byte(reg: Register) -> Vec<u8> {
        todo!("inc_byte({reg:?}");
    }
    fn dec_reg(reg: Register) -> Vec<u8> {
        todo!("dec_reg({reg:?}");
    }
    fn dec_byte(reg: Register) -> Vec<u8> {
        todo!("dec_byte({reg:?}");
    }
}

pub const X86_64_INTER: ArchInfo<Register, X86_64Inter> = ArchInfo::<Register, X86_64Inter> {
    registers: Registers::<Register> {
        sc_num: Register::ScNum,
        arg1: Register::Arg1,
        arg2: Register::Arg2,
        arg3: Register::Arg3,
        bf_ptr: Register::BfPtr,
    },
    sc_nums: SyscallNums {
        sc_read: 0,
        sc_write: 1,
        sc_exit: 60,
    },
    jump_size: 9usize,
    em_arch: ELFArch::X86_64,
    elfdata_byte_order: ELFDataByteOrder::ELFDATA2LSB,
    inter: X86_64Inter {},
};

pub fn bfc_set_reg(reg: Register, imm: i64) -> Vec<u8> {
    let reg = reg as u8;
    match imm {
        // XOR reg, reg
        0 => vec![0x31_u8, 0xc0_u8 | (reg << 3) | reg],
        // PUSH imm8; POP reg
        i if i < i8::MAX.into() => vec![0x6a, imm as u8, 0x58 + reg],
        // MOV reg, imm32
        i if i < i32::MAX.into() => {
            let mut v = vec![0xb8 + reg];
            v.extend((i as i32).to_le_bytes());
            v
        }
        // MOV reg, imm64
        i => {
            let mut v = vec![0x48, 0xb8 + reg];
            v.extend(i.to_le_bytes());
            v
        }
    }
}

// Returns instruction that copies the contents of the register src to the register dst
pub fn bfc_reg_copy(dst: Register, src: Register) -> Vec<u8> {
    // MOV dst, src
    vec![0x89_u8, 0xc0 + ((src as u8) << 3) + (dst as u8)]
}

// Returns the syscall instruction
pub fn bfc_syscall() -> Vec<u8> {
    // SYSCALL
    vec![0x0f_u8, 0x05_u8]
}

macro_rules! fn_test_jcc {
    ($fn_name:ident, $tttn:literal) => {
        pub fn $fn_name(reg: Register, offset: i64) -> Result<Vec<u8>, BFCompileError> {
            let reg = reg as u8;
            // Ensure only lower 4 bits of tttn are used - the const _: () mess forces the check to
            // run at compile time rather than runtime.
            const _: () = assert!($tttn & 0xf0_u8 == 0);
            let offset_bytes = TryInto::<i32>::try_into(offset)
                .map_err(|_| BFCompileError::Basic {
                    id: String::from("JUMP_TOO_LONG"),
                    msg: format!("{offset} is outside the range of possible 32-bit signed values"),
                })?
                .to_le_bytes();
            #[rustfmt::skip]
            let mut v = vec![
                // TEST byte [reg], 0xff
                0xf6_u8, reg, 0xff_u8,
                // Jcc|tttn (must be followed by a 32-bit immediate jump offset)
                0x0f_u8, 0x80_u8|$tttn
            ];
            v.extend(offset_bytes);
            Ok(v)
        }
    };
}

// according to B.1.4.7 Table B-10 in the Intel Manual, 0101 is not equal/not zero
fn_test_jcc!(bfc_jump_not_zero, 0b0101_u8);
// according to B.1.4.7 Table B-10 in the Intel Manual, 0100 is equal/zero
fn_test_jcc!(bfc_jump_zero, 0b0100_u8);

pub fn bfc_nop_loop_open() -> [u8; arch_info::JUMP_SIZE] {
    // times JUMP_SIZE NOP
    [0x90; arch_info::JUMP_SIZE]
}

// INC and DEC are encoded very similarly with very few differences between
// the encoding for operating on registers and operating on bytes pointed to by
// registers. Because of the similarity, one function can be used for all 4 of
// the `+`, `-`, `>`, and `<` brainfuck instructions in one inline function.
//
// `+` is INC byte [reg], which is encoded as 0xfe reg
// `-` is DEC byte [reg], which is encoded as 0xfe 0x08|reg
// `>` is INC reg, which is encoded as 0xff 0xc0|reg
// `<` is DEC reg, which is encoded as 0xff 0xc8|reg
//
// Therefore, setting op to 0 for INC and 8 for DEC and adm (Address Mode) to 3
// when working on registers and 0 when working on memory, then doing some messy
// bitwise hackery, the following constants and function can be used.

#[derive(Debug)]
enum OffsetOp {
    Inc = 0,
    Dec = 8,
}

#[derive(Debug)]
enum OffsetMode {
    BytePtr = 0,
    Reg = 3,
}

#[inline]
fn x86_offset(op: OffsetOp, mode: OffsetMode, reg: Register) -> Vec<u8> {
    // as it's used more than once, cast mode in advance
    let mode = mode as u8;
    vec![0xfe_u8 | (mode & 1), (op as u8) | (reg as u8) | (mode << 6)]
}

pub fn bfc_inc_reg(reg: Register) -> Vec<u8> {
    // INC reg
    x86_offset(OffsetOp::Inc, OffsetMode::Reg, reg)
}

pub fn bfc_dec_reg(reg: Register) -> Vec<u8> {
    // DEC reg
    x86_offset(OffsetOp::Dec, OffsetMode::Reg, reg)
}

pub fn bfc_inc_byte(reg: Register) -> Vec<u8> {
    // INC byte [reg]
    x86_offset(OffsetOp::Inc, OffsetMode::BytePtr, reg)
}

pub fn bfc_dec_byte(reg: Register) -> Vec<u8> {
    // DEC byte [reg]
    x86_offset(OffsetOp::Dec, OffsetMode::BytePtr, reg)
}

// many add/subtract instructions use these bit values for the upper five bits and the target
// register for the lower 3 bits to encode instructions.
enum ArithOp {
    Add = 0b11000000,
    Sub = 0b11101000,
}

fn bfc_add_reg_imm8(reg: Register, imm8: i8) -> Vec<u8> {
    vec![0x83, ArithOp::Add as u8 | reg as u8, imm8 as u8]
}

fn bfc_sub_reg_imm8(reg: Register, imm8: i8) -> Vec<u8> {
    vec![0x83, ArithOp::Sub as u8 | reg as u8, imm8 as u8]
}

fn bfc_add_reg_imm32(reg: Register, imm32: i32) -> Vec<u8> {
    let mut v = vec![0x81, ArithOp::Add as u8 | reg as u8];
    v.extend(imm32.to_le_bytes());
    v
}

fn bfc_sub_reg_imm32(reg: Register, imm32: i32) -> Vec<u8> {
    let mut v = vec![0x81, ArithOp::Sub as u8 | reg as u8];
    v.extend(imm32.to_le_bytes());
    v
}

// There are no instructions to add or subtract a 64-bit immediate. Instead,
// the approach  to use is first PUSH the value of a different register, MOV
// the 64-bit immediate to that register, ADD/SUB that register to the
// target register, then POP that temporary register, to restore its
// original value.
#[inline]
fn add_sub_qw(reg: Register, imm64: i64, op: ArithOp) -> Vec<u8> {
    // cast reg in advanced as it's used multiple times
    let reg = reg as u8;
    // the temporary register shouldn't be the target register. This guarantees it won't be.
    let tmp_reg = if reg == 0 { 1_u8 } else { 0_u8 };
    #[rustfmt::skip]
    let mut v = vec![
        // PUSH tmp_reg
        0x50_u8|tmp_reg,
        // MOV tmp_reg, (imm64 to be appended)
        0x48_u8, 0xb8_u8|tmp_reg
    ];
    v.extend(imm64.to_le_bytes());
    #[rustfmt::skip]
    v.extend([
        // (ADD||SUB) reg, tmp_reg
        0x48_u8, 0x01_u8 | op as u8, 0xc0_u8 + (tmp_reg << 3) + reg,
        // POP tmp_reg
        0x58 + tmp_reg,
    ]);
    v
}

fn bfc_add_reg_imm64(reg: Register, imm64: i64) -> Vec<u8> {
    add_sub_qw(reg, imm64, ArithOp::Add)
}

fn bfc_sub_reg_imm64(reg: Register, imm64: i64) -> Vec<u8> {
    add_sub_qw(reg, imm64, ArithOp::Sub)
}

pub fn bfc_add_reg(reg: Register, imm: usize) -> Result<Vec<u8>, BFCompileError> {
    match imm {
        i if i <= i8::MAX as usize => Ok(bfc_add_reg_imm8(reg, imm as i8)),
        i if i <= i32::MAX as usize => Ok(bfc_add_reg_imm32(reg, imm as i32)),
        i if i <= i64::MAX as usize => Ok(bfc_add_reg_imm64(reg, imm as i64)),
        _ => Err(BFCompileError::Basic {
            id: String::from("TOO_MANY_INSTRUCTIONS"),
            msg: String::from("Over 8192 PiB of consecitive `>` instructions!"),
        }),
    }
}

pub fn bfc_sub_reg(reg: Register, imm: usize) -> Result<Vec<u8>, BFCompileError> {
    match imm {
        i if i <= i8::MAX as usize => Ok(bfc_sub_reg_imm8(reg, imm as i8)),
        i if i <= i32::MAX as usize => Ok(bfc_sub_reg_imm32(reg, imm as i32)),
        i if i <= i64::MAX as usize => Ok(bfc_sub_reg_imm64(reg, imm as i64)),
        _ => Err(BFCompileError::Basic {
            id: String::from("TOO_MANY_INSTRUCTIONS"),
            msg: String::from("Over 8192 PiB of consecitive `<` instructions!"),
        }),
    }
}

pub fn bfc_add_mem(reg: Register, imm8: i8) -> Vec<u8> {
    // ADD byte [reg], imm8
    vec![0x80_u8, reg as u8, imm8 as u8]
}

pub fn bfc_sub_mem(reg: Register, imm8: i8) -> Vec<u8> {
    // SUB byte [reg], imm8
    vec![0x80_u8, 0b00101000_u8 | (reg as u8), imm8 as u8]
}

pub fn bfc_zero_mem(reg: Register) -> Vec<u8> {
    // MOV byte [reg], 0
    vec![0x67_u8, 0xc6_u8, reg as u8, 0x00_u8]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_set_reg() -> Result<(), String> {
        // test that appropriate encodings are used for different immediates
        assert_eq!(
            bfc_set_reg(registers::REG_BF_PTR, 0),
            // XOR EBX, EBX
            vec![0x31, 0xc0 | 0b011000 | 0b011]
        );
        assert_eq!(
            bfc_set_reg(registers::REG_BF_PTR, 101),
            // PUSH 101; POP RBX
            vec![0x6a, 101, 0x58 | 0b011]
        );
        assert_eq!(
            bfc_set_reg(registers::REG_BF_PTR, 128),
            // MOV EBX, 128
            vec![0xb8 | 0b011, 128, 0, 0, 0]
        );

        #[rustfmt::skip]
        assert_eq!(
            bfc_set_reg(registers::REG_BF_PTR, i64::MAX - 0xffff),
            // MOV RBX, 0x7fffffffffff0000
            vec![0x48, 0xb8 | 0b011, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f]
        );

        Ok(())
    }
}
