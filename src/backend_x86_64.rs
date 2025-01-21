// SPDX-FileCopyrightText: 2024 - 2025 Eli Array Minkoff
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

use super::arch_inter::{ArchInter, FailableInstrEncoding, Registers, SyscallNums};
use super::elf_tools::{EIData, ELFArch};
use super::err::{BFCompileError, BFErrorID};

#[derive(Debug, Copy, Clone)]
#[repr(u8)]
pub enum X86_64Register {
    RAX = 0b000,
    RDI = 0b111,
    RSI = 0b110,
    RDX = 0b010,
    RBX = 0b011,
}

// many add/subtract instructions use these bit values for the upper five bits and the target
// register for the lower 3 bits to encode instructions.
#[derive(Debug)]
#[repr(u8)]
enum ArithOp {
    Add = 0xc0,
    Sub = 0xe8,
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
// bitwise hackery, the following enums and function can be used.

#[derive(Debug)]
#[repr(u8)]
enum OffsetOp {
    Inc = 0,
    Dec = 8,
}

#[derive(Debug, Clone, Copy)]
#[repr(u8)]
enum OffsetMode {
    BytePtr = 0,
    Reg = 3,
}

fn x86_offset(code_buf: &mut Vec<u8>, op: OffsetOp, mode: OffsetMode, reg: X86_64Register) {
    // as it's used more than once, cast mode in advance
    code_buf.extend([
        0xfe | (mode as u8 & 1),
        (op as u8) | (reg as u8) | ((mode as u8) << 6),
    ]);
}

#[derive(Clone, Copy)]
#[repr(u8)]
enum ConditionCode {
    // according to B.1.4.7 Table B-10 in the Intel Manual, 0101 is not equal/not zero
    Zero = 0b0100,
    // according to B.1.4.7 Table B-10 in the Intel Manual, 0100 is equal/zero
    NotZero = 0b0101,
}

fn conditional_jump(
    code_buf: &mut Vec<u8>,
    reg: X86_64Register,
    offset: i64,
    condition: ConditionCode,
) -> FailableInstrEncoding {
    let offset_bytes = i32::try_from(offset)
        .map_err(|_| {
            BFCompileError::basic(
                BFErrorID::JUMP_TOO_LONG,
                format!("{offset} is outside the range of possible 32-bit signed values"),
            )
        })?
        .to_le_bytes();
    #[rustfmt::skip]
    code_buf.extend([
        // TEST byte [reg], 0xff
        0xf6, reg as u8, 0xff,
        // Jcc|tttn (must be followed by a 32-bit immediate jump offset)
        0x0f, 0x80| (condition as u8)
    ]);
    code_buf.extend(offset_bytes);
    Ok(())
}

pub struct X86_64Inter;
impl ArchInter for X86_64Inter {
    type RegType = X86_64Register;
    const JUMP_SIZE: usize = 9;
    const E_FLAGS: u32 = 0;

    const REGISTERS: Registers<X86_64Register> = Registers {
        sc_num: X86_64Register::RAX,
        arg1: X86_64Register::RDI,
        arg2: X86_64Register::RSI,
        arg3: X86_64Register::RDX,
        bf_ptr: X86_64Register::RBX,
    };
    const SC_NUMS: SyscallNums = SyscallNums {
        read: 0,
        write: 1,
        exit: 60,
    };
    const ARCH: ELFArch = ELFArch::X86_64;
    const EI_DATA: EIData = EIData::ELFDATA2LSB;
    // Chooses the shortest instrution to set a register to an immediate value, from the following:
    // XOR reg, reg
    // MOV reg, imm32
    // MOV reg, imm64
    fn set_reg(code_buf: &mut Vec<u8>, reg: X86_64Register, imm: i64) {
        let reg = reg as u8;
        match imm {
            // XOR reg, reg
            0 => code_buf.extend([0x31, 0xc0 | (reg << 3) | reg]),
            // MOV reg, imm32
            i if i < i32::MAX.into() => {
                code_buf.push(0xb8 + reg);
                code_buf.extend((i as i32).to_le_bytes());
            }
            // MOV reg, imm64
            i => {
                code_buf.extend(&[0x48, 0xb8 + reg]);
                code_buf.extend(&i.to_le_bytes());
            }
        }
    }
    fn reg_copy(code_buf: &mut Vec<u8>, dst: X86_64Register, src: X86_64Register) {
        // MOV dst, src
        code_buf.extend([0x89, 0xc0 + ((src as u8) << 3) + dst as u8]);
    }
    fn syscall(code_buf: &mut Vec<u8>) {
        // SYSCALL
        code_buf.extend([0x0f, 0x05]);
    }

    fn jump_zero(code_buf: &mut Vec<u8>, reg: Self::RegType, offset: i64) -> FailableInstrEncoding {
        conditional_jump(code_buf, reg, offset, ConditionCode::Zero)
    }
    fn jump_not_zero(
        code_buf: &mut Vec<u8>,
        reg: Self::RegType,
        offset: i64,
    ) -> FailableInstrEncoding {
        conditional_jump(code_buf, reg, offset, ConditionCode::NotZero)
    }

    fn nop_loop_open(code_buf: &mut Vec<u8>) {
        // times JUMP_SIZE NOP
        code_buf.extend([0x90; Self::JUMP_SIZE]);
    }

    fn inc_reg(code_buf: &mut Vec<u8>, reg: X86_64Register) {
        // INC reg
        x86_offset(code_buf, OffsetOp::Inc, OffsetMode::Reg, reg);
    }
    fn inc_byte(code_buf: &mut Vec<u8>, reg: X86_64Register) {
        // INC byte [reg]
        x86_offset(code_buf, OffsetOp::Inc, OffsetMode::BytePtr, reg);
    }
    fn dec_reg(code_buf: &mut Vec<u8>, reg: X86_64Register) {
        // DEC reg
        x86_offset(code_buf, OffsetOp::Dec, OffsetMode::Reg, reg);
    }
    fn dec_byte(code_buf: &mut Vec<u8>, reg: X86_64Register) {
        // DEC byte [reg]
        x86_offset(code_buf, OffsetOp::Dec, OffsetMode::BytePtr, reg);
    }
    fn add_reg(code_buf: &mut Vec<u8>, reg: X86_64Register, imm: i64) {
        match imm {
            i if (i64::from(i8::MIN)..=i64::from(i8::MAX)).contains(&i) => {
                add_reg_imm8(code_buf, reg, imm as i8);
            }
            i if (i64::from(i32::MIN)..=i64::from(i32::MAX)).contains(&i) => {
                add_reg_imm32(code_buf, reg, imm as i32);
            }
            _ => add_reg_imm64(code_buf, reg, imm),
        }
    }
    fn add_byte(code_buf: &mut Vec<u8>, reg: X86_64Register, imm: i8) {
        // ADD byte [reg], imm8
        code_buf.extend([0x80, reg as u8, imm as u8]);
    }
    fn sub_reg(code_buf: &mut Vec<u8>, reg: X86_64Register, imm: i64) {
        match imm {
            i if (i64::from(i8::MIN)..=i64::from(i8::MAX)).contains(&i) => {
                sub_reg_imm8(code_buf, reg, imm as i8);
            }
            i if (i64::from(i32::MIN)..=i64::from(i32::MAX)).contains(&i) => {
                sub_reg_imm32(code_buf, reg, imm as i32);
            }
            _ => sub_reg_imm64(code_buf, reg, imm),
        }
    }
    fn sub_byte(code_buf: &mut Vec<u8>, reg: X86_64Register, imm: i8) {
        // SUB byte [reg], imm8
        code_buf.extend([0x80, 0x28 | (reg as u8), imm as u8]);
    }
    fn zero_byte(code_buf: &mut Vec<u8>, reg: X86_64Register) {
        // MOV byte [reg], 0
        code_buf.extend([0x67, 0xc6, reg as u8, 0x00]);
    }
}

fn add_reg_imm8(code_buf: &mut Vec<u8>, reg: X86_64Register, imm8: i8) {
    code_buf.extend([0x83, ArithOp::Add as u8 | reg as u8, imm8 as u8]);
}

fn sub_reg_imm8(code_buf: &mut Vec<u8>, reg: X86_64Register, imm8: i8) {
    code_buf.extend([0x83, ArithOp::Sub as u8 | reg as u8, imm8 as u8]);
}

fn add_reg_imm32(code_buf: &mut Vec<u8>, reg: X86_64Register, imm32: i32) {
    code_buf.extend([0x81, ArithOp::Add as u8 | reg as u8]);
    code_buf.extend(imm32.to_le_bytes());
}

fn sub_reg_imm32(code_buf: &mut Vec<u8>, reg: X86_64Register, imm32: i32) {
    code_buf.extend([0x81, ArithOp::Sub as u8 | reg as u8]);
    code_buf.extend(imm32.to_le_bytes());
}

// There are no instructions to add or subtract a 64-bit immediate. Instead,
// the approach  to use is first PUSH the value of a different register, MOV
// the 64-bit immediate to that register, ADD/SUB that register to the
// target register, then POP that temporary register, to restore its
// original value.
fn add_sub_qw(code_buf: &mut Vec<u8>, reg: X86_64Register, imm64: i64, op: ArithOp) {
    // cast reg in advanced as it's used multiple times
    // the temporary register shouldn't be the target register, so using RCX, which is a volatile
    // register not used anywhere else in eambfc, encoded as 0b001.
    const TMP_REG: u8 = 0b001;
    code_buf.extend([
        // MOV tmp_reg, (imm64 to be appended)
        0x48,
        0xb8 | TMP_REG,
    ]);
    code_buf.extend(imm64.to_le_bytes());
    code_buf.extend([
        // (ADD||SUB) reg, tmp_reg
        0x48,
        0x01 | op as u8,
        0xc0 + (TMP_REG << 3) + (reg as u8),
    ]);
}

fn add_reg_imm64(code_buf: &mut Vec<u8>, reg: X86_64Register, imm64: i64) {
    add_sub_qw(code_buf, reg, imm64, ArithOp::Add);
}

fn sub_reg_imm64(code_buf: &mut Vec<u8>, reg: X86_64Register, imm64: i64) {
    add_sub_qw(code_buf, reg, imm64, ArithOp::Sub);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_set_reg() {
        // test that appropriate encodings are used for different immediates
        let mut v: Vec<u8> = Vec::new();
        X86_64Inter::set_reg(&mut v, X86_64Register::RBX, 0);
        assert_eq!(
            v,
            // XOR EBX, EBX
            vec![0x31, 0xc0 | (0b011 << 3) | 0b011]
        );
        v.clear();
        X86_64Inter::set_reg(&mut v, X86_64Register::RBX, 128);
        assert_eq!(
            v,
            // MOV EBX, 128
            vec![0xb8 | 0b011, 128, 0, 0, 0]
        );

        v.clear();
        X86_64Inter::set_reg(&mut v, X86_64Register::RBX, i64::MAX - 0xffff);

        #[rustfmt::skip]
        assert_eq!(
            v,
            // MOV RBX, 0x7fffffffffff0000
            vec![0x48, 0xb8 | 0b011, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f]
        );
    }
}
