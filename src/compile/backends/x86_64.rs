// SPDX-FileCopyrightText: 2024 - 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

// This file contains functions that append x86_64 machine code to buffers

// Throughout this file, "Intel® 64 and IA-32 Architectures Software Developer Manuals" or x86_64
// machine code in general may be referenced in comments.
// For context or clarification, see the manual, which is available at no cost as of 2024-07-11.
//
// https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html

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
use crate::Backend;
use super::x86_common::{ArithOp, ConditionCode, X86Register, x86_common_impl};

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

pub(crate) struct X86_64Inter;
impl ArchInter for X86_64Inter {
    const REGISTERS: Registers<X86Register> = Registers {
        sc_num: X86Register::Eax,
        arg1: X86Register::Edi,
        arg2: X86Register::Esi,
        arg3: X86Register::Edx,
        bf_ptr: X86Register::Ebx,
    };
    const SC_NUMS: SyscallNums = SyscallNums {
        read: 0,
        write: 1,
        exit: 60,
    };
    const ARCH: Backend = Backend::X86_64;

    // SYSCALL
    const SYSCALL_INSTR: &[u8] = &[0x0f, 0x05];

    x86_common_impl!();

    // Chooses the shortest instrution to set a register to an immediate value, from the following:
    // XOR reg, reg
    // MOV reg, imm32
    // MOV reg, imm64
    fn set_reg(code_buf: &mut Vec<u8>, reg: X86Register, imm: i64) -> FailableInstrEncoding {
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
        Ok(())
    }

    fn inc_reg(code_buf: &mut Vec<u8>, reg: X86Register) {
        // INC reg
        code_buf.extend([0x48, 0xff, 0xc0 | (reg as u8)]);
    }

    fn dec_reg(code_buf: &mut Vec<u8>, reg: X86Register) {
        // DEC reg
        code_buf.extend([0x48, 0xff, 0xc8 | (reg as u8)]);
    }

    fn add_reg(code_buf: &mut Vec<u8>, reg: X86Register, imm: u64) -> FailableInstrEncoding {
        if imm == 1 {
            Self::inc_reg(code_buf, reg);
        } else if let Ok(imm8) = i8::try_from(imm) {
            add_reg_imm8(code_buf, reg, imm8);
        } else if let Ok(imm32) = i32::try_from(imm) {
            add_reg_imm32(code_buf, reg, imm32);
        } else {
            add_reg_imm64(code_buf, reg, imm);
        }
        Ok(())
    }

    fn sub_reg(code_buf: &mut Vec<u8>, reg: X86Register, imm: u64) -> FailableInstrEncoding {
        if imm == 1 {
            Self::dec_reg(code_buf, reg);
        } else if let Ok(imm8) = i8::try_from(imm) {
            sub_reg_imm8(code_buf, reg, imm8);
        } else if let Ok(imm32) = i32::try_from(imm) {
            sub_reg_imm32(code_buf, reg, imm32);
        } else {
            sub_reg_imm64(code_buf, reg, imm);
        }
        Ok(())
    }
}

fn add_reg_imm8(code_buf: &mut Vec<u8>, reg: X86Register, imm8: i8) {
    code_buf.extend([0x48, 0x83, ArithOp::Add as u8 | reg as u8, imm8 as u8]);
}

fn sub_reg_imm8(code_buf: &mut Vec<u8>, reg: X86Register, imm8: i8) {
    code_buf.extend([0x48, 0x83, ArithOp::Sub as u8 | reg as u8, imm8 as u8]);
}

fn add_reg_imm32(code_buf: &mut Vec<u8>, reg: X86Register, imm32: i32) {
    code_buf.extend([0x48, 0x81, ArithOp::Add as u8 | reg as u8]);
    code_buf.extend(imm32.to_le_bytes());
}

fn sub_reg_imm32(code_buf: &mut Vec<u8>, reg: X86Register, imm32: i32) {
    code_buf.extend([0x48, 0x81, ArithOp::Sub as u8 | reg as u8]);
    code_buf.extend(imm32.to_le_bytes());
}

// There are no instructions to add or subtract a 64-bit immediate. Instead,
// the approach  to use is first PUSH the value of a different register, MOV
// the 64-bit immediate to that register, ADD/SUB that register to the
// target register, then POP that temporary register, to restore its
// original value.
fn add_sub_qw(code_buf: &mut Vec<u8>, reg: X86Register, imm64: u64, op: ArithOp) {
    // the temporary register shouldn't be the target register, so using RCX, which is a volatile
    // register not used anywhere else in this backend
    code_buf.extend([
        // MOV RCX, (imm64 to be appended)
        0x48,
        0xb8 | X86Register::Ecx as u8,
    ]);
    code_buf.extend(imm64.to_le_bytes());
    code_buf.extend([
        // (ADD||SUB) reg, rcx
        0x48,
        (op as u8) - 0xbf,
        0xc0 + ((X86Register::Ecx as u8) << 3) + (reg as u8),
    ]);
}

fn add_reg_imm64(code_buf: &mut Vec<u8>, reg: X86Register, imm64: u64) {
    add_sub_qw(code_buf, reg, imm64, ArithOp::Add);
}

fn sub_reg_imm64(code_buf: &mut Vec<u8>, reg: X86Register, imm64: u64) {
    add_sub_qw(code_buf, reg, imm64, ArithOp::Sub);
}

#[cfg(test)]
mod tests {
    #[cfg(all(feature = "disasmtests", not(cross_compiled)))]
    use super::super::test_utils::Disassembler;
    #[cfg(all(feature = "disasmtests", not(cross_compiled)))]
    use super::*;
    use test_macros::disasm_test;

    #[cfg(all(feature = "disasmtests", not(cross_compiled)))]
    fn disassembler() -> Disassembler {
        Disassembler::new(Backend::X86_64)
    }

    #[disasm_test]
    fn test_set_reg() {
        // test that appropriate encodings are used for different immediates
        let mut v: Vec<u8> = Vec::new();
        let mut ds = disassembler();

        X86_64Inter::set_reg(&mut v, X86Register::Ebx, 0).unwrap();
        assert_eq!(ds.disassemble(v.clone()), ["xor ebx, ebx"]);
        v.clear();
        X86_64Inter::set_reg(&mut v, X86Register::Ebx, 128).unwrap();
        assert_eq!(ds.disassemble(v.clone()), ["mov ebx, 0x80"]);

        v.clear();
        X86_64Inter::set_reg(&mut v, X86Register::Ebx, i64::MAX - 0xffff).unwrap();
        assert_eq!(
            ds.disassemble(v),
            // movabs is an internal term some dis/assemblers have for MOV variant for large
            // immediates.
            ["movabs rbx, 0x7fffffffffff0000"]
        );
    }

    #[disasm_test]
    fn test_jump_instructions() {
        let mut v: Vec<u8> = vec![0; 9];
        X86_64Inter::jump_open(&mut v, 0, X86Register::Edi, 9).unwrap();
        X86_64Inter::jump_close(&mut v, X86Register::Edi, -18).unwrap();
        X86_64Inter::pad_loop_open(&mut v);
        let mut disasm_lines = disassembler().disassemble(v).into_iter();
        // NOTE: the disassembly uses absolute addresses, not relative addresses.
        assert_eq!(disasm_lines.next().unwrap(), "test byte ptr [rdi], -0x1");
        assert_eq!(disasm_lines.next().unwrap(), "je 0x9");
        assert_eq!(disasm_lines.next().unwrap(), "test byte ptr [rdi], -0x1");
        assert_eq!(disasm_lines.next().unwrap(), "jne -0x12");
        assert_eq!(disasm_lines.next().unwrap(), "ud2");
        // ensure that there are 7 1-byte NOP instructions remaining.
        for i in 0..7 {
            assert_eq!(
                disasm_lines.next().unwrap(),
                "nop",
                "only {i}/7 nop bytes were matched"
            );
        }
        assert!(disasm_lines.next().is_none());
    }

    #[disasm_test]
    fn add_sub_small_imm() {
        let mut v = Vec::with_capacity(4);
        let mut ds = disassembler();
        X86_64Inter::add_reg(&mut v, X86Register::Esi, 0x20).unwrap();
        assert_eq!(v.len(), 4);
        assert_eq!(ds.disassemble(v), ["add rsi, 0x20"]);

        let mut v = Vec::with_capacity(4);
        X86_64Inter::sub_reg(&mut v, X86Register::Esi, 0x20).unwrap();
        assert_eq!(v.len(), 4);
        assert_eq!(ds.disassemble(v), ["sub rsi, 0x20"]);
    }

    #[disasm_test]
    fn add_sub_medium_imm() {
        let mut v = Vec::with_capacity(7);
        let mut ds = disassembler();
        X86_64Inter::add_reg(&mut v, X86Register::Edx, 0xdead).unwrap();
        assert_eq!(v.len(), 7);
        assert_eq!(ds.disassemble(v), ["add rdx, 0xdead"]);

        let mut v = Vec::with_capacity(7);
        X86_64Inter::sub_reg(&mut v, X86Register::Edx, 0xbeef).unwrap();
        assert_eq!(v.len(), 7);
        assert_eq!(ds.disassemble(v), ["sub rdx, 0xbeef"]);
    }

    #[disasm_test]
    fn add_sub_large_imm() {
        let mut v: Vec<u8> = Vec::new();
        let mut ds = disassembler();

        #[allow(clippy::unreadable_literal, reason = "deadbeef is famously readable")]
        X86_64Inter::add_reg(&mut v, X86Register::Ebx, 0xdeadbeef).unwrap();
        assert_eq!(
            ds.disassemble(v),
            ["movabs rcx, 0xdeadbeef", "add rbx, rcx",]
        );

        let mut v: Vec<u8> = Vec::new();
        #[allow(clippy::unreadable_literal, reason = "deadbeef is famously readable")]
        X86_64Inter::sub_reg(&mut v, X86Register::Ebx, 0xdeadbeef).unwrap();
        assert_eq!(
            ds.disassemble(v),
            ["movabs rcx, 0xdeadbeef", "sub rbx, rcx",]
        );
    }

    #[disasm_test]
    fn test_add_sub_byte() {
        let mut v: Vec<u8> = Vec::new();
        X86_64Inter::add_byte(&mut v, X86Register::Edi, 0x23);
        X86_64Inter::sub_byte(&mut v, X86Register::Edi, 0x23);
        assert_eq!(
            disassembler().disassemble(v),
            ["add byte ptr [rdi], 0x23", "sub byte ptr [rdi], 0x23"]
        );
    }

    #[disasm_test]
    fn test_zero_byte() {
        let mut v: Vec<u8> = Vec::new();
        X86_64Inter::zero_byte(&mut v, X86Register::Edx);
        assert_eq!(disassembler().disassemble(v), ["mov byte ptr [rdx], 0x0"]);
    }

    #[disasm_test]
    /// ensure that `inc` and `dec` use the 64-bit register variants
    fn test_inc_dec_is_64_bit() {
        let mut v: Vec<u8> = Vec::new();
        let mut ds = disassembler();

        X86_64Inter::inc_reg(&mut v, X86Register::Eax);
        X86_64Inter::dec_reg(&mut v, X86Register::Eax);
        X86_64Inter::inc_byte(&mut v, X86Register::Eax);
        X86_64Inter::dec_byte(&mut v, X86Register::Eax);

        assert_eq!(
            ds.disassemble(v),
            [
                "inc rax",
                "dec rax",
                "inc byte ptr [rax]",
                "dec byte ptr [rax]"
            ]
        );
    }
}
