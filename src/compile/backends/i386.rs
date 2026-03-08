// SPDX-FileCopyrightText: 2024 - 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

// This file contains functions that append i386 machine code to buffers

// Throughout this file, "Intel® 64 and IA-32 Architectures Software Developer Manuals" or i386
// machine code in general may be referenced in comments.
// For context or clarification, see the manual, which is available at no cost as of 2024-07-11.
//
// https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html

// the Linux kernel reads system call numbers from EAX on i386 systems, and reads arguments from
// EBX, ECX, EDX, ESI, EDI, AND EBP.
//
// None of the system calls that eambfc-rs needs use more than 3 arguments
//
// the EBX register is preserved through system calls, so it's useful as the tape pointer.
//
// Thus, for eambfc, the registers to care about are EAX, EDI, ESI, EDX, and EBX
//
// Oversimpifying a bit, in x86 assembly, when specifying a register, a 3-bit value is used to
// identify it.
//
// * EAX is 000b
// * EDI is 111b
// * ESI is 110b
// * EDX is 010b
// * EBX is 011b

use super::arch_inter::{ArchInter, FailableInstrEncoding, Registers, SyscallNums};
use super::x86_common::{ArithOp, ConditionCode, X86Register, x86_common_impl};
use crate::Backend;
use crate::err::{BFCompileError, BFErrorID};

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

pub(crate) struct I386Inter;
impl ArchInter for I386Inter {
    const REGISTERS: Registers<X86Register> = Registers {
        sc_num: X86Register::Eax,
        arg1: X86Register::Ebx,
        arg2: X86Register::Ecx,
        arg3: X86Register::Edx,
        bf_ptr: X86Register::Esi,
    };
    const SC_NUMS: SyscallNums = SyscallNums {
        read: 3,
        write: 4,
        exit: 1,
    };
    const ARCH: Backend = Backend::I386;
    // INT 0x80
    const SYSCALL_INSTR: &[u8] = &[0xcd, 0x80];
    x86_common_impl!();

    // Chooses the shortest instruction to set a register to an immediate value, from the following:
    // XOR reg, reg
    // MOV reg, imm32
    fn set_reg(code_buf: &mut Vec<u8>, reg: X86Register, imm: i64) -> FailableInstrEncoding {
        let raw_reg = reg as u8;
        if imm == 0 {
            // XOR reg, reg
            code_buf.extend([0x31, 0xc0 | (raw_reg << 3) | raw_reg]);
            return Ok(());
        }
        let i: [u8; 4] = i32::try_from(imm)
            .map(i32::to_le_bytes)
            .or_else(|_| u32::try_from(imm).map(u32::to_le_bytes))
            .map_err(|_| {
                Self::set_reg(code_buf, reg, imm & 0xffff_ffff).expect("truncated to fit");
                BFCompileError::basic(
                    BFErrorID::CodeTooLarge,
                    format!("Cannot set 32-bit register to 64-bit value {imm}"),
                )
            })?;
        code_buf.push(0xb8 + raw_reg);
        code_buf.extend(i);
        Ok(())
    }

    fn inc_reg(code_buf: &mut Vec<u8>, reg: X86Register) {
        // INC reg
        code_buf.extend([0xff, 0xc0 | (reg as u8)]);
    }

    fn dec_reg(code_buf: &mut Vec<u8>, reg: X86Register) {
        // DEC reg
        code_buf.extend([0xff, 0xc8 | (reg as u8)]);
    }

    fn add_reg(code_buf: &mut Vec<u8>, reg: X86Register, imm: u64) -> FailableInstrEncoding {
        if imm == 0 {
            return Ok(());
        } else if imm == 1 {
            Self::inc_reg(code_buf, reg);
        } else if let Ok(imm8) = i8::try_from(imm) {
            add_reg_imm8(code_buf, reg, imm8);
        } else if let Ok(imm32) =
            i32::try_from(imm).or_else(|_| u32::try_from(imm).map(u32::cast_signed))
        {
            add_reg_imm32(code_buf, reg, imm32);
        } else {
            return Err(BFCompileError::basic(
                BFErrorID::CodeTooLarge,
                format!("{imm} is too large for 32-bit backends"),
            ));
        }
        Ok(())
    }

    fn sub_reg(code_buf: &mut Vec<u8>, reg: X86Register, imm: u64) -> FailableInstrEncoding {
        if imm == 0 {
            return Ok(())
        } else if imm == 1 {
            Self::dec_reg(code_buf, reg);
        } else if let Ok(imm8) = i8::try_from(imm) {
            sub_reg_imm8(code_buf, reg, imm8);
        } else if let Ok(imm32) =
            i32::try_from(imm).or_else(|_| u32::try_from(imm).map(u32::cast_signed))
        {
            sub_reg_imm32(code_buf, reg, imm32);
        } else {
            return Err(BFCompileError::basic(
                BFErrorID::CodeTooLarge,
                format!("{imm} is too large for 32-bit backends"),
            ));
        }
        Ok(())
    }
}

fn add_reg_imm8(code_buf: &mut Vec<u8>, reg: X86Register, imm8: i8) {
    code_buf.extend([0x83, ArithOp::Add as u8 | reg as u8, imm8.cast_unsigned()]);
}

fn sub_reg_imm8(code_buf: &mut Vec<u8>, reg: X86Register, imm8: i8) {
    code_buf.extend([0x83, ArithOp::Sub as u8 | reg as u8, imm8.cast_unsigned()]);
}

fn add_reg_imm32(code_buf: &mut Vec<u8>, reg: X86Register, imm32: i32) {
    code_buf.extend([0x81, ArithOp::Add as u8 | reg as u8]);
    code_buf.extend(imm32.to_le_bytes());
}

fn sub_reg_imm32(code_buf: &mut Vec<u8>, reg: X86Register, imm32: i32) {
    code_buf.extend([0x81, ArithOp::Sub as u8 | reg as u8]);
    code_buf.extend(imm32.to_le_bytes());
}

#[cfg(test)]
mod tests {
    #[cfg(all(feature = "disasmtests", not(cross_compiled)))]
    use super::super::test_utils::Disassembler;
    use super::*;
    use crate::err::BFErrorID;
    use test_macros::disasm_test;

    #[cfg(all(feature = "disasmtests", not(cross_compiled)))]
    fn disassembler() -> Disassembler {
        Disassembler::new(Backend::I386)
    }

    #[disasm_test]
    fn test_set_reg() {
        // test that appropriate encodings are used for different immediates
        let mut v: Vec<u8> = Vec::new();
        let mut ds = disassembler();

        I386Inter::set_reg(&mut v, X86Register::Ebx, 0).unwrap();
        assert_eq!(ds.disassemble(v.clone()), ["xor ebx, ebx"]);
        v.clear();
        I386Inter::set_reg(&mut v, X86Register::Ebx, 128).unwrap();
        assert_eq!(ds.disassemble(v.clone()), ["mov ebx, 0x80"]);
        v.clear();
    }
    #[disasm_test]
    fn fits_i32_or_u32() {
        let mut a: Vec<u8> = Vec::new();
        let mut b: Vec<u8> = Vec::new();
        I386Inter::set_reg(&mut a, X86Register::Eax, u32::MAX.into()).unwrap();
        I386Inter::set_reg(&mut b, X86Register::Eax, -1).unwrap();
        assert_eq!(a, b);
        assert_eq!(disassembler().disassemble(a), ["mov eax, 0xffffffff"]);
    }

    #[test]
    fn set_reg_imm_too_large() {
        assert_eq!(
            I386Inter::set_reg(&mut Vec::new(), X86Register::Ebx, i64::from(u32::MAX) + 1)
                .unwrap_err()
                .error_id(),
            BFErrorID::CodeTooLarge
        );
    }

    #[disasm_test]
    fn test_jump_instructions() {
        let mut v: Vec<u8> = vec![0; 9];
        I386Inter::jump_open(&mut v, 0, X86Register::Edi, 9).unwrap();
        I386Inter::jump_close(&mut v, X86Register::Edi, -18).unwrap();
        I386Inter::pad_loop_open(&mut v);
        let mut disasm_lines = disassembler().disassemble(v).into_iter();
        // NOTE: the disassembly uses absolute addresses, not relative addresses.
        assert_eq!(disasm_lines.next().unwrap(), "test byte ptr [edi], -0x1");
        assert_eq!(disasm_lines.next().unwrap(), "je 0x9");
        assert_eq!(disasm_lines.next().unwrap(), "test byte ptr [edi], -0x1");
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
        I386Inter::add_reg(&mut v, X86Register::Esi, 0x20).unwrap();
        assert_eq!(v.len(), 3);
        assert_eq!(ds.disassemble(v), ["add esi, 0x20"]);

        let mut v = Vec::with_capacity(4);
        I386Inter::sub_reg(&mut v, X86Register::Esi, 0x20).unwrap();
        assert_eq!(v.len(), 3);
        assert_eq!(ds.disassemble(v), ["sub esi, 0x20"]);
    }

    #[disasm_test]
    fn add_sub_medium_imm() {
        let mut v = Vec::with_capacity(6);
        let mut ds = disassembler();
        I386Inter::add_reg(&mut v, X86Register::Edx, 0xdead).unwrap();
        assert_eq!(v.len(), 6);
        assert_eq!(ds.disassemble(v), ["add edx, 0xdead"]);

        let mut v = Vec::with_capacity(6);
        I386Inter::sub_reg(&mut v, X86Register::Edx, 0xbeef).unwrap();
        assert_eq!(v.len(), 6);
        assert_eq!(ds.disassemble(v), ["sub edx, 0xbeef"]);
    }

    #[disasm_test]
    fn test_add_sub_byte() {
        let mut v: Vec<u8> = Vec::new();
        I386Inter::add_byte(&mut v, X86Register::Edi, 0x23);
        I386Inter::sub_byte(&mut v, X86Register::Edi, 0x23);
        assert_eq!(
            disassembler().disassemble(v),
            ["add byte ptr [edi], 0x23", "sub byte ptr [edi], 0x23"]
        );
    }

    #[disasm_test]
    fn test_set_byte() {
        let mut dis = disassembler();
        let mut v: Vec<u8> = Vec::new();
        I386Inter::set_byte(&mut v, X86Register::Edx, 0);
        assert_eq!(dis.disassemble(v), ["mov byte ptr [edx], 0x0"]);

        let mut v = Vec::new();
        I386Inter::set_byte(&mut v, X86Register::Edx, 0x40);
        assert_eq!(dis.disassemble(v), ["mov byte ptr [edx], 0x40"]);
    }

    #[test]
    fn add_sub_zero_does_nothing() {
        let mut v = Vec::new();
        I386Inter::add_byte(&mut v, X86Register::Eax, 0);
        I386Inter::sub_byte(&mut v, X86Register::Eax, 0);
        I386Inter::add_reg(&mut v, X86Register::Eax, 0).unwrap();
        I386Inter::sub_reg(&mut v, X86Register::Eax, 0).unwrap();
        assert!(v.is_empty());
    }
}
