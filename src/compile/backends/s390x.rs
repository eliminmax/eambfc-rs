// SPDX-FileCopyrightText: 2024 - 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use crate::err::{BFCompileError, BFErrorID};

use super::arch_inter::{ArchInter, FailableInstrEncoding, Registers, SyscallNums};
use super::elf_tools::{ByteOrdering, ElfArch};

// The z/Architecture Principles of Operation comprehensively documents the
// z/Architecture ISA, and its 14th edition was the main source for information
// about the architecture when writing this backend. As of 2024-10-29, IBM
// provides a PDF of that edition at the following URL:
// https://www.ibm.com/docs/en/module_1678991624569/pdf/SA22-7832-13.pdf
//
// The z/Architecture Reference Summary provides a selection of the information
// from the Principles of Operation in a more concise form, and is a helpful
// supplement to it. As of 2024-10-29, IBM provides the 11th edition at the
// following URL:
// https://ibm.com/support/pages/sites/default/files/2021-05/SA22-7871-10.pdf
//
// Additional information about the ISA is available in the ELF Application
// Binary Interface s390x Supplement, Version 1.6.1. As f 2024-10-29, IBM
// provides it at the following URL:
// https://github.com/IBM/s390x-abi/releases/download/v1.6.1/lzsabi_s390x.pdf
//
// Information about the Linux Kernel's use of different registers was obtained
// from the "Debugging on Linux for s/390 & z/Architecture" page in the docs for
// Linux 5.3.0, available at the following URL:
// https://www.kernel.org/doc/html/v5.3/s390/debugging390.html
//
// Finally, some information was gleaned from examining existing s390x binaries
// with the rasm2 assembler/disassembler from the Radare2 project - mainly an
// implementation of a minimal 'clear' command, made in a hex editor.
// https://rada.re/n/radare2.html
// https://github.com/eliminmax/tiny-clear-elf/tree/main/s390x/ */
// ISA Information
//
// This is explained here, rather than being repeated throughout the comments
// throughout this file.
//
// the z/Architecture ISA has 16 general-purpose registers, r0 to r15. If any
// value other than zero is stored in r0, an exception occurs, so it can always
// be assumed to contain zero.
//
// Some instructions take a memory operand, which consists of a 12-bit
// displacement 'd', an optional index register 'x', and an optional base
// register 'b'. Others take a 20-bit displacement, split into the 12 lower bits
// 'dl', and the 8 higher bits 'dh'. In both cases, the values in the index and
// base registers are added to the displacement to get a memory address.
//
// Bits are grouped into 8-bit "bytes", as is almost universal.
//
// Bytes can be grouped into larger structures, most commonly 2-byte
// "halfwords", though 4-byte "words", 8-byte "doublewords", and more exist.
// The full list is on page "3-4" of the Principles of Operation book, but what
// must be understood is that they must be aligned properly (e.g. half-words
// must start on even-numbered bytes).
//
// Instructions are 1, 2, or 3 halfwords long.
//
// There are numerous formats for instructions, which are given letter codes,
// such as E, I, IE, MII, RI-a, and so on. They are listed in the Reference
// Summary, starting on page #1, which is actually the 13th page of the PDF.
//
// The instruction formats used in eambfc are listed below:
//
// * I (1 halfword, 8-bit opcode, [byte immediate])
//  - bits 0-8: opcode
//  - bits 8-16: immediate
//
// * RI-a (2 halfwords, 12-bit opcode, [register, halfword immediate])
//  - bits 0-7: higher 8 bits of opcode
//  - bits 8-11: register
//  - bits 12-15: lower 4 bits of opcode
//  - bits 16-31: immediate
//
// * RIL-a (3 halfwords, 12-bit opcode, [register, word immediate])
//  - bits 0-7: higher 8 bits of opcode
//  - bits 8-11: register
//  - bits 12-15: lower 4 bits of opcode
//  - bits 16-47: immediate
//
// * RIL-c (3 halfwords, 12-bit opcode, [mask, 32-bit relative immediate])
//  - bits 0-7: higher 8 bits of opcode
//  - bits 8-11: mask
//  - bits 12-15: lower 4 bits of opcode
//  - bits 16-47: relative immediate
//
// * RX-a (2 halfwords, 8-bit opcode, [register, memory])
//  - bits 0-7: opcode
//  - bits 8-11: register
//  - bits 12-15: memory index register
//  - bits 16-19: memory base register
//  - bits 20-31: memory displacement
//
// * RX-b (2 halfwords, 8-bit opcode, [mask, memory])
//  - bits 0-7: opcode
//  - bits 8-11: mask
//  - bits 12-15: memory index register
//  - bits 16-19: memory base register
//  - bits 20-31: memory displacement
//
// * RXY-a (3 halfwords, 16-bit opcode, [register, extended memory])
//  - bits 0-7: higher 8 bits of opcode
//  - bits 8-11: register
//  - bits 12-15: memory index register
//  - bits 16-19: memory base register
//  - bits 20-31: memory displacement (lower 12 bits)
//  - bits 32-39: memory displacement (higher 8 bits)
//  - bits 40-47: lower 8 bits of opcode
//
// * RR (1 halfword, 8-bit opcode, [register or mask, register])
//  - bits 0-7: opcode
//  - bits 8-11: first register or mask
//  - bits 12-15: second register
//
// * RRE (2 halfwords, 16-bit opcode, [register, register])
//  - bits 0-15: opcode
//  - bits 16-23: unassigned (must be set to 0)
//  - bits 24-27: first register
//  - bits 28-31: second register
//
// As with other backends, when a machine instruction appears, it has the
// corresponding assembly in a comment nearby. Unlike other backends, that
// comment is followed by the instruction format in curly braces.

// ISA Information
//
// This is explained here, rather than being repeated throughout the comments
// throughout this file.
//
// the z/Architecture ISA has 16 general-purpose registers, r0 to r15. If any
// value other than zero is stored in r0, an exception occurs, so it can always
// be assumed to contain zero.
//
// Some instructions take a memory operand, which consists of a 12-bit
// displacement 'd', an optional index register 'x', and an optional base
// register 'b'. Others take a 20-bit displacement, split into the 12 lower bits
// 'dl', and the 8 higher bits 'dh'. In both cases, the values in the index and
// base registers are added to the displacement to get a memory address.
//
// Bits are grouped into 8-bit "bytes", as is almost universal.
//
// Bytes can be grouped into larger structures, most commonly 2-byte
// "halfwords", though 4-byte "words", 8-byte "doublewords", and more exist.
// The full list is on page "3-4" of the Principles of Operation book, but what
// must be understood is that they must be aligned properly (e.g. half-words
// must start on even-numbered bytes).
//
// Instructions are 1, 2, or 3 halfwords long.
//
// There are numerous formats for instructions, which are given letter codes,
// such as E, I, IE, MII, RI-a, and so on. They are listed in the Reference
// Summary, starting on page #1, which is actually the 13th page of the PDF.
//
// The instruction formats used in eambfc are listed below:
//
// * I (1 halfword, 8-bit opcode, [byte immediate])
//  - bits 0-8: opcode
//  - bits 8-16: immediate
//
// * RI-a (2 halfwords, 12-bit opcode, [register, halfword immediate])
//  - bits 0-7: higher 8 bits of opcode
//  - bits 8-11: register
//  - bits 12-15: lower 4 bits of opcode
//  - bits 16-31: immediate
//
// * RIL-a (3 halfwords, 12-bit opcode, [register, word immediate])
//  - bits 0-7: higher 8 bits of opcode
//  - bits 8-11: register
//  - bits 12-15: lower 4 bits of opcode
//  - bits 16-47: immediate
//
// * RIL-c (3 halfwords, 12-bit opcode, [mask, 32-bit relative immediate])
//  - bits 0-7: higher 8 bits of opcode
//  - bits 8-11: mask
//  - bits 12-15: lower 4 bits of opcode
//  - bits 16-47: relative immediate
//
// * RX-a (2 halfwords, 8-bit opcode, [register, memory])
//  - bits 0-7: opcode
//  - bits 8-11: register
//  - bits 12-15: memory index register
//  - bits 16-19: memory base register
//  - bits 20-31: memory displacement
//
// * RX-b (2 halfwords, 8-bit opcode, [mask, memory])
//  - bits 0-7: opcode
//  - bits 8-11: mask
//  - bits 12-15: memory index register
//  - bits 16-19: memory base register
//  - bits 20-31: memory displacement
//
// * RXY-a (3 halfwords, 16-bit opcode, [register, extended memory])
//  - bits 0-7: higher 8 bits of opcode
//  - bits 8-11: register
//  - bits 12-15: memory index register
//  - bits 16-19: memory base register
//  - bits 20-31: memory displacement (lower 12 bits)
//  - bits 32-39: memory displacement (higher 8 bits)
//  - bits 40-47: lower 8 bits of opcode
//
// * RR (2 halfwords, 8-bit opcode, [register or mask, register])
//  - bits 0-7: opcode
//  - bits 8-11: first register or mask
//  - bits 12-15: second register
//
// * RRE (2 halfwords, 16-bit opcode, [register, register])
//  - bits 0-15: opcode
//  - bits 16-23: unassigned (must be set to 0)
//  - bits 24-27: first register
//  - bits 28-31: second register
//
// As with other backends, when a machine instruction appears, it has the
// corresponding assembly in a comment nearby. Unlike other backends, that
// comment is followed by the instruction format in curly braces.

#[derive(Clone, Copy, PartialEq)]
#[repr(u8)]
pub(in super::super) enum S390xRegister {
    R0 = 0, // zero register
    R1 = 1, // syscall register
    R2 = 2, // arg1 register
    R3 = 3, // arg2 register
    R4 = 4, // arg3 register
    R5 = 5, // temporary scratch register
    R8 = 8, // bf pointer register
}

#[repr(u8)]
enum ComparisonMask {
    MaskEQ = 8,
    MaskNE = 6, // `MaskLT | MaskGT` (i.e. 4 | 2)
}

// temporary scratch register
const TMP_REG: S390xRegister = S390xRegister::R5;

fn store_to_byte(reg: S390xRegister, aux: S390xRegister) -> [u8; 4] {
    /* STC aux, 0(reg) {RX-a} */
    [0x42, ((aux as u8) << 4) | (reg as u8), 0x00, 0x00]
}

fn load_from_byte(reg: S390xRegister) -> [u8; 6] {
    // LLGC aux, 0(reg) {RXY-a}
    [
        0xe3,
        ((TMP_REG as u8) << 4) | (reg as u8),
        0x00, // base register and displacement are set to 0.
        0x00,
        0x00,
        0x90,
    ]
}

fn branch_cond(
    reg: S390xRegister,
    offset: i64,
    comp_mask: ComparisonMask,
) -> Result<[u8; 18], BFCompileError> {
    let offset: i32 = i16::try_from(offset >> 1)
        .map_err(|_| {
            BFCompileError::basic(
                BFErrorID::JumpTooLong,
                "offset out of range for this architecture",
            )
        })?
        .into();
    let mut code_buf = [0; 18];
    code_buf[..6].clone_from_slice(&load_from_byte(reg));
    // CFI aux, 0 {RIL-a}
    code_buf[6] = 0xc2;
    code_buf[7] = ((TMP_REG as u8) << 4) | 0x0d;
    code_buf[8..12].clone_from_slice(&[0; 4]);
    // BRCL mask, offset
    code_buf[12] = 0xc0;
    code_buf[13] = ((comp_mask as u8) << 4) | 0x04;
    code_buf[14..].clone_from_slice(&offset.to_be_bytes());

    Ok(code_buf)
}

fn add_reg_signed(code_buf: &mut Vec<u8>, reg: S390xRegister, imm: i64) {
    if let Ok(imm16) = i16::try_from(imm) {
        // AGHI reg, imm {RI-a}
        code_buf.extend(u16::to_be_bytes(0xa70b | ((reg as u16) << 4)));
        code_buf.extend(imm16.to_be_bytes());
    } else if let Ok(imm32) = i32::try_from(imm) {
        // AGFI reg, imm {RIL-a}
        code_buf.extend(u16::to_be_bytes(0xc208 | ((reg as u16) << 4)));
        code_buf.extend(imm32.to_be_bytes());
    } else {
        let (imm_h, imm_l) = (imm >> 32, imm as i32);
        if imm_l != 0 {
            add_reg_signed(code_buf, reg, i64::from(imm_l));
        }
        // AIH reg, imm {RIL-a}
        code_buf.extend(u16::to_be_bytes(0xcc08 | ((reg as u16) << 4)));
        code_buf.extend((imm_h as i32).to_be_bytes());
    }
}

pub(crate) struct S390xInter;
impl ArchInter for S390xInter {
    type RegType = S390xRegister;
    const JUMP_SIZE: usize = 18;
    const E_FLAGS: u32 = 0;

    const REGISTERS: Registers<S390xRegister> = Registers {
        sc_num: S390xRegister::R1,
        arg1: S390xRegister::R2,
        arg2: S390xRegister::R3,
        arg3: S390xRegister::R4,
        bf_ptr: S390xRegister::R8,
    };
    const SC_NUMS: SyscallNums = SyscallNums {
        read: 3,
        write: 4,
        exit: 1,
    };

    const ARCH: ElfArch = ElfArch::S390x;
    const EI_DATA: ByteOrdering = ByteOrdering::BigEndian;

    fn set_reg(code_buf: &mut Vec<u8>, reg: S390xRegister, imm: i64) {
        if imm == 0 {
            Self::reg_copy(code_buf, reg, S390xRegister::R0);
        } else if let Ok(imm16) = i16::try_from(imm) {
            // if it fits in a halfword, use Load Halfword Immediate (64 <- 16)
            // LGHI r.reg, imm {RI-a}
            code_buf.extend(u16::to_be_bytes(0xa709 | ((reg as u16) << 4)));
            code_buf.extend(imm16.to_be_bytes());
        } else if let Ok(imm32) = i32::try_from(imm) {
            // if it fits within a word, use Load Immediate (64 <- 32)
            // LGFI r.reg, imm {RIL-a}
            code_buf.extend(u16::to_be_bytes(0xc001 | ((reg as u16) << 4)));
            code_buf.extend(imm32.to_be_bytes());
        } else {
            Self::set_reg(code_buf, reg, i64::from(imm as i32));

            let default_val: i16 = if imm.is_negative() { -1 } else { 0 };

            let imm_high = (imm >> 32) as i32;

            match ((imm_high >> 16) as i16, imm_high as i16) {
                (n, imm_high_low) if n == default_val => {
                    // set bits 16-31 of the register to the immediate, leave other bits as-is
                    // IIHL reg, upper_imm {RI-a}
                    code_buf.extend(u16::to_be_bytes(0xa501 | ((reg as u16) << 4)));
                    code_buf.extend(imm_high_low.to_be_bytes());
                }
                (imm_high_high, n) if n == default_val => {
                    // set bits 0-15 of the register to the immediate, leave other bits as-is
                    // IIHH reg, upper_imm {RI-a}
                    code_buf.extend(u16::to_be_bytes(0xa500 | ((reg as u16) << 4)));
                    code_buf.extend(imm_high_high.to_be_bytes());
                }
                _ => {
                    // need to set the full upper word, with Insert Immediate (high)
                    // IIHF reg, imm {RIL-a}
                    code_buf.extend(u16::to_be_bytes(0xc008 | ((reg as u16) << 4)));
                    code_buf.extend(imm_high.to_be_bytes());
                }
            }
        }
    }

    fn reg_copy(code_buf: &mut Vec<u8>, dst: S390xRegister, src: S390xRegister) {
        // LGR dst, src {RRE}
        code_buf.extend([0xb9, 0x04, 0x00, ((dst as u8) << 4) | (src as u8)]);
    }

    fn syscall(code_buf: &mut Vec<u8>) {
        // SVC 0 {I}
        code_buf.extend([0x0a, 0x00]);
    }

    fn jump_open(
        code_buf: &mut [u8],
        index: usize,
        reg: S390xRegister,
        offset: i64,
    ) -> FailableInstrEncoding {
        code_buf[index..index + Self::JUMP_SIZE].copy_from_slice(&branch_cond(
            reg,
            offset,
            ComparisonMask::MaskEQ,
        )?);
        Ok(())
    }

    fn jump_close(
        code_buf: &mut Vec<u8>,
        reg: S390xRegister,
        offset: i64,
    ) -> FailableInstrEncoding {
        code_buf.extend(branch_cond(reg, offset, ComparisonMask::MaskNE)?);
        Ok(())
    }

    fn nop_loop_open(code_buf: &mut Vec<u8>) {
        // BRANCH ON CONDITION with all operands set to zero is used as a NO-OP.
        // BC and BCR are variants of BRANCH ON CONDITION with different encodings, and extended
        // mnemonics for when used as NOP instructions
        // BC 0, 0 {RX-b}
        const NOPR: [u8; 4] = [0x47, 0x00, 0x00, 0x00];
        // BCR 0, 0 {RR}
        const NOP: [u8; 2] = [0x07, 0x00];
        code_buf.extend(NOPR.repeat(4));
        code_buf.extend(NOP);
    }

    fn inc_reg(code_buf: &mut Vec<u8>, reg: S390xRegister) {
        add_reg_signed(code_buf, reg, 1);
    }

    fn inc_byte(code_buf: &mut Vec<u8>, reg: S390xRegister) {
        S390xInter::add_byte(code_buf, reg, 1);
    }

    fn dec_reg(code_buf: &mut Vec<u8>, reg: S390xRegister) {
        add_reg_signed(code_buf, reg, -1);
    }

    fn dec_byte(code_buf: &mut Vec<u8>, reg: S390xRegister) {
        S390xInter::sub_byte(code_buf, reg, 1);
    }

    fn add_reg(code_buf: &mut Vec<u8>, reg: S390xRegister, imm: u64) {
        add_reg_signed(code_buf, reg, imm as i64);
    }

    fn add_byte(code_buf: &mut Vec<u8>, reg: S390xRegister, imm: u8) {
        code_buf.extend(load_from_byte(reg));
        add_reg_signed(code_buf, TMP_REG, i64::from(imm));
        code_buf.extend(store_to_byte(reg, TMP_REG));
    }

    fn sub_reg(code_buf: &mut Vec<u8>, reg: S390xRegister, imm: u64) {
        // There are no equivalent sub instructions to any of the add instructions used.
        // Given that in 2's complement with wrapping, adding i64::MIN and subtracting i64::MIN are
        // equivalent (except possibly for effect on overflow flag, which is never checked in this
        // program), simply make sure that if imm is i64::MIN, pass it directly, otherwise, pass
        // `-imm`
        // check that "-imm" won't cause problems, then call add_reg with negative imm.
        add_reg_signed(code_buf, reg, (imm as i64).wrapping_neg());
    }

    fn sub_byte(code_buf: &mut Vec<u8>, reg: S390xRegister, imm: u8) {
        code_buf.extend(load_from_byte(reg));
        add_reg_signed(code_buf, TMP_REG, -i64::from(imm as i8));
        code_buf.extend(store_to_byte(reg, TMP_REG));
    }

    fn zero_byte(code_buf: &mut Vec<u8>, reg: S390xRegister) {
        code_buf.extend(store_to_byte(reg, S390xRegister::R0));
    }
}

// This test suite was made far more difficult by the fact that some of the mnemonics used by
// real-world assemblers are different from the opcodes used in the documentation cited above.
#[cfg(test)]
#[cfg_attr(
    feature = "disasmtests",
    expect(
        overflowing_literals,
        reason = "needed to demonstrate bitwise equivalence"
    )
)]
mod tests {
    #[cfg(feature = "disasmtests")]
    use super::super::test_utils::Disassembler;
    use super::*;
    use test_macros::disasm_test;

    #[cfg_attr(
        not(feature = "disasmtests"),
        expect(unused_macros, reason = "macro only used in disassembly tests")
    )]
    /// Given that even though it is set to use hex immediates, the LLVM disassembler for this
    /// architecture often uses decimal immediates, it's sometimes necessary to explain why a given
    /// immediate is expected in the disassembly, so this macro can be used as a compiler-checked
    /// way to explain the reasoning
    macro_rules! given_that {
        ($expr: expr) => {
            #[allow(
                clippy::unreadable_literal,
                reason = "disasm doesn't have _ in literals"
            )]
            const {
                assert!($expr);
            }
        };
    }

    #[cfg(feature = "disasmtests")]
    fn disassembler() -> Disassembler {
        Disassembler::new(ElfArch::S390x)
    }

    #[disasm_test]
    fn test_store_load() {
        let mut ds = disassembler();
        assert_eq!(
            ds.disassemble(load_from_byte(S390xRegister::R8).into()),
            ["llgc %r5, 0(%r8,0)"]
        );
        assert_eq!(
            ds.disassemble(store_to_byte(S390xRegister::R8, S390xRegister::R5).into()),
            ["stc %r5, 0(%r8,0)"]
        );
        assert_eq!(
            ds.disassemble(store_to_byte(S390xRegister::R5, S390xRegister::R8).into()),
            ["stc %r8, 0(%r5,0)"]
        );
    }

    #[disasm_test]
    fn test_reg_copy() {
        let mut v: Vec<u8> = Vec::new();
        S390xInter::reg_copy(&mut v, S390xRegister::R2, S390xRegister::R1);
        assert_eq!(disassembler().disassemble(v), ["lgr %r2, %r1"]);
    }

    #[disasm_test]
    fn test_set_reg_zero() {
        let (mut a, mut b): (Vec<u8>, Vec<u8>) = (Vec::new(), Vec::new());
        S390xInter::set_reg(&mut a, S390xRegister::R2, 0);
        S390xInter::reg_copy(&mut b, S390xRegister::R2, S390xRegister::R0);
        assert_eq!(a, b);
        assert_eq!(disassembler().disassemble(a), ["lgr %r2, %r0"]);
    }

    #[disasm_test]
    fn test_reg_set_small_imm() {
        let mut v: Vec<u8> = Vec::new();
        S390xInter::set_reg(&mut v, S390xRegister::R5, 12345);
        S390xInter::set_reg(&mut v, S390xRegister::R8, -12345);
        assert_eq!(
            disassembler().disassemble(v),
            ["lghi %r5, 12345", "lghi %r8, -12345"]
        );
    }

    #[disasm_test]
    fn test_set_medium_imm() {
        let mut v: Vec<u8> = Vec::new();
        S390xInter::set_reg(&mut v, S390xRegister::R4, 0x1234_abcd);
        S390xInter::set_reg(&mut v, S390xRegister::R4, -0x1234_abcd);
        assert_eq!(
            disassembler().disassemble(v),
            ["lgfi %r4, 305441741", "lgfi %r4, -305441741"]
        );
    }

    #[disasm_test]
    fn test_set_large_imm() {
        let mut ds = Disassembler::new(ElfArch::S390x);
        // this one's messy, due to the number of possible combinations
        let mut v: Vec<u8> = Vec::new();
        S390xInter::set_reg(&mut v, S390xRegister::R1, 0xdead_0000_beef);
        given_that!(0xdead == 57005 && 0xbeef == 48879);
        assert_eq!(
            ds.disassemble(v.clone()),
            ["lgfi %r1, 48879", "iihl %r1, 57005"]
        );
        v.clear();

        S390xInter::set_reg(&mut v, S390xRegister::R2, -0xdead_0000_beef);
        given_that!(-0xbeef_i16 == -48879 && !0xdead_i16 == 8530);
        assert_eq!(
            ds.disassemble(v.clone()),
            ["lgfi %r2, -48879", "iihl %r2, 8530"]
        );
        v.clear();

        S390xInter::set_reg(&mut v, S390xRegister::R3, 0xdead_0000_0000);
        assert_eq!(
            ds.disassemble(v.clone()),
            ["lgr %r3, %r0", "iihl %r3, 57005"]
        );
        v.clear();

        S390xInter::set_reg(&mut v, S390xRegister::R4, i64::MAX ^ (0xffff << 32));
        assert_eq!(
            ds.disassemble(v.clone()),
            ["lghi %r4, -1", "iihh %r4, 32767"]
        );
        v.clear();

        S390xInter::set_reg(&mut v, S390xRegister::R5, i64::MIN ^ (0xffff << 32));
        assert_eq!(
            ds.disassemble(v.clone()),
            ["lgr %r5, %r0", "iihh %r5, 32768"]
        );
        v.clear();

        S390xInter::set_reg(&mut v, S390xRegister::R8, 0x1234_5678_9abc_def0);
        given_that!(0x1234_5678 == 305419896);
        given_that!(0x9abc_def0_u32 as i32 == -1698898192);
        assert_eq!(
            ds.disassemble(v.clone()),
            ["lgfi %r8, -1698898192", "iihf %r8, 305419896"]
        );
        v.clear();

        S390xInter::set_reg(&mut v, S390xRegister::R8, -0x1234_5678_9abc_def0);
        assert_eq!(
            ds.disassemble(v.clone()),
            ["lgfi %r8, 1698898192", "iihf %r8, 3989547399"]
        );
    }

    #[disasm_test]
    fn jump_tests() {
        assert_eq!(
            S390xInter::jump_open(&mut [0; 18], 0, S390xRegister::R3, 0x1_2345_6789_abcd)
                .unwrap_err()
                .error_id(),
            BFErrorID::JumpTooLong
        );
        let mut v: Vec<u8> = vec![0; 18];
        S390xInter::jump_open(&mut v, 0, S390xRegister::R3, 18).unwrap();
        S390xInter::jump_close(&mut v, S390xRegister::R3, -36).unwrap();
        S390xInter::nop_loop_open(&mut v);
        // it took a while, but I found a comment in the LLVM source code* that explained that
        // it uses "jge" instead of the IBM-documented "jle" extended mnemonic for
        // `brcl 8,addr` because "jl" is also "jump if less". Thinking that Capstone was
        // getting this wrong is part of what motivated me to switch to LLVM disassembler in
        // the first place.
        //
        // Argh!
        //
        // * I ran `apt source llvm-19` on Debian Bookworm and found it in the file within the
        // source tree at llvm/lib/Target/SystemZ/SystemZInstrInfo.td
        let mut disasm_lines = Disassembler::new(ElfArch::S390x).disassemble(v).into_iter();
        assert_eq!(disasm_lines.next().unwrap(), "llgc %r5, 0(%r3,0)");
        assert_eq!(disasm_lines.next().unwrap(), "cfi %r5, 0");
        assert_eq!(disasm_lines.next().unwrap(), "jge 0x12");
        assert_eq!(disasm_lines.next().unwrap(), "llgc %r5, 0(%r3,0)");
        assert_eq!(disasm_lines.next().unwrap(), "cfi %r5, 0");
        // lh for low | high (i.e. not equal).
        // For some reason, LLVM treats operand as an unsigned immediate after sign extending it to
        // the full 64 bits, so -0x24i32 becomes 0xffffffffffffffdcu64
        given_that!(-0x24_i32 as i64 as u64 == 0xffffffffffffffdc);
        assert_eq!(disasm_lines.next().unwrap(), "jglh 0xffffffffffffffdc");
        // LLVM apparently also flips the nop and nopr mnemonics, and requires that they have
        // arguments. I double-checked the IBM docs on this one after seeing this, and I got it
        // the right way around, so I'm confused here.
        for i in 0..4 {
            assert_eq!(
                disasm_lines.next().unwrap(),
                "nop 0",
                "only {i}/4 nopr instructions were matched"
            );
        }
        assert_eq!(disasm_lines.next().unwrap(), "nopr %r0");
        assert!(disasm_lines.next().is_none());
    }

    #[disasm_test]
    fn syscall_test() {
        let mut v: Vec<u8> = Vec::new();
        S390xInter::syscall(&mut v);
        assert_eq!(Disassembler::new(ElfArch::S390x).disassemble(v), ["svc 0"]);
    }

    #[disasm_test]
    fn zero_byte_test() {
        let mut v: Vec<u8> = Vec::new();
        S390xInter::zero_byte(&mut v, S390xInter::REGISTERS.bf_ptr);
        assert_eq!(
            v,
            store_to_byte(S390xInter::REGISTERS.bf_ptr, S390xRegister::R0)
        );
        assert_eq!(disassembler().disassemble(v), ["stc %r0, 0(%r8,0)"]);
    }

    #[disasm_test]
    /// test `S390xInter::inc_reg`, `S390xInter::dec_reg`, and test `S390xInter::add_reg` and
    /// `S390xInter::sub_reg` for immediates that can be expressed with 16 bits
    fn reg_arith_small_imms() {
        let mut ds = disassembler();

        let mut a: Vec<u8> = Vec::new();
        let mut b: Vec<u8> = Vec::new();
        S390xInter::add_reg(&mut a, S390xRegister::R8, 1);
        S390xInter::inc_reg(&mut b, S390xRegister::R8);
        // check that inc_reg is the same as add_reg(.., 1)
        assert_eq!(a, b);
        assert_eq!(ds.disassemble(a), ["aghi %r8, 1"]);

        let mut a: Vec<u8> = Vec::new();
        b.clear();
        S390xInter::sub_reg(&mut a, S390xRegister::R8, 1);
        S390xInter::dec_reg(&mut b, S390xRegister::R8);
        // check that dec_reg is the same as sub_reg(.., 1)
        assert_eq!(a, b);
        // make sure that the disassembly is as expected.
        assert_eq!(ds.disassemble(a), ["aghi %r8, -1"]);

        let mut a: Vec<u8> = Vec::new();
        b.clear();
        S390xInter::add_reg(&mut a, S390xRegister::R8, 12345);
        S390xInter::sub_reg(&mut a, S390xRegister::R8, 12345);

        S390xInter::sub_reg(&mut b, S390xRegister::R8, -12345_i64 as u64);
        S390xInter::add_reg(&mut b, S390xRegister::R8, -12345_i64 as u64);
        assert_eq!(a, b);
        assert_eq!(ds.disassemble(a), ["aghi %r8, 12345", "aghi %r8, -12345"]);
    }

    #[disasm_test]
    /// test `S390xInter::add_reg` and `S390xInter::sub_reg` for immediates that fit within 32
    /// bits
    fn reg_arith_medium_imms() {
        let mut ds = disassembler();

        let mut v: Vec<u8> = Vec::new();
        S390xInter::add_reg(&mut v, S390xRegister::R8, 0x123_456);
        given_that!(0x123_456 == 1193046);
        assert_eq!(ds.disassemble(v), ["agfi %r8, 1193046"]);

        let mut a: Vec<u8> = Vec::new();
        given_that!(0 - 0x123_456 == -1193046);
        S390xInter::sub_reg(&mut a, S390xRegister::R8, 0x123_456);
        assert_eq!(ds.disassemble(a), ["agfi %r8, -1193046"]);
    }

    #[disasm_test]
    /// test `S390xInter::add_reg` and `S390x::sub_reg` for immediates too large to fit within
    /// 32 bits
    fn reg_arith_large_imms() {
        let mut ds = disassembler();
        let mut v: Vec<u8> = Vec::new();
        S390xInter::add_reg(&mut v, S390xRegister::R8, 9_876_543_210);
        given_that!(9_876_543_210_i64 as i32 == 1286608618);
        given_that!((9_876_543_210_i64 >> 32) == 2);
        assert_eq!(ds.disassemble(v), ["agfi %r8, 1286608618", "aih %r8, 2"]);

        let mut a: Vec<u8> = Vec::new();
        S390xInter::sub_reg(&mut a, S390xRegister::R8, 9_876_543_210);
        given_that!(-9_876_543_210_i32 == -1286608618);
        given_that!((-9_876_543_210_i64 >> 32) == -3);
        assert_eq!(ds.disassemble(a), ["agfi %r8, -1286608618", "aih %r8, -3"]);

        // make sure that if the lower bits are zero, the `agfi` instruction is skipped
        let mut a: Vec<u8> = Vec::new();
        S390xInter::add_reg(&mut a, S390xRegister::R8, 0x1234_abcd_0000_0000);
        given_that!(0x1234_abcd_0000_0000_i64 >> 32 == 305441741);
        assert_eq!(ds.disassemble(a), ["aih %r8, 305441741"]);
    }

    /// check that `S390xInter::sub_reg` and `S390xInter::add_reg` output the same code with `imm`
    /// set to `i64::MIN as u64`
    #[test]
    fn sub_reg_int_min() {
        let mut a: Vec<u8> = Vec::new();
        let mut b: Vec<u8> = Vec::new();
        S390xInter::add_reg(&mut a, S390xRegister::R4, i64::MIN as u64);
        S390xInter::sub_reg(&mut b, S390xRegister::R4, i64::MIN as u64);
        assert_eq!(a, b);
    }

    #[disasm_test]
    /// test `S390xInter::add_byte`, `S390xInter::sub_byte`, `S390xInter::inc_byte`, and
    /// `S390xInter::dec_byte`
    fn test_byte_arith() {
        let mut ds = disassembler();

        let mut expected = Vec::from(load_from_byte(S390xRegister::R8));
        S390xInter::inc_reg(&mut expected, TMP_REG);
        expected.extend(store_to_byte(S390xRegister::R8, TMP_REG));

        let mut a: Vec<u8> = Vec::new();
        let mut b: Vec<u8> = Vec::new();

        S390xInter::inc_byte(&mut a, S390xRegister::R8);
        S390xInter::add_byte(&mut b, S390xRegister::R8, 1);
        assert_eq!(a, b);
        assert_eq!(a, expected);
        assert_eq!(
            ds.disassemble(b),
            ["llgc %r5, 0(%r8,0)", "aghi %r5, 1", "stc %r5, 0(%r8,0)"]
        );

        expected = Vec::from(load_from_byte(S390xRegister::R8));
        S390xInter::dec_reg(&mut expected, TMP_REG);
        expected.extend(store_to_byte(S390xRegister::R8, TMP_REG));
        a.clear();
        let mut b: Vec<u8> = Vec::new();
        S390xInter::dec_byte(&mut a, S390xRegister::R8);
        S390xInter::sub_byte(&mut b, S390xRegister::R8, 1);
        assert_eq!(a, b);
        assert_eq!(a, expected);
        assert_eq!(
            ds.disassemble(b),
            ["llgc %r5, 0(%r8,0)", "aghi %r5, -1", "stc %r5, 0(%r8,0)"]
        );

        a.clear();
        S390xInter::add_byte(&mut a, S390xRegister::R8, 32);
        S390xInter::sub_byte(&mut a, S390xRegister::R8, 32);
        assert_eq!(
            ds.disassemble(a),
            [
                "llgc %r5, 0(%r8,0)",
                "aghi %r5, 32",
                "stc %r5, 0(%r8,0)",
                "llgc %r5, 0(%r8,0)",
                "aghi %r5, -32",
                "stc %r5, 0(%r8,0)"
            ]
        );
    }
}
