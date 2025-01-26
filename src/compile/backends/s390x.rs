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

#[derive(Debug, Copy, Clone, PartialEq)]
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

macro_rules! encode_ri_op {
    ($code_buf:ident, $opcode:literal, $reg:ident) => {{
        // Ensure only lower 12 bits of cond are used
        const { assert!($opcode & (!0xfff) == 0) };
        $code_buf.extend([
            ($opcode >> 4) as u8,
            ($reg as u8) << 4 | (($opcode & 0xf) as u8),
        ]);
    }};
    ($code_buf:ident, $opcode:literal, $reg:ident, $t:ty, $imm:expr) => {{
        encode_ri_op!($code_buf, $opcode, $reg);
        $code_buf.extend(($imm as $t).to_be_bytes());
    }};
    ($code_buf:ident, $opcode:literal, $reg:ident, $imm:literal) => {{
        encode_ri_op!($code_buf, $opcode, $reg);
        #[allow(
            clippy::unseparated_literal_suffix,
            reason = "Need to specify type for literal"
        )]
        $code_buf.extend($imm.to_be_bytes());
    }};
    ($code_buf:ident, $opcode:literal, $reg:ident, $imm:expr) => {{
        encode_ri_op!($code_buf, $opcode, $reg);
        $code_buf.extend($imm.to_be_bytes());
    }};
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
    code_buf: &mut Vec<u8>,
    reg: S390xRegister,
    offset: i64,
    comp_mask: ComparisonMask,
) -> FailableInstrEncoding {
    let offset: i32 = i16::try_from(offset >> 1)
        .map_err(|_| {
            BFCompileError::basic(
                BFErrorID::JumpTooLong,
                "offset out of range for this architecture",
            )
        })?
        .into();
    code_buf.extend(load_from_byte(reg));
    // CFI aux, 0 {RIL-a}
    encode_ri_op!(code_buf, 0xc2d, TMP_REG, 0i32);
    // BRCL mask, offset
    encode_ri_op!(code_buf, 0xc04, comp_mask, offset);

    Ok(())
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
            encode_ri_op!(code_buf, 0xa79, reg, imm16);
        } else if let Ok(imm32) = i32::try_from(imm) {
            // if it fits within a word, use Load Immediate (64 <- 32)
            // LGFI r.reg, imm {RIL-a}
            encode_ri_op!(code_buf, 0xc01, reg, imm32);
        } else {
            Self::set_reg(code_buf, reg, ((imm as u64) & 0xffff_ffff) as i64);

            let default_val: i16 = if imm.is_negative() { -1 } else { 0 };

            let imm_high = (imm >> 32) as i32;

            match ((imm_high >> 16) as i16, imm_high as i16) {
                (n, imm_high_low) if n == default_val => {
                    // set bits 16-31 of the register to the immediate, leave other bits as-is
                    // IIHL reg, upper_imm {RI-a}
                    encode_ri_op!(code_buf, 0xa51, reg, imm_high_low);
                }
                (imm_high_high, n) if n == default_val => {
                    // set bits 0-15 of the register to the immediate, leave other bits as-is
                    // IIHH reg, upper_imm {RI-a}
                    encode_ri_op!(code_buf, 0xa50, reg, imm_high_high);
                }
                _ => {
                    // need to set the full upper word, with Insert Immediate (high)
                    // IIHF reg, imm {RIL-a}
                    encode_ri_op!(code_buf, 0xc09, reg, imm_high);
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

    fn jump_zero(code_buf: &mut Vec<u8>, reg: S390xRegister, offset: i64) -> FailableInstrEncoding {
        branch_cond(code_buf, reg, offset, ComparisonMask::MaskEQ)
    }

    fn jump_not_zero(
        code_buf: &mut Vec<u8>,
        reg: S390xRegister,
        offset: i64,
    ) -> FailableInstrEncoding {
        branch_cond(code_buf, reg, offset, ComparisonMask::MaskNE)
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
        S390xInter::add_reg(code_buf, reg, 1);
    }

    fn inc_byte(code_buf: &mut Vec<u8>, reg: S390xRegister) {
        S390xInter::add_byte(code_buf, reg, 1);
    }

    fn dec_reg(code_buf: &mut Vec<u8>, reg: S390xRegister) {
        S390xInter::add_reg(code_buf, reg, -1);
    }

    fn dec_byte(code_buf: &mut Vec<u8>, reg: S390xRegister) {
        S390xInter::add_byte(code_buf, reg, -1);
    }

    fn add_reg(code_buf: &mut Vec<u8>, reg: S390xRegister, imm: i64) {
        match imm {
            i if (i64::from(i16::MIN)..=i64::from(i16::MAX)).contains(&i) => {
                // AGHI reg, imm {RI-a}
                encode_ri_op!(code_buf, 0xa7b, reg, i16, imm);
            }
            i if (i64::from(i32::MIN)..=i64::from(i32::MAX)).contains(&i) => {
                // AFGI reg, imm {RIL-a}
                encode_ri_op!(code_buf, 0xc28, reg, i32, imm);
            }
            _ => {
                let (imm_h, imm_l) = (imm >> 32, imm as i32);
                if imm_l != 0 {
                    S390xInter::add_reg(code_buf, reg, i64::from(imm_l));
                }
                // AIX reg, imm {RIL-a}
                encode_ri_op!(code_buf, 0xcc8, reg, i32, imm_h);
            }
        }
    }

    fn add_byte(code_buf: &mut Vec<u8>, reg: S390xRegister, imm: i8) {
        code_buf.extend(load_from_byte(reg));
        S390xInter::add_reg(code_buf, TMP_REG, i64::from(imm));
        code_buf.extend(store_to_byte(reg, TMP_REG));
    }

    fn sub_reg(code_buf: &mut Vec<u8>, reg: S390xRegister, imm: i64) {
        // there are not equivalent sub instructions to any of the add instructions used, so just
        // check that "-imm" won't cause problems, then call add_reg with negative imm.
        if imm == i64::MIN {
            S390xInter::add_reg(code_buf, reg, -i64::MAX);
            S390xInter::add_reg(code_buf, reg, -1);
        } else {
            S390xInter::add_reg(code_buf, reg, -imm);
        }
    }

    fn sub_byte(code_buf: &mut Vec<u8>, reg: S390xRegister, imm: i8) {
        code_buf.extend(load_from_byte(reg));
        S390xInter::add_reg(code_buf, TMP_REG, i64::from(-imm));
        code_buf.extend(store_to_byte(reg, TMP_REG));
    }

    fn zero_byte(code_buf: &mut Vec<u8>, reg: S390xRegister) {
        code_buf.extend(store_to_byte(reg, S390xRegister::R0));
    }
}

#[cfg(test)]
mod tests {
    use super::super::disassemble;
    use super::*;
    use capstone::prelude::*;

    fn engine() -> Capstone {
        Capstone::new()
            .sysz()
            .mode(arch::sysz::ArchMode::Default)
            .build()
            .expect("Failed to build Capstone inteface")
    }

    #[test]
    fn test_store_load() {
        let cs = engine();
        assert_eq!(
            disassemble(&load_from_byte(S390xRegister::R8), &cs),
            ["llgc %r5, 0(%r8)"]
        );
        assert_eq!(
            disassemble(&store_to_byte(S390xRegister::R8, S390xRegister::R5), &cs),
            ["stc %r5, 0(%r8)"]
        );
        assert_eq!(
            disassemble(&store_to_byte(S390xRegister::R5, S390xRegister::R8), &cs),
            ["stc %r8, 0(%r5)"]
        );
    }

    #[test]
    fn test_reg_copy() {
        let mut v: Vec<u8> = Vec::new();
        S390xInter::reg_copy(&mut v, S390xRegister::R2, S390xRegister::R1);
        assert_eq!(disassemble(&v, &engine()), ["lgr %r2, %r1"]);
    }

    #[test]
    fn test_set_reg_zero() {
        let (mut a, mut b): (Vec<u8>, Vec<u8>) = (Vec::new(), Vec::new());
        S390xInter::set_reg(&mut a, S390xRegister::R2, 0);
        S390xInter::reg_copy(&mut b, S390xRegister::R2, S390xRegister::R0);
        assert_eq!(disassemble(&a, &engine()), ["lgr %r2, %r0"]);
        assert_eq!(a, b);
    }

    #[test]
    fn test_reg_set_small_imm() {
        let mut v: Vec<u8> = Vec::new();
        let cs = engine();
        S390xInter::set_reg(&mut v, S390xRegister::R5, 0xabc);
        assert_eq!(disassemble(&v, &cs), ["lghi %r5, 0xabc"]);
        v.clear();

        S390xInter::set_reg(&mut v, S390xRegister::R8, -0xabc);
        assert_eq!(disassemble(&v, &cs), ["lghi %r8, -0xabc"]);
    }

    #[test]
    fn test_set_medium_imm() {
        let mut v: Vec<u8> = Vec::new();
        S390xInter::set_reg(&mut v, S390xRegister::R4, 0x1234_abcd);
        S390xInter::set_reg(&mut v, S390xRegister::R4, -0x1234_abcd);
        assert_eq!(
            disassemble(&v, &engine()),
            ["lgfi %r4, 0x1234abcd", "lgfi %r4, -0x1234abcd"]
        );
    }

    #[test]
    fn test_set_large_imm() {
        // this one's messy, due to the number of possible combinations
        let mut v: Vec<u8> = Vec::new();
        let cs = engine();
        S390xInter::set_reg(&mut v, S390xRegister::R1, 0xdead_0000_beef);
        assert_eq!(disassemble(&v, &cs), ["lgfi %r1, 0xbeef", "iihl %r1, 0xdead"]);
        v.clear();

        S390xInter::set_reg(&mut v, S390xRegister::R2, -0xdead_0000_beef);
        // 2's complement of 0xdead is 0x2152
        assert_eq!(disassemble(&v, &cs), ["lgfi %r2, -0xbeef", "iihl %r2, 0x2152"]);
        v.clear();

        S390xInter::set_reg(&mut v, S390xRegister::R3, 0xdead_0000_0000);
        assert_eq!(disassemble(&v, &cs), ["lgr %r3, %r0", "iihl %r3, 0xdead"]);
        v.clear();

        S390xInter::set_reg(&mut v, S390xRegister::R4, i64::MAX ^ (0xffff << 32));
        assert_eq!(disassemble(&v, &cs), ["lghi %r4, -1", "iihh %r4, 0x7fff"]);
        v.clear();

        S390xInter::set_reg(&mut v, S390xRegister::R5, i64::MIN ^ (0xffff << 32));
        assert_eq!(disassemble(&v, &cs), ["lgr %r5, %r0", "iihh %r5, 0x8000"]);
        v.clear();

        S390xInter::set_reg(&mut v, S390xRegister::R8, 0x1234_5678_9abc_def0);
        // 0x9abcdef0_u32 has the same bit representation as -0x65432110_i32
        assert_eq!(disassemble(&v, &cs), ["lgfi %r8, -0x65432110", "iihf %r8, 0x12345678"]);
        v.clear();

        S390xInter::set_reg(&mut v, S390xRegister::R8, -0x1234_5678_9abc_def0);
        assert_eq!(disassemble(&v, &cs), ["lgfi %r8, 0x65432110", "iihf %r8, 0xedcba987"]);
    }
}
