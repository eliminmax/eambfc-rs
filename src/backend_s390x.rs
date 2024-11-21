// SPDX-FileCopyrightText: 2024 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use super::arch_inter::{ArchInter, Registers, SyscallNums};
use super::compile::BFCompile;
use super::elf_tools::{EIData, ELFArch};
use super::err::BFCompileError;

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
pub enum S390xRegister {
    R0 = 0, // zero register
    R1 = 1, // syscall register
    R2 = 2, // arg1 register
    R3 = 3, // arg2 register
    R4 = 4, // arg3 register, scratch register
    R5 = 5, // scratch register
    R8 = 8, // bf pointer register
}

macro_rules! encode_ri_op {
    ($opcode:literal, $reg:ident) => {{
        // Ensure only lower 4 bits of cond are used - the const _: () mess forces the check to
        // run at compile time rather than runtime.
        const _: () = assert!($opcode & (!0xfff) == 0);
        vec![
            ($opcode >> 4) as u8,
            ($reg as u8) << 4 | (($opcode & 0xf) as u8),
        ]
    }};
    ($opcode:literal, $reg:ident, $t:ty, $imm:ident) => {{
        let mut v: Vec<u8> = encode_ri_op!($opcode, $reg);
        v.extend(($imm as $t).to_be_bytes());
        v
    }};
    ($opcode:literal, $reg:ident, $t:ty, $imm:literal) => {{
        let mut v: Vec<u8> = encode_ri_op!($opcode, $reg);
        v.extend(($imm as $t).to_be_bytes());
        v
    }};
}

#[repr(u8)]
enum ComparisonMask {
    MaskEQ = 8,
    MaskNE = 6, // `MaskLT | MaskGT` (i.e. 4 | 2)
}

fn aux_reg(reg: S390xRegister) -> S390xRegister {
    if reg == S390xRegister::R4 {
        S390xRegister::R5
    } else {
        S390xRegister::R4
    }
}

fn store_to_byte(reg: S390xRegister, aux: S390xRegister) -> [u8; 4] {
    /* STC aux, 0(reg) {RX-a} */
    [0x42u8, ((aux as u8) << 4) | (reg as u8), 0x00, 0x00]
}

fn load_from_byte(reg: S390xRegister, aux: S390xRegister) -> [u8; 6] {
    // LLGC aux, 0(reg) {RXY-a}
    [
        0xe3,
        ((aux as u8) << 4) | (reg as u8),
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
) -> Result<Vec<u8>, BFCompileError> {
    // jumps are done by halfwords, not bytes, so make sure it's a valid offset with that in mind
    match offset {
        i if i % 2 != 0 => Err(BFCompileError::Basic {
            id: String::from("INVALID_JUMP_ADDRESS"),
            msg: String::from("offset is not on a halfword boundary"),
        }),
        i if (i > 0 && (i >> 17) != 0) || (i < 0 && (i >> 17 != -1)) => {
            Err(BFCompileError::Basic {
                id: String::from("JUMP_TOO_LONG"),
                msg: String::from("offset out of range for this architecture"),
            })
        }
        _ => {
            let aux = aux_reg(reg);
            let mut v = Vec::<u8>::from(load_from_byte(reg, aux));
            let offset = offset >> 1;
            // CFI aux, 0 {RIL-a}
            v.extend(encode_ri_op!(0xc2d, aux, i32, 0));
            // BRCL mask, offset
            v.extend(encode_ri_op!(0xc04, comp_mask, i32, offset));

            Ok(v)
        }
    }
}

pub struct S390xInter;
impl ArchInter for S390xInter {
    type RegType = S390xRegister;
    const JUMP_SIZE: usize = 18;
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

    const ARCH: ELFArch = ELFArch::S390x;
    const EI_DATA: EIData = EIData::ELFDATA2MSB;

    fn set_reg(reg: S390xRegister, imm: i64) -> Vec<u8> {
        match imm {
            0 => Self::reg_copy(reg, S390xRegister::R0),
            i if ((i16::MIN as i64)..=(i16::MAX as i64)).contains(&i) => {
                // if it fits in a halfword, use Load Halfword Immediate (64 <- 16)
                // LGHI r.reg, imm {RI-a}
                encode_ri_op!(0xa79, reg, i16, imm)
            }
            i if ((i32::MIN as i64)..=(i32::MAX as i64)).contains(&i) => {
                // if it fits within a word, use Load Immediate (64 <- 32)
                // LGFI r.reg, imm {RIL-a}
                encode_ri_op!(0xc01, reg, i32, imm)
            }
            _ => {
                let (imm_h, imm_l) = ((imm >> 32) as i32, imm as i32);
                let mut v: Vec<u8> = if imm_l == 0 {
                    vec![]
                } else {
                    Self::set_reg(reg, imm_l as i64)
                };
                v.extend(match ((imm_h >> 16) as i16, imm_h as i16) {
                    (0, 0) => unreachable!(),
                    (0, imm_hl) => {
                        // set bits 16-31 of the register to the immediate, leave other bits as-is
                        // IIHL reg, upper_imm {RI-a}
                        encode_ri_op!(0xa51, reg, i16, imm_hl)
                    }
                    (imm_hh, 0) => {
                        // set bits 0-15 of the register to the immediate, leave other bits as-is
                        // IIHH reg, upper_imm {RI-a}
                        encode_ri_op!(0xa50, reg, i16, imm_hh)
                    }
                    _ => {
                        // need to set the full upper word, with Insert Immediate (high)
                        // IIHF reg, imm {RIL-a}
                        encode_ri_op!(0xc09, reg, i32, imm_h)
                    }
                });
                v
            }
        }
    }

    fn reg_copy(dst: S390xRegister, src: S390xRegister) -> Vec<u8> {
        // LGR dst, src {RRE}
        vec![0xb9, 0x04, 0x00, (dst as u8) << 4 | (src as u8)]
    }

    fn syscall() -> Vec<u8> {
        // SVC 0 {I}
        vec![0x0a_u8, 0x00]
    }

    fn jump_zero(reg: S390xRegister, offset: i64) -> Result<Vec<u8>, BFCompileError> {
        branch_cond(reg, offset, ComparisonMask::MaskEQ)
    }

    fn jump_not_zero(reg: S390xRegister, offset: i64) -> Result<Vec<u8>, BFCompileError> {
        branch_cond(reg, offset, ComparisonMask::MaskNE)
    }

    fn nop_loop_open() -> Vec<u8> {
        // BRANCH ON CONDITION with all operands set to zero is used as a NO-OP.
        // BC and BCR are variants of BRANCH ON CONDITION with different encodings, and extended
        // mnemonics for when used as NOP instructions
        // BC 0, 0 {RX-b}
        const NOPR: [u8; 4] = [0x47, 0x00, 0x00, 0x00];
        // BCR 0, 0 {RR}
        const NOP: [u8; 2] = [0x07, 0x00];
        let mut v = Vec::<u8>::with_capacity(Self::JUMP_SIZE);
        v.extend(NOPR);
        v.extend(NOPR);
        v.extend(NOPR);
        v.extend(NOPR);
        v.extend(NOP);
        v
    }

    fn inc_reg(reg: S390xRegister) -> Vec<u8> {
        S390xInter::add_reg(reg, 1).expect("S390xInter::add_reg doesn't return Err variant")
    }

    fn inc_byte(reg: S390xRegister) -> Vec<u8> {
        S390xInter::add_byte(reg, 1)
    }

    fn dec_reg(reg: S390xRegister) -> Vec<u8> {
        S390xInter::add_reg(reg, -1).expect("S390xInter::add_reg doesn't return Err variant")
    }

    fn dec_byte(reg: S390xRegister) -> Vec<u8> {
        S390xInter::add_byte(reg, -1)
    }

    fn add_reg(reg: S390xRegister, imm: i64) -> Result<Vec<u8>, BFCompileError> {
        match imm {
            i if ((i16::MIN as i64)..=(i16::MAX as i64)).contains(&i) => {
                // AGHI reg, imm {RI-a}
                Ok(encode_ri_op!(0xa7b, reg, i16, imm))
            }
            i if ((i32::MIN as i64)..=(i32::MAX as i64)).contains(&i) => {
                // AFGI reg, imm {RIL-a}
                Ok(encode_ri_op!(0xc28, reg, i32, imm))
            }
            _ => {
                let (imm_h, imm_l) = (imm >> 32, imm as i32);
                let mut v: Vec<u8> = if imm_l == 0 {
                    vec![]
                } else {
                    S390xInter::add_reg(reg, imm_l as i64)
                        .expect("S390xInter::add_reg doesn't return Err variant")
                };
                // AIX reg, imm {RIL-a}
                v.extend(encode_ri_op!(0xcc8, reg, i32, imm_h));
                Ok(v)
            }
        }
    }

    fn add_byte(reg: S390xRegister, imm: i8) -> Vec<u8> {
        let aux = aux_reg(reg);
        let mut v = Vec::from(load_from_byte(reg, aux));
        v.extend(
            S390xInter::add_reg(aux, imm as i64)
                .expect("S390xInter::add_reg doesn't return Err variant"),
        );
        v.extend(store_to_byte(reg, aux));
        v
    }

    fn sub_reg(reg: S390xRegister, imm: i64) -> Result<Vec<u8>, BFCompileError> {
        // there are not equivalent sub instructions to any of the add instructions used, so just
        // check that "-imm" won't cause problems, then call add_reg with negative imm.
        if imm == i64::MIN {
            let mut v = S390xInter::add_reg(reg, -i64::MAX)?;
            v.extend(S390xInter::add_reg(reg, -1)?);
            Ok(v)
        } else {
            S390xInter::add_reg(reg, -imm)
        }
    }

    fn sub_byte(reg: S390xRegister, imm: i8) -> Vec<u8> {
        let aux = aux_reg(reg);
        let mut v = Vec::from(load_from_byte(reg, aux));
        v.extend(
            S390xInter::add_reg(aux, -imm as i64)
                .expect("S390xInter::add_reg doesn't return Err variant"),
        );
        v.extend(store_to_byte(reg, aux));
        v
    }

    fn zero_byte(reg: S390xRegister) -> Vec<u8> {
        Vec::<u8>::from(store_to_byte(reg, S390xRegister::R0))
    }
}

impl BFCompile for S390xInter {}
