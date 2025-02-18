// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use super::arch_inter::{ArchInter, FailableInstrEncoding, Registers, SyscallNums};
use super::elf_tools::{ByteOrdering, ElfArch};
use super::MinimumBits;
use crate::err::{BFCompileError, BFErrorID};

/// A `const` assertion that `$val` fits within `$size` bits. `$val` is assumed to be a positive
/// integer.
macro_rules! validate_size {
    ($label: literal, $size: literal, $val: literal) => {
        const {
            assert!(
                $val >> $size == 0,
                concat!($label, " can't be more than ", $size, " bits.")
            )
        };
    };
}

macro_rules! encode_instr {
    ([R] $op: literal, $rd: expr, $rs1: expr, $rs2: expr, $funct3: literal, $funct7: literal) => {{
        validate_size!("opcode", 7, $op);
        validate_size!("funct3", 3, $funct3);
        validate_size!("funct7", 7, $funct7);
        u32::to_le_bytes(
            ($funct7 << 25)
                | (($rs2 as u32) << 20)
                | (($rs1 as u32) << 15)
                | ($funct3 << 12)
                | (($rd as u32) << 7)
                | $op,
        )
    }};
    ([I] $op: literal, $rd: expr, $rs1: expr, $funct3: literal, $imm: expr) => {{
        validate_size!("opcode", 7, $op);
        validate_size!("funct3", 3, $funct3);
        assert!(
            $imm.fits_within_bits(12),
            "I-type expressions take 12-bit immediates"
        );
        #[allow(clippy::cast_lossless, reason = "Need to convert both ints and enums")]
        u32::to_le_bytes(
            ($imm as u32) << 20
                | (($rs1 as u32) << 15)
                | ($funct3 << 12)
                | (($rd as u32) << 7)
                | $op,
        )
    }};
    ([S] $op: literal, $rs1: expr, $rs2: expr, $funct3: literal, $imm: expr) => {{
        validate_size!("opcode", 7, $op);
        validate_size!("funct3", 3, $funct3);
        assert!(
            $imm.fits_within_bits(12),
            "S-type expressions take 12-bit immediates"
        );
        #[allow(clippy::cast_lossless, reason = "Need to convert both ints and enums")]
        u32::to_le_bytes(
            ($imm & 0xfe0) << 25
                | (($rs2 as u32) << 20)
                | (($rs1 as u32) << 15)
                | (($funct3 as u32) << 12)
                | ($imm & 0x1f) << 7
                | $op,
        )
    }};
    ([U] $op: literal, $rd: expr, $imm: expr) => {{
        validate_size!("opcode", 7, $op);
        assert!(
            $imm.fits_within_bits(20),
            "U-type instructions take 20-bit immediates"
        );
        #[allow(clippy::cast_lossless, reason = "Need to convert both ints and enums")]
        u32::to_le_bytes((($imm as u32) << 12) | (($rd as u32) << 7) | $op)
    }};
    ([CI] $op: literal, $rd_rs1: expr, $funct3: literal, $imm: expr) => {{
        validate_size!("opcode", 2, $op);
        validate_size!("funct3", 3, $funct3);
        assert!(
            $imm.fits_within_bits(6),
            "CI-type expressions take 6-bit immediates"
        );
        let imm = $imm as u16;
        #[allow(clippy::cast_lossless, reason = "Need to convert both ints and enums")]
        u16::to_le_bytes(
            $funct3 << 13
                | (imm & (1 << 5)) << 7
                | (($rd_rs1 as u16) << 7)
                | ((imm & 0x1f) << 2)
                | $op,
        )
    }};
}

/// Truncate `val` to `amnt` bits and sign extend the result
const fn sign_extend(val: i64, amnt: u32) -> i64 {
    val << (i64::BITS - amnt) >> (i64::BITS - amnt)
}

// SPDX-SnippetCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only AND Apache-2.0 WITH LLVM-exception
//
// SPDX-SnippetCopyrightText: 2021 Alexander Pivovarov
// SPDX-SnippetCopyrightText: 2021 Ben Shi
// SPDX-SnippetCopyrightText: 2021 Craig Topper
// SPDX-SnippetCopyrightText: 2021 Jim Lin
// SPDX-SnippetCopyrightText: 2020 Simon Pilgrim
// SPDX-SnippetCopyrightText: 2018 - 2019 Alex Bradbury
// SPDX-SnippetCopyrightText: 2019 Chandler Carruth
// SPDX-SnippetCopyrightText: 2019 Sam Elliott
//
// modification copyright 2025 Eli Array Minkoff
//
// And yes, I did have to go through the git commit history of the original file to find everyone
// who had contributed as of 2022, because I didn't want to just go
// "Copyright 2018-2022 LLVM Contributors"
// and call it a day - I believe firmly in giving credit where credit is do.

/// A modified port of LLVM's logic for resolving the `li` (load immediate) pseudo-instruction,
/// as it existed in 2022.
fn encode_li(code_buf: &mut Vec<u8>, reg: u8, val: i64) {
    let lo12 = sign_extend(val, 12);
    if val.fits_within_bits(32) {
        let hi20 = sign_extend(((val as u64).wrapping_add(0x800) >> 12) as i64, 20);
        if hi20 != 0 {
            if hi20.fits_within_bits(6) {
                // C.LUI
                code_buf.extend(encode_instr!([CI] 0b01, reg, 0b011, hi20));
            } else {
                // LUI
                code_buf.extend(encode_instr!([U] 0b011_0111, reg, hi20));
            }
        }
        match (lo12, hi20) {
            (n, 0) if n.fits_within_bits(6) => {
                // C.LI
                code_buf.extend(encode_instr!([CI] 0b01, reg, 0b010, lo12));
            }
            (0, _) => (),
            (n, _) if n.fits_within_bits(6) => {
                // C.ADDIW
                code_buf.extend(encode_instr!([CI] 0b01, reg, 0b001, lo12));
            }
            (_, 0) => {
                // ADDI reg, zero, lo12
                code_buf.extend(encode_instr!([I] 0b001_0011, reg, 0, 0, lo12));
            }
            _ => {
                // ADDIW reg, reg, lo12
                code_buf.extend(encode_instr!([I] 0b001_1011, reg, reg, 0, lo12));
            }
        }
        return;
    }
    // Below this point, the code is more-or-less a straight translation of the original LLVM code,
    // comments and all

    // In the following, constants are processed from LSB to MSB but instruction emission is
    // performed from MSB to LSB by recursively calling encode_li. In each recursion, first the
    // lowest 12 bits are removed from the constant and the optimal shift amount, which can be
    // greater than 12 bits if the constant is sparse, is determined. Then, the shifted remaining
    // constant is processed recursively and gets emitted as soon as it fits into 32 bits. The
    // emission of the shifts and additions is subsequently performed when the recursion returns.
    let mut hi52 = ((val as u64 + 0x800) >> 12) as i64;
    let mut shift_amount = hi52.trailing_zeros() + 12;
    hi52 = sign_extend(hi52 >> (shift_amount - 12), 64 - shift_amount);
    // If the remaining bits don't fit in 12 bits, we might be able to reduce the shift amount in
    // order to use LUI which will zero the lower 12 bits.
    if shift_amount > 12 && !hi52.fits_within_bits(12) && (hi52 << 12).fits_within_bits(32) {
        // Reduce the shift amount and add zeros to the LSBs so it will match LUI.
        shift_amount -= 12;
        hi52 = ((hi52 as u64) << 12) as i64;
    }
    // Recursive call
    encode_li(code_buf, reg, hi52);
    // Generation of the instruction
    if shift_amount != 0 {
        if shift_amount.fits_within_bits(6) {
            // C.SLLI
            code_buf.extend(encode_instr!([CI] 0b10, reg, 0, shift_amount));
        } else {
            // SLLI
            code_buf.extend(encode_instr!([I] 0b001_0011, reg, reg, 0b111, shift_amount));
        }
    }
    if lo12 != 0 {
        if lo12.fits_within_bits(6) {
            code_buf.extend(c_addi(reg, lo12 as i8));
        } else {
            code_buf.extend(addi(reg, lo12 as i16));
        }
    }
}

// SPDX-SnippetEnd

#[derive(Debug, Clone, Copy, PartialEq)]
#[repr(u8)]
pub(in super::super) enum RiscVRegister {
    S0 = 8,  // X8, bf pointer register
    A0 = 10, // X10, arg1 register
    A1 = 11, // X11, arg2 register
    A2 = 12, // X12, arg3 register
    A7 = 17, // X17, syscall register
}

/// Private unrepresentable scratch register used within certain operations
const TEMP_REG: u8 = 6;

pub(crate) struct RiscV64Inter;

fn addi(reg: u8, i: i16) -> [u8; 4] {
    assert!(
        reg != 0 && reg.fits_within_bits(5),
        "reg must be a valid register number"
    );
    assert!(
        i.fits_within_bits(12),
        "addi immediate must fit within 12 bits"
    );
    encode_instr!([I] 0b001_0011, reg, reg, 0, i)
}

#[derive(Clone, Copy, PartialEq)]
enum CompareType {
    Eq,
    Ne,
}

const fn b_type_bithack(dist: i16) -> u32 {
    assert!(
        dist >= -4096 && dist < 4096 && (dist & 1 == 0),
        "B-type offset distance must be even number within -4096..4096"
    );

    let mut dist = (dist as i64) & 0x1ffe;
    dist |= (dist & 0x800) >> 12;
    dist |= (dist & 0x1000) >> 1;
    sign_extend(dist, 12) as u32
}

fn cond_jump(
    reg: RiscVRegister,
    comp_type: CompareType,
    distance: i64,
) -> Result<[u8; 12], BFCompileError> {
    assert!(
        distance & 1 == 0,
        "<…>::riscv64::cond_jump distance offset must be even"
    );
    if !distance.fits_within_bits(21) {
        return Err(BFCompileError::basic(
            BFErrorID::JumpTooLong,
            "Jump too long for riscv64 backend",
        ));
    }
    // B-type is a variant of S-type with 2 specific immediate bits swapped, used for
    // branch instructions.

    // use this macro instead of passing `$cond_code` because encode_instr uses const assert to
    // make sure its in range, so it needs to take constant values
    macro_rules! branch {
        ($cond_code: literal) => {{
            // B-type instruction, which is like an S type, but the immediate is bits 12:1 not 11:0
            // (as the lowest bit is always zero), and for some reason, bit 11 of the immediate is
            // moved to where bit 0 normally is. that said, given that
            encode_instr!([S] 0b110_0011, TEMP_REG, 0, $cond_code, b_type_bithack(8))
        }}
    }
    let mut code = [0; 12];
    // load
    code[..4].clone_from_slice(&load_from_byte(reg));
    code[4..8].clone_from_slice(&if comp_type == CompareType::Eq {
        branch!(1)
    } else {
        branch!(0)
    });

    // J-type is a variant of U-type with the bits scrambled around to simplify hardware
    // implementation at the expense of compiler/assembler implementation
    let jump_dist = distance as u32 + 4;
    let encoded_jump_dist = ((jump_dist & (1 << 20)) >> 1)
        | ((jump_dist & 0x7fe) << 8)
        | ((jump_dist & (1 << 11)) >> 3)
        | ((jump_dist & 0xff000) >> 12);
    code[8..].clone_from_slice(&encode_instr!([U] 0b110_1111, 0, encoded_jump_dist));

    Ok(code)
}

fn c_addi(reg: u8, i: i8) -> [u8; 2] {
    assert!(
        reg != 0 && reg.fits_within_bits(5),
        "reg must be a valid register number"
    );
    assert!(
        i.fits_within_bits(6),
        "c_addi must only be called with 6-bit signed immediates"
    );
    // C.ADDI (expands to `addi reg, reg, imm`, and reg and imm must not be zero
    assert!(i != 0, "C.ADDI requires nonzero arguments");
    let imm = i16::from(i) as u16;
    u16::to_le_bytes(0x0001 | (imm & (1 << 5)) << 7 | (u16::from(reg) << 7) | ((imm & 0x1f) << 2))
}

fn store_to_byte(addr: RiscVRegister) -> [u8; 4] {
    // SB
    encode_instr!([S] 0b100_011, addr, TEMP_REG, 0, 0)
}

fn load_from_byte(addr: RiscVRegister) -> [u8; 4] {
    // LB
    encode_instr!([I] 0b000_011, TEMP_REG, addr, 0, 0)
}

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
    const JUMP_SIZE: usize = 12;
    const ARCH: ElfArch = ElfArch::RiscV64;
    const E_FLAGS: u32 = 5; // EF_RISCV_RVC | EF_RISCV_FLOAT_ABI_DOUBLE (chosen to match Debian)
    const EI_DATA: ByteOrdering = ByteOrdering::LittleEndian;

    fn set_reg(code_buf: &mut Vec<u8>, reg: Self::RegType, imm: i64) {
        encode_li(code_buf, reg as u8, imm);
    }

    fn reg_copy(code_buf: &mut Vec<u8>, dst: Self::RegType, src: Self::RegType) {
        // C.MV src, dst
        code_buf.extend(u16::to_le_bytes(
            0x8002 | (dst as u16) << 7 | (src as u16) << 2,
        ));
    }

    fn syscall(code_buf: &mut Vec<u8>) {
        // ecall
        code_buf.extend(u32::to_le_bytes(0x73));
    }

    fn nop_loop_open(code_buf: &mut Vec<u8>) {
        // nop
        code_buf.extend(u32::to_le_bytes(0x13).repeat(3));
    }

    fn jump_open(
        code_buf: &mut [u8],
        index: usize,
        reg: Self::RegType,
        offset: i64,
    ) -> FailableInstrEncoding {
        code_buf[index..index + 12].clone_from_slice(&cond_jump(reg, CompareType::Eq, offset)?);
        Ok(())
    }

    fn jump_close(
        code_buf: &mut Vec<u8>,
        reg: Self::RegType,
        offset: i64,
    ) -> FailableInstrEncoding {
        code_buf.extend(cond_jump(reg, CompareType::Ne, offset)?);
        Ok(())
    }

    fn sub_byte(code_buf: &mut Vec<u8>, reg: Self::RegType, imm: u8) {
        code_buf.extend(load_from_byte(reg));
        if (imm as i8).fits_within_bits(6) {
            code_buf.extend(c_addi(TEMP_REG, -(imm as i8)));
        } else {
            code_buf.extend(addi(TEMP_REG, -i16::from(imm)));
        }
        code_buf.extend(store_to_byte(reg));
    }

    fn sub_reg(code_buf: &mut Vec<u8>, reg: Self::RegType, imm: u64) {
        Self::add_reg(code_buf, reg, (imm as i16).wrapping_neg() as u64);
    }

    fn add_byte(code_buf: &mut Vec<u8>, reg: Self::RegType, imm: u8) {
        code_buf.extend(load_from_byte(reg));
        if (imm as i8).fits_within_bits(6) {
            code_buf.extend(c_addi(TEMP_REG, imm as i8));
        } else {
            code_buf.extend(addi(TEMP_REG, i16::from(imm)));
        }
        code_buf.extend(store_to_byte(reg));
    }

    fn add_reg(code_buf: &mut Vec<u8>, reg: Self::RegType, imm: u64) {
        match imm as i64 {
            0 => (),
            -32..0 | 1..32 => code_buf.extend(c_addi(reg as u8, imm as i8)),
            -2048..-32 | 32..2048 => code_buf.extend(addi(reg as u8, imm as i16)),
            _ => {
                encode_li(code_buf, TEMP_REG, imm as i64);
                // C.ADD reg, aux
                code_buf.extend(u16::to_le_bytes(
                    0x9002 | (reg as u16) << 7 | u16::from(TEMP_REG) << 2,
                ));
            }
        }
    }

    fn inc_reg(code_buf: &mut Vec<u8>, reg: Self::RegType) {
        code_buf.extend(c_addi(reg as u8, 1));
    }

    fn dec_reg(code_buf: &mut Vec<u8>, reg: Self::RegType) {
        code_buf.extend(c_addi(reg as u8, -1));
    }

    fn inc_byte(code_buf: &mut Vec<u8>, reg: Self::RegType) {
        code_buf.extend(load_from_byte(reg));
        code_buf.extend(c_addi(TEMP_REG, 1));
        code_buf.extend(store_to_byte(reg));
    }

    fn dec_byte(code_buf: &mut Vec<u8>, reg: Self::RegType) {
        code_buf.extend(load_from_byte(reg));
        code_buf.extend(c_addi(TEMP_REG, -1));
        code_buf.extend(store_to_byte(reg));
    }

    fn zero_byte(code_buf: &mut Vec<u8>, reg: Self::RegType) {
        // SB reg, zero
        code_buf.extend(encode_instr!([S] 0b100_011, reg, 0, 0, 0));
    }
}

#[cfg(test)]
mod test {
    #[cfg(feature = "disasmtests")]
    use super::super::test_utils::Disassembler;
    use super::*;
    use test_macros::disasm_test;

    #[cfg(feature = "disasmtests")]
    fn disassembler() -> Disassembler {
        Disassembler::new(ElfArch::RiscV64)
    }

    #[disasm_test]
    /// test `RiscV64Inter::set_reg` for immediates that fit within 32 bits
    fn test_set_reg_32() {
        let mut v = Vec::with_capacity(32);
        RiscV64Inter::set_reg(&mut v, RiscVRegister::A0, 0);
        assert_eq!(v.len(), 2);
        RiscV64Inter::set_reg(&mut v, RiscVRegister::A1, 1);
        assert_eq!(v.len(), 4);
        RiscV64Inter::set_reg(&mut v, RiscVRegister::A2, -2);
        assert_eq!(v.len(), 6);
        RiscV64Inter::set_reg(&mut v, RiscVRegister::A7, 0x123);
        assert_eq!(v.len(), 10);
        RiscV64Inter::set_reg(&mut v, RiscVRegister::A0, -0x123);
        assert_eq!(v.len(), 14);
        RiscV64Inter::set_reg(&mut v, RiscVRegister::S0, 0x100_000);
        assert_eq!(v.len(), 18);
        RiscV64Inter::set_reg(&mut v, RiscVRegister::A7, 0x123_456);
        assert_eq!(v.len(), 26);
        RiscV64Inter::set_reg(&mut v, RiscVRegister::A0, 0x1000);
        assert_eq!(v.len(), 28);
        RiscV64Inter::set_reg(&mut v, RiscVRegister::A1, 0x1001);
        assert_eq!(v.len(), 32);
        assert_eq!(
            disassembler().disassemble(v),
            [
                "li a0, 0x0",
                "li a1, 0x1",
                "li a2, -0x2",
                "li a7, 0x123",
                "li a0, -0x123",
                "lui s0, 0x100",
                "lui a7, 0x123",
                "addiw a7, a7, 0x456",
                "lui a0, 0x1",
                "lui a1, 0x1",
                "addiw a1, a1, 0x1"
            ]
        );
    }

    #[disasm_test]
    fn test_set_reg_64() {
        use std::borrow::Cow;
        let mut ds = disassembler();
        let mut v = Vec::with_capacity(124);
        let mut val = i64::from(i32::MAX) + 1;
        let mut expected: Vec<Cow<'_, str>> = Vec::new();
        let mut expected_len = 4;
        while val < i64::MAX / 2 {
            RiscV64Inter::set_reg(&mut v, RiscVRegister::A7, val);
            val <<= 1;
            expected.push("li a7, 0x1".into());
            let shift_lvl = val.trailing_zeros() - 1;
            expected.push(format!("slli a7, a7, {shift_lvl:#x}").into());
            assert_eq!(v.len(), expected_len);
            expected_len += 4;
        }
        assert_eq!(ds.disassemble(v), expected);

        // worst case scenario - alternating bits 0b0101 = 0x5, so this is every other bit in the
        // immediate set
        //
        // Try with both 48 and 64 bit values
        let mut v = Vec::with_capacity(6);
        RiscV64Inter::set_reg(&mut v, RiscVRegister::A7, 0x5555 << 24);
        assert_eq!(ds.disassemble(v), ["lui a7, 0x5555", "slli a7, a7, 0xc"]);

        let mut v12 = Vec::with_capacity(40);
        RiscV64Inter::set_reg(&mut v12, RiscVRegister::S0, 0x5555_5555_5555);
        RiscV64Inter::set_reg(&mut v12, RiscVRegister::A7, -0x5555_5555_5555);
        let mut v16 = Vec::with_capacity(56);
        RiscV64Inter::set_reg(&mut v16, RiscVRegister::S0, 0x5555_5555_5555_5555);
        RiscV64Inter::set_reg(&mut v16, RiscVRegister::A7, -0x5555_5555_5555_5555);
        assert_eq!(
            ds.disassemble(v12),
            // this is what LLVM 19 generates for these instructions:
            // ```sh
            // llvm-mc --triple=riscv64-linux-gnu -mattr=+c --print-imm-hex - <<<EOF
            // li s0, 0x555555555555
            // li a7, -0x555555555555
            // EOF
            // ```
            [
                "lui s0, 0x555",
                "addiw s0, s0, 0x555",
                "slli s0, s0, 0xc",
                "addi s0, s0, 0x555",
                "slli s0, s0, 0xc",
                "addi s0, s0, 0x555",
                "lui a7, 0xffaab",
                "addiw a7, a7, -0x555",
                "slli a7, a7, 0xc",
                "addi a7, a7, -0x555",
                "slli a7, a7, 0xc",
                "addi a7, a7, -0x555",
            ]
        );
        assert_eq!(
            ds.disassemble(v16),
            // this is what LLVM 19 generates for these instructions:
            // ```sh
            // llvm-mc --triple=riscv64-linux-gnu -mattr=+c --print-imm-hex - <<<EOF
            // li s0, 0x5555555555555555
            // li a7, -0x5555555555555555
            // EOF
            // ```
            [
                "lui s0, 0x5555",
                "addiw s0, s0, 0x555",
                "slli s0, s0, 0xc",
                "addi s0, s0, 0x555",
                "slli s0, s0, 0xc",
                "addi s0, s0, 0x555",
                "slli s0, s0, 0xc",
                "addi s0, s0, 0x555",
                "lui a7, 0xfaaab",
                "addiw a7, a7, -0x555",
                "slli a7, a7, 0xc",
                "addi a7, a7, -0x555",
                "slli a7, a7, 0xc",
                "addi a7, a7, -0x555",
                "slli a7, a7, 0xc",
                "addi a7, a7, -0x555",
            ]
        );
    }

    #[disasm_test]
    fn test_caddi() {
        let mut v = Vec::from(c_addi(RiscVRegister::A0 as u8, -1));
        v.extend(c_addi(RiscVRegister::A1 as u8, 0x1f));
        assert_eq!(
            disassembler().disassemble(v),
            ["addi a0, a0, -0x1", "addi a1, a1, 0x1f"]
        );
    }

    #[disasm_test]
    fn test_addi() {
        let mut v = Vec::from(addi(RiscVRegister::S0 as u8, -0x789));
        v.extend(addi(RiscVRegister::A7 as u8, 0x123));
        assert_eq!(
            disassembler().disassemble(v),
            ["addi s0, s0, -0x789", "addi a7, a7, 0x123"]
        );
    }

    #[test]
    #[should_panic = "c_addi must only be called with 6-bit signed immediates"]
    fn test_caddi_guard_positive() {
        c_addi(RiscVRegister::A0 as u8, 0b0111_0000);
    }

    #[test]
    #[should_panic = "c_addi must only be called with 6-bit signed immediates"]
    fn test_caddi_guard_negative() {
        c_addi(RiscVRegister::A0 as u8, -0b0111_0000);
    }

    #[disasm_test]
    fn test_syscall() {
        let mut v: Vec<u8> = Vec::with_capacity(4);
        RiscV64Inter::syscall(&mut v);
        assert_eq!(disassembler().disassemble(v), ["ecall"]);
    }

    #[disasm_test]
    fn test_reg_copies() {
        let mut v: Vec<u8> = Vec::with_capacity(4);
        RiscV64Inter::reg_copy(&mut v, RiscVRegister::A1, RiscVRegister::S0);
        RiscV64Inter::reg_copy(&mut v, RiscVRegister::S0, RiscVRegister::A7);
        assert_eq!(disassembler().disassemble(v), ["mv a1, s0", "mv s0, a7"]);
    }

    #[disasm_test]
    fn load_and_store() {
        let mut v = Vec::from(load_from_byte(RiscVRegister::A0));
        v.extend(store_to_byte(RiscVRegister::A0));
        assert_eq!(
            disassembler().disassemble(v),
            ["lb t1, 0x0(a0)", "sb t1, 0x0(a0)"]
        );
    }

    #[disasm_test]
    fn test_zero_byte() {
        let mut v = Vec::with_capacity(4);
        RiscV64Inter::zero_byte(&mut v, RiscVRegister::A2);
        assert_eq!(disassembler().disassemble(v), ["sb zero, 0x0(a2)"]);
    }
}
