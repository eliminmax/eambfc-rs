// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use super::arch_inter::{ArchInter, FailableInstrEncoding, Registers, SyscallNums};
use super::elf_tools::{ByteOrdering, ElfArch};
use super::MinimumBits;
use crate::err::{BFCompileError, BFErrorID};

use std::num::NonZeroI8;

/// A `const` assertion that `$val` fits within `$size` bits. `$val` is assumed to be a positive
/// integer.
macro_rules! validate_size {
    ($label: literal, $size: literal, $val: literal) => {
        const {
            debug_assert!(
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
        debug_assert!(
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
        debug_assert!(
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
        debug_assert!(
            $imm.fits_within_bits(20),
            "U-type instructions take 20-bit immediates"
        );
        #[allow(clippy::cast_lossless, reason = "Need to convert both ints and enums")]
        u32::to_le_bytes((($imm as u32) << 12) | (($rd as u32) << 7) | $op)
    }};
    ([CI] $op: literal, $rd_rs1: expr, $funct3: literal, $imm: expr) => {{
        validate_size!("opcode", 2, $op);
        validate_size!("funct3", 3, $funct3);
        debug_assert!(
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
fn encode_li(code_buf: &mut Vec<u8>, reg: RawReg, val: i64) {
    let lo12 = sign_extend(val, 12);
    if val.fits_within_bits(32) {
        let hi20 = sign_extend(((val as u64).wrapping_add(0x800) >> 12) as i64, 20);
        if hi20 != 0 {
            if hi20.fits_within_bits(6) {
                // C.LUI
                code_buf.extend(encode_instr!([CI] 0b01, *reg, 0b011, hi20));
            } else {
                // LUI
                code_buf.extend(encode_instr!([U] 0b011_0111, *reg, hi20));
            }
        }
        match (lo12, hi20) {
            (n, 0) if n.fits_within_bits(6) => {
                // C.LI
                code_buf.extend(encode_instr!([CI] 0b01, *reg, 0b010, lo12));
            }
            (0, _) => (),
            (n, _) if n.fits_within_bits(6) => {
                // C.ADDIW
                code_buf.extend(encode_instr!([CI] 0b01, *reg, 0b001, lo12));
            }
            (_, 0) => {
                // ADDI reg.into(), zero, lo12
                code_buf.extend(encode_instr!([I] 0b001_0011, *reg, 0, 0, lo12));
            }
            _ => {
                // ADDIW reg.into(), reg.into(), lo12
                code_buf.extend(encode_instr!([I] 0b001_1011, *reg, *reg, 0, lo12));
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
        // This will always fit within 6 bits, as 63_u32 fits within 6 bits, and is the highest
        // value that wouldn't shift the whole value out of bounds.
        // C.SLLI
        code_buf.extend(encode_instr!([CI] 0b10, *reg, 0, shift_amount));
    }
    if lo12 != 0 {
        if lo12.fits_within_bits(6) {
            code_buf.extend(c_addi(
                reg,
                NonZeroI8::new(lo12 as i8).unwrap_or_else(|| unreachable!()),
            ));
        } else {
            code_buf.extend(addi(reg, lo12 as i16));
        }
    }
}

// SPDX-SnippetEnd
const NZ1: NonZeroI8 = NonZeroI8::new(1).expect("1 != 0");
const NZ_NEG1: NonZeroI8 = NonZeroI8::new(-1).expect("1 != 0");

/// Internal type representing a raw register identifier. Implements `Deref<Target = u8>`.
#[derive(PartialEq, Copy, Clone)]
struct RawReg(u8);
impl std::ops::Deref for RawReg {
    type Target = u8;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl From<RiscVRegister> for RawReg {
    fn from(value: RiscVRegister) -> Self {
        RawReg(value as u8)
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
#[repr(u8)]
pub(in super::super) enum RiscVRegister {
    S0 = 8,  // X8, bf pointer register
    A0 = 10, // X10, arg1 register
    A1 = 11, // X11, arg2 register
    A2 = 12, // X12, arg3 register
    A7 = 17, // X17, syscall register
}

/// Private scratch register used within certain operations
const TEMP_REG: RawReg = RawReg(6);

pub(crate) struct RiscV64Inter;

fn addi(reg: RawReg, i: i16) -> [u8; 4] {
    debug_assert!(
        i.fits_within_bits(12),
        "addi immediate must fit within 12 bits"
    );
    encode_instr!([I] 0b001_0011, *reg, *reg, 0, i)
}

#[derive(Clone, Copy, PartialEq)]
enum CompareType {
    // This bit needs to be set in cond_jump for jump_open
    Eq = 1 << 12,
    Ne = 0,
}

fn cond_jump(
    reg: RiscVRegister,
    comp_type: CompareType,
    distance: i64,
) -> Result<[u8; 12], BFCompileError> {
    debug_assert!(
        distance & 1 == 0,
        "<…>::riscv64::cond_jump distance offset must be even"
    );
    if !distance.fits_within_bits(21) {
        return Err(BFCompileError::basic(
            BFErrorID::JumpTooLong,
            "Jump too long for riscv64 backend",
        ));
    }

    // there are 2 types of instructions used here for control flow - branches, which can
    // conditionally move up to 4 KiB away, and jumps, which unconditionally move up to 1MiB away.
    // The former is too short, and the latter is unconditional, so the solution is to use an
    // inverted branch condition and set it to branch over the unconditional jump. Ugly, but it
    // works.
    //
    // There are C.BNEZ and C.BEQZ instructions that could branch smaller distances and always
    // compare their operand register against the zero register, but they only work with a specific
    // subset of registers, all of which are non-volatile.

    let mut code = [0; 12];
    // load byte to compare
    code[..4].clone_from_slice(&load_from_byte(reg));

    let mut code = [0; 12];
    // load
    code[..4].clone_from_slice(&load_from_byte(reg));

    // `BNEZ t1, 8` if comp_type == Eq, otherwise `BEQZ t1, 8`
    code[4..8].clone_from_slice(&u32::to_le_bytes(0x0003_0463 | (comp_type as u32)));

    // J-type is a variant of U-type with the bits scrambled around to simplify hardware
    // implementation at the expense of compiler/assembler implementation.
    let jump_dist = distance as u32 + 4;
    let encoded_jump_dist = ((jump_dist & (1 << 20)) << 11)
        | ((jump_dist & 0x7fe) << 20)
        | ((jump_dist & (1 << 11)) << 9)
        | (jump_dist & 0xff000);

    // J distance
    code[8..].clone_from_slice(&(encoded_jump_dist | 0b110_1111).to_le_bytes());

    Ok(code)
}

fn c_addi(reg: RawReg, i: NonZeroI8) -> [u8; 2] {
    debug_assert!(
        i.get().fits_within_bits(6),
        "c_addi must only be called with 6-bit signed immediates"
    );
    let imm = i16::from(i.get()) as u16;
    u16::to_le_bytes(0x0001 | (imm & (1 << 5)) << 7 | (u16::from(reg.0) << 7) | ((imm & 0x1f) << 2))
}

fn store_to_byte(addr: RiscVRegister) -> [u8; 4] {
    // SB
    encode_instr!([S] 0b100_011, addr, *TEMP_REG, 0, 0)
}

fn load_from_byte(addr: RiscVRegister) -> [u8; 4] {
    // LB
    encode_instr!([I] 0b000_011, *TEMP_REG, addr, 0, 0)
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
        encode_li(code_buf, reg.into(), imm);
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
        if let Some(nzimm) = NonZeroI8::new(imm as i8) {
            code_buf.extend(load_from_byte(reg));
            if nzimm.wrapping_neg().get().fits_within_bits(6) {
                code_buf.extend(c_addi(TEMP_REG, -nzimm));
            } else {
                code_buf.extend(addi(TEMP_REG, -i16::from(nzimm.get())));
            }
            code_buf.extend(store_to_byte(reg));
        }
    }

    fn sub_reg(code_buf: &mut Vec<u8>, reg: Self::RegType, imm: u64) {
        Self::add_reg(code_buf, reg, (imm as i64).wrapping_neg() as u64);
    }

    fn add_byte(code_buf: &mut Vec<u8>, reg: Self::RegType, imm: u8) {
        if let Some(nzimm) = NonZeroI8::new(imm as i8) {
            code_buf.extend(load_from_byte(reg));
            if nzimm.get().fits_within_bits(6) {
                code_buf.extend(c_addi(TEMP_REG, nzimm));
            } else {
                code_buf.extend(addi(TEMP_REG, nzimm.get().into()));
            }
            code_buf.extend(store_to_byte(reg));
        }
    }

    fn add_reg(code_buf: &mut Vec<u8>, reg: Self::RegType, imm: u64) {
        match imm as i64 {
            0 => (),
            -32..0 | 1..32 => code_buf.extend(c_addi(
                reg.into(),
                NonZeroI8::new(imm as i8).unwrap_or_else(|| unreachable!()),
            )),
            -2048..-32 | 32..2048 => code_buf.extend(addi(reg.into(), imm as i16)),
            _ => {
                encode_li(code_buf, TEMP_REG, imm as i64);
                // C.ADD reg, aux
                code_buf.extend(u16::to_le_bytes(
                    0x9002 | (reg as u16) << 7 | u16::from(*TEMP_REG) << 2,
                ));
            }
        }
    }

    fn inc_reg(code_buf: &mut Vec<u8>, reg: Self::RegType) {
        code_buf.extend(c_addi(reg.into(), NZ1));
    }

    fn dec_reg(code_buf: &mut Vec<u8>, reg: Self::RegType) {
        code_buf.extend(c_addi(reg.into(), NZ_NEG1));
    }

    fn inc_byte(code_buf: &mut Vec<u8>, reg: Self::RegType) {
        code_buf.extend(load_from_byte(reg));
        code_buf.extend(c_addi(TEMP_REG, NZ1));
        code_buf.extend(store_to_byte(reg));
    }

    fn dec_byte(code_buf: &mut Vec<u8>, reg: Self::RegType) {
        code_buf.extend(load_from_byte(reg));
        code_buf.extend(c_addi(TEMP_REG, NZ_NEG1));
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
    use test_macros::{debug_assert_test, disasm_test};

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
    fn compressed_set_reg_64() {
        // make sure that when it can use compressed instrucitons, it does so
        let mut v = Vec::with_capacity(12);
        RiscV64Inter::set_reg(&mut v, RiscVRegister::A1, 0xf_0000_0010);
        assert_eq!(v.len(), 6);
        let mut expected =
            vec![["li a1, 0xf"], ["slli a1, a1, 0x20"], ["addi a1, a1, 0x10"]].into_iter();
        // this loop makes sure each instruction is exactly 2 bytes in size
        for chunk in v.chunks(2) {
            assert_eq!(
                disassembler().disassemble(chunk.to_owned()),
                expected.next().unwrap()
            );
        }
    }

    #[disasm_test]
    fn test_caddi() {
        let mut v = Vec::from(c_addi(RiscVRegister::A0.into(), NZ_NEG1));
        v.extend(c_addi(
            RiscVRegister::A1.into(),
            const { NonZeroI8::new(0x1f).unwrap() },
        ));
        assert_eq!(
            disassembler().disassemble(v),
            ["addi a0, a0, -0x1", "addi a1, a1, 0x1f"]
        );
    }

    #[disasm_test]
    fn test_addi() {
        let mut v = Vec::from(addi(RiscVRegister::S0.into(), -0x789));
        v.extend(addi(RiscVRegister::A7.into(), 0x123));
        assert_eq!(
            disassembler().disassemble(v),
            ["addi s0, s0, -0x789", "addi a7, a7, 0x123"]
        );
    }

    #[debug_assert_test("c_addi must only be called with 6-bit signed immediates")]
    fn test_caddi_guard_positive() {
        c_addi(
            RiscVRegister::A0.into(),
            const { NonZeroI8::new(0b0111_0000).unwrap() },
        );
    }

    #[debug_assert_test("c_addi must only be called with 6-bit signed immediates")]
    fn test_caddi_guard_negative() {
        c_addi(
            RiscVRegister::A0.into(),
            const { NonZeroI8::new(-0b0111_0000).unwrap() },
        );
    }

    #[debug_assert_test("<…>::riscv64::cond_jump distance offset must be even")]
    fn bad_address_guard() {
        cond_jump(RiscV64Inter::REGISTERS.bf_ptr, CompareType::Eq, 1).unwrap();
    }

    #[test]
    fn jump_too_long() {
        assert_eq!(
            cond_jump(RiscV64Inter::REGISTERS.sc_num, CompareType::Eq, 2 << 32)
                .unwrap_err()
                .error_id(),
            BFErrorID::JumpTooLong
        );
    }

    #[debug_assert_test("addi immediate must fit within 12 bits")]
    fn addi_imm_guard_positive() {
        addi(RiscVRegister::A0.into(), 0x1fff);
    }

    #[debug_assert_test("addi immediate must fit within 12 bits")]
    fn addi_imm_guard_negative() {
        addi(RiscVRegister::A0.into(), -0x1fff);
    }

    #[disasm_test]
    fn test_syscall() {
        let mut v = Vec::with_capacity(4);
        RiscV64Inter::syscall(&mut v);
        assert_eq!(disassembler().disassemble(v), ["ecall"]);
    }

    #[disasm_test]
    fn test_reg_copies() {
        let mut v = Vec::with_capacity(4);
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

    #[disasm_test]
    fn nop_pad() {
        let mut v = Vec::with_capacity(12);
        RiscV64Inter::nop_loop_open(&mut v);
        assert_eq!(v.len(), 12);
        assert_eq!(disassembler().disassemble(v), ["nop"].repeat(3));
    }

    #[disasm_test]
    fn successfull_jumps_test() {
        let mut v = vec![0; 12];
        RiscV64Inter::jump_open(&mut v, 0, RiscVRegister::S0, 32).unwrap();
        RiscV64Inter::jump_close(&mut v, RiscVRegister::S0, -32).unwrap();
        assert_eq!(
            disassembler().disassemble(v),
            [
                "lb t1, 0x0(s0)",
                "bnez t1, 0x8",
                "j 0x24",
                "lb t1, 0x0(s0)",
                "beqz t1, 0x8",
                "j -0x1c",
            ]
        );
    }

    #[disasm_test]
    fn inc_dec() {
        let mut v = Vec::with_capacity(24);
        RiscV64Inter::inc_byte(&mut v, RiscVRegister::S0);
        assert_eq!(v.len(), 10);
        RiscV64Inter::dec_byte(&mut v, RiscVRegister::S0);
        assert_eq!(v.len(), 20);
        RiscV64Inter::inc_reg(&mut v, RiscVRegister::S0);
        assert_eq!(v.len(), 22);
        RiscV64Inter::dec_reg(&mut v, RiscVRegister::S0);
        assert_eq!(v.len(), 24);
        assert_eq!(
            disassembler().disassemble(v),
            [
                "lb t1, 0x0(s0)",
                "addi t1, t1, 0x1",
                "sb t1, 0x0(s0)",
                "lb t1, 0x0(s0)",
                "addi t1, t1, -0x1",
                "sb t1, 0x0(s0)",
                "addi s0, s0, 0x1",
                "addi s0, s0, -0x1",
            ]
        );
    }

    #[disasm_test]
    fn add_sub_byte() {
        let mut ds = disassembler();

        let mut v = Vec::with_capacity(24);
        RiscV64Inter::add_byte(&mut v, RiscV64Inter::REGISTERS.arg1, 0);
        RiscV64Inter::sub_byte(&mut v, RiscV64Inter::REGISTERS.arg1, 0);
        assert!(v.is_empty());
        RiscV64Inter::add_byte(&mut v, RiscV64Inter::REGISTERS.arg2, 0x10);
        RiscV64Inter::sub_byte(&mut v, RiscV64Inter::REGISTERS.arg2, 0x10);
        assert_eq!(v.len(), 20);
        assert_eq!(
            ds.disassemble(v),
            [
                "lb t1, 0x0(a1)",
                "addi t1, t1, 0x10",
                "sb t1, 0x0(a1)",
                "lb t1, 0x0(a1)",
                "addi t1, t1, -0x10",
                "sb t1, 0x0(a1)",
            ]
        );

        let mut v = Vec::with_capacity(28);
        RiscV64Inter::add_byte(&mut v, RiscV64Inter::REGISTERS.arg3, 0x70);
        RiscV64Inter::sub_byte(&mut v, RiscV64Inter::REGISTERS.arg3, 0x70);
        assert_eq!(
            ds.disassemble(v),
            [
                "lb t1, 0x0(a2)",
                "addi t1, t1, 0x70",
                "sb t1, 0x0(a2)",
                "lb t1, 0x0(a2)",
                "addi t1, t1, -0x70",
                "sb t1, 0x0(a2)",
            ]
        );

        // if the imm is >= 0x80, it will become negative due to the casting that's done, but will
        // have the same byte value once truncated down.
        let mut v = Vec::with_capacity(28);
        RiscV64Inter::add_byte(&mut v, RiscV64Inter::REGISTERS.arg3, 0x80);
        RiscV64Inter::sub_byte(&mut v, RiscV64Inter::REGISTERS.arg3, 0x80);
        const { assert!((1_i16 + 0x80) as u8 == (1_i16 - 0x80) as u8) };
        assert_eq!(
            ds.disassemble(v),
            [
                "lb t1, 0x0(a2)",
                "addi t1, t1, -0x80",
                "sb t1, 0x0(a2)",
                "lb t1, 0x0(a2)",
                "addi t1, t1, 0x80",
                "sb t1, 0x0(a2)",
            ]
        );
    }
}
