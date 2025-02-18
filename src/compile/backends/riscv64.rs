// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only AND Apache-2.0 WITH LLVM-exception

use super::arch_inter::{ArchInter, FailableInstrEncoding, Registers, SyscallNums};
use super::elf_tools::{ByteOrdering, ElfArch};
use super::MinimumBits;
use crate::err::{BFCompileError, BFErrorID};
#[derive(Debug, Clone, Copy, PartialEq)]
#[repr(u8)]
pub(in super::super) enum RiscVRegister {
    // read-only zero register
    T1 = 6,  // X6, scratch register
    T2 = 7,  // X7, scratch register
    S0 = 8,  // X8, bf pointer register
    A0 = 10, // X10, arg1 register
    A1 = 11, // X11, arg2 register
    A2 = 12, // X12, arg3 register
    A7 = 17, // X17, syscall register
}

impl RiscVRegister {
    fn aux(self) -> Self {
        if self == RiscVRegister::T2 {
            RiscVRegister::T1
        } else {
            RiscVRegister::T2
        }
    }
}

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
fn encode_li(code_buf: &mut Vec<u8>, reg: RiscVRegister, val: i64) {
    let lo12 = sign_extend(val, 12);
    if val.fits_within_bits(32) {
        let hi20 = ((val as u64).wrapping_add(0x800) >> 12) as i64 & 0xfff;
        if hi20 != 0 {
            if hi20.fits_within_bits(6) {
                // C.LUI
                code_buf.extend(encode_instr!([CI] 0b01, reg, 0b011, hi20 as u16));
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
    if shift_amount.fits_within_bits(6) && shift_amount != 0 {
        // C.SLLI
        code_buf.extend(encode_instr!([CI] 0b10, reg, 0, shift_amount));
    } else {
        // SLLI
        code_buf.extend(encode_instr!([I] 0b001_0011, reg, reg, 0b111, shift_amount));
    }
    if lo12 != 0 && lo12.fits_within_bits(6) {
        code_buf.extend(c_addi(reg, lo12 as i8));
    } else if lo12 != 0 {
        code_buf.extend(addi(reg, lo12 as i16));
    }
}

// SPDX-SnippetEnd

pub(crate) struct RiscV64Inter;

fn addi(reg: RiscVRegister, i: i16) -> [u8; 4] {
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
    let aux = reg.aux();

    // use this macro instead of passing `$cond_code` because encode_instr uses const assert to
    // make sure its in range, so it needs to take constant values
    macro_rules! branch {
        ($cond_code: literal) => {{
            // B-type instruction, which is like an S type, but the immediate is bits 12:1 not 11:0
            // (as the lowest bit is always zero), and for some reason, bit 11 of the immediate is
            // moved to where bit 0 normally is. that said, given that
            encode_instr!([S] 0b110_0011, aux, 0, $cond_code, b_type_bithack(8))
        }}
    }
    let mut code = [0; 12];
    // load
    code[..4].clone_from_slice(&load_from_byte(reg, aux));
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

fn c_addi(reg: RiscVRegister, i: i8) -> [u8; 2] {
    assert!(
        i.fits_within_bits(6),
        "c_addi must only be called with 6-bit signed immediates"
    );
    // C.ADDI (expands to `addi reg, reg, imm`, and reg and imm must not be zero
    assert!(i != 0, "C.ADDI requires nonzero arguments");
    let imm = i16::from(i) as u16;
    u16::to_le_bytes(0x0001 | (imm & (1 << 5)) << 7 | ((reg as u16) << 7) | ((imm & 0x1f) << 2))
}

fn store_to_byte(addr: RiscVRegister, src: RiscVRegister) -> [u8; 4] {
    // SB
    encode_instr!([S] 0b100_011, addr, src, 0, 0)
}

fn load_from_byte(addr: RiscVRegister, dst: RiscVRegister) -> [u8; 4] {
    // LB
    encode_instr!([I] 0b000_011, dst, addr, 0, 0)
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
        encode_li(code_buf, reg, imm);
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
        let aux = reg.aux();
        code_buf.extend(load_from_byte(reg, aux));
        if (imm as i8).fits_within_bits(6) {
            code_buf.extend(c_addi(reg, -(imm as i8)));
        } else {
            code_buf.extend(addi(reg, -i16::from(imm)));
        }
        code_buf.extend(store_to_byte(reg, aux));
    }

    fn sub_reg(code_buf: &mut Vec<u8>, reg: Self::RegType, imm: u64) {
        Self::add_reg(code_buf, reg, (imm as i16).wrapping_neg() as u64);
    }

    fn add_byte(code_buf: &mut Vec<u8>, reg: Self::RegType, imm: u8) {
        let aux = reg.aux();
        code_buf.extend(load_from_byte(reg, aux));
        if (imm as i8).fits_within_bits(6) {
            code_buf.extend(c_addi(reg, imm as i8));
        } else {
            code_buf.extend(addi(reg, i16::from(imm)));
        }
        code_buf.extend(store_to_byte(reg, aux));
    }

    fn add_reg(code_buf: &mut Vec<u8>, reg: Self::RegType, imm: u64) {
        match imm as i64 {
            0 => (),
            -32..0 | 1..32 => code_buf.extend(c_addi(reg, imm as i8)),
            -2048..-32 | 32..2048 => code_buf.extend(addi(reg, imm as i16)),
            _ => {
                let aux = reg.aux();
                Self::set_reg(code_buf, aux, imm as i64);
                // C.ADDI reg, aux
                code_buf.extend(u16::to_le_bytes(
                    0x9002 | (reg as u16) << 7 | (aux as u16) << 2,
                ));
            }
        }
    }

    fn inc_reg(code_buf: &mut Vec<u8>, reg: Self::RegType) {
        // C.ADDI reg, 1
        code_buf.extend(c_addi(reg, 1));
    }

    fn dec_reg(code_buf: &mut Vec<u8>, reg: Self::RegType) {
        // C.ADDI reg, -1
        code_buf.extend(c_addi(reg, -1));
    }

    fn inc_byte(code_buf: &mut Vec<u8>, reg: Self::RegType) {
        let aux = reg.aux();
        code_buf.extend(load_from_byte(reg, aux));
        code_buf.extend(c_addi(reg, 1));
        code_buf.extend(store_to_byte(reg, aux));
    }

    fn dec_byte(code_buf: &mut Vec<u8>, reg: Self::RegType) {
        let aux = reg.aux();
        code_buf.extend(load_from_byte(reg, aux));
        code_buf.extend(c_addi(reg, -1));
        code_buf.extend(store_to_byte(reg, aux));
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
    fn test_set_reg() {
        let mut v = Vec::new();
        RiscV64Inter::set_reg(&mut v, RiscVRegister::A0, 0);
        RiscV64Inter::set_reg(&mut v, RiscVRegister::A1, 1);
        RiscV64Inter::set_reg(&mut v, RiscVRegister::A2, -2);
        RiscV64Inter::set_reg(&mut v, RiscVRegister::T1, 0x123);
        RiscV64Inter::set_reg(&mut v, RiscVRegister::T2, -0x123);
        RiscV64Inter::set_reg(&mut v, RiscVRegister::S0, 0x100_000);
        RiscV64Inter::set_reg(&mut v, RiscVRegister::A7, 0x123_456);
        assert_eq!(
            disassembler().disassemble(v),
            [
                "li a0, 0x0",
                "li a1, 0x1",
                "li a2, -0x2",
                "li t1, 0x123",
                "li t2, -0x123",
                "lui s0, 0x100",
                "lui a7, 0x123",
                "addiw a7, a7, 0x456",
            ]
        );
    }

    #[disasm_test]
    fn test_caddi() {
        let mut v = Vec::from(c_addi(RiscVRegister::A0, -1));
        v.extend(c_addi(RiscVRegister::A1, 0x1f));
        assert_eq!(
            disassembler().disassemble(v),
            ["addi a0, a0, -0x1", "addi a1, a1, 0x1f"]
        );
    }

    #[disasm_test]
    fn test_addi() {
        assert_eq!(addi(RiscVRegister::A0, 1), [0x13, 0x05, 0x15, 0x00]);
        let mut v = Vec::from(addi(RiscVRegister::T2, -0x789));
        v.extend(addi(RiscVRegister::T1, 0x123));
        assert_eq!(
            disassembler().disassemble(v),
            ["addi t2, t2, -0x789", "addi t1, t1, 0x123"]
        );
    }

    #[test]
    #[should_panic = "c_addi must only be called with 6-bit signed immediates"]
    fn test_caddi_guard_positive() {
        c_addi(RiscVRegister::T2, 0b0111_0000);
    }
    #[test]
    #[should_panic = "c_addi must only be called with 6-bit signed immediates"]
    fn test_caddi_guard_negative() {
        c_addi(RiscVRegister::T2, -0b0111_0000);
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
        let mut v = Vec::from(load_from_byte(RiscVRegister::A0, RiscVRegister::T2));
        v.extend(store_to_byte(RiscVRegister::A0, RiscVRegister::T2));
        assert_eq!(
            disassembler().disassemble(v),
            ["lb t2, 0x0(a0)", "sb t2, 0x0(a0)"]
        );
    }

    #[disasm_test]
    fn test_zero_byte() {
        let mut v = Vec::with_capacity(4);
        RiscV64Inter::zero_byte(&mut v, RiscVRegister::A2);
        assert_eq!(disassembler().disassemble(v), ["sb zero, 0x0(a2)"]);
    }
}
