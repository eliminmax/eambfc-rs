// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use super::arch_inter::{ArchInter, FailableInstrEncoding, Registers, SyscallNums};
use super::elf_tools::{ByteOrdering, ElfArch};
use super::MinimumBits;
use crate::err::{BFCompileError, BFErrorID};

#[derive(Debug, Clone, Copy, PartialEq)]
#[repr(u8)]
pub(in super::super) enum RiscVRegister {
    // read-only zero register
    Zero = 0, // always-zero read-only register
    T0 = 5,   // X5, scratch register
    T1 = 6,   // X6, scratch register
    S0 = 8,   // X8, bf pointer register
    A0 = 10,  // X10, arg1 register
    A1 = 11,  // X11, arg2 register
    A2 = 12,  // X12, arg3 register
    A7 = 17,  // X17, syscall register
}

// #[derive(Debug, Clone, Copy, PartialEq)]
// #[repr(u8)]
// /// Some RISC-V "C" extension compressed instructions use 3-bit rather than the normal 5-bit
// /// encodings for the register operands, to save space, with the trade-off of not being able to
// /// refer to all registers.
// enum RiscVCompressedRegister {
//     S0 = 0b000,
//     A0 = 0b010,
//     A1 = 0b011,
//     A2 = 0b100,
// }

// impl TryFrom<RiscVRegister> for RiscVCompressedRegister {
//     type Error = ();
//     fn try_from(value: RiscVRegister) -> Result<Self, Self::Error> {
//         value.compressed_form().ok_or(())
//     }
// }

impl RiscVRegister {
    // const fn compressed_form(self) -> Option<RiscVCompressedRegister> {
    //     match self {
    //         Self::S0 => Some(RiscVCompressedRegister::S0),
    //         Self::A0 => Some(RiscVCompressedRegister::A0),
    //         Self::A1 => Some(RiscVCompressedRegister::A1),
    //         Self::A2 => Some(RiscVCompressedRegister::A2),
    //         _ => None,
    //     }
    // }
    fn aux(self) -> Self {
        if self == RiscVRegister::T0 {
            RiscVRegister::T1
        } else {
            RiscVRegister::T0
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
            $imm.min_bits() <= 12,
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
            $imm.min_bits() <= 12,
            "S-type expressions take 12-bit immediates"
        );
        u32::to_le_bytes(
            ($imm & 0xfe) << 25
                | (($rs2 as u32) << 20)
                | (($rs1 as u32) << 15)
                | (($funct3 as u32) << 12)
                | ($imm & 0x1f) << 7
                | $op,
        )
    }};
    ([U] $op: literal, $rd: expr, $imm: expr) => {{
        validate_size!("opcode", 6, $op);
        assert_eq!(
            $imm & 0xfff,
            0,
            "U-type instructions must have lowest 12 immediate bits set to 0"
        );
        u32::to_le_bytes(($imm as u32 & !0xfff) | (($rd as u32) << 7) | $op)
    }};
}

pub(crate) struct RiscV64Inter;

fn addi(reg: RiscVRegister, i: i16) -> [u8; 4] {
    encode_instr!([I] 0b001_0011, reg, reg, 0, i)
}

#[derive(Clone, Copy, PartialEq)]
enum CompareType {
    Eq,
    Ne,
}

fn cond_jump(
    reg: RiscVRegister,
    comp_type: CompareType,
    mut distance: i64,
) -> Result<[u8; 8], BFCompileError> {
    assert!(
        distance & 1 == 0,
        "<...>::riscv64::cond_jump distance offset must be even"
    );
    distance >>= 1;
    if distance.min_bits() > 12 {
        return Err(BFCompileError::basic(
            BFErrorID::JumpTooLong,
            "Jump too long for riscv64 backend",
        ));
    }
    // B-type is a variant of an existing type with 2 specific immediate bits swapped, used for
    // branch instructions.
    let dist = distance as u32;
    let dist = (dist & 0xbfe) | (dist & 0x400) >> 10 | (dist & 1) << 10;
    let aux = reg.aux();

    // use this macro instead of passing `$cond_code` because encode_instr uses const assert to
    // make sure its in range, so it needs to take constant values
    macro_rules! branch {
        ($cond_code: literal) => {{
            encode_instr!([S] 0b110_0011, aux, RiscVRegister::Zero, $cond_code, dist)
        }}
    }
    let mut code = [0; 8];
    // load
    code[..4].clone_from_slice(&load_from_byte(reg, aux));
    code[4..].clone_from_slice(&if comp_type == CompareType::Eq {
        branch!(0)
    } else {
        branch!(1)
    });
    Ok(code)
}

fn c_addi(reg: RiscVRegister, i: i8) -> [u8; 2] {
    assert!(
        i.min_bits() <= 6,
        "c_addi must only be called with 6-bit signed immediates"
    );
    // C.ADDI (expands to `addi reg, reg, imm`, and reg and imm must not be zero
    assert!(
        i != 0 && reg != RiscVRegister::Zero,
        "C.ADDI requires nonzero arguments"
    );
    let mut instr = [(reg as u8 & 1) << 7 | 0b0101, (reg as u8) >> 1];
    instr[1] |= ((i as u8) & 0b100_000) >> 1;
    instr[0] |= ((i as u8) & 0b11_111) << 2;
    instr
}

fn store_to_byte(addr: RiscVRegister, src: RiscVRegister) -> [u8; 4] {
    encode_instr!([S] 0b100_011, addr, src, 0, 0)
}

fn load_from_byte(addr: RiscVRegister, dst: RiscVRegister) -> [u8; 4] {
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
    const JUMP_SIZE: usize = 8;
    const ARCH: ElfArch = ElfArch::RiscV64;
    const E_FLAGS: u32 = 5; // EF_RISCV_RVC | EF_RISCV_FLOAT_ABI_DOUBLE (chosen to match Debian)
    const EI_DATA: ByteOrdering = ByteOrdering::LittleEndian;

    fn set_reg(code_buf: &mut Vec<u8>, reg: Self::RegType, imm: i64) {
        match imm.min_bits() {
            1..=6 => {
                // C.LI reg (expands to addi rd, x0, imm[5:0])
                let high_bit = ((imm & (1 << 6)) << 6) as u16;
                code_buf.extend(u16::to_le_bytes(
                    0x4001 | high_bit | ((reg as u16) << 7) | (imm & 0x3f << 2) as u16,
                ));
            }
            0 | 7..=12 => {
                // the LI pseudoinstruction is implemented as ADDI rd, zero, imm
                code_buf.extend(encode_instr!([I] 0b001_0011, reg, RiscVRegister::Zero, 0, imm));
            }
            13..=18 => {
                let high_bit = ((imm & (1 << 17)) >> 5) as u16;
                // C.LUI reg (expands to addi rd, x0, imm[5:0])
                code_buf.extend(u16::to_le_bytes(
                    0x6001 | high_bit | ((reg as u16) << 7) | (imm & 0xf0_00 >> 10) as u16,
                ));
                Self::add_reg(code_buf, reg, (imm & 0xfff) as u64);
            }
            19..=32 => {
                // this sign-extends the lowest 12 bits
                let lower_12 = ((imm as i32) & 0xfff) << 20 >> 20;
                let upper_20 = ((imm as i32) - lower_12) >> 12 << 12;
                // LUI reg, imm&!0xfff
                code_buf.extend(encode_instr!([U] 0b011_0111, reg, upper_20));
                if lower_12 != 0 {
                    Self::add_reg(code_buf, reg, i64::from(lower_12) as u64);
                }
            }
            _ => todo!(),
        }
    }

    fn reg_copy(code_buf: &mut Vec<u8>, dst: Self::RegType, src: Self::RegType) {
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
        code_buf.extend(u32::to_le_bytes(0x13));
        code_buf.extend(u32::to_le_bytes(0x13));
    }

    fn jump_open(
        code_buf: &mut [u8],
        index: usize,
        reg: Self::RegType,
        offset: i64,
    ) -> FailableInstrEncoding {
        code_buf[index..index + 8].clone_from_slice(&cond_jump(reg, CompareType::Eq, offset)?);
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
        if (imm as i8).min_bits() <= 6 {
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
        if (imm as i8).min_bits() <= 6 {
            code_buf.extend(c_addi(reg, imm as i8));
        } else {
            code_buf.extend(addi(reg, i16::from(imm)));
        }
        code_buf.extend(store_to_byte(reg, aux));
    }

    fn add_reg(code_buf: &mut Vec<u8>, reg: Self::RegType, imm: u64) {
        match (imm as i64).min_bits() {
            0 => (),
            1..=6 => code_buf.extend(c_addi(reg, imm as i8)),
            7..=12 => code_buf.extend(addi(reg, imm as i16)),
            13.. => {
                let aux = reg.aux();
                Self::set_reg(code_buf, aux, imm as i64);
                code_buf.extend(encode_instr!([R] 0b011_0011, reg, reg, aux, 0, 0));
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
        code_buf.extend(store_to_byte(reg, RiscVRegister::Zero));
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
        let mut v = Vec::from(addi(RiscVRegister::T0, -0x789));
        v.extend(addi(RiscVRegister::T1, 0x123));
        assert_eq!(
            disassembler().disassemble(v),
            ["addi t0, t0, -0x789", "addi t1, t1, 0x123"]
        );
    }

    #[test]
    #[should_panic = "c_addi must only be called with 6-bit signed immediates"]
    fn test_caddi_guard_positive() {
        c_addi(RiscVRegister::T0, 0b0111_0000);
    }
    #[test]
    #[should_panic = "c_addi must only be called with 6-bit signed immediates"]
    fn test_caddi_guard_negative() {
        c_addi(RiscVRegister::T0, -0b0111_0000);
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
        let mut v = Vec::from(load_from_byte(RiscVRegister::A0, RiscVRegister::T0));
        v.extend(store_to_byte(RiscVRegister::A0, RiscVRegister::T0));
        assert_eq!(
            disassembler().disassemble(v),
            ["lb t0, 0x0(a0)", "sb t0, 0x0(a0)"]
        );
    }

    #[disasm_test]
    fn test_zero_byte() {
        let mut v = Vec::with_capacity(4);
        RiscV64Inter::zero_byte(&mut v, RiscVRegister::A2);
        assert_eq!(disassembler().disassemble(v), ["sb zero, 0x0(a2)"]);
    }
}
