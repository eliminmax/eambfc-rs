// SPDX-FileCopyrightText: 2024-2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use super::arch_inter::{ArchInter, FailableInstrEncoding, Registers, SyscallNums};
use super::compile::BFCompile;
use super::elf_tools::{EIData, ELFArch};
use super::err::BFCompileError;

// 64-bit ARM systems have 31 general-purpose registers which can be addressed in 32-bit or 64-bit
// forms. w8 is the 32-bit form for register #8, and x0 is the 64-bit form for register #0.
// X19 is the first register that the ABI guarantees to be preserved across function calls, and the
// rest are used by the Linux system call interface for the platform.
// Other registers are not defined because they are not needed for eambfc-rs, but they go up to 31.
// 32 is a special case not relevant here.

#[derive(Debug, Copy, Clone, PartialEq)]
#[repr(u8)]
pub enum Arm64Register {
    X0 = 0,   // arg1 register
    X1 = 1,   // arg2 register
    X2 = 2,   // arg3 register
    X8 = 8,   // syscall register
    X16 = 16, // scratch register
    X17 = 17, // scratch register
    X19 = 19, // bf pointer register
}

#[derive(Debug, Copy, Clone, PartialEq)]
#[repr(u8)]
enum ShiftLevel {
    NoShift = 0b0000000,
    Shift16 = 0b0100000,
    Shift32 = 0b1000000,
    Shift48 = 0b1100000,
}

#[derive(Debug, PartialEq)]
#[repr(u8)]
enum MoveType {
    Keep = 0xf2,
    Zero = 0xd2,
    Invert = 0x92,
}

fn inject_reg_operands(rt: Arm64Register, rn: Arm64Register, template: [u8; 4]) -> [u8; 4] {
    let rn = rn as u8; // helpful as rn is used more than once
    [
        template[0] | (rt as u8) | (rn << 5),
        template[1] | (rn >> 3),
        template[2],
        template[3],
    ]
}

fn inject_imm16_operands(
    imm16: u16,
    shift: ShiftLevel,
    reg: Arm64Register,
    template: [u8; 4],
) -> [u8; 4] {
    [
        template[0] | reg as u8 | ((imm16 & 0b111) << 5) as u8,
        // why doesn't ARM's A64 align immediate bits with byte boundries?
        template[1] | (imm16 >> 3) as u8,
        // need to combine the highest 5 bits of imm16 with the shift
        template[2] | shift as u8 | (imm16 >> 11) as u8,
        template[3],
    ]
}

fn mov(move_type: MoveType, imm16: u16, shift: ShiftLevel, reg: Arm64Register) -> [u8; 4] {
    // depending on MoveType, it will be one of MOVK, MOVN, or MOVZ
    // bitwise not to invert imm16 if needed.
    let imm16 = if move_type == MoveType::Invert {
        !imm16
    } else {
        imm16
    };
    inject_imm16_operands(imm16, shift, reg, [0x00u8, 0x00, 0x80, move_type as u8])
}

fn aux_reg(reg: Arm64Register) -> Arm64Register {
    if reg == Arm64Register::X17 {
        Arm64Register::X16
    } else {
        Arm64Register::X17
    }
}

fn load_from_byte(addr: Arm64Register, dst: Arm64Register) -> [u8; 4] {
    // LDRB dst, addr
    inject_reg_operands(dst, addr, [0x00, 0x04, 0x40, 0x38])
}

fn store_to_byte(addr: Arm64Register, src: Arm64Register) -> [u8; 4] {
    // STRB src, addr
    inject_reg_operands(src, addr, [0x00, 0x04, 0x00, 0x38])
}

macro_rules! fn_byte_arith_wrapper {
    ($fn_name:ident, $inner:ident, internal_fn) => {
        fn $fn_name(code_buf: &mut Vec<u8>, reg: Arm64Register) {
            let aux = aux_reg(reg);
            code_buf.extend(load_from_byte(reg, aux));
            Self::$inner(code_buf, aux);
            code_buf.extend(store_to_byte(reg, aux));
        }
    };
    ($fn_name:ident, $op:ident, arith_op) => {
        fn $fn_name(code_buf: &mut Vec<u8>, reg: Arm64Register, imm: i8) {
            let aux = aux_reg(reg);
            code_buf.extend(load_from_byte(reg, aux));
            // Either ADD aux, aux, imm or SUB aux, aux, imm depending on op_code
            code_buf.extend([
                aux as u8 | (aux as u8) << 5,
                (imm as u8) << 2 | (aux as u8) >> 3,
                (imm as u8) >> 6,
                ArithOp::$op as u8,
            ]);
            code_buf.extend(store_to_byte(reg, aux));
        }
    };
}

macro_rules! fn_branch_cond {
    ($fn_name:ident, $cond:literal) => {
        fn $fn_name(
            code_buf: &mut Vec<u8>,
            reg: Arm64Register,
            offset: i64,
        ) -> FailableInstrEncoding {
            // Ensure only lower 4 bits of cond are used - the const _: () mess forces the check to
            // run at compile time rather than runtime.
            const _: () = assert!($cond & 0xf0_u8 == 0);
            // as A64 uses fixed-size 32-bit instructions, offset must be a multiple of 4.
            if offset % 4 != 0 {
                return Err(BFCompileError::Basic {
                    id: String::from("INVALID_JUMP_ADDRESS"),
                    msg: format!("{offset} is an invalid address offset (offset % 4 != 0)"),
                });
            }
            // Encoding uses 19 immediate bits, and treats it as having an implicit 0b00 at the
            // end, as it needs to be a multiple of 4 anyway. The result is that it must be a
            // 21-bit value. Make sure that it fits within that value.
            if std::cmp::max(offset.leading_ones(), offset.leading_zeros()) < 44 {
                return Err(BFCompileError::Basic {
                    id: String::from("JUMP_TOO_LONG"),
                    msg: format!("{offset} is outside the range of possible 21-bit signed values"),
                });
            }
            let offset = 1 + ((offset as u32) >> 2) & 0x7ffff;
            let aux = aux_reg(reg);
            code_buf.extend(load_from_byte(reg, aux));
            code_buf.extend([
                // TST reg, 0xff (technically an alias for ANDS xzr, reg, 0xff)
                0x1f_u8 | (aux as u8) << 5,
                (aux as u8) >> 3 | 0x1c,
                0x40,
                0xf2,
                // B.$cond {offset}
                $cond | (offset << 5) as u8,
                (offset >> 3) as u8,
                (offset >> 11) as u8,
                0x54,
            ]);
            Ok(())
        }
    };
}

pub struct Arm64Inter;
impl ArchInter for Arm64Inter {
    type RegType = Arm64Register;
    const JUMP_SIZE: usize = 12;

    const REGISTERS: Registers<Arm64Register> = Registers {
        // Linux uses w8 for system call numbers, but w8 is just the lower 32 bits of x8.
        sc_num: Arm64Register::X8,
        arg1: Arm64Register::X0,
        arg2: Arm64Register::X1,
        arg3: Arm64Register::X2,
        bf_ptr: Arm64Register::X19,
    };

    const SC_NUMS: SyscallNums = SyscallNums {
        read: 63,
        write: 64,
        exit: 93,
    };

    const ARCH: ELFArch = ELFArch::Arm64;
    const EI_DATA: EIData = EIData::ELFDATA2LSB;
    fn set_reg(code_buf: &mut Vec<u8>, reg: Arm64Register, imm: i64) {
        // split the immediate into 4 16-bit parts - high, medium-high, medium-low, and low
        let parts: [(u16, ShiftLevel); 4] = [
            (imm as u16, ShiftLevel::NoShift),
            ((imm >> 16) as u16, ShiftLevel::Shift16),
            ((imm >> 32) as u16, ShiftLevel::Shift32),
            ((imm >> 48) as u16, ShiftLevel::Shift48),
        ];
        let (test_val, first_mov_type): (u16, MoveType) = if imm < 0 {
            (0xffff, MoveType::Invert)
        } else {
            (0, MoveType::Zero)
        };
        let mut parts = parts.iter().filter(|(imm16, _)| *imm16 != test_val);
        let fallback = (test_val, ShiftLevel::NoShift);
        let (lead_imm, lead_shift) = parts.next().unwrap_or(&fallback);
        // (MOVZ or MOVN) reg, lead_imm << lead_shift
        code_buf.extend(mov(first_mov_type, *lead_imm, *lead_shift, reg));
        parts.for_each(|(imm16, shift)| {
            // MOVK reg, imm16 << shift
            code_buf.extend(mov(MoveType::Keep, *imm16, *shift, reg));
        });
    }

    fn reg_copy(code_buf: &mut Vec<u8>, dst: Arm64Register, src: Arm64Register) {
        // MOV dst, src
        // technically an alias for ORR dst, XZR, src (XZR is a read-only zero register)
        code_buf.extend([0xe0 | dst as u8, 0x01, src as u8, 0xaa]);
    }
    fn syscall(code_buf: &mut Vec<u8>) {
        // SVC 0
        code_buf.extend([0x01u8, 0x00, 0x00, 0xd4]);
    }
    fn nop_loop_open(code_buf: &mut Vec<u8>) {
        // 3 NOP instructions.
        const NOP: [u8; 4] = [0x1f, 0x20, 0x30, 0xd5];
        code_buf.extend(NOP.repeat(3));
    }

    fn inc_reg(code_buf: &mut Vec<u8>, reg: Arm64Register) {
        let reg = reg as u8; // helpful as it's used more than once
        code_buf.extend([
            reg | (reg << 5),
            0x04 | (reg >> 3),
            0x00,
            ArithOp::Add as u8,
        ]); // ADD reg, reg, 1
    }
    fn dec_reg(code_buf: &mut Vec<u8>, reg: Arm64Register) {
        let reg = reg as u8; // helpful as it's used more than once
        code_buf.extend([
            reg | (reg << 5),
            0x04 | (reg >> 3),
            0x00,
            ArithOp::Sub as u8,
        ]); // SUB reg, reg, 1
    }

    fn add_reg(code_buf: &mut Vec<u8>, reg: Arm64Register, imm: i64) -> FailableInstrEncoding {
        add_sub(code_buf, reg, imm, ArithOp::Add)
    }
    fn sub_reg(code_buf: &mut Vec<u8>, reg: Arm64Register, imm: i64) -> FailableInstrEncoding {
        add_sub(code_buf, reg, imm, ArithOp::Sub)
    }

    fn zero_byte(code_buf: &mut Vec<u8>, reg: Arm64Register) {
        let aux = aux_reg(reg);
        Arm64Inter::set_reg(code_buf, aux, 0);
        code_buf.extend(store_to_byte(reg, aux));
    }
    fn_byte_arith_wrapper!(add_byte, Add, arith_op);
    fn_byte_arith_wrapper!(sub_byte, Sub, arith_op);
    fn_byte_arith_wrapper!(inc_byte, inc_reg, internal_fn);
    fn_byte_arith_wrapper!(dec_byte, dec_reg, internal_fn);
    fn_branch_cond!(jump_not_zero, 0x1u8);
    fn_branch_cond!(jump_zero, 0x00u8);
}

impl BFCompile for Arm64Inter {}

// discriminants used here are often, but not always, the last byte in an ADD or SUB instructions
#[derive(Clone, Copy, Debug, PartialEq)]
#[repr(u8)]
enum ArithOp {
    Add = 0x91,
    Sub = 0xd1,
}

fn add_sub_imm(
    code_buf: &mut Vec<u8>,
    reg: Arm64Register,
    imm: i64,
    op: ArithOp,
    shift: bool,
) -> FailableInstrEncoding {
    if (shift && (imm & !0xfff000) != 0) || (!shift && (imm & !0xfff) != 0) {
        return Err(BFCompileError::Basic {
            id: String::from("IMMEDIATE_TOO_LARGE"),
            msg: format!(
                "0x{imm:x} is invalid for shift level {}",
                12 * (shift as u8)
            ),
        });
    }
    let reg = reg as u8; // helpful as it's used multiple times.
    let imm = if shift { imm >> 12 } else { imm };
    // either ADD reg, reg, imm or SUB reg, reg, imm, depending on op
    code_buf.extend([
        reg | (reg << 5),
        (reg >> 3) | (imm << 2) as u8,
        (imm >> 6) as u8 | if shift { 0x40 } else { 0 },
        op as u8,
    ]);
    Ok(())
}

fn add_sub(
    code_buf: &mut Vec<u8>,
    reg: Arm64Register,
    imm: i64,
    op: ArithOp,
) -> FailableInstrEncoding {
    match imm {
        i if i < 0x1000 => add_sub_imm(code_buf, reg, imm, op, false)?,
        i if i < 0x1000000 => {
            add_sub_imm(code_buf, reg, imm & 0xfff000, op, true)?;
            if i & 0xfff != 0 {
                add_sub_imm(code_buf, reg, imm & 0xfff, op, false)?;
            }
        }
        i => {
            let op_byte: u8 = match op {
                ArithOp::Add => 0x8b,
                ArithOp::Sub => 0xcb,
            };
            let aux = aux_reg(reg);
            Arm64Inter::set_reg(code_buf, aux, i);
            // either ADD reg, reg, aux or SUB reg, reg, aux
            code_buf.extend(inject_reg_operands(
                reg,
                reg,
                [0u8, 0u8, aux as u8, op_byte],
            ));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_set_reg_simple() -> Result<(), String> {
        // the following can be set with 1 instruction each.
        let mut v: Vec<u8> = Vec::new();
        Arm64Inter::set_reg(&mut v, Arm64Register::X0, 0);
        assert_eq!(
            v,
            vec![0x00, 0x00, 0x80, 0xd2] // MOVN x0, 0
        );

        v.clear();
        Arm64Inter::set_reg(&mut v, Arm64Register::X0, -1);
        assert_eq!(
            v,
            vec![0x00, 0x00, 0x80, 0x92] // MOVN X0, -1
        );

        v.clear();
        Arm64Inter::set_reg(&mut v, Arm64Register::X0, -0x100001);
        assert_eq!(v, vec![0x00, 0x02, 0xa0, 0x92]);

        v.clear();

        Arm64Inter::set_reg(&mut v, Arm64Register::X1, 0xbeef);
        assert_eq!(
            v,
            vec![0xe1, 0xdd, 0x97, 0xd2], // MOVZ x1, 0xbeef
        );
        Ok(())
    }

    #[test]
    fn test_reg_multiple() -> Result<(), String> {
        let mut v: Vec<u8> = Vec::new();
        Arm64Inter::set_reg(&mut v, Arm64Register::X0, 0xdeadbeef);
        assert_eq!(
            v,
            vec![
                0xe0, 0xdd, 0x97, 0xd2, // MOVZ x0, 0xbeef
                0xa0, 0xd5, 0xbb, 0xf2, // MOVK x0, 0xdead, lsl #16
            ],
        );
        Ok(())
    }

    #[test]
    fn test_reg_split() -> Result<(), String> {
        let mut v: Vec<u8> = Vec::new();
        Arm64Inter::set_reg(&mut v, Arm64Register::X19, 0xdead0000beef);
        assert_eq!(
            v,
            vec![
                0xf3, 0xdd, 0x97, 0xd2, // MOVZ x19, 0xbeef
                0xb3, 0xd5, 0xdb, 0xf2, // MOVK x19, 0xdead, lsl #32
            ],
        );
        Ok(())
    }

    #[test]
    fn test_reg_neg() -> Result<(), String> {
        let mut v: Vec<u8> = Vec::new();
        Arm64Inter::set_reg(&mut v, Arm64Register::X19, -0xdeadbeef);
        assert_eq!(
            v,
            vec![
                0xd3, 0xdd, 0x97, 0x92, // MOVN x19, 0xbeee
                0x53, 0x2a, 0xa4, 0xf2, // MOVK x19, ~0xdead, lsl #16
            ],
        );
        Ok(())
    }

    #[test]
    fn test_inc_dec_reg() -> Result<(), String> {
        let mut v: Vec<u8> = Vec::new();
        Arm64Inter::inc_reg(&mut v, Arm64Register::X0);
        assert_eq!(
            v,
            vec![0x00, 0x04, 0x00, 0x91], // ADD x0, x0, 1
        );

        v.clear();
        Arm64Inter::inc_reg(&mut v, Arm64Register::X19);
        assert_eq!(
            v,
            vec![0x73, 0x06, 0x00, 0x91], // ADD x19, x19, 1
        );

        v.clear();
        Arm64Inter::dec_reg(&mut v, Arm64Register::X1);
        assert_eq!(
            v,
            vec![0x21, 0x04, 0x00, 0xd1], // SUB x1, x1, 1
        );

        v.clear();
        Arm64Inter::dec_reg(&mut v, Arm64Register::X19);
        assert_eq!(
            v,
            vec![0x73, 0x06, 0x00, 0xd1], // SUB x19, x19, 1
        );
        Ok(())
    }

    #[test]
    fn test_load_store() -> Result<(), String> {
        assert_eq!(
            load_from_byte(Arm64Register::X19, Arm64Register::X16),
            [0x70, 0x06, 0x40, 0x38], // LRDB w16, [x19], 0
        );

        assert_eq!(
            store_to_byte(Arm64Register::X19, Arm64Register::X16),
            [0x70, 0x06, 0x00, 0x38], // STDB w16, [x19], 0
        );
        Ok(())
    }

    #[test]
    fn test_add_sub_reg() -> Result<(), String> {
        let mut v: Vec<u8> = Vec::new();
        // Handling of 24-bit values
        assert!(add_sub(&mut v, Arm64Register::X16, 0xabcdef, ArithOp::Add).is_ok());
        assert_eq!(
            v,
            vec![
                0x10, 0xf2, 0x6a, 0x91, // ADD x16, x16, 0xabc, lsl 12
                0x10, 0xbe, 0x37, 0x91, // ADD x16, x16, 0xdef
            ],
        );

        // Ensure that if it fits within 24 bits and the lowest 12 are 0, no ADD or SUB 0 is
        // included
        v.clear();
        assert!(add_sub(&mut v, Arm64Register::X16, 0xabc000, ArithOp::Sub).is_ok());
        assert_eq!(
            v,
            vec![
                0x10, 0xf2, 0x6a, 0xd1, // SUB x16, x16, 0xabc, lsl 12
            ],
        );
        Ok(())
    }

    #[test]
    fn test_add_sub_byte() -> Result<(), String> {
        let mut v: Vec<u8> = Vec::new();
        Arm64Inter::add_byte(&mut v, Arm64Register::X19, 0xa5u8 as i8);
        assert_eq!(
            v,
            vec![
                0x71, 0x06, 0x40, 0x38, // LRDB w17, [x19], 0
                0x31, 0x96, 0x02, 0x91, // ADD x17, x17, 0xa5
                0x71, 0x06, 0x00, 0x38, // STDB w17, [x19], 0
            ],
        );
        Ok(())
    }

    #[test]
    fn test_zero_byte() -> Result<(), String> {
        let mut v: Vec<u8> = Vec::new();
        Arm64Inter::zero_byte(&mut v, Arm64Register::X19);
        assert_eq!(
            v,
            vec![
                0x11, 0x00, 0x80, 0xd2, // MOVZ x17, 0
                0x71, 0x06, 0x00, 0x38, // STRB w17, [X19], 0
            ]
        );
        Ok(())
    }
}
