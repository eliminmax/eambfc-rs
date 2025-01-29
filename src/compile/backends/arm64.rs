// SPDX-FileCopyrightText: 2024 - 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use crate::err::{BFCompileError, BFErrorID};

use super::arch_inter::{ArchInter, FailableInstrEncoding, Registers, SyscallNums};
use super::elf_tools::{ByteOrdering, ElfArch};

// 64-bit ARM systems have 31 general-purpose registers which can be addressed in 32-bit or 64-bit
// forms. w8 is the 32-bit form for register #8, and x0 is the 64-bit form for register #0.
// X19 is the first register that the ABI guarantees to be preserved across function calls, and the
// rest are used by the Linux system call interface for the platform.
// Other registers are not defined because they are not needed for eambfc-rs, but they go up to 31.
// 32 is a special case not relevant here.

#[derive(Debug, Clone, Copy, PartialEq)]
#[repr(u8)]
pub(in super::super) enum Arm64Register {
    X0 = 0,   // arg1 register
    X1 = 1,   // arg2 register
    X2 = 2,   // arg3 register
    X8 = 8,   // syscall register
    X16 = 16, // scratch register
    X17 = 17, // scratch register
    X19 = 19, // bf pointer register
}

#[derive(Clone, Copy, PartialEq)]
#[repr(u8)]
enum ShiftLevel {
    NoShift = 0b000_0000,
    Shift16 = 0b010_0000,
    Shift32 = 0b100_0000,
    Shift48 = 0b110_0000,
}

#[derive(PartialEq)]
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
        // why doesn't ARM's A64 align immediate bits with byte boundaries?
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
    inject_imm16_operands(imm16, shift, reg, [0x00, 0x00, 0x80, move_type as u8])
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

#[derive(PartialEq)]
enum ConditionCode {
    Eq = 0,
    Ne = 1,
}

fn branch_cond(
    reg: Arm64Register,
    offset: i64,
    cond: ConditionCode,
) -> Result<[u8; 12], BFCompileError> {
    // as A64 uses fixed-size 32-bit instructions, offset must be a multiple of 4.
    assert!(
        offset.trailing_zeros() >= 2,
        "offset {offset} is invalid for architecture (offset % 4 != 0)"
    );
    // Encoding uses 19 immediate bits, and treats it as having an implicit 0b00 at the
    // end, as it needs to be a multiple of 4 anyway. The result is that it must be a
    // 21-bit value. Make sure that it fits within that value.
    if std::cmp::max(offset.leading_ones(), offset.leading_zeros()) < 44 {
        return Err(BFCompileError::basic(
            BFErrorID::JumpTooLong,
            format!("{offset} is outside the range of possible 21-bit signed values"),
        ));
    }
    let offset = (1 + ((offset as u32) >> 2)) & 0x7ffff;
    let aux = aux_reg(reg);
    let mut code_buf = [0; 12];
    code_buf[..4].clone_from_slice(&load_from_byte(reg, aux));
    code_buf[4..].clone_from_slice(&[
        // TST reg, 0xff (technically an alias for ANDS xzr, reg, 0xff)
        0x1f | (aux as u8) << 5,
        (aux as u8) >> 3 | 0x1c,
        0x40,
        0xf2,
        // B.cond {offset}
        (cond as u8) | (offset << 5) as u8,
        (offset >> 3) as u8,
        (offset >> 11) as u8,
        0x54,
    ]);
    Ok(code_buf)
}

pub(crate) struct Arm64Inter;
impl ArchInter for Arm64Inter {
    type RegType = Arm64Register;
    const JUMP_SIZE: usize = 12;
    const E_FLAGS: u32 = 0;

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

    const ARCH: ElfArch = ElfArch::Arm64;
    const EI_DATA: ByteOrdering = ByteOrdering::LittleEndian;
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
        code_buf.extend([0xe0 | dst as u8, 0x03, src as u8, 0xaa]);
    }
    fn syscall(code_buf: &mut Vec<u8>) {
        // SVC 0
        code_buf.extend([0x01, 0x00, 0x00, 0xd4]);
    }
    fn nop_loop_open(code_buf: &mut Vec<u8>) {
        // 3 NOP instructions.
        const NOP: [u8; 4] = [0x1f, 0x20, 0x03, 0xd5];
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

    fn add_reg(code_buf: &mut Vec<u8>, reg: Arm64Register, imm: i64) {
        add_sub(code_buf, reg, imm, ArithOp::Add);
    }
    fn sub_reg(code_buf: &mut Vec<u8>, reg: Arm64Register, imm: i64) {
        add_sub(code_buf, reg, imm, ArithOp::Sub);
    }

    fn zero_byte(code_buf: &mut Vec<u8>, reg: Arm64Register) {
        let aux = aux_reg(reg);
        Arm64Inter::set_reg(code_buf, aux, 0);
        code_buf.extend(store_to_byte(reg, aux));
    }

    fn add_byte(code_buf: &mut Vec<u8>, reg: Arm64Register, imm: i8) {
        let aux = aux_reg(reg);
        code_buf.extend(load_from_byte(reg, aux));
        add_sub(code_buf, aux, (imm as u8).into(), ArithOp::Add);
        code_buf.extend(store_to_byte(reg, aux));
    }

    fn sub_byte(code_buf: &mut Vec<u8>, reg: Arm64Register, imm: i8) {
        let aux = aux_reg(reg);
        code_buf.extend(load_from_byte(reg, aux));
        add_sub(code_buf, aux, (imm as u8).into(), ArithOp::Sub);
        code_buf.extend(store_to_byte(reg, aux));
    }

    fn inc_byte(code_buf: &mut Vec<u8>, reg: Arm64Register) {
        let aux = aux_reg(reg);
        code_buf.extend(load_from_byte(reg, aux));
        Self::inc_reg(code_buf, aux);
        code_buf.extend(store_to_byte(reg, aux));
    }

    fn dec_byte(code_buf: &mut Vec<u8>, reg: Arm64Register) {
        let aux = aux_reg(reg);
        code_buf.extend(load_from_byte(reg, aux));
        Self::dec_reg(code_buf, aux);
        code_buf.extend(store_to_byte(reg, aux));
    }

    fn jump_close(
        code_buf: &mut Vec<u8>,
        reg: Self::RegType,
        offset: i64,
    ) -> FailableInstrEncoding {
        code_buf.extend(branch_cond(reg, offset, ConditionCode::Ne)?);
        Ok(())
    }

    fn jump_open(
        code_buf: &mut [u8],
        index: usize,
        reg: Self::RegType,
        offset: i64,
    ) -> FailableInstrEncoding {
        code_buf[index..index + Self::JUMP_SIZE].swap_with_slice(&mut branch_cond(
            reg,
            offset,
            ConditionCode::Eq,
        )?);
        Ok(())
    }
}

// discriminants used here are often, but not always, the last byte in an ADD or SUB instructions
#[derive(Clone, Copy, PartialEq)]
#[repr(u8)]
enum ArithOp {
    Add = 0x91,
    Sub = 0xd1,
}

fn add_sub_imm(code_buf: &mut Vec<u8>, reg: Arm64Register, imm: i64, op: ArithOp, shift: bool) {
    assert!((shift && (imm & !0xfff_000) == 0) || (!shift && (imm & !0xfff) == 0));
    let reg = reg as u8; // helpful as it's used multiple times.
    let imm = if shift { imm >> 12 } else { imm };
    // either ADD reg, reg, imm or SUB reg, reg, imm, depending on op
    code_buf.extend([
        reg | (reg << 5),
        (reg >> 3) | (imm << 2) as u8,
        (imm >> 6) as u8 | if shift { 0x40 } else { 0 },
        op as u8,
    ]);
}

fn add_sub(code_buf: &mut Vec<u8>, reg: Arm64Register, imm: i64, op: ArithOp) {
    match imm {
        i if i < 0x1_000 => add_sub_imm(code_buf, reg, imm, op, false),
        i if i < 0x1_000_000 => {
            add_sub_imm(code_buf, reg, imm & 0xfff_000, op, true);
            if i & 0xfff != 0 {
                add_sub_imm(code_buf, reg, imm & 0xfff, op, false);
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
            code_buf.extend(inject_reg_operands(reg, reg, [0, 0, aux as u8, op_byte]));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::test_utils::Disassembler;
    use super::*;

    fn disassembler() -> Disassembler {
        Disassembler::new(ElfArch::Arm64)
    }

    #[test]
    fn test_set_reg_simple() {
        let mut ds = disassembler();
        // the following can be set with 1 instruction each.
        let mut v: Vec<u8> = Vec::new();
        Arm64Inter::set_reg(&mut v, Arm64Register::X0, 0);
        assert_eq!(ds.disassemble(v), ["mov x0, #0x0"],);

        let mut v: Vec<u8> = Vec::new();
        Arm64Inter::set_reg(&mut v, Arm64Register::X0, -1);
        assert_eq!(ds.disassemble(v), ["mov x0, #-0x1"],);

        let mut v: Vec<u8> = Vec::new();
        Arm64Inter::set_reg(&mut v, Arm64Register::X0, -0x100_001);
        assert_eq!(ds.disassemble(v), ["mov x0, #-0x100001"]);

        let mut v: Vec<u8> = Vec::new();
        Arm64Inter::set_reg(&mut v, Arm64Register::X1, 0xbeef);
        assert_eq!(ds.disassemble(v), ["mov x1, #0xbeef"]);
    }

    #[test]
    fn test_reg_multiple() {
        let mut v: Vec<u8> = Vec::new();
        #[allow(clippy::unreadable_literal, reason = "deadbeef is famously readable")]
        Arm64Inter::set_reg(&mut v, Arm64Register::X0, 0xdeadbeef);
        assert_eq!(
            disassembler().disassemble(v),
            ["mov x0, #0xbeef", "movk x0, #0xdead, lsl #16"],
        );
    }

    #[test]
    fn test_reg_split() {
        let mut v: Vec<u8> = Vec::new();
        Arm64Inter::set_reg(&mut v, Arm64Register::X19, 0xdead_0000_beef);
        assert_eq!(
            disassembler().disassemble(v),
            ["mov x19, #0xbeef", "movk x19, #0xdead, lsl #32"],
        );
    }

    #[test]
    fn test_reg_neg() {
        let mut v: Vec<u8> = Vec::new();
        #[allow(clippy::unreadable_literal, reason = "deadbeef is famously readable")]
        Arm64Inter::set_reg(&mut v, Arm64Register::X19, -0xdeadbeef);
        assert_eq!(
            disassembler().disassemble(v),
            [
                "mov x19, #-0xbeef",
                // the bitwise negation of 0xdead is 0x2152
                "movk x19, #0x2152, lsl #16",
            ],
        );
    }

    #[test]
    fn test_inc_dec_reg() {
        let mut ds = disassembler();
        let mut v: Vec<u8> = Vec::new();
        Arm64Inter::inc_reg(&mut v, Arm64Register::X0);
        assert_eq!(ds.disassemble(v), ["add x0, x0, #0x1"]);

        let mut v: Vec<u8> = Vec::new();
        Arm64Inter::inc_reg(&mut v, Arm64Register::X19);
        assert_eq!(ds.disassemble(v), ["add x19, x19, #0x1"]);

        let mut v: Vec<u8> = Vec::new();
        Arm64Inter::dec_reg(&mut v, Arm64Register::X1);
        assert_eq!(ds.disassemble(v), ["sub x1, x1, #0x1"]);

        let mut v: Vec<u8> = Vec::new();
        Arm64Inter::dec_reg(&mut v, Arm64Register::X19);
        assert_eq!(ds.disassemble(v), ["sub x19, x19, #0x1"]);
    }

    #[test]
    fn test_load_store() {
        let mut ds = disassembler();
        assert_eq!(
            ds.disassemble(load_from_byte(Arm64Register::X19, Arm64Register::X16).into()),
            ["ldrb w16, [x19], #0x0"],
        );

        assert_eq!(
            ds.disassemble(store_to_byte(Arm64Register::X19, Arm64Register::X16).into()),
            ["strb w16, [x19], #0x0"],
        );
    }

    #[test]
    fn test_add_sub_reg() {
        let mut ds = disassembler();

        // Handling of 24-bit values
        let mut v: Vec<u8> = Vec::with_capacity(24);
        add_sub(&mut v, Arm64Register::X16, 0xabc_def, ArithOp::Add);
        assert_eq!(
            ds.disassemble(v),
            ["add x16, x16, #0xabc, lsl #12", "add x16, x16, #0xdef"]
        );

        // Ensure that if it fits within 24 bits and the lowest 12 are 0, no ADD or SUB 0 is
        // included
        let mut v: Vec<u8> = Vec::with_capacity(24);
        add_sub(&mut v, Arm64Register::X16, 0xabc_000, ArithOp::Sub);
        assert_eq!(ds.disassemble(v), ["sub x16, x16, #0xabc, lsl #12"]);

        let mut v: Vec<u8> = Vec::with_capacity(24);
        #[allow(clippy::unreadable_literal, reason = "deadbeef is famously readable")]
        Arm64Inter::add_reg(&mut v, Arm64Register::X16, 0xdeadbeef);
        #[allow(clippy::unreadable_literal, reason = "deadbeef is famously readable")]
        Arm64Inter::sub_reg(&mut v, Arm64Register::X16, 0xdeadbeef);
        assert_eq!(
            ds.disassemble(v),
            [
                "mov x17, #0xbeef",
                "movk x17, #0xdead, lsl #16",
                "add x16, x16, x17",
                "mov x17, #0xbeef",
                "movk x17, #0xdead, lsl #16",
                "sub x16, x16, x17",
            ],
        );
    }

    #[test]
    fn test_add_sub_byte() {
        let mut v: Vec<u8> = Vec::new();
        Arm64Inter::add_byte(&mut v, Arm64Register::X19, i8::from_le_bytes([0xa5]));
        Arm64Inter::sub_byte(&mut v, Arm64Register::X19, i8::from_le_bytes([0xa5]));
        assert_eq!(
            disassembler().disassemble(v),
            [
                "ldrb w17, [x19], #0x0",
                "add x17, x17, #0xa5",
                "strb w17, [x19], #0x0",
                "ldrb w17, [x19], #0x0",
                "sub x17, x17, #0xa5",
                "strb w17, [x19], #0x0",
            ],
        );
    }

    #[test]
    fn test_zero_byte() {
        let mut v: Vec<u8> = Vec::new();
        Arm64Inter::zero_byte(&mut v, Arm64Register::X19);
        assert_eq!(
            disassembler().disassemble(v),
            ["mov x17, #0x0", "strb w17, [x19], #0x0"]
        );
    }

    #[test]
    fn test_aux_reg() {
        let aux_regs: Vec<_> = [
            Arm64Register::X0,
            Arm64Register::X1,
            Arm64Register::X2,
            Arm64Register::X8,
            Arm64Register::X16,
            Arm64Register::X17,
            Arm64Register::X19,
        ]
        .into_iter()
        .map(aux_reg)
        .collect();
        let mut expected = vec![Arm64Register::X17; 7];
        expected[5] = Arm64Register::X16;
        assert_eq!(expected, aux_regs);
    }

    #[test]
    fn test_inc_dec_wrapper() {
        let mut v: Vec<u8> = Vec::with_capacity(24);
        Arm64Inter::inc_byte(&mut v, Arm64Register::X1);
        Arm64Inter::dec_byte(&mut v, Arm64Register::X17);
        assert_eq!(
            disassembler().disassemble(v),
            [
                "ldrb w17, [x1], #0x0",
                "add x17, x17, #0x1",
                "strb w17, [x1], #0x0",
                "ldrb w16, [x17], #0x0",
                "sub x16, x16, #0x1",
                "strb w16, [x17], #0x0",
            ]
        );
    }

    #[test]
    fn test_reg_copy() {
        let mut v: Vec<u8> = Vec::with_capacity(12);
        Arm64Inter::reg_copy(&mut v, Arm64Register::X1, Arm64Register::X19);
        Arm64Inter::reg_copy(&mut v, Arm64Register::X2, Arm64Register::X17);
        Arm64Inter::reg_copy(&mut v, Arm64Register::X8, Arm64Register::X16);
        assert_eq!(
            disassembler().disassemble(v),
            ["mov x1, x19", "mov x2, x17", "mov x8, x16"]
        );
    }

    #[test]
    fn test_syscall() {
        let mut v: Vec<u8> = Vec::with_capacity(4);
        Arm64Inter::syscall(&mut v);
        assert_eq!(disassembler().disassemble(v), ["svc #0"]);
    }

    #[test]
    fn test_nops() {
        let mut v = Vec::with_capacity(12);
        Arm64Inter::nop_loop_open(&mut v);
        assert_eq!(disassembler().disassemble(v), ["nop", "nop", "nop"]);
    }

    #[test]
    #[should_panic(expected = "offset 31 is invalid for architecture (offset % 4 != 0)")]
    fn invalid_offset_panics() {
        Arm64Inter::jump_open(&mut [0; 12], 0, Arm64Register::X0, 31).unwrap();
    }

    #[test]
    fn out_of_bounds_jumps_test() {
        assert!(
            Arm64Inter::jump_open(&mut [0; 12], 0, Arm64Register::X0, i64::MAX ^ 0b11)
                .is_err_and(|e| e.kind == BFErrorID::JumpTooLong)
        );
    }

    #[test]
    fn successfull_jumps_test() {
        let mut v = vec![0; 12];
        Arm64Inter::jump_open(&mut v, 0, Arm64Register::X0, 32).unwrap();
        Arm64Inter::jump_close(&mut v, Arm64Register::X0, -32).unwrap();
        assert_eq!(
            disassembler().disassemble(v),
            [
                "ldrb w17, [x0], #0x0",
                "tst x17, #0xff",
                "b.eq #0x24",
                "ldrb w17, [x0], #0x0",
                "tst x17, #0xff",
                "b.ne #-0x1c",
            ]
        );
    }
}
