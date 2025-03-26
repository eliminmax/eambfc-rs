// SPDX-FileCopyrightText: 2024 - 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use crate::err::{BFCompileError, BFErrorID};

use super::arch_inter::{ArchInter, FailableInstrEncoding, Registers, SyscallNums};
use super::elf_tools::{ByteOrdering, ElfArch};
use super::MinimumBits;

// 64-bit ARM systems have 31 general-purpose registers which can be addressed in 32-bit or 64-bit
// forms. w8 is the 32-bit form for register #8, and x0 is the 64-bit form for register #0.
// X19 is the first register that the ABI guarantees to be preserved across function calls, and the
// rest are used by the Linux system call interface for the platform.
// Other registers are not defined because they are not needed for eambfc-rs, but they go up to 31.
// 32 is a special case that is either a zero register or the stack pointer, depending on the
// instruction

#[derive(Debug, Clone, Copy, PartialEq)]
#[repr(u8)]
pub(in super::super) enum Arm64Register {
    X0 = 0,   // arg1 register
    X1 = 1,   // arg2 register
    X2 = 2,   // arg3 register
    X8 = 8,   // syscall register
    X19 = 19, // bf pointer register
}

/// Internal type representing a raw register identifier.
#[derive(PartialEq, Copy, Clone)]
struct RawReg(u8);

impl From<Arm64Register> for RawReg {
    fn from(value: Arm64Register) -> Self {
        RawReg(value as u8)
    }
}

/// Private scratch register used within certain operations
const TEMP_REG: RawReg = RawReg(17);

#[derive(Clone, Copy, PartialEq)]
#[repr(u8)]
enum ShiftLevel {
    NoShift = 0b00,
    Shift16 = 0b01,
    Shift32 = 0b10,
    Shift48 = 0b11,
}

#[derive(PartialEq)]
#[repr(u8)]
enum MoveType {
    Keep = 0b11,
    Zero = 0b10,
    Invert = 0b00,
}

fn mov(move_type: MoveType, imm16: u16, shift: ShiftLevel, RawReg(reg): RawReg) -> [u8; 4] {
    // depending on MoveType, it will be one of MOVK, MOVN, or MOVZ
    // bitwise not to invert imm16 if needed.
    let imm16 = if move_type == MoveType::Invert {
        !imm16
    } else {
        imm16
    };
    u32::to_le_bytes(
        0x9280_0000
            | ((move_type as u32) << 29)
            | ((shift as u32) << 21)
            | (u32::from(imm16) << 5)
            | u32::from(reg),
    )
}

fn load_from_byte(addr: Arm64Register) -> [u8; 4] {
    // LDRB w17, addr
    u32::to_le_bytes(0x3840_0411 | ((addr as u32) << 5))
}

fn store_to_byte(addr: Arm64Register) -> [u8; 4] {
    // STRB w17, addr
    u32::to_le_bytes(0x3800_0411 | ((addr as u32) << 5))
}

#[derive(PartialEq, Copy, Clone)]
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
    if !offset.fits_within_bits(21) {
        return Err(BFCompileError::basic(
            BFErrorID::JumpTooLong,
            format!("{offset} is outside the range of possible 21-bit signed values"),
        ));
    }
    let offset = (1 + ((offset as u32) >> 2)) & 0x7ffff;
    let mut code_buf = [0; 12];
    code_buf[..4].clone_from_slice(&load_from_byte(reg));

    // TST reg, 0xff (technically an alias for ANDS xzr, reg, 0xff)
    code_buf[4..8].clone_from_slice(&u32::to_le_bytes(0xf240_1e3f));
    // B.cond {offset}
    code_buf[8..].clone_from_slice(&u32::to_le_bytes(
        0x5400_0000 | (cond as u32) | (offset << 5),
    ));
    Ok(code_buf)
}

fn set_raw_reg(code_buf: &mut Vec<u8>, reg: RawReg, imm: i64) {
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
        set_raw_reg(code_buf, reg.into(), imm);
    }

    fn reg_copy(code_buf: &mut Vec<u8>, dst: Arm64Register, src: Arm64Register) {
        // MOV dst, src
        // technically an alias for ORR dst, XZR, src (XZR is a read-only zero register)
        code_buf.extend(u32::to_le_bytes(
            0xaa00_03e0 | (dst as u32) | ((src as u32) << 16),
        ));
    }

    fn syscall(code_buf: &mut Vec<u8>) {
        // SVC 0
        code_buf.extend(const { u32::to_le_bytes(0xd400_0001) });
    }

    fn pad_loop_open(code_buf: &mut Vec<u8>) {
        // BRK 1; NOP; NOP
        const INSTR_SEQUENCE: [[u8; 4]; 3] = [
            u32::to_le_bytes(0xd420_0020),
            u32::to_le_bytes(0xd503_201f),
            u32::to_le_bytes(0xd503_201f),
        ];
        code_buf.extend(INSTR_SEQUENCE.into_iter().flatten());
    }

    fn inc_reg(code_buf: &mut Vec<u8>, reg: Arm64Register) {
        // ADD reg, reg, 1
        code_buf.extend(u32::to_le_bytes(
            0x9100_0400 | ((reg as u32) << 5) | (reg as u32),
        ));
    }

    fn dec_reg(code_buf: &mut Vec<u8>, reg: Arm64Register) {
        // SUB reg, reg, 1
        code_buf.extend(u32::to_le_bytes(
            0xd100_0400 | ((reg as u32) << 5) | (reg as u32),
        ));
    }

    fn add_reg(code_buf: &mut Vec<u8>, reg: Arm64Register, imm: u64) {
        add_sub(code_buf, reg, imm, ArithOp::Add);
    }

    fn sub_reg(code_buf: &mut Vec<u8>, reg: Arm64Register, imm: u64) {
        add_sub(code_buf, reg, imm, ArithOp::Sub);
    }

    fn zero_byte(code_buf: &mut Vec<u8>, reg: Arm64Register) {
        code_buf.extend(u32::to_le_bytes(0x3800_041f | ((reg as u32) << 5)));
    }

    fn add_byte(code_buf: &mut Vec<u8>, reg: Arm64Register, imm: u8) {
        code_buf.extend(load_from_byte(reg));
        add_sub_imm(code_buf, TEMP_REG, u64::from(imm), ArithOp::Add, false);
        code_buf.extend(store_to_byte(reg));
    }

    fn sub_byte(code_buf: &mut Vec<u8>, reg: Arm64Register, imm: u8) {
        code_buf.extend(load_from_byte(reg));
        add_sub_imm(code_buf, TEMP_REG, u64::from(imm), ArithOp::Sub, false);
        code_buf.extend(store_to_byte(reg));
    }

    fn inc_byte(code_buf: &mut Vec<u8>, reg: Arm64Register) {
        code_buf.extend(load_from_byte(reg));
        // add x17, x17, 1
        code_buf.extend(u32::to_le_bytes(0x9100_0631));
        code_buf.extend(store_to_byte(reg));
    }

    fn dec_byte(code_buf: &mut Vec<u8>, reg: Arm64Register) {
        code_buf.extend(load_from_byte(reg));
        // sub x17, x17, 1
        code_buf.extend(u32::to_le_bytes(0xd100_0631));
        code_buf.extend(store_to_byte(reg));
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
        code_buf[index..index + Self::JUMP_SIZE].clone_from_slice(&branch_cond(
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

fn add_sub_imm(code_buf: &mut Vec<u8>, RawReg(reg): RawReg, imm: u64, op: ArithOp, shift: bool) {
    assert!(
        (shift && (imm & !0xfff_000) == 0) || (!shift && (imm & !0xfff) == 0),
        "{imm} is invalid for shift level"
    );
    let aligned_imm = if shift { imm >> 2 } else { imm << 10 } as u32;
    // either ADD reg, reg, imm or SUB reg, reg, imm, depending on op
    code_buf.extend(u32::to_le_bytes(
        ((op as u32) << 24)
            | if shift { 1 << 22 } else { 0 }
            | aligned_imm
            | (u32::from(reg) << 5)
            | u32::from(reg),
    ));
}

fn add_sub(code_buf: &mut Vec<u8>, reg: Arm64Register, imm: u64, op: ArithOp) {
    match imm {
        i if i < 0x1_000 => add_sub_imm(code_buf, reg.into(), imm, op, false),
        i if i < 0x1_000_000 => {
            add_sub_imm(code_buf, reg.into(), imm & 0xfff_000, op, true);
            if i & 0xfff != 0 {
                add_sub_imm(code_buf, reg.into(), imm & 0xfff, op, false);
            }
        }
        i => {
            set_raw_reg(code_buf, TEMP_REG, i as i64);
            // either ADD reg, reg, x17 or SUB reg, reg, x17
            code_buf.extend(u32::to_le_bytes(
                0x8b11_0000
                    | if op == ArithOp::Sub { 1 << 30 } else { 0 }
                    | ((reg as u32) << 5)
                    | (reg as u32),
            ));
        }
    }
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "disasmtests")]
    use super::super::test_utils::Disassembler;
    use super::*;
    use test_macros::disasm_test;

    #[cfg(feature = "disasmtests")]
    fn disassembler() -> Disassembler {
        Disassembler::new(ElfArch::Arm64)
    }

    #[disasm_test]
    fn test_set_reg_simple() {
        let mut ds = disassembler();
        // the following can be set with 1 instruction each.
        let mut v: Vec<u8> = Vec::with_capacity(4);
        Arm64Inter::set_reg(&mut v, Arm64Register::X0, 0);
        assert_eq!(ds.disassemble(v), ["mov x0, #0x0"]);

        let mut v: Vec<u8> = Vec::with_capacity(4);
        Arm64Inter::set_reg(&mut v, Arm64Register::X0, -1);
        assert_eq!(ds.disassemble(v), ["mov x0, #-0x1"]);

        let mut v: Vec<u8> = Vec::with_capacity(4);
        Arm64Inter::set_reg(&mut v, Arm64Register::X0, -0x100_001);
        assert_eq!(ds.disassemble(v), ["mov x0, #-0x100001"]);

        let mut v: Vec<u8> = Vec::with_capacity(4);
        Arm64Inter::set_reg(&mut v, Arm64Register::X1, 0xbeef);
        assert_eq!(ds.disassemble(v), ["mov x1, #0xbeef"]);
    }

    #[test]
    #[should_panic = "32 is invalid for shift level"]
    fn test_add_sub_imm_guard() {
        add_sub_imm(&mut vec![], RawReg(8), 32, ArithOp::Add, true);
    }

    #[disasm_test]
    fn test_reg_multiple() {
        let mut v: Vec<u8> = Vec::with_capacity(8);
        #[allow(clippy::unreadable_literal, reason = "deadbeef is famously readable")]
        Arm64Inter::set_reg(&mut v, Arm64Register::X0, 0xdeadbeef);
        assert_eq!(
            disassembler().disassemble(v),
            ["mov x0, #0xbeef", "movk x0, #0xdead, lsl #16"],
        );
    }

    #[disasm_test]
    fn test_reg_split() {
        let mut v: Vec<u8> = Vec::with_capacity(8);
        Arm64Inter::set_reg(&mut v, Arm64Register::X19, 0xdead_0000_beef);
        assert_eq!(
            disassembler().disassemble(v),
            ["mov x19, #0xbeef", "movk x19, #0xdead, lsl #32"],
        );
    }

    #[disasm_test]
    fn test_reg_neg() {
        let mut v: Vec<u8> = Vec::with_capacity(8);
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

    #[disasm_test]
    fn test_reg_split_neg() {
        let mut v: Vec<u8> = Vec::with_capacity(8);
        Arm64Inter::set_reg(&mut v, Arm64Register::X19, -0xdead_0000_beef);
        assert_eq!(
            disassembler().disassemble(v),
            [
                "mov x19, #-0xbeef",
                // the bitwise negation of 0xdead is 0x2152
                "movk x19, #0x2152, lsl #32",
            ]
        );
        let mut v: Vec<u8> = Vec::with_capacity(12);
        Arm64Inter::set_reg(&mut v, Arm64Register::X8, -0xdead_beef_0000);
        assert_eq!(
            disassembler().disassemble(v),
            [
                "mov x8, #-0x10000",
                // the bitwise negation of 0xbeef is 0x4110
                // (Add 1 because that's how 2's complement works)
                "movk x8, #0x4111, lsl #16",
                // the bitwise negation of 0xdead is 0x2152
                "movk x8, #0x2152, lsl #32",
            ],
        );
    }

    #[disasm_test]
    fn test_inc_dec_reg() {
        let mut ds = disassembler();
        let mut v: Vec<u8> = Vec::with_capacity(4);
        Arm64Inter::inc_reg(&mut v, Arm64Register::X0);
        assert_eq!(ds.disassemble(v), ["add x0, x0, #0x1"]);

        let mut v: Vec<u8> = Vec::with_capacity(4);
        Arm64Inter::inc_reg(&mut v, Arm64Register::X19);
        assert_eq!(ds.disassemble(v), ["add x19, x19, #0x1"]);

        let mut v: Vec<u8> = Vec::with_capacity(4);
        Arm64Inter::dec_reg(&mut v, Arm64Register::X1);
        assert_eq!(ds.disassemble(v), ["sub x1, x1, #0x1"]);

        let mut v: Vec<u8> = Vec::with_capacity(4);
        Arm64Inter::dec_reg(&mut v, Arm64Register::X19);
        assert_eq!(ds.disassemble(v), ["sub x19, x19, #0x1"]);
    }

    #[disasm_test]
    fn test_load_store() {
        let mut ds = disassembler();
        assert_eq!(
            ds.disassemble(load_from_byte(Arm64Register::X19).into()),
            ["ldrb w17, [x19], #0x0"],
        );

        assert_eq!(
            ds.disassemble(store_to_byte(Arm64Register::X19).into()),
            ["strb w17, [x19], #0x0"],
        );
    }

    #[disasm_test]
    fn test_add_sub_reg() {
        let mut ds = disassembler();

        // Handling of 24-bit values
        let mut v: Vec<u8> = Vec::with_capacity(8);
        add_sub(&mut v, Arm64Register::X8, 0xabc_def, ArithOp::Add);
        assert_eq!(
            ds.disassemble(v),
            ["add x8, x8, #0xabc, lsl #12", "add x8, x8, #0xdef"]
        );

        // Ensure that if it fits within 24 bits and the lowest 12 are 0, no ADD or SUB 0 is
        // included
        let mut v: Vec<u8> = Vec::with_capacity(4);
        add_sub(&mut v, Arm64Register::X8, 0xabc_000, ArithOp::Sub);
        assert_eq!(ds.disassemble(v), ["sub x8, x8, #0xabc, lsl #12"]);

        let mut v: Vec<u8> = Vec::with_capacity(24);
        #[allow(clippy::unreadable_literal, reason = "deadbeef is famously readable")]
        Arm64Inter::add_reg(&mut v, Arm64Register::X8, 0xdeadbeef);
        #[allow(clippy::unreadable_literal, reason = "deadbeef is famously readable")]
        Arm64Inter::sub_reg(&mut v, Arm64Register::X8, 0xdeadbeef);
        assert_eq!(
            ds.disassemble(v),
            [
                "mov x17, #0xbeef",
                "movk x17, #0xdead, lsl #16",
                "add x8, x8, x17",
                "mov x17, #0xbeef",
                "movk x17, #0xdead, lsl #16",
                "sub x8, x8, x17",
            ],
        );
    }

    #[disasm_test]
    fn test_add_sub_byte() {
        let mut v: Vec<u8> = Vec::with_capacity(24);
        Arm64Inter::add_byte(&mut v, Arm64Register::X19, 0xa5);
        Arm64Inter::sub_byte(&mut v, Arm64Register::X19, 0xa5);
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

    #[disasm_test]
    fn test_zero_byte() {
        let mut v: Vec<u8> = Vec::with_capacity(4);
        Arm64Inter::zero_byte(&mut v, Arm64Register::X19);
        assert_eq!(disassembler().disassemble(v), ["strb wzr, [x19], #0x0"]);
    }

    #[disasm_test]
    fn test_inc_dec_wrapper() {
        let mut v: Vec<u8> = Vec::with_capacity(24);
        Arm64Inter::inc_byte(&mut v, Arm64Register::X1);
        Arm64Inter::dec_byte(&mut v, Arm64Register::X8);
        assert_eq!(
            disassembler().disassemble(v),
            [
                "ldrb w17, [x1], #0x0",
                "add x17, x17, #0x1",
                "strb w17, [x1], #0x0",
                "ldrb w17, [x8], #0x0",
                "sub x17, x17, #0x1",
                "strb w17, [x8], #0x0",
            ]
        );
    }

    #[disasm_test]
    fn test_reg_copy() {
        let mut v: Vec<u8> = Vec::with_capacity(12);
        Arm64Inter::reg_copy(&mut v, Arm64Register::X1, Arm64Register::X19);
        Arm64Inter::reg_copy(&mut v, Arm64Register::X2, Arm64Register::X0);
        Arm64Inter::reg_copy(&mut v, Arm64Register::X8, Arm64Register::X8);
        assert_eq!(
            disassembler().disassemble(v),
            ["mov x1, x19", "mov x2, x0", "mov x8, x8"]
        );
    }

    #[disasm_test]
    fn test_syscall() {
        let mut v: Vec<u8> = Vec::with_capacity(4);
        Arm64Inter::syscall(&mut v);
        assert_eq!(disassembler().disassemble(v), ["svc #0"]);
    }

    #[disasm_test]
    fn test_jump_pad() {
        let mut v = Vec::with_capacity(12);
        Arm64Inter::pad_loop_open(&mut v);
        assert_eq!(disassembler().disassemble(v), ["brk #0x1", "nop", "nop"]);
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
                .is_err_and(|e| e.error_id() == BFErrorID::JumpTooLong)
        );
    }

    #[disasm_test]
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
