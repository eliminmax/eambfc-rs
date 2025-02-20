// SPDX-FileCopyrightText: 2024 - 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use crate::compile::elf_tools::{ByteOrdering, ElfArch};
use crate::err::BFCompileError;

pub(super) type FailableInstrEncoding = Result<(), BFCompileError>;

/// A trait for interfaces to given target architecture - can be implemented for Zero-sized types
/// to allow them to be used as backends.
///
/// Used to implement `eambfc_rs::compile::BFCompiler`
pub(super) trait ArchInter {
    /// The type used to represent this architecture's registers
    type RegType: Copy;
    /// The size of the jump instruction (including any preceding "test", "cmp", etc) for this
    /// architecture
    const JUMP_SIZE: usize;
    /// A struct which defines the registers used for specific purposes - namely the system call
    /// number register and the first three arguments in the Linux system call interface, and one
    /// non-clobbered register to use as the brainfuck tape pointer
    const REGISTERS: Registers<Self::RegType>;
    /// The syscall numbers of the read, write, and exit Linux system calls for this architecture
    const SC_NUMS: SyscallNums;
    /// The `ElfArch` value for this architecture
    const ARCH: ElfArch;
    /// The cpu flags needed in the `E_FLAGS` field of the ELF header for this architecture
    const E_FLAGS: u32;
    /// the byte ordering for this architecture
    const EI_DATA: ByteOrdering;
    /// append code to `code_buf` that sets `reg` to `imm`
    fn set_reg(code_buf: &mut Vec<u8>, reg: Self::RegType, imm: i64);
    /// append code to `code_buf` that copies the value in `src` to `dst`
    fn reg_copy(code_buf: &mut Vec<u8>, dst: Self::RegType, src: Self::RegType);
    /// append machine code for the system call instruction to `code_buf`
    fn syscall(code_buf: &mut Vec<u8>);
    /// overwrite `code_buf[index..index + Self::JUMP_SIZE]` with machine code to test if the byte
    /// pointed to by `reg` is zero, and jump `offset` bytes away if so
    ///
    /// Should return an error if `offset` is too large of a jump for this architecture
    fn jump_open(
        code_buf: &mut [u8],
        index: usize,
        reg: Self::RegType,
        offset: i64,
    ) -> FailableInstrEncoding;
    /// append machine code to `code_buf` to test if the byte pointed to by `reg` is zero, and jump
    /// `offset` bytes away if not
    ///
    ///
    /// Should return an error if `offset` is too large of a jump for this architecture
    fn jump_close(code_buf: &mut Vec<u8>, reg: Self::RegType, offset: i64)
    -> FailableInstrEncoding;
    /// append non-op instructions `code_buf` as padding bytes to to make room for `jump_open`
    /// instruction once `offset` is known. Must extend it by `Self::JUMP_SIZE` bytes.
    fn nop_loop_open(code_buf: &mut Vec<u8>);
    /// append machine code to `code_buf` to increment the value in `reg` by 1
    fn inc_reg(code_buf: &mut Vec<u8>, reg: Self::RegType);
    /// append machine code to `code_buf` to increment the byte pointed to by `reg` by 1
    fn inc_byte(code_buf: &mut Vec<u8>, reg: Self::RegType);
    /// append machine code to `code_buf` to decrement the value in `reg` by 1
    fn dec_reg(code_buf: &mut Vec<u8>, reg: Self::RegType);
    /// append machine code to `code_buf` to decrement the byte pointed to by `reg` by 1
    fn dec_byte(code_buf: &mut Vec<u8>, reg: Self::RegType);
    /// append machine code to `code_buf` to add `imm` to the value in `reg`
    fn add_reg(code_buf: &mut Vec<u8>, reg: Self::RegType, imm: u64);
    /// append machine code to `code_buf` to add `imm` to the byte pointed to by `reg`
    fn add_byte(code_buf: &mut Vec<u8>, reg: Self::RegType, imm: u8);
    /// append machine code to `code_buf` to subtract `imm` from the value in `reg`
    fn sub_reg(code_buf: &mut Vec<u8>, reg: Self::RegType, imm: u64);
    /// append machine code to `code_buf` to subtract `imm` from the byte pointed to by `reg`
    fn sub_byte(code_buf: &mut Vec<u8>, reg: Self::RegType, imm: u8);
    /// append machine code to `code_buf` to set the byte pointed to by `reg` to `0`
    fn zero_byte(code_buf: &mut Vec<u8>, reg: Self::RegType);
}

/// The registers needed when encoding the machine code
pub(super) struct Registers<R: Copy> {
    /// The register that the Linux kernel checks for the system call number
    pub sc_num: R,
    /// The register that the Linux kernel checks for the 1st syscall argument
    pub arg1: R,
    /// The register that the Linux kernel checks for the 2nd syscall argument
    pub arg2: R,
    /// The register that the Linux kernel checks for the 3rd syscall argument
    pub arg3: R,
    /// A non-clobbered register that can safely be used as the brainfuck tape pointer
    pub bf_ptr: R,
}

/// The numbers used by the Linux kernel system-call interface for the system calls needed to
/// implement `BFCompile`
pub(super) struct SyscallNums {
    pub read: i64,
    pub write: i64,
    pub exit: i64,
}
