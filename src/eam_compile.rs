// SPDX-FileCopyrightText: 2024 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only
use super::elf_tools::{serialize_ehdr64_le, serialize_phdr64_le, Elf64_Ehdr, Elf64_Phdr};
use super::err::BFCompileError;
use super::instr_encoders::registers::*;
use super::instr_encoders::syscall_nums::*;
use super::instr_encoders::*;
use std::io::{BufReader, Read, Write};

struct Position {
    line: usize,
    col: usize,
}

// number of 4-KiB blocks to allocate for the tape
const TAPE_BLOCKS: u64 = 8;

// ELF addressing stuff
const EHDR_SIZE: u16 = 64u16;
const PHDR_SIZE: u16 = 56u16;
const PHTB_SIZE: u64 = (PHDR_SIZE * PHNUM) as u64;
const TAPE_ADDR: u64 = 0x10000;
const PHNUM: u16 = 2;
const TAPE_SIZE: u64 = TAPE_BLOCKS * 0x1000;
const LOAD_VADDR: u64 = ((TAPE_ADDR + TAPE_SIZE) & (!0xffffu64)) + 0x10000u64;
const START_PADDR: u64 = ((EHDR_SIZE as u64 + PHTB_SIZE) & (!0xffu64)) + 0x100u64;
const START_VADDR: u64 = START_PADDR + LOAD_VADDR;

fn write_headers<W: Write>(output: &mut W, codesize: usize) -> Result<(), BFCompileError> {
    let e_ident_vals: [u8; 16] = [
        // first 4 bytes are the magic values pre-defined and used to mark this as an ELF file
        0x7fu8, b'E', b'L', b'F',
        // EI_CLASS = ELFCLASS64 (i.e. this is a 64-bit ELF file)
        2u8, // EI_DATA = ELFDATA2LSB (i.e. this is a LSB-ordered ELF file)
        1u8, // EI_VERSION = EV_CURRENT (the only valid option)
        1u8, // EI_OSABI = ELFOSABI_SYSV,
        0u8, // EI_ABIVERSION = 0 (ELFOSABI_SYSV doesn't define any ABI versions)
        0u8, // remaining bytes are for padding
        0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
    ];
    let ehdr = Elf64_Ehdr {
        e_ident: e_ident_vals,
        e_type: 2,     // ET_EXEC
        e_machine: 62, // the identifier for X86_64 machines
        e_version: 1,
        e_phnum: PHNUM,
        e_shnum: 0,
        e_phoff: EHDR_SIZE as u64,
        e_shoff: 0, // no section header table, must be 0
        e_ehsize: EHDR_SIZE,
        e_phentsize: PHDR_SIZE,
        e_shentsize: 0, // no section header table, must be 0
        e_shstrndx: 0,  // no section header table, must be 0
        e_entry: START_VADDR,
        e_flags: 0, // ISA-specific flags. None are defined for x86_64, so set to 0.
    };
    let phtb: [Elf64_Phdr; 2] = [
        Elf64_Phdr {
            p_type: 1,          // PT_LOAD ( loadable segment )
            p_flags: 2 | 4,     // PF_R | PF_W (readable and writable)
            p_offset: 0,        // load bytes from this index in the file
            p_vaddr: TAPE_ADDR, // load segment into this section of memory
            p_paddr: 0,         // load from this physical address
            p_filesz: 0,        // load this many bytes from file, then zero-initialize the rest
            p_memsz: TAPE_SIZE, // allocate this many bytes of memory for this segment
            p_align: 0x1000,    // align with this power of 2
        },
        Elf64_Phdr {
            p_type: 1,                               // PT_LOAD ( loadable segment )
            p_flags: 2 | 1,                          // PF_R | PF_X (readable and executable)
            p_offset: 0,                             // load bytes from this index in the file
            p_vaddr: LOAD_VADDR,                     // load segment into this section of memory
            p_paddr: 0,                              // load from this physical address
            p_filesz: START_PADDR + codesize as u64, // load this many bytes from file…
            p_memsz: START_PADDR + codesize as u64,  // allocate this many bytes of memory…
            p_align: 1,                              // align with this power of 2
        },
    ];
    let mut to_write = Vec::<u8>::new();
    serialize_ehdr64_le(ehdr, &mut to_write);
    serialize_phdr64_le(phtb[0], &mut to_write);
    serialize_phdr64_le(phtb[1], &mut to_write);
    match output.write(to_write.as_slice()) {
        Ok(_) => Ok(()),
        Err(_) => Err(BFCompileError::Basic {
            id: String::from("FAILED_WRITE"),
            msg: String::from("Failed to write ELF header and program header table"),
        }),
    }
}

#[inline]
// The brainfuck instructions "." and "," are similar from an implementation
// perspective. Both require making system calls for I/O, and the system calls
// have 3 nearly identical arguments:
//  - arg1 is the file descriptor
//  - arg2 is the memory address of the data source (write)/dest (read)
//  - arg3 is the number of bytes to write/read
//
// Due to their similarity, ',' and '.' are both implemented with bf_io./
fn bf_io(sc: i64, fd: i32) -> Vec<u8> {
    // To start, move the system call number into the system call register, then, move the file
    // descriptor into the arg1 register, and copy the destination address into the arg2 register,
    // and the number of bytes to read/write to the arg3 register. Finally, end with the syscall
    // instruction.
    let mut instr_bytes = bfc_set_reg(REG_SC_NUM, sc.into());
    instr_bytes.extend(bfc_set_reg(REG_ARG1, fd.into()));
    instr_bytes.extend(bfc_reg_copy(REG_ARG2, REG_BF_PTR));
    instr_bytes.extend(bfc_set_reg(REG_ARG3, 1));
    instr_bytes.extend(bfc_syscall());
    instr_bytes
}

#[allow(unused_variables)]
fn compile_instr<W: Write>(
    instr: u8,
    dst: &mut W,
    pos: &mut Position,
    jump_stack: &mut Vec<usize>,
) -> Result<usize, BFCompileError> {
    pos.col += 1;
    let mut result: Result<usize, std::io::Error> = Ok(0_usize);
    match instr {
        // decrement the tape pointer register
        b'<' => result = dst.write(bfc_dec_reg(REG_BF_PTR).as_slice()),
        // increment the tape pointer register
        b'>' => result = dst.write(bfc_inc_reg(REG_BF_PTR).as_slice()),
        // decrement the current cell value
        b'-' => result = dst.write(bfc_dec_byte(REG_BF_PTR).as_slice()),
        // increment the current cell value
        b'+' => result = dst.write(bfc_inc_byte(REG_BF_PTR).as_slice()),
        // Write 1 byte at REG_BF_PTR to STDOUT
        b'.' => result = dst.write(bf_io(SC_WRITE, 1).as_slice()),
        // Read 1 byte to REG_BF_PTR from STDIN
        b',' => result = dst.write(bf_io(SC_READ, 0).as_slice()),
        b'[' | b']' => {
            return Err(BFCompileError::Position {
                id: String::from("UNIMPLEMENTED"),
                msg: String::from("`[` and `]` are not yet implemented in eambfc-rs"),
                instr: instr.into(),
                col: pos.col,
                line: pos.line,
            })
        }
        b'\n' => {
            pos.col = 1;
            pos.line += 1;
        }
        _ => {}
    };
    match result {
        Err(_) => Err(BFCompileError::Position {
            id: String::from("FAILED_WRITE"),
            msg: String::from(""),
            instr: instr.into(),
            col: pos.col,
            line: pos.line,
        }),
        Ok(size) => Ok(size),
    }
}

pub fn bf_compile<W: Write, R: Read>(
    in_f: R,
    mut out_f: W,
    optimize: bool,
) -> Result<(), BFCompileError> {
    let mut jump_stack = Vec::<usize>::new();
    let mut pos = Position { line: 1, col: 0 };
    if optimize {
        return Err(BFCompileError::Basic {
            id: String::from("UNIMPLEMENTED"),
            msg: String::from("Optimization not implemented"),
        });
    }
    let mut code_buf = Vec::<u8>::new();
    let codesize: usize = Result::<Vec<usize>, BFCompileError>::from_iter(
        BufReader::new(in_f).bytes().map(|maybe_byte| {
            let byte = maybe_byte.map_err(|_| BFCompileError::Position {
                id: String::from("FAILED_READ"),
                msg: String::from("Failed to read byte after current position"),
                line: pos.line,
                col: pos.col,
                instr: '\0',
            })?;
            compile_instr(byte, &mut code_buf, &mut pos, &mut jump_stack)
        }),
    )?
    .into_iter()
    .sum();
    write_headers(&mut out_f, codesize)?;
    match out_f.write(code_buf.as_slice()) {
        Ok(_) => Ok(()),
        Err(_) => Err(BFCompileError::Basic {
            id: String::from("FAILED_WRITE"),
            msg: String::from(""),
        }),
    }
}
