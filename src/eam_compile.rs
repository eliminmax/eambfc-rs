// SPDX-FileCopyrightText: 2024 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only
use super::elf_tools::{Ehdr, Phdr};
use super::err::BFCompileError;
use super::instr_encoders::arch_info::*;
use super::instr_encoders::registers::*;
use super::instr_encoders::syscall_nums::*;
use super::instr_encoders::*;
use super::optimize::{to_condensed, CondensedInstruction};
use std::io::{BufReader, Read, Write};

struct Position {
    line: usize,
    col: usize,
}

// ELF addressing stuff
const EHDR_SIZE: u16 = 64u16;
const PHDR_SIZE: u16 = 56u16;
const PHTB_SIZE: u64 = (PHDR_SIZE * PHNUM) as u64;
const TAPE_ADDR: u64 = 0x10000;
const PHNUM: u16 = 2;

fn write_headers<W: Write>(
    output: &mut W,
    codesize: usize,
    tape_blocks: u64,
) -> Result<(), BFCompileError> {
    // more ELF addressing stuff - depends on tape_blocks, so can't be const
    let tape_size: u64 = tape_blocks * 0x1000;
    let load_vaddr: u64 = ((TAPE_ADDR + tape_size) & (!0xffffu64)) + 0x10000u64;
    let start_paddr: u64 = ((EHDR_SIZE as u64 + PHTB_SIZE) & (!0xffu64)) + 0x100u64;
    let start_vaddr: u64 = start_paddr + load_vaddr;

    let e_ident_vals: [u8; 16] = [
        // first 4 bytes are the magic values pre-defined and used to mark this as an ELF file
        0x7fu8,
        b'E',
        b'L',
        b'F',
        2u8, // EI_CLASS = ELFCLASS64 (i.e. this is a 64-bit ELF file)
        ELFDATA_BYTE_ORDER,
        1u8, // EI_VERSION = EV_CURRENT (the only valid option)
        0u8, // EI_OSABI = ELFOSABI_SYSV,
        0u8, // EI_ABIVERSION = 0 (ELFOSABI_SYSV doesn't define any ABI versions)
        0u8, // remaining bytes are for padding
        0u8,
        0u8,
        0u8,
        0u8,
        0u8,
        0u8,
    ];
    let ehdr = Ehdr {
        e_ident: e_ident_vals,
        e_type: 2, // ET_EXEC
        e_machine: EM_ARCH,
        e_version: 1, // The only valid version number
        e_phnum: PHNUM,
        e_shnum: 0,
        e_phoff: EHDR_SIZE as u64,
        e_shoff: 0, // no section header table, must be 0
        e_ehsize: EHDR_SIZE,
        e_phentsize: PHDR_SIZE,
        e_shentsize: 0, // no section header table, must be 0
        e_shstrndx: 0,  // no section header table, must be 0
        e_entry: start_vaddr,
        e_flags: 0, // ISA-specific flags. None are defined for x86_64, so set to 0.
    };
    let tape_segment = Phdr {
        p_type: 1,          // PT_LOAD ( loadable segment )
        p_flags: 4 | 2,     // PF_R | PF_W (readable and writable)
        p_offset: 0,        // load bytes from this index in the file
        p_vaddr: TAPE_ADDR, // load segment into this section of memory
        p_paddr: 0,         // load from this physical address
        p_filesz: 0,        // don't load anything from file, just zero-initialize it
        p_memsz: tape_size, // allocate this many bytes of memory for this segment
        p_align: 0x1000,    // align with this power of 2
    };
    let code_segment = Phdr {
        p_type: 1,                               // PT_LOAD ( loadable segment )
        p_flags: 4 | 1,                          // PF_R | PF_X (readable and executable)
        p_offset: 0,                             // load bytes from this index in the file
        p_vaddr: load_vaddr,                     // load segment into this section of memory
        p_paddr: 0,                              // load from this physical address
        p_filesz: start_paddr + codesize as u64, // load this many bytes from file…
        p_memsz: start_paddr + codesize as u64,  // allocate this many bytes of memory…
        p_align: 1,                              // align with this power of 2
    };
    let mut to_write = Vec::<u8>::from(ehdr);
    to_write.extend(Vec::<u8>::from(tape_segment).as_slice());
    to_write.extend(Vec::<u8>::from(code_segment).as_slice());

    // add padding bytes
    to_write.resize(start_paddr as usize, 0u8);
    match output.write(to_write.as_slice()) {
        Ok(count) if count == to_write.len() => Ok(()),
        Ok(count) => Err(BFCompileError::Basic {
            id: String::from("FAILED_WRITE"),
            msg: format!(
                "Expected to write {} bytes of ELF header and program header table, wrote {}",
                to_write.len(),
                count,
            ),
        }),
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
    let mut instr_bytes = bfc_set_reg(REG_SC_NUM, sc);
    instr_bytes.extend(bfc_set_reg(REG_ARG1, fd.into()));
    instr_bytes.extend(bfc_reg_copy(REG_ARG2, REG_BF_PTR));
    instr_bytes.extend(bfc_set_reg(REG_ARG3, 1));
    instr_bytes.extend(bfc_syscall());
    instr_bytes
}

struct JumpLocation {
    src_line: usize,
    src_col: usize,
    index: usize,
}

fn compile_condensed(
    condensed_instr: CondensedInstruction,
    dst: &mut Vec<u8>,
    jump_stack: &mut Vec<JumpLocation>,
) -> Result<(), BFCompileError> {
    let to_write: Vec<u8> = match condensed_instr {
        CondensedInstruction::SetZero => bfc_zero_mem(REG_BF_PTR),
        CondensedInstruction::RepeatAdd(count) => bfc_add_mem(REG_BF_PTR, count as i8),
        CondensedInstruction::RepeatSub(count) => bfc_sub_mem(REG_BF_PTR, count as i8),
        CondensedInstruction::RepeatMoveR(count) => bfc_add_reg(REG_BF_PTR, count)?,
        CondensedInstruction::RepeatMoveL(count) => bfc_sub_reg(REG_BF_PTR, count)?,
        CondensedInstruction::BFInstruction(i) => {
            return compile_instr(
                i,
                dst,
                // throwaway position value
                &mut Position { line: 0, col: 0 },
                jump_stack,
            );
        }
    };
    match dst.write(to_write.as_slice()) {
        Ok(count) if count == to_write.len() => Ok(()),
        Ok(count) => Err(BFCompileError::Basic {
            id: String::from("FAILED_WRITE"),
            msg: format!(
                "Expected to write {} bytes when compiling, wrote {}",
                to_write.len(),
                count
            ),
        }),
        Err(_) => Err(BFCompileError::Basic {
            id: String::from("FAILED_WRITE"),
            msg: String::from("Failed to write to buffer."),
        }),
    }
}

fn compile_instr(
    instr: u8,
    dst: &mut Vec<u8>,
    pos: &mut Position,
    jump_stack: &mut Vec<JumpLocation>,
) -> Result<(), BFCompileError> {
    pos.col += 1;
    let to_write: Vec<u8> = match instr {
        // decrement the tape pointer registebr
        b'<' => bfc_dec_reg(REG_BF_PTR),
        // increment the tape pointer register
        b'>' => bfc_inc_reg(REG_BF_PTR),
        // decrement the current cell value
        b'-' => bfc_dec_byte(REG_BF_PTR),
        // increment the current cell value
        b'+' => bfc_inc_byte(REG_BF_PTR),
        // Write 1 byte at [REG_BF_PTR] to STDOUT
        b'.' => bf_io(SC_WRITE, 1),
        // Read 1 byte to [REG_BF_PTR] from STDIN
        b',' => bf_io(SC_READ, 0),
        // for this, skip over JUMP_SIZE bytes, and push the location to jump_stack.
        // will compile when reaching the corresponding ']' instruction
        b'[' => {
            jump_stack.push(JumpLocation {
                src_line: pos.line,
                src_col: pos.col,
                index: dst.len(),
            });
            dst.extend([0xffu8; JUMP_SIZE]);
            return Ok(());
        }
        b']' => {
            // First, compile the skipped '[' instruction
            let open_location =
                jump_stack
                    .pop()
                    .ok_or::<BFCompileError>(BFCompileError::Position {
                        id: String::from("UNMATCHED_CLOSE"),
                        msg: String::from("Found ']' without matching '['."),
                        instr: b']',
                        col: pos.col,
                        line: pos.line,
                    })?;
            let open_address = open_location.index;
            let distance = dst.len() - open_address;
            // This gets messy. Jump length must be within the limit allowed by the architecture.
            // usize may be longer than 32 bits on 64-bit platforms.
            // need to cast to 32 bit signed integer, but if it's too big, throw a JUMP_TOO_LONG
            if distance > MAX_JUMP_DISTANCE {
                return Err(BFCompileError::Position {
                    id: String::from("JUMP_TOO_LONG"),
                    msg: String::from("Attempted a jump longer than the maximum length."),
                    instr: b'[',
                    col: open_location.src_col,
                    line: open_location.src_line,
                });
            }

            dst[open_address..open_address + JUMP_SIZE]
                .swap_with_slice(&mut bfc_jump_zero(REG_BF_PTR, distance as JumpDistance));
            // now, we know that distance fits within the 32-bit integer limit, so we can
            // simply cast without another check needed when compiling the `]` instruction itself
            bfc_jump_not_zero(REG_BF_PTR, -(distance as JumpDistance))
        }
        b'\n' => {
            pos.col = 1;
            pos.line += 1;
            return Ok(());
        }
        _ => {
            return Ok(());
        }
    };
    match dst.write(to_write.as_slice()) {
        Ok(count) if count == to_write.len() => Ok(()),
        Ok(count) => Err(BFCompileError::Position {
            id: String::from("FAILED_WRITE"),
            msg: format!(
                "Expected to write {} bytes when compiling, wrote {}",
                to_write.len(),
                count
            ),

            instr,
            col: pos.col,
            line: pos.line,
        }),
        Err(_) => Err(BFCompileError::Position {
            id: String::from("FAILED_WRITE"),
            msg: String::from("Failed to write to buffer."),
            instr,
            col: pos.col,
            line: pos.line,
        }),
    }
}

pub fn bf_compile<W: Write, R: Read>(
    in_f: R,
    mut out_f: W,
    optimize: bool,
    tape_blocks: u64,
) -> Result<(), Vec<BFCompileError>> {
    let mut jump_stack = Vec::<JumpLocation>::new();
    let mut pos = Position { line: 1, col: 0 };
    let mut code_buf = bfc_set_reg(REG_BF_PTR, TAPE_ADDR as i64);
    let mut errs = Vec::<BFCompileError>::new();

    let reader = BufReader::new(in_f);

    if optimize {
        errs.append(&mut match to_condensed(reader) {
            Ok(condensed) => condensed
                .into_iter()
                .filter_map(|i| {
                    if let Err(e) = compile_condensed(i, &mut code_buf, &mut jump_stack) {
                        Some(e)
                    } else {
                        None
                    }
                })
                .collect::<Vec<BFCompileError>>(),
            Err(e) => vec![e],
        });
    } else {
        reader.bytes().for_each(|maybe_byte| match maybe_byte {
            Ok(byte) => {
                if let Err(e) = compile_instr(byte, &mut code_buf, &mut pos, &mut jump_stack) {
                    errs.push(e);
                }
            }
            Err(_) => {
                errs.push(BFCompileError::Position {
                    id: String::from("FAILED_READ"),
                    msg: String::from("Failed to read byte after current position"),
                    line: pos.line,
                    col: pos.col,
                    instr: b'\0',
                });
            }
        });
    }

    // quick check to make sure that there are no unterminated loops
    if let Some(jl) = jump_stack.pop() {
        errs.push(BFCompileError::Position {
            id: String::from("UNMATCHED_OPEN"),
            msg: String::from("Reached the end of the file with an unmatched '['"),
            line: jl.src_line,
            col: jl.src_col,
            instr: b'[',
        });
    }
    // finally, after that mess, end with an exit(0)
    code_buf.extend(bfc_set_reg(REG_SC_NUM, SC_EXIT));
    code_buf.extend(bfc_set_reg(REG_ARG1, 0));
    code_buf.extend(bfc_syscall());

    let code_sz = code_buf.len();
    if let Err(e) = write_headers(&mut out_f, code_sz, tape_blocks) {
        errs.push(e);
    }
    match out_f.write(code_buf.as_slice()) {
        Ok(count) if count == code_sz => (),
        Ok(count) => errs.push(BFCompileError::Basic {
            id: String::from("FAILED_WRITE"),
            msg: format!("Only wrote {count} out of expected {code_sz} machine code bytes"),
        }),
        Err(_) => errs.push(BFCompileError::Basic {
            id: String::from("FAILED_WRITE"),
            msg: String::from("Failed to write internal code buffer to output file"),
        }),
    };
    if errs.is_empty() {
        Ok(())
    } else {
        Err(errs)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn compile_all_bf_instructions() -> Result<(), String> {
        bf_compile(b"+[>]<-,.".as_slice(), Vec::<u8>::new(), false, 8)
            .map_err(|e| format!("Failed to compile: {:?}", e))
    }

    #[test]
    fn compile_nested_loops() -> Result<(), String> {
        // An algorithm to set a cell to the number 33, contributed to esolangs.org in 2005 by
        // user Calamari. esolangs.org contents are available under a CC0-1.0 license.
        bf_compile(b">+[-->---[-<]>]>+".as_slice(), Vec::<u8>::new(), false, 8)
            .map_err(|e| format!("Failed to compile: {:?}", e))
    }

    #[test]
    fn unmatched_open() -> Result<(), String> {
        assert!(
            bf_compile(b"[".as_slice(), Vec::<u8>::new(), false, 8).is_err_and(|e| {
                match e.into_iter().next().unwrap() {
                    BFCompileError::Basic { id, .. }
                    | BFCompileError::Instruction { id, .. }
                    | BFCompileError::Position { id, .. } => id == String::from("UNMATCHED_OPEN"),
                    BFCompileError::UnknownFlag(_) => false,
                }
            })
        );
        Ok(())
    }

    #[test]
    fn unmatched_close() -> Result<(), String> {
        assert!(
            bf_compile(b"]".as_slice(), Vec::<u8>::new(), false, 8).is_err_and(|e| {
                match e.into_iter().next().unwrap() {
                    BFCompileError::Basic { id, .. }
                    | BFCompileError::Instruction { id, .. }
                    | BFCompileError::Position { id, .. } => id == String::from("UNMATCHED_CLOSE"),
                    BFCompileError::UnknownFlag(_) => false,
                }
            })
        );
        Ok(())
    }
}
