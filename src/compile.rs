// SPDX-FileCopyrightText: 2024 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only
use super::arch_inter::{ArchInfo, ArchInter};
use super::elf_tools::{EIClass, EIdent, ELFType, ELFVersion, Ehdr, PType, Phdr, ELFOSABI};
use super::err::BFCompileError;
use super::optimize::{to_condensed, CondensedInstruction as CI};
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

fn write_headers<T: Copy, I: ArchInter>(
    output: &mut dyn Write,
    codesize: usize,
    tape_blocks: u64,
    arch_info: &ArchInfo<T, I>,
) -> Result<(), BFCompileError> {
    // more ELF addressing stuff - depends on tape_blocks, so can't be const
    let tape_size: u64 = tape_blocks * 0x1000;
    let load_vaddr: u64 = ((TAPE_ADDR + tape_size) & (!0xffffu64)) + 0x10000u64;
    let start_paddr: u64 = ((EHDR_SIZE as u64 + PHTB_SIZE) & (!0xffu64)) + 0x100u64;
    let start_vaddr: u64 = start_paddr + load_vaddr;

    let ehdr = Ehdr {
        e_ident: EIdent {
            ei_class: EIClass::ELFClass64,
            ei_data: arch_info.elfdata_byte_order,
            ei_osabi: ELFOSABI::SYSV,
        },
        e_type: ELFType::Exec,
        e_machine: arch_info.em_arch,
        e_version: ELFVersion::EvCurrent, // The only valid version number
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
        e_data: arch_info.elfdata_byte_order,
        p_type: PType::Load, // loadable segment
        p_flags: 4 | 2,      // PF_R | PF_W (readable and writable)
        p_offset: 0,         // load bytes from this index in the file
        p_vaddr: TAPE_ADDR,  // load segment into this section of memory
        p_paddr: 0,          // load from this physical address
        p_filesz: 0,         // don't load anything from file, just zero-initialize it
        p_memsz: tape_size,  // allocate this many bytes of memory for this segment
        p_align: 0x1000,     // align with this power of 2
    };
    let code_segment = Phdr {
        e_data: arch_info.elfdata_byte_order,
        p_type: PType::Load,                     // loadable segment
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

// The brainfuck instructions "." and "," are similar from an implementation
// perspective. Both require making system calls for I/O, and the system calls
// have 3 nearly identical arguments:
//  - arg1 is the file descriptor
//  - arg2 is the memory address of the data source (write)/dest (read)
//  - arg3 is the number of bytes to write/read
//
// Due to their similarity, ',' and '.' are both implemented with bf_io.
#[inline]
fn bf_io<T: Copy, I: ArchInter<RegType = T>>(
    sc: i64,
    fd: i64,
    arch_info: &ArchInfo<T, I>,
) -> Vec<u8> {
    // set the system call number register to $sc_num
    let mut instr_bytes = I::set_reg(arch_info.registers.sc_num, sc);
    // set the first argument to the file descriptor
    instr_bytes.extend(I::set_reg(arch_info.registers.arg1, fd));
    // byte to read in to or write out from is in the brainfuck pointer
    instr_bytes.extend(I::reg_copy(
        arch_info.registers.arg2,
        arch_info.registers.bf_ptr,
    ));
    // only one byte is read/written
    instr_bytes.extend(I::set_reg(arch_info.registers.arg3, 1));
    // append the system call instruction
    instr_bytes.extend(I::syscall());
    // return the instr_bytes vector
    instr_bytes
}

struct JumpLocation {
    src_line: usize,
    src_col: usize,
    index: usize,
}

fn compile_condensed<T: Copy, I: ArchInter<RegType = T>>(
    condensed_instr: CI,
    dst: &mut Vec<u8>,
    jump_stack: &mut Vec<JumpLocation>,
    arch_info: &ArchInfo<T, I>,
) -> Result<(), BFCompileError> {
    let to_write: Vec<u8> = match condensed_instr {
        CI::SetZero => I::zero_byte(arch_info.registers.bf_ptr),
        CI::RepeatAdd(count) => I::add_byte(arch_info.registers.bf_ptr, count as i8),
        CI::RepeatSub(count) => I::sub_byte(arch_info.registers.bf_ptr, count as i8),
        CI::RepeatMoveR(count) => I::add_reg(arch_info.registers.bf_ptr, count as u64)?,
        CI::RepeatMoveL(count) => I::sub_reg(arch_info.registers.bf_ptr, count as u64)?,
        CI::BFInstruction(i) => {
            return compile_instr(
                i,
                dst,
                // throwaway position value
                &mut Position { line: 0, col: 0 },
                jump_stack,
                arch_info,
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

fn compile_instr<T: Copy, I: ArchInter<RegType = T>>(
    instr: u8,
    dst: &mut Vec<u8>,
    pos: &mut Position,
    jump_stack: &mut Vec<JumpLocation>,
    arch_info: &ArchInfo<T, I>,
) -> Result<(), BFCompileError> {
    pos.col += 1;
    let to_write: Vec<u8> = match instr {
        // decrement the tape pointer register
        b'<' => I::dec_reg(arch_info.registers.bf_ptr),
        // increment the tape pointer register
        b'>' => I::inc_reg(arch_info.registers.bf_ptr),
        // decrement the current cell value
        b'-' => I::dec_byte(arch_info.registers.bf_ptr),
        // increment the current cell value
        b'+' => I::inc_byte(arch_info.registers.bf_ptr),
        // Write 1 byte at [bf_ptr] to STDOUT
        b'.' => bf_io(arch_info.sc_nums.sc_write, 1, arch_info),
        // Read 1 byte to [bf_ptr] from STDIN
        b',' => bf_io(arch_info.sc_nums.sc_read, 0, arch_info),
        // for this, fill jump_size bytes with NOPs, and push the location to jump_stack.
        // will replace when reaching the corresponding ']' instruction
        b'[' => {
            jump_stack.push(JumpLocation {
                src_line: pos.line,
                src_col: pos.col,
                index: dst.len(),
            });
            dst.extend(I::nop_loop_open());
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
            dst[open_address..open_address + arch_info.jump_size].swap_with_slice(
                &mut I::jump_zero(arch_info.registers.bf_ptr, distance as i64)?,
            );
            // now, we know that distance fits within the 32-bit integer limit, so we can
            // simply cast without another check needed when compiling the `]` instruction itself
            I::jump_not_zero(arch_info.registers.bf_ptr, -(distance as i64))?
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

pub fn bf_compile<T: Copy, I: ArchInter<RegType = T>>(
    in_f: Box<dyn Read>,
    mut out_f: Box<dyn Write>,
    optimize: bool,
    tape_blocks: u64,
    arch_info: ArchInfo<T, I>,
) -> Result<(), Vec<BFCompileError>> {
    let mut jump_stack = Vec::<JumpLocation>::new();
    let mut pos = Position { line: 1, col: 0 };
    let mut code_buf = I::set_reg(arch_info.registers.bf_ptr, TAPE_ADDR as i64);
    let mut errs = Vec::<BFCompileError>::new();

    let reader = BufReader::new(in_f);

    if optimize {
        errs.append(&mut match to_condensed(Box::new(reader)) {
            Ok(condensed) => condensed
                .into_iter()
                .filter_map(|i| {
                    if let Err(e) = compile_condensed(i, &mut code_buf, &mut jump_stack, &arch_info)
                    {
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
                if let Err(e) =
                    compile_instr(byte, &mut code_buf, &mut pos, &mut jump_stack, &arch_info)
                {
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
    code_buf.extend(I::set_reg(
        arch_info.registers.sc_num,
        arch_info.sc_nums.sc_exit,
    ));
    code_buf.extend(I::set_reg(arch_info.registers.arg1, 0));
    code_buf.extend(I::syscall());

    let code_sz = code_buf.len();
    if let Err(e) = write_headers(&mut out_f, code_sz, tape_blocks, &arch_info) {
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
    use super::super::x86_64_encoders::X86_64_INTER;
    use super::*;
    #[test]
    fn compile_all_bf_instructions() -> Result<(), String> {
        bf_compile(
            Box::new(b"+[>]<-,.".as_slice()),
            Box::new(Vec::<u8>::new()),
            false,
            8,
            X86_64_INTER,
        )
        .map_err(|e| format!("Failed to compile: {:?}", e))
    }

    #[test]
    fn compile_nested_loops() -> Result<(), String> {
        // An algorithm to set a cell to the number 33, contributed to esolangs.org in 2005 by
        // user Calamari. esolangs.org contents are available under a CC0-1.0 license.
        bf_compile(
            Box::new(b">+[-->---[-<]>]>+".as_slice()),
            Box::new(Vec::<u8>::new()),
            false,
            8,
            X86_64_INTER,
        )
        .map_err(|e| format!("Failed to compile: {:?}", e))
    }

    #[test]
    fn unmatched_open() -> Result<(), String> {
        assert!(bf_compile(
            Box::new(b"[".as_slice()),
            Box::new(Vec::<u8>::new()),
            false,
            8,
            X86_64_INTER
        )
        .is_err_and(|e| {
            match e.into_iter().next().unwrap() {
                BFCompileError::Basic { id, .. }
                | BFCompileError::Instruction { id, .. }
                | BFCompileError::Position { id, .. } => id == String::from("UNMATCHED_OPEN"),
                BFCompileError::UnknownFlag(_) => false,
            }
        }));
        Ok(())
    }

    #[test]
    fn unmatched_close() -> Result<(), String> {
        assert!(bf_compile(
            Box::new(b"]".as_slice()),
            Box::new(Vec::<u8>::new()),
            false,
            8,
            X86_64_INTER
        )
        .is_err_and(|e| {
            match e.into_iter().next().unwrap() {
                BFCompileError::Basic { id, .. }
                | BFCompileError::Instruction { id, .. }
                | BFCompileError::Position { id, .. } => id == String::from("UNMATCHED_CLOSE"),
                BFCompileError::UnknownFlag(_) => false,
            }
        }));
        Ok(())
    }
}
