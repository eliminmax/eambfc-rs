// SPDX-FileCopyrightText: 2024 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only
use super::arch_inter::ArchInter;
use super::elf_tools::{
    EIClass, EIData, EIdent, ELFArch, ELFType, ELFVersion, Ehdr, PType, Phdr, ELFOSABI,
};
use super::err::{BFCompileError, CodePosition};
use super::optimize::{to_condensed, CondensedInstruction as CI};
use std::io::{BufReader, Read, Write};

pub struct JumpLocation {
    loc: CodePosition,
    index: usize,
}

// ELF addressing stuff
const EHDR_SIZE: u16 = 64u16;
const PHDR_SIZE: u16 = 56u16;
const PHTB_SIZE: u64 = (PHDR_SIZE * PHNUM) as u64;
const TAPE_ADDR: u64 = 0x10000;
const PHNUM: u16 = 2;

fn write_headers(
    output: &mut dyn Write,
    codesize: usize,
    tape_blocks: u64,
    ei_data: EIData,
    elf_arch: ELFArch,
) -> Result<(), BFCompileError> {
    // ELF addressing stuff that depends on tape_blocks, so can't be constant
    let tape_size: u64 = tape_blocks * 0x1000;
    let load_vaddr: u64 = ((TAPE_ADDR + tape_size) & (!0xffffu64)) + 0x10000u64;
    let start_paddr: u64 = ((EHDR_SIZE as u64 + PHTB_SIZE) & (!0xffu64)) + 0x100u64;
    let start_vaddr: u64 = start_paddr + load_vaddr;
    let ehdr = Ehdr {
        e_ident: EIdent {
            ei_class: EIClass::ELFClass64,
            ei_data,
            ei_osabi: ELFOSABI::SYSV,
        },
        e_type: ELFType::Exec,
        e_machine: elf_arch,
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
        e_data: ei_data,
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
        e_data: ei_data,
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

pub trait BFCompile: ArchInter {
    // The brainfuck instructions "." and "," are similar from an implementation
    // perspective. Both require making system calls for I/O, and the system calls
    // have 3 nearly identical arguments:
    //  - arg1 is the file descriptor
    //  - arg2 is the memory address of the data source (write)/dest (read)
    //  - arg3 is the number of bytes to write/read
    //
    // Due to their similarity, ',' and '.' are both implemented with bf_io.
    fn bf_io(&self, sc: i64, fd: i64) -> Vec<u8> {
        let mut instr_bytes = Self::set_reg(Self::REGISTERS.sc_num, sc);
        instr_bytes.extend(Self::set_reg(Self::REGISTERS.arg1, fd));
        instr_bytes.extend(Self::reg_copy(Self::REGISTERS.arg2, Self::REGISTERS.bf_ptr));
        instr_bytes.extend(Self::set_reg(Self::REGISTERS.arg3, 1));
        instr_bytes.extend(Self::syscall());
        instr_bytes
    }

    fn compile_instr(
        &self,
        instr: u8,
        dst: &mut Vec<u8>,
        loc: &mut CodePosition,
        jump_stack: &mut Vec<JumpLocation>,
    ) -> Result<(), BFCompileError> {
        loc.col += 1;
        let to_write: Vec<u8> = match instr {
            // decrement the tape pointer register
            b'<' => Self::dec_reg(Self::REGISTERS.bf_ptr),
            // increment the tape pointer register
            b'>' => Self::inc_reg(Self::REGISTERS.bf_ptr),
            // decrement the current cell value
            b'-' => Self::dec_byte(Self::REGISTERS.bf_ptr),
            // increment the current cell value
            b'+' => Self::inc_byte(Self::REGISTERS.bf_ptr),
            // Write 1 byte at [bf_ptr] to STDOUT
            b'.' => self.bf_io(Self::SC_NUMS.write, 1),
            // Read 1 byte to [bf_ptr] from STDIN
            b',' => self.bf_io(Self::SC_NUMS.read, 0),
            // for this, fill jump_size bytes with NOPs, and push the location to jump_stack.
            // will replace when reaching the corresponding ']' instruction
            b'[' => {
                jump_stack.push(JumpLocation {
                    loc: loc.clone(),
                    index: dst.len(),
                });
                dst.extend(Self::nop_loop_open());
                return Ok(());
            }
            b']' => {
                // First, compile the skipped '[' instruction
                let open_location =
                    jump_stack
                        .pop()
                        .ok_or::<BFCompileError>(BFCompileError::Positional {
                            id: String::from("UNMATCHED_CLOSE"),
                            msg: String::from("Found ']' without matching '['."),
                            instr: b']',
                            loc: loc.clone(),
                        })?;
                let open_address = open_location.index;
                let distance = dst.len() - open_address;
                dst[open_address..open_address + Self::JUMP_SIZE].swap_with_slice(
                    &mut Self::jump_zero(Self::REGISTERS.bf_ptr, distance as i64)?,
                );
                Self::jump_not_zero(Self::REGISTERS.bf_ptr, -(distance as i64))?
            }
            b'\n' => {
                loc.col = 1;
                loc.line += 1;
                return Ok(());
            }
            _ => {
                return Ok(());
            }
        };
        match dst.write(to_write.as_slice()) {
            Ok(count) if count == to_write.len() => Ok(()),
            Ok(count) => Err(BFCompileError::Positional {
                id: String::from("FAILED_WRITE"),
                msg: format!(
                    "Expected to write {} bytes when compiling, wrote {}",
                    to_write.len(),
                    count
                ),

                instr,
                loc: loc.clone(),
            }),
            Err(_) => Err(BFCompileError::Positional {
                id: String::from("FAILED_WRITE"),
                msg: String::from("Failed to write to buffer."),
                instr,
                loc: loc.clone(),
            }),
        }
    }

    fn compile_condensed(
        &self,
        condensed_instr: CI,
        dst: &mut Vec<u8>,
        jump_stack: &mut Vec<JumpLocation>,
    ) -> Result<(), BFCompileError> {
        let to_write: Vec<u8> = match condensed_instr {
            CI::SetZero => Self::zero_byte(Self::REGISTERS.bf_ptr),
            CI::RepeatAdd(count) => Self::add_byte(Self::REGISTERS.bf_ptr, count as i8),
            CI::RepeatSub(count) => Self::sub_byte(Self::REGISTERS.bf_ptr, count as i8),
            CI::RepeatMoveR(count) => Self::add_reg(Self::REGISTERS.bf_ptr, count as u64)?,
            CI::RepeatMoveL(count) => Self::sub_reg(Self::REGISTERS.bf_ptr, count as u64)?,
            CI::BFInstruction(i) => {
                return self.compile_instr(
                    i,
                    dst,
                    // throwaway position value
                    &mut CodePosition { line: 0, col: 0 },
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

    fn compile(
        &self,
        in_f: Box<dyn Read>,
        mut out_f: Box<dyn Write>,
        optimize: bool,
        tape_blocks: u64,
    ) -> Result<(), Vec<BFCompileError>> {
        let mut jump_stack = Vec::<JumpLocation>::new();
        let mut loc = CodePosition { line: 1, col: 0 };
        let mut code_buf = Self::set_reg(Self::REGISTERS.bf_ptr, TAPE_ADDR as i64);
        let mut errs = Vec::<BFCompileError>::new();

        let reader = BufReader::new(in_f);

        if optimize {
            errs.append(&mut match to_condensed(Box::new(reader)) {
                Ok(condensed) => condensed
                    .into_iter()
                    .filter_map(|i| {
                        if let Err(e) = self.compile_condensed(i, &mut code_buf, &mut jump_stack) {
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
                        self.compile_instr(byte, &mut code_buf, &mut loc, &mut jump_stack)
                    {
                        errs.push(e);
                    }
                }
                Err(_) => {
                    errs.push(BFCompileError::Positional {
                        id: String::from("FAILED_READ"),
                        msg: String::from("Failed to read byte after current position"),
                        instr: b'\0',
                        loc: loc.clone(),
                    });
                }
            });
        }

        // quick check to make sure that there are no unterminated loops
        if let Some(jl) = jump_stack.pop() {
            errs.push(BFCompileError::Positional {
                id: String::from("UNMATCHED_OPEN"),
                msg: String::from("Reached the end of the file with an unmatched '['"),
                instr: b'[',
                loc: jl.loc,
            });
        }
        // finally, after that mess, end with an exit(0)
        code_buf.extend(Self::set_reg(Self::REGISTERS.sc_num, Self::SC_NUMS.exit));
        code_buf.extend(Self::set_reg(Self::REGISTERS.arg1, 0));
        code_buf.extend(Self::syscall());

        let code_sz = code_buf.len();
        if let Err(e) = write_headers(&mut out_f, code_sz, tape_blocks, Self::EI_DATA, Self::ARCH) {
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
}

#[cfg(test)]
mod tests {
    use super::super::x86_64_encoders::X86_64Inter;
    use super::*;

    const X86_64_INTER: X86_64Inter = X86_64Inter;
    #[test]
    fn compile_all_bf_instructions() -> Result<(), String> {
        X86_64_INTER
            .compile(
                Box::new(b"+[>]<-,.".as_slice()),
                Box::new(Vec::<u8>::new()),
                false,
                8,
            )
            .map_err(|e| format!("Failed to compile: {:?}", e))
    }

    #[test]
    fn compile_nested_loops() -> Result<(), String> {
        // An algorithm to set a cell to the number 33, contributed to esolangs.org in 2005 by
        // user Calamari. esolangs.org contents are available under a CC0-1.0 license.
        X86_64_INTER
            .compile(
                Box::new(b">+[-->---[-<]>]>+".as_slice()),
                Box::new(Vec::<u8>::new()),
                false,
                8,
            )
            .map_err(|e| format!("Failed to compile: {:?}", e))
    }

    #[test]
    fn unmatched_open() -> Result<(), String> {
        assert!(X86_64_INTER
            .compile(
                Box::new(b"[".as_slice()),
                Box::new(Vec::<u8>::new()),
                false,
                8,
            )
            .is_err_and(|e| {
                match e.into_iter().next().unwrap() {
                    BFCompileError::Basic { id, .. }
                    | BFCompileError::Instruction { id, .. }
                    | BFCompileError::Positional { id, .. } => id == String::from("UNMATCHED_OPEN"),
                    BFCompileError::UnknownFlag(_) => false,
                }
            }));
        Ok(())
    }

    #[test]
    fn unmatched_close() -> Result<(), String> {
        assert!(X86_64_INTER
            .compile(
                Box::new(b"]".as_slice()),
                Box::new(Vec::<u8>::new()),
                false,
                8,
            )
            .is_err_and(|e| {
                match e.into_iter().next().unwrap() {
                    BFCompileError::Basic { id, .. }
                    | BFCompileError::Instruction { id, .. }
                    | BFCompileError::Positional { id, .. } => {
                        id == String::from("UNMATCHED_CLOSE")
                    }
                    BFCompileError::UnknownFlag(_) => false,
                }
            }));
        Ok(())
    }
}
