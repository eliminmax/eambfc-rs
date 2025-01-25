// SPDX-FileCopyrightText: 2024 - 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only
mod fsutil;
use fsutil::rm_ext;
mod optimize;
use optimize::{to_condensed, CondensedInstruction};
mod arch_inter;
use arch_inter::ArchInter;

pub mod backends;
pub mod elf_tools;

use elf_tools::{
    ByteOrdering, EIdent, Ehdr, ElfArch, ElfClass, ElfOsAbi, ElfType, ElfVersion, PType, Phdr,
    EHDR_SIZE, PHDR_SIZE,
};
use crate::err::{BFCompileError, BFErrorID, CodePosition};

use std::ffi::OsStr;
use std::io::{BufReader, Read, Write};

pub struct JumpLocation {
    loc: CodePosition,
    index: usize,
}

// ELF addressing stuff
const PHTB_SIZE: u64 = (PHDR_SIZE * PHNUM) as u64;
const TAPE_ADDR: u64 = 0x10000;
const PHNUM: u16 = 2;

fn write_headers(
    output: &mut impl Write,
    codesize: usize,
    tape_blocks: u64,
    ei_data: ByteOrdering,
    elf_arch: ElfArch,
    e_flags: u32,
) -> Result<(), BFCompileError> {
    // ELF addressing stuff that depends on tape_blocks, so can't be constant
    let tape_size: u64 = tape_blocks * 0x1000;
    let load_vaddr: u64 = ((TAPE_ADDR + tape_size) & (!0xffff)) + 0x10000;
    let start_addr: u64 = ((u64::from(EHDR_SIZE) + PHTB_SIZE) & (!0xff)) + 0x100;
    let start_virt_addr: u64 = start_addr + load_vaddr;
    let ehdr = Ehdr {
        ident: EIdent {
            class: ElfClass::ELFClass64,
            data: ei_data,
            osabi: ElfOsAbi::None,
        },
        elf_type: ElfType::Exec,
        machine: elf_arch,
        version: ElfVersion::EvCurrent, // The only valid version number
        phnum: PHNUM,
        shnum: 0,
        phoff: u64::from(EHDR_SIZE),
        shoff: 0, // no section header table, must be 0
        ehsize: EHDR_SIZE,
        phentsize: PHDR_SIZE,
        shentsize: 0, // no section header table, must be 0
        shstrndx: 0,  // no section header table, must be 0
        entry: start_virt_addr,
        flags: e_flags,
    };
    let tape_segment = Phdr {
        byte_order: ei_data,
        header_type: PType::Load, // loadable segment
        flags: 4 | 2,             // PF_R | PF_W (readable and writable)
        offset: 0,                // load bytes from this index in the file
        vaddr: TAPE_ADDR,         // load segment into this section of memory
        paddr: 0,                 // load from this physical address
        filesz: 0,                // don't load anything from file, just zero-initialize it
        memsz: tape_size,         // allocate this many bytes of memory for this segment
        align: 0x1000,            // align with this power of 2
    };
    let code_segment = Phdr {
        byte_order: ei_data,
        header_type: PType::Load,             // loadable segment
        flags: 4 | 1,                         // PF_R | PF_X (readable and executable)
        offset: 0,                            // load bytes from this index in the file
        vaddr: load_vaddr,                    // load segment into this section of memory
        paddr: 0,                             // load from this physical address
        filesz: start_addr + codesize as u64, // load this many bytes from file…
        memsz: start_addr + codesize as u64,  // allocate this many bytes of memory…
        align: 1,                             // align with this power of 2
    };
    let mut to_write = Vec::<u8>::from(ehdr);
    to_write.extend(Vec::<u8>::from(tape_segment));
    to_write.extend(Vec::<u8>::from(code_segment));

    // add padding bytes
    to_write.resize(start_addr as usize, 0);
    match output.write(to_write.as_slice()) {
        Ok(count) if count == to_write.len() => Ok(()),
        Ok(count) => Err(BFCompileError::basic(
            BFErrorID::FailedWrite,
            format!(
                "Expected to write {} bytes of ELF header and program header table, wrote {}",
                to_write.len(),
                count,
            ),
        )),
        Err(_) => Err(BFCompileError::basic(
            BFErrorID::FailedWrite,
            "Failed to write ELF header and program header table",
        )),
    }
}

pub trait BFCompile {
    // compile the contents of in_f, writing the output to out_f
    fn compile(
        in_f: impl Read,
        out_f: impl Write,
        optimize: bool,
        tape_blocks: u64,
    ) -> Result<(), Vec<BFCompileError>>;

    // handle opening file_name, and writing the executable
    fn compile_file(
        file_name: &OsStr,
        extension: &OsStr,
        optimize: bool,
        keep: bool,
        tape_blocks: u64,
    ) -> Result<(), Vec<BFCompileError>> {
        use std::fs::{remove_file, File, OpenOptions};

        let mut open_options = OpenOptions::new();
        open_options.write(true).create(true).truncate(true);
        #[cfg(unix)]
        {
            use std::os::unix::fs::OpenOptionsExt;
            open_options.mode(0o755);
        };

        let outfile_name = rm_ext(file_name, extension)?;

        let infile = File::open(file_name).map_err(|_| {
            vec![BFCompileError::basic(
                BFErrorID::OpenReadFailed,
                format!(
                    "Failed to open {} for reading.",
                    file_name.to_string_lossy()
                ),
            )]
        })?;
        let outfile = open_options.open(&outfile_name).map_err(|_| {
            vec![BFCompileError::basic(
                BFErrorID::OpenWriteFailed,
                format!(
                    "Failed to open {} for writing.",
                    outfile_name.to_string_lossy()
                ),
            )]
        })?;
        let ret = Self::compile(infile, outfile, optimize, tape_blocks);
        if ret.is_err() && !keep {
            // try to delete the file
            #[allow(
                clippy::let_underscore_must_use,
                reason = "if file can't be deleted, there's nothing to do"
            )]
            let _ = remove_file(outfile_name);
        }
        ret
    }
}

trait BFCompileHelper: ArchInter {
    // The brainfuck instructions "." and "," are similar from an implementation
    // perspective. Both require making system calls for I/O, and the system calls
    // have 3 nearly identical arguments:
    //  - arg1 is the file descriptor
    //  - arg2 is the memory address of the data source (write)/dest (read)
    //  - arg3 is the number of bytes to write/read
    //
    // Due to their similarity, ',' and '.' are both implemented with bf_io.
    fn bf_io(code_buf: &mut Vec<u8>, sc: i64, fd: i64) {
        Self::set_reg(code_buf, Self::REGISTERS.sc_num, sc);
        Self::set_reg(code_buf, Self::REGISTERS.arg1, fd);
        Self::reg_copy(code_buf, Self::REGISTERS.arg2, Self::REGISTERS.bf_ptr);
        Self::set_reg(code_buf, Self::REGISTERS.arg3, 1);
        Self::syscall(code_buf);
    }

    fn compile_instr(
        instr: u8,
        code_buf: &mut Vec<u8>,
        loc: &mut CodePosition,
        jump_stack: &mut Vec<JumpLocation>,
    ) -> Result<(), BFCompileError> {
        loc.col += 1;
        match instr {
            // decrement the tape pointer register
            b'<' => Self::dec_reg(code_buf, Self::REGISTERS.bf_ptr),
            // increment the tape pointer register
            b'>' => Self::inc_reg(code_buf, Self::REGISTERS.bf_ptr),
            // decrement the current cell value
            b'-' => Self::dec_byte(code_buf, Self::REGISTERS.bf_ptr),
            // increment the current cell value
            b'+' => Self::inc_byte(code_buf, Self::REGISTERS.bf_ptr),
            // Write 1 byte at [bf_ptr] to STDOUT
            b'.' => Self::bf_io(code_buf, Self::SC_NUMS.write, 1),
            // Read 1 byte to [bf_ptr] from STDIN
            b',' => Self::bf_io(code_buf, Self::SC_NUMS.read, 0),
            // for this, fill jump_size bytes with NOPs, and push the location to jump_stack.
            // will replace when reaching the corresponding ']' instruction
            b'[' => {
                jump_stack.push(JumpLocation {
                    loc: *loc,
                    index: code_buf.len(),
                });
                Self::nop_loop_open(code_buf);
            }
            b']' => {
                // First, compile the skipped '[' instruction
                let open_location =
                    jump_stack
                        .pop()
                        .ok_or::<BFCompileError>(BFCompileError::positional(
                            BFErrorID::UnmatchedClose,
                            "Found ']' without matching '['.",
                            b']',
                            *loc,
                        ))?;
                let open_address = open_location.index;
                let distance = code_buf.len() - open_address;
                let mut jump_code: Vec<u8> = Vec::with_capacity(Self::JUMP_SIZE);
                Self::jump_zero(&mut jump_code, Self::REGISTERS.bf_ptr, distance as i64)?;
                code_buf[open_address..open_address + Self::JUMP_SIZE]
                    .swap_with_slice(&mut jump_code);
                Self::jump_not_zero(code_buf, Self::REGISTERS.bf_ptr, -(distance as i64))?;
            }
            b'\n' => {
                loc.col = 0;
                loc.line += 1;
            }
            _ => (),
        }
        Ok(())
    }

    fn compile_condensed(
        condensed_instr: CondensedInstruction,
        dst: &mut Vec<u8>,
        jump_stack: &mut Vec<JumpLocation>,
    ) -> Result<(), BFCompileError> {
        use CondensedInstruction as CI;

        match condensed_instr {
            CI::SetZero => Self::zero_byte(dst, Self::REGISTERS.bf_ptr),
            CI::RepeatAdd(count) => Self::add_byte(dst, Self::REGISTERS.bf_ptr, count.get() as i8),
            CI::RepeatSub(count) => Self::sub_byte(dst, Self::REGISTERS.bf_ptr, count.get() as i8),
            CI::RepeatMoveR(count) => {
                Self::add_reg(dst, Self::REGISTERS.bf_ptr, count.get() as i64);
            }
            CI::RepeatMoveL(count) => {
                Self::sub_reg(dst, Self::REGISTERS.bf_ptr, count.get() as i64);
            }
            CI::BFInstruction(i) => {
                Self::compile_instr(
                    i,
                    dst,
                    // throwaway position value
                    &mut CodePosition { line: 0, col: 0 },
                    jump_stack,
                )?;
            }
        }
        Ok(())
    }
}

impl<A: ArchInter> BFCompileHelper for A {}

impl<B: BFCompileHelper> BFCompile for B {
    fn compile(
        in_f: impl Read,
        mut out_f: impl Write,
        optimize: bool,
        tape_blocks: u64,
    ) -> Result<(), Vec<BFCompileError>> {
        let mut jump_stack = Vec::<JumpLocation>::new();
        let mut loc = CodePosition { line: 1, col: 0 };
        let mut code_buf: Vec<u8> = Vec::new();
        Self::set_reg(&mut code_buf, Self::REGISTERS.bf_ptr, TAPE_ADDR as i64);
        let mut errs = Vec::<BFCompileError>::new();

        let reader = BufReader::new(in_f);

        if optimize {
            errs.append(&mut match to_condensed(Box::new(reader)) {
                Ok(condensed) => condensed
                    .into_iter()
                    .filter_map(|i| {
                        if let Err(e) = Self::compile_condensed(i, &mut code_buf, &mut jump_stack) {
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
                        Self::compile_instr(byte, &mut code_buf, &mut loc, &mut jump_stack)
                    {
                        errs.push(e);
                    }
                }
                Err(_) => {
                    errs.push(BFCompileError::positional(
                        BFErrorID::FailedRead,
                        String::from("Failed to read byte after current position"),
                        b'\0',
                        loc,
                    ));
                }
            });
        }

        // quick check to make sure that there are no unterminated loops
        if let Some(jl) = jump_stack.pop() {
            errs.push(BFCompileError::positional(
                BFErrorID::UnmatchedOpen,
                String::from("Reached the end of the file with an unmatched '['"),
                b'[',
                jl.loc,
            ));
        }
        // finally, after that mess, end with an exit(0)
        Self::set_reg(&mut code_buf, Self::REGISTERS.sc_num, Self::SC_NUMS.exit);
        Self::set_reg(&mut code_buf, Self::REGISTERS.arg1, 0);
        Self::syscall(&mut code_buf);

        let code_sz = code_buf.len();
        if let Err(e) = write_headers(
            &mut out_f,
            code_sz,
            tape_blocks,
            Self::EI_DATA,
            Self::ARCH,
            Self::E_FLAGS,
        ) {
            errs.push(e);
        }
        match out_f.write(code_buf.as_slice()) {
            Ok(count) if count == code_sz => (),
            Ok(count) => errs.push(BFCompileError::basic(
                BFErrorID::FailedWrite,
                format!("Only wrote {count} out of expected {code_sz} machine code bytes"),
            )),
            Err(_) => errs.push(BFCompileError::basic(
                BFErrorID::FailedWrite,
                "Failed to write internal code buffer to output file",
            )),
        };
        if errs.is_empty() {
            Ok(())
        } else {
            Err(errs)
        }
    }
}

#[cfg(feature = "x86_64")]
#[cfg(test)]
mod tests {
    use super::*;
    use backends::x86_64::X86_64Inter;

    #[test]
    fn compile_all_bf_instructions() -> Result<(), String> {
        X86_64Inter::compile(
            Box::new(b"+[>]<-,.".as_slice()),
            Box::new(Vec::<u8>::new()),
            false,
            8,
        )
        .map_err(|e| format!("Failed to compile: {e:?}"))
    }

    #[test]
    fn compile_nested_loops() -> Result<(), String> {
        // An algorithm to set a cell to the number 33, contributed to esolangs.org in 2005 by
        // user Calamari. esolangs.org contents are available under a CC0-1.0 license.
        X86_64Inter::compile(
            Box::new(b">+[-->---[-<]>]>+".as_slice()),
            Box::new(Vec::<u8>::new()),
            false,
            8,
        )
        .map_err(|e| format!("Failed to compile: {e:?}"))
    }

    #[test]
    fn unmatched_open() {
        assert!(X86_64Inter::compile(
            Box::new(b"[".as_slice()),
            Box::new(Vec::<u8>::new()),
            false,
            8,
        )
        .is_err_and(|e| e[0].kind == BFErrorID::UnmatchedOpen));
    }

    #[test]
    fn unmatched_close() {
        assert!(X86_64Inter::compile(
            Box::new(b"]".as_slice()),
            Box::new(Vec::<u8>::new()),
            false,
            8,
        )
        .is_err_and(|e| e[0].kind == BFErrorID::UnmatchedClose));
    }
}
