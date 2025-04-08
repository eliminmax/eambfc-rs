// SPDX-FileCopyrightText: 2024 - 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only
mod fsutil;
use fsutil::set_extension;
mod optimize;
use optimize::filtered_read;
mod arch_inter;
use arch_inter::ArchInter;

pub(crate) mod backends;
pub(crate) mod elf_tools;

use crate::err::{BFCompileError, BFErrorID, CodePosition};
use elf_tools::Backend;

use std::ffi::OsStr;
use std::io::{BufReader, Read, Write};

struct JumpLocation {
    loc: Option<CodePosition>,
    index: usize,
}

// ELF addressing stuff
const TAPE_ADDR: u64 = 0x10000;
const START_ADDR: u64 = 256;

fn write_headers(
    output: &mut impl Write,
    codesize: usize,
    tape_blocks: u64,
    elf_arch: Backend,
    e_flags: u32,
) -> Result<(), BFCompileError> {
    // ELF addressing stuff that depends on tape_blocks, so can't be constant
    let tape_size: u64 = tape_blocks * 0x1000;
    let load_vaddr: u64 = ((TAPE_ADDR + tape_size) & (!0xffff)) + 0x10000;
    let start_virt_addr: u64 = START_ADDR + load_vaddr;
    let ehdr = elf_tools::BinInfo {
        arch: elf_arch,
        entry: start_virt_addr,
        flags: e_flags,
    };
    let tape_segment = elf_tools::Phdr {
        arch: elf_arch,
        flags: 4 | 2,     // PF_R | PF_W (readable and writable)
        offset: 0,        // load bytes from this index in the file
        vaddr: TAPE_ADDR, // load segment into this section of memory
        filesz: 0,        // don't load anything from file, just zero-initialize it
        memsz: tape_size, // allocate this many bytes of memory for this segment
        align: 0x1000,    // align with this power of 2
    };
    let code_segment = elf_tools::Phdr {
        arch: elf_arch,
        flags: 4 | 1,                         // PF_R | PF_X (readable and executable)
        offset: 0,                            // load bytes from this index in the file
        vaddr: load_vaddr,                    // load segment into this section of memory
        filesz: START_ADDR + codesize as u64, // load this many bytes from file…
        memsz: START_ADDR + codesize as u64,  // allocate this many bytes of memory…
        align: 1,                             // align with this power of 2
    };
    let mut to_write = Vec::<u8>::from(ehdr);
    to_write.extend(Vec::<u8>::from(tape_segment));
    to_write.extend(Vec::<u8>::from(code_segment));

    // add padding bytes
    to_write.resize(START_ADDR as usize, 0);
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

pub(crate) trait BFCompile {
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
        out_suffix: Option<&OsStr>,
    ) -> Result<(), Vec<BFCompileError>> {
        use std::fs::{File, OpenOptions, remove_file};

        let mut open_options = OpenOptions::new();
        open_options.write(true).create(true).truncate(true);
        #[cfg(unix)]
        {
            use std::os::unix::fs::OpenOptionsExt;
            open_options.mode(0o755);
        };

        let outfile_name = set_extension(file_name, extension, out_suffix)?;

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
        let mut ret = Self::compile(infile, outfile, optimize, tape_blocks);
        if let Err(ref mut errs) = ret {
            errs.iter_mut().for_each(|e| e.set_file(file_name));
        }
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
    /// The brainfuck instructions `b'.'` and `b','` are similar from an implementation
    /// perspective. Both require making system calls for I/O, and the system calls
    /// have 3 nearly identical arguments:
    ///  - arg1 is the file descriptor
    ///  - arg2 is the memory address of the data source (write)/dest (read)
    ///  - arg3 is the number of bytes to write/read
    ///
    /// Due to their similarity, `b','` and b`'.'` are both implemented with `bf_io`.
    fn bf_io(code_buf: &mut Vec<u8>, sc: i64, fd: i64) {
        Self::set_reg(code_buf, Self::REGISTERS.sc_num, sc);
        Self::set_reg(code_buf, Self::REGISTERS.arg1, fd);
        Self::reg_copy(code_buf, Self::REGISTERS.arg2, Self::REGISTERS.bf_ptr);
        Self::set_reg(code_buf, Self::REGISTERS.arg3, 1);
        Self::syscall(code_buf);
    }

    /// Compile `instr`, appending the machine code to `code_buf`. `jump_stack` is used to track
    /// the jump locations.
    ///
    /// If `loc` is `Some`, then it will be updated with the current position within the brainfuck
    /// source code, which is used for more detailed error messages.
    ///
    /// If the compilation of jump instructions results in an error, it's passed along, and if
    /// `instr` is `b']'` and `jump_stack` is empty, it returns an error.
    fn compile_instr(
        instr: u8,
        code_buf: &mut Vec<u8>,
        mut loc: Option<&mut CodePosition>,
        jump_stack: &mut Vec<JumpLocation>,
    ) -> Result<(), BFCompileError> {
        if let Some(ref mut pos) = loc {
            if instr & 0xc0 != 0x80 {
                pos.col += 1;
            }
        }
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
            // pad `Self::JUMP_SIZE` bytes with a trap instruction followed by no-ops.
            // will replace when reaching the corresponding ']' instruction
            b'[' => {
                jump_stack.push(JumpLocation {
                    loc: loc.copied(),
                    index: code_buf.len(),
                });
                Self::pad_loop_open(code_buf);
            }
            b']' => {
                // First, compile the skipped '[' instruction
                let Some(open_location) = jump_stack.pop() else {
                    return Err(BFCompileError::new(
                        BFErrorID::UnmatchedClose,
                        "Found ']' without matching '['.",
                        Some(b']'),
                        loc.copied(),
                    ));
                };
                let distance = code_buf.len() - open_location.index;
                Self::jump_open(
                    code_buf,
                    open_location.index,
                    Self::REGISTERS.bf_ptr,
                    distance as i64,
                )?;
                Self::jump_close(code_buf, Self::REGISTERS.bf_ptr, -(distance as i64))?;
            }
            b'\n' => {
                if let Some(ref mut pos) = loc {
                    pos.col = 0;
                    pos.line += 1;
                }
            }
            _ => (),
        }
        Ok(())
    }

    /// Compile a sequence of `count` copies of `instr` in a row. If `count` is more than 1, and
    /// `instr` is one of `b'+'`, `b'-'`, `b'<'`, or `b'>'`, it's able to combine them into more
    /// efficient machine code. If `instr` is `b'@'`, then it was originally `[-]` or `[+]`, and
    /// it should be zeroed out.
    fn compile_condensed_instr(
        instr: optimize::FilteredInstr,
        count: usize,
        dst: &mut Vec<u8>,
        jump_stack: &mut Vec<JumpLocation>,
    ) -> Result<(), BFCompileError> {
        use optimize::FilteredInstr as FI;
        if instr != FI::SetZero && count == 1 {
            return Self::compile_instr(instr as u8, dst, None, jump_stack);
        }
        match instr {
            FI::SetZero => Self::zero_byte(dst, Self::REGISTERS.bf_ptr),
            FI::Add => Self::add_byte(dst, Self::REGISTERS.bf_ptr, count as u8),
            FI::Sub => Self::sub_byte(dst, Self::REGISTERS.bf_ptr, count as u8),
            FI::MoveL => Self::sub_reg(dst, Self::REGISTERS.bf_ptr, count as u64),
            FI::MoveR => Self::add_reg(dst, Self::REGISTERS.bf_ptr, count as u64),
            _ => {
                for _ in 0..count {
                    Self::compile_instr(instr as u8, dst, None, jump_stack)?;
                }
            }
        }
        Ok(())
    }

    fn compile_condensed(
        dst: &mut Vec<u8>,
        jump_stack: &mut Vec<JumpLocation>,
        filtered_code: Vec<optimize::FilteredInstr>,
    ) -> Result<(), Vec<BFCompileError>> {
        let mut filtered_code = filtered_code.into_iter();
        let Some(mut prev_instr) = filtered_code.next() else {
            return Ok(());
        };

        let mut count: usize = 1;
        for instr in filtered_code {
            if instr == prev_instr {
                count += 1;
            } else {
                Self::compile_condensed_instr(prev_instr, count, dst, jump_stack)?;
                prev_instr = instr;
                count = 1;
            }
        }
        Self::compile_condensed_instr(prev_instr, count, dst, jump_stack)?;
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
            match filtered_read(reader) {
                Ok(filtered_code) => {
                    if let Err(e) =
                        Self::compile_condensed(&mut code_buf, &mut jump_stack, filtered_code)
                    {
                        errs.extend(e);
                    }
                }
                Err(e) => errs.push(e),
            }
        } else {
            reader.bytes().for_each(|maybe_byte| match maybe_byte {
                Ok(byte) => {
                    if let Err(e) =
                        Self::compile_instr(byte, &mut code_buf, Some(&mut loc), &mut jump_stack)
                    {
                        errs.push(e);
                    }
                }
                Err(_) => {
                    errs.push(BFCompileError::new(
                        BFErrorID::FailedRead,
                        String::from("Failed to read byte after current position"),
                        None,
                        Some(loc),
                    ));
                }
            });
        }

        // quick check to make sure that there are no unterminated loops
        jump_stack.reverse();
        while let Some(jl) = jump_stack.pop() {
            errs.push(BFCompileError::new(
                BFErrorID::UnmatchedOpen,
                String::from("Reached the end of the file with an unmatched '['"),
                Some(b'['),
                jl.loc,
            ));
        }
        // finally, after that mess, end with an exit(0)
        Self::set_reg(&mut code_buf, Self::REGISTERS.sc_num, Self::SC_NUMS.exit);
        Self::set_reg(&mut code_buf, Self::REGISTERS.arg1, 0);
        Self::syscall(&mut code_buf);

        let code_sz = code_buf.len();
        if let Err(e) = write_headers(&mut out_f, code_sz, tape_blocks, Self::ARCH, Self::E_FLAGS) {
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
        }
        if errs.is_empty() { Ok(()) } else { Err(errs) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[cfg(eambfc_default_arch = "arm64")]
    use backends::Arm64Inter as TestInter;
    #[cfg(eambfc_default_arch = "riscv64")]
    use backends::RiscV64Inter as TestInter;
    #[cfg(eambfc_default_arch = "s390x")]
    use backends::S390xInter as TestInter;
    #[cfg(eambfc_default_arch = "x86_64")]
    use backends::X86_64Inter as TestInter;
    use std::io;

    #[test]
    fn compile_all_bf_instructions() -> Result<(), String> {
        TestInter::compile(b"+[>]<-,.".as_slice(), Vec::<u8>::new(), false, 8)
            .map_err(|e| format!("Failed to compile: {e:?}"))
    }

    #[test]
    fn compile_nested_loops() -> Result<(), String> {
        // An algorithm to set a cell to the number 33, contributed to esolangs.org in 2005 by
        // user Calamari. esolangs.org contents are available under a CC0-1.0 license.
        TestInter::compile(b">+[-->---[-<]>]>+".as_slice(), Vec::<u8>::new(), false, 8)
            .map_err(|e| format!("Failed to compile: {e:?}"))
    }

    #[test]
    fn unmatched_open() {
        assert!(
            TestInter::compile(b"[".as_slice(), Vec::<u8>::new(), false, 8,)
                .is_err_and(|e| e[0].error_id() == BFErrorID::UnmatchedOpen)
        );
    }

    #[test]
    fn unmatched_close() {
        assert!(
            TestInter::compile(b"]".as_slice(), Vec::<u8>::new(), false, 8,)
                .is_err_and(|e| e[0].error_id() == BFErrorID::UnmatchedClose)
        );
    }

    struct FailingWriter {
        fail_after: usize,
    }

    impl Write for FailingWriter {
        fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
            if self.fail_after == 0 {
                Err(io::Error::new(
                    io::ErrorKind::Other,
                    "testing write failure handling",
                ))
            } else if buf.len() < self.fail_after {
                self.fail_after -= buf.len();
                Ok(buf.len())
            } else {
                let ret = self.fail_after;
                self.fail_after = 0;
                Ok(ret)
            }
        }

        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    #[test]
    fn write_failures_handled() {
        // partial write failure while writing headers
        assert!(
            TestInter::compile(b"[-]".as_slice(), FailingWriter { fail_after: 60 }, true, 8)
                .is_err_and(|e| e[0].error_id() == BFErrorID::FailedWrite)
        );
        // total write failure while writing headers
        assert!(
            TestInter::compile(b"[-]".as_slice(), FailingWriter { fail_after: 0 }, true, 8)
                .is_err_and(|e| e[0].error_id() == BFErrorID::FailedWrite)
        );
        // partial write failure while writing code
        assert!(
            TestInter::compile(
                b"[-]".as_slice(),
                FailingWriter {
                    fail_after: START_ADDR as usize + 1
                },
                true,
                8
            )
            .is_err_and(|e| e[0].error_id() == BFErrorID::FailedWrite)
        );
        // total write failure after writing headers
        assert!(
            TestInter::compile(
                b"[-]".as_slice(),
                FailingWriter {
                    fail_after: START_ADDR as usize
                },
                true,
                8
            )
            .is_err_and(|e| e[0].error_id() == BFErrorID::FailedWrite)
        );
    }
}
