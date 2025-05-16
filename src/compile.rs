// SPDX-FileCopyrightText: 2024 - 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only
mod fsutil;
use fsutil::set_extension;
mod optimize;
use optimize::{CombinedInstruction, combine_instructions};
mod arch_inter;
use arch_inter::ArchInter;

pub(crate) mod backends;

use crate::err::{BFCompileError, BFErrorID, CodePosition};
#[cfg(have_32bit_targets)]
pub(crate) use backends::ElfClass;
use backends::{Backend, BinInfo, SegmentInfo};

use std::ffi::OsStr;
use std::io::{BufReader, Read, Write};

struct JumpLocation {
    loc: Option<CodePosition>,
    index: usize,
}

/// a brainfuck instruction
#[derive(PartialEq, Clone, Copy)]
#[cfg_attr(test, derive(Debug))]
#[repr(u8)]
enum FilteredInstr {
    /// The brainfuck `+` instruction
    Add = b'+',
    /// The brainfuck `-` instruction
    Sub = b'-',
    /// The brainfuck `<` instruction
    MoveL = b'<',
    /// The brainfuck `>` instruction
    MoveR = b'>',
    /// The brainfuck `,` instruction
    Read = b',',
    /// The brainfuck `.` instruction
    Write = b'.',
    /// The brainfuck `[` instruction
    LoopOpen = b'[',
    /// The brainfuck `]` instruction
    LoopClose = b']',
}

impl FilteredInstr {
    /// return `Some(FilteredInstr)` if `b` is a brainfuck instruction, and `None` otherwise
    fn from_byte(b: u8) -> Option<Self> {
        match b {
            b'+' => Some(Self::Add),
            b'-' => Some(Self::Sub),
            b'<' => Some(Self::MoveL),
            b'>' => Some(Self::MoveR),
            b',' => Some(Self::Read),
            b'.' => Some(Self::Write),
            b'[' => Some(Self::LoopOpen),
            b']' => Some(Self::LoopClose),
            _ => None,
        }
    }
}

/// An iterator that returns `FilteredInstr`uctions read from a reader that implements `BufRead`,
/// tracking code position
struct CodeReader<R> {
    byte_reader: std::io::Bytes<R>,
    pos: CodePosition,
}

impl<R: Read> CodeReader<BufReader<R>> {
    fn new(inner_reader: R) -> Self {
        Self {
            byte_reader: BufReader::new(inner_reader).bytes(),
            pos: CodePosition { line: 1, col: 0 },
        }
    }
}

impl<R: Read> Iterator for CodeReader<R> {
    type Item = Result<FilteredInstr, BFCompileError>;
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(b) = self.byte_reader.by_ref().next() {
            let b = match b {
                Ok(ok) => ok,
                Err(err) => {
                    return Some(Err(BFCompileError::new(
                        BFErrorID::FailedRead,
                        format!("An I/O error occurred reading from file: {err:?}"),
                        None,
                        Some(self.pos),
                    )));
                }
            };
            // This comparison that a byte isn't a continuation byte within a UTF-8 multi-byte
            // sequence, so if it's either a new UTF-8 codepoint or invalid UTF-8, this will
            // increment the column counter, but it won't if it's a byte that's typically a
            // continuatio of a UTF-8 sequence
            if b & 0xc0 != 0x80 {
                self.pos.col += 1;
            }
            if let Some(fi) = FilteredInstr::from_byte(b) {
                return Some(Ok(fi));
            }
            if b == b'\n' {
                self.pos.col = 0;
                self.pos.line += 1;
            }
        }
        None
    }
}

// ELF addressing stuff
/// Memory address of tape segment
const TAPE_ADDR: u64 = 0x10000;

/// The address within the file of the first machine code - must be able to fit an Ehdr and 2 Phdr
/// entries.
///
/// 256 was chosen as it's an easy enough number to work with, and it gives enough padding for both
/// 32-bit and 64-bit backends - 32-bit ELFs will have 140 bytes of padding, and 64-bit ELFs will
/// have 80 bytes of padding.
const START_ADDR: usize = 256;

/// Write the headers and padding bytes to `output`
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
    let start_virt_addr = u64::try_from(START_ADDR).unwrap_or_else(|_| unreachable!()) + load_vaddr;

    let Some(Ok(file_size)) = START_ADDR.checked_add(codesize).map(u64::try_from) else {
        return Err(BFCompileError::basic(
            BFErrorID::CodeTooLarge,
            "code too large to fit in 64-bit address space",
        ));
    };

    let ehdr = BinInfo {
        arch: elf_arch,
        entry: start_virt_addr,
        flags: e_flags,
    };
    let tape_segment = SegmentInfo {
        arch: elf_arch,
        flags: 6,         // PF_R | PF_W (readable and writable)
        vaddr: TAPE_ADDR, // load segment into this section of memory
        size: tape_size,  // allocate this many bytes of memory for this segment
        file_backed: false,
        align: 0x1000, // align with this power of 2
    };
    let code_segment = SegmentInfo {
        arch: elf_arch,
        flags: 5,          // PF_R | PF_X (readable and executable)
        vaddr: load_vaddr, // load segment into this section of memory
        size: file_size,   // load this many bytes from file…
        file_backed: true,
        align: 1, // align with this power of 2
    };
    let mut to_write = Vec::<u8>::from(ehdr);
    to_write.extend(Vec::<u8>::from(tape_segment));
    to_write.extend(Vec::<u8>::from(code_segment));

    // pad until start address
    to_write.resize(START_ADDR, 0);
    output.write_all(to_write.as_slice()).map_err(|e| {
        BFCompileError::basic(
            BFErrorID::FailedWrite,
            format!("Failed to write ELF header and program header table: {e:?}"),
        )
    })
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
        Self::set_reg(code_buf, Self::REGISTERS.arg1, fd).expect("stdin/stdout fds fit in regs");
        Self::reg_copy(code_buf, Self::REGISTERS.arg2, Self::REGISTERS.bf_ptr);
        Self::set_reg(code_buf, Self::REGISTERS.arg3, 1).expect("1 fits in regs");
        Self::syscall(code_buf, sc);
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
            // This comparison that a byte isn't a continuation byte within a UTF-8 multi-byte
            // sequence, so if it's either a new UTF-8 codepoint or invalid UTF-8, this will
            // increment the column counter, but it won't if it's a byte that's typically a
            // continuatio of a UTF-8 sequence
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
                let distance: i64 = (code_buf.len() - open_location.index).try_into().map_err(|_| BFCompileError::basic(BFErrorID::CodeTooLarge, "Jump distance exceeds 64-bit integer limit"))?;
                Self::jump_open(
                    code_buf,
                    open_location.index,
                    Self::REGISTERS.bf_ptr,
                    distance
                )?;
                Self::jump_close(code_buf, Self::REGISTERS.bf_ptr, -distance)?;
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

    /// Compile IR operations from `code`, writing machine code to `dst`
    fn compile_combined(
        dst: &mut Vec<u8>,
        code: Vec<CombinedInstruction>,
    ) -> Result<(), BFCompileError> {
        let mut jump_stack = Vec::new();
        #[rustfmt::skip]
        macro_rules! compile_as_bf {
            ($bf_instr: literal) => {{
                Self::compile_instr($bf_instr, dst, None, &mut jump_stack)
            }};
        }
        #[rustfmt::skip]
        macro_rules! compile_combined {
            ($inner_func: ident, $val: ident) => {{
                Self::$inner_func(dst, Self::REGISTERS.bf_ptr, $val)
            }};
        }
        for ir_instr in code {
            match ir_instr {
                CombinedInstruction::LoopOpen => compile_as_bf!(b'[')?,
                CombinedInstruction::LoopClose => compile_as_bf!(b']')?,
                CombinedInstruction::Read => compile_as_bf!(b',')?,
                CombinedInstruction::Write => compile_as_bf!(b'.')?,
                CombinedInstruction::Add(i) => compile_combined!(add_byte, i),
                CombinedInstruction::Sub(i) => compile_combined!(sub_byte, i),
                CombinedInstruction::MoveLeft(i) => compile_combined!(sub_reg, i)?,
                CombinedInstruction::MoveRight(i) => compile_combined!(add_reg, i)?,
                CombinedInstruction::SetCell(i) => Self::set_byte(dst, Self::REGISTERS.bf_ptr, i),
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
        #[cfg(all(have_32bit_targets, debug_assertions))]
        if Self::ARCH.ei_class() == ElfClass::ELFClass32 {
            debug_assert!(
                u32::try_from(tape_blocks * 0x1000).is_ok(),
                "tape size should've been validated during arg parsing"
            );
        }
        let mut jump_stack = Vec::<JumpLocation>::new();
        let mut loc = CodePosition { line: 1, col: 0 };
        let mut code_buf: Vec<u8> = Vec::new();
        Self::set_reg(&mut code_buf, Self::REGISTERS.bf_ptr, TAPE_ADDR.cast_signed())
            .expect("tape address fits in regs");
        let mut errs = Vec::<BFCompileError>::new();

        let reader = BufReader::new(in_f);

        if optimize {
            Self::compile_combined(
                &mut code_buf,
                combine_instructions(CodeReader::new(reader))?,
            )?;
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
        Self::set_reg(&mut code_buf, Self::REGISTERS.arg1, 0).expect("0 fits in regs");
        Self::syscall(&mut code_buf, Self::SC_NUMS.exit);

        let code_sz = code_buf.len();
        if let Err(e) = write_headers(&mut out_f, code_sz, tape_blocks, Self::ARCH, Self::E_FLAGS) {
            errs.push(e);
        }
        if let Err(e) = out_f.write_all(code_buf.as_slice()) {
            errs.push(BFCompileError::basic(
                BFErrorID::FailedWrite,
                format!("Failed to write internal code buffer to output file: {e:?}"),
            ));
        }
        if errs.is_empty() { Ok(()) } else { Err(errs) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[cfg(eambfc_default_arch = "arm64")]
    use backends::Arm64Inter as TestInter;
    #[cfg(eambfc_default_arch = "i386")]
    use backends::I386Inter as TestInter;
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
                Err(io::Error::other(
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
                b">>[-]".as_slice(),
                FailingWriter {
                    fail_after: START_ADDR + 1
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
                    fail_after: START_ADDR
                },
                true,
                8
            )
            .is_err_and(|e| e[0].error_id() == BFErrorID::FailedWrite)
        );
    }
}
