// SPDX-FileCopyrightText: 2024 - 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use crate::compile::elf_tools::ElfArch;
use crate::err::{BFCompileError, BFErrorID};
use crate::OutMode;
use std::convert::{TryFrom, TryInto};
use std::ffi::OsString;
use std::os::unix::ffi::{OsStrExt, OsStringExt};

#[derive(PartialEq, Debug)]
pub(crate) struct StandardRunConfig {
    pub out_mode: OutMode,
    pub optimize: bool,
    pub keep: bool,
    pub cont: bool,
    pub tape_blocks: u64,
    pub extension: OsString,
    pub source_files: Vec<OsString>,
    pub arch: ElfArch,
}

#[derive(Default)]
struct PartialRunConfig {
    out_mode: OutMode,
    optimize: bool,
    keep: bool,
    cont: bool,
    tape_blocks: Option<u64>,
    extension: Option<OsString>,
    source_files: Option<Vec<OsString>>,
    arch: Option<ElfArch>,
}

impl TryFrom<PartialRunConfig> for StandardRunConfig {
    type Error = (BFCompileError, OutMode);
    fn try_from(pcfg: PartialRunConfig) -> Result<Self, Self::Error> {
        let PartialRunConfig {
            out_mode,
            optimize,
            keep,
            cont,
            tape_blocks,
            extension,
            source_files,
            arch,
        } = pcfg;
        let source_files = source_files.ok_or((
            BFCompileError::basic(BFErrorID::NoSourceFiles, "No source files provided"),
            out_mode,
        ))?;
        Ok(StandardRunConfig {
            out_mode,
            optimize,
            keep,
            cont,
            tape_blocks: tape_blocks.unwrap_or(8),
            extension: extension.unwrap_or(".bf".into()),
            source_files,
            arch: arch.unwrap_or_default(),
        })
    }
}

impl PartialRunConfig {
    fn parse_standalone_flag(&mut self, flag: u8) -> Result<(), (BFCompileError, OutMode)> {
        match flag {
            b'j' => self.out_mode.json(),
            b'q' => self.out_mode.quiet(),
            b'O' => self.optimize = true,
            b'k' => self.keep = true,
            b'c' => self.cont = true,
            bad_arg => {
                return Err((
                    BFCompileError::basic(
                        BFErrorID::UnknownArg,
                        format!("'{}' is not a recognized argument", bad_arg.escape_ascii()),
                    ),
                    self.out_mode,
                ))
            }
        }
        Ok(())
    }

    fn gen_err(
        &self,
        kind: BFErrorID,
        msg: impl Into<std::borrow::Cow<'static, str>>,
    ) -> (BFCompileError, OutMode) {
        (BFCompileError::basic(kind, msg), self.out_mode)
    }

    fn set_arch(&mut self, param: &[u8]) -> Result<(), (BFCompileError, OutMode)> {
        if self.arch.is_some() {
            return Err(self.gen_err(BFErrorID::MultipleArches, "passed -a multiple times"));
        }
        self.arch = match param {
            #[cfg(feature = "x86_64")]
            b"x86_64" | b"x64" | b"amd64" | b"x86-64" => Some(ElfArch::X86_64),
            #[cfg(feature = "arm64")]
            b"arm64" | b"aarch64" => Some(ElfArch::Arm64),
            #[cfg(feature = "s390x")]
            b"s390x" | b"s390" | b"z/architecture" => Some(ElfArch::S390x),
            f => {
                return Err((
                    BFCompileError::basic(
                        BFErrorID::UnknownArch,
                        format!("{} is not a recognized architecture", f.escape_ascii()),
                    ),
                    self.out_mode,
                ))
            }
        };
        Ok(())
    }

    fn set_ext(&mut self, param: Vec<u8>) -> Result<(), (BFCompileError, OutMode)> {
        if self.extension.is_some() {
            return Err(self.gen_err(BFErrorID::MultipleExtensions, "passed -e multiple times"));
        }
        self.extension = Some(OsString::from_vec(param));
        Ok(())
    }

    fn set_tape_size(&mut self, param: Vec<u8>) -> Result<(), (BFCompileError, OutMode)> {
        if self.tape_blocks.is_some() {
            return Err(self.gen_err(
                BFErrorID::MultipleTapeBlockCounts,
                "passed -t multiple times",
            ));
        }
        match OsString::from_vec(param).to_string_lossy().parse::<u64>() {
            Ok(0) => Err((
                BFCompileError::basic(BFErrorID::NoTape, "Tape value for -t must be at least 1"),
                self.out_mode,
            )),
            Ok(i) if i >= u64::MAX >> 12 => Err((
                BFCompileError::basic(
                    BFErrorID::TapeTooLarge,
                    "tape size exceeds 64-bit integer limit",
                ),
                self.out_mode,
            )),
            Ok(i) => {
                self.tape_blocks = Some(i);
                Ok(())
            }
            Err(_) => Err((
                BFCompileError::basic(
                    BFErrorID::NotNumeric,
                    "tape size could not be parsed as a numeric value",
                ),
                self.out_mode,
            )),
        }
    }
}

#[derive(PartialEq, Debug)]
pub(crate) enum RunConfig {
    StandardRun(StandardRunConfig),
    ShowHelp,
    ShowVersion,
    ListArches,
}

pub(crate) fn parse_args<T: Iterator<Item = OsString>>(
    mut args: T,
) -> Result<RunConfig, (BFCompileError, OutMode)> {
    let mut pcfg = PartialRunConfig::default();

    while let Some(arg) = args.next() {
        // handle non-flag values
        if arg == "--" {
            pcfg.source_files = Some(args.collect());
            break;
        }
        let arg_bytes = arg.into_vec();
        if arg_bytes[0] != b'-' {
            let mut sf = vec![OsString::from_vec(arg_bytes)];
            sf.extend(args);
            pcfg.source_files = Some(sf);
            break;
        }

        let mut arg_byte_iter = arg_bytes.into_iter().skip(1);

        while let Some(b) = arg_byte_iter.next() {
            match b {
                b'h' => return Ok(RunConfig::ShowHelp),
                b'V' => return Ok(RunConfig::ShowVersion),
                b'A' => return Ok(RunConfig::ListArches),
                p if b"aet".contains(&p) => {
                    let mut remainder: Vec<u8> = arg_byte_iter.collect();
                    if remainder.is_empty() {
                        if let Some(next_arg) = args.next() {
                            remainder.extend_from_slice(next_arg.as_bytes());
                        } else {
                            return Err(pcfg.gen_err(
                                BFErrorID::MissingOperand,
                                format!("-{} requires an additional argument", p.escape_ascii()),
                            ));
                        }
                    }
                    match p {
                        b'a' => pcfg.set_arch(&remainder)?,
                        b'e' => pcfg.set_ext(remainder)?,
                        b't' => pcfg.set_tape_size(remainder)?,
                        _ => unreachable!(),
                    }
                    break;
                }
                flag => pcfg.parse_standalone_flag(flag)?,
            };
        }
    }
    Ok(RunConfig::StandardRun(pcfg.try_into()?))
}

#[cfg(test)]
mod tests;
