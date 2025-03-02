// SPDX-FileCopyrightText: 2024 - 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

#![cfg_attr(
    all(not(test), feature = "longopts"),
    expect(unused_imports, reason = "Used without longopts")
)]
use crate::compile::elf_tools::ElfArch;
use crate::err::{BFCompileError, BFErrorID};
use crate::OutMode;
use std::convert::{TryFrom, TryInto};
use std::ffi::OsString;
#[cfg(unix)]
use std::os::unix::ffi::{OsStrExt, OsStringExt};
#[cfg(target_os = "wasi")]
use std::os::wasi::ffi::{OsStrExt, OsStringExt};
#[cfg(feature = "longopts")]
pub(crate) mod longopts;

#[derive(PartialEq, Debug)]
pub(crate) struct StandardRunConfig {
    pub out_mode: OutMode,
    pub optimize: bool,
    pub keep: bool,
    pub cont: bool,
    pub tape_blocks: u64,
    pub extension: OsString,
    pub source_files: Vec<OsString>,
    pub out_suffix: Option<OsString>,
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
    out_suffix: Option<OsString>,
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
            out_suffix,
            arch,
        } = pcfg;

        if extension.as_deref().or(Some(".bf".as_ref())) == out_suffix.as_deref() {
            return Err((
                BFCompileError::basic(
                    BFErrorID::InputIsOutput,
                    "Extension can't be the same as output suffix",
                ),
                out_mode,
            ));
        }
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
            out_suffix,
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
                ));
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
            return Err(self.gen_err(BFErrorID::MultipleArchitectures, "passed -a multiple times"));
        }
        self.arch = match param {
            #[cfg(feature = "arm64")]
            b"arm64" | b"aarch64" => Some(ElfArch::Arm64),
            #[cfg(feature = "riscv64")]
            b"riscv64" | b"riscv" => Some(ElfArch::RiscV64),
            #[cfg(feature = "s390x")]
            b"s390x" | b"s390" | b"z/architecture" => Some(ElfArch::S390x),
            #[cfg(feature = "x86_64")]
            b"x86_64" | b"x64" | b"amd64" | b"x86-64" => Some(ElfArch::X86_64),
            f => {
                return Err((
                    BFCompileError::basic(
                        BFErrorID::UnknownArch,
                        format!("{} is not a recognized architecture", f.escape_ascii()),
                    ),
                    self.out_mode,
                ));
            }
        };
        Ok(())
    }

    #[cfg(any(unix, target_os = "wasi"))]
    fn set_ext(&mut self, param: Vec<u8>) -> Result<(), (BFCompileError, OutMode)> {
        if self.extension.is_none() {
            self.extension = Some(OsString::from_vec(param));
            Ok(())
        } else {
            Err(self.gen_err(BFErrorID::MultipleExtensions, "passed -e multiple times"))
        }
    }

    #[cfg(not(tarpaulin_include))]
    #[cfg(not(any(unix, target_os = "wasi")))]
    fn set_ext(&mut self, param: Vec<u8>) -> Result<(), (BFCompileError, OutMode)> {
        if self.extension.is_some() {
            return Err(self.gen_err(BFErrorID::MultipleExtensions, "passed -e multiple times"));
        }
        if let Ok(s) = String::from_utf8(param) {
            self.extension = Some(OsString::from(s));
            Ok(())
        } else {
            Err(self.gen_err(
                BFErrorID::NonUTF8,
                "Can't handle non-unicode file extensions on non-unix platforms",
            ))
        }
    }

    fn set_suffix(&mut self, suf: Vec<u8>) -> Result<(), (BFCompileError, OutMode)> {
        if self.out_suffix.is_none() {
            #[cfg(any(unix, target_os = "wasi"))]
            {
                self.out_suffix = Some(OsString::from_vec(suf));
            };
            #[cfg(not(tarpaulin_include))]
            #[cfg(not(any(unix, target_os = "wasi")))]
            {
                self.out_suffix = Some(
                    String::from_utf8(suf)
                        .map_err(|_| {
                            self.gen_err(
                                BFErrorID::NonUTF8,
                                "Can't handle non-Unicode suffixes on non-unix platforms",
                            )
                        })?
                        .into(),
                );
            };
            Ok(())
        } else {
            Err(self.gen_err(
                BFErrorID::MultipleOutputExtensions,
                "passed -s multiple times",
            ))
        }
    }

    fn set_tape_size(&mut self, param: Vec<u8>) -> Result<(), (BFCompileError, OutMode)> {
        use std::str::FromStr;
        if self.tape_blocks.is_some() {
            return Err(self.gen_err(
                BFErrorID::MultipleTapeBlockCounts,
                "passed -t multiple times",
            ));
        }
        let Ok(Ok(tape_size)) = String::from_utf8(param).map(|s| u64::from_str(&s)) else {
            return Err(self.gen_err(
                BFErrorID::TapeSizeNotNumeric,
                "tape size could not be parsed as a numeric value",
            ));
        };
        match tape_size {
            0 => Err(self.gen_err(
                BFErrorID::TapeSizeZero,
                "Tape value for -t must be at least 1",
            )),
            i if i >= u64::MAX >> 12 => Err(self.gen_err(
                BFErrorID::TapeTooLarge,
                "tape size exceeds 64-bit integer limit",
            )),
            i => {
                self.tape_blocks = Some(i);
                Ok(())
            }
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

#[cfg(any(test, not(feature = "longopts")))]
pub(crate) fn parse_args<T: Iterator<Item = OsString>>(
    mut args: T,
) -> Result<RunConfig, (BFCompileError, OutMode)> {
    let mut pcfg = PartialRunConfig::default();

    while let Some(arg) = args.next() {
        #[cfg(not(tarpaulin_include))]
        #[cfg(not(any(unix, target_os = "wasi")))]
        let arg = arg.into_string().map_err(|a| {
            pcfg.gen_err(
                BFErrorID::NonUTF8,
                format!("Non-Unicode argument {:?} provided", a.to_string_lossy()),
            )
        })?;
        // handle non-flag values
        if arg == "--" {
            pcfg.source_files = Some(args.collect());
            break;
        }
        let arg_bytes = arg.as_bytes();
        if arg_bytes[0] != b'-' {
            #[cfg_attr(
                any(unix, target_os = "wasi"),
                expect(clippy::useless_conversion, reason = "not useless on other targets")
            )]
            let mut source_files: Vec<OsString> = vec![arg.into()];
            source_files.extend(args);
            pcfg.source_files = Some(source_files);
            break;
        }

        let mut arg_byte_iter = arg_bytes[1..].iter().copied();

        while let Some(b) = arg_byte_iter.next() {
            match b {
                b'h' => return Ok(RunConfig::ShowHelp),
                b'V' => return Ok(RunConfig::ShowVersion),
                b'A' => return Ok(RunConfig::ListArches),
                p if b"aest".contains(&p) => {
                    let mut remainder: Vec<u8> = arg_byte_iter.collect();
                    if remainder.is_empty() {
                        if let Some(next_arg) = args.next() {
                            #[cfg(any(unix, target_os = "wasi"))]
                            remainder.extend_from_slice(next_arg.as_bytes());
                            #[cfg(not(tarpaulin_include))]
                            #[cfg(not(any(unix, target_os = "wasi")))]
                            remainder.extend(
                                next_arg
                                    .into_string()
                                    .map_err(|a| {
                                        pcfg.gen_err(
                                            BFErrorID::NonUTF8,
                                            format!(
                                                "Non-Unicode argument {:?} provided",
                                                a.to_string_lossy()
                                            ),
                                        )
                                    })?
                                    .into_bytes(),
                            );
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
                        b's' => pcfg.set_suffix(remainder)?,
                        b't' => pcfg.set_tape_size(remainder)?,
                        _ => unreachable!(),
                    }
                    break;
                }
                flag => pcfg.parse_standalone_flag(flag)?,
            }
        }
    }
    Ok(RunConfig::StandardRun(pcfg.try_into()?))
}

#[cfg(test)]
mod tests;
