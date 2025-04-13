// SPDX-FileCopyrightText: 2024 - 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

#![cfg_attr(
    all(not(test), feature = "longopts"),
    expect(unused_imports, reason = "Used without longopts")
)]
use crate::OutMode;
use crate::compile::backends::Backend;
use crate::err::{BFCompileError, BFErrorID};
use std::convert::{TryFrom, TryInto};
use std::ffi::{OsStr, OsString};
#[cfg(unix)]
use std::os::unix::ffi::{OsStrExt, OsStringExt};
#[cfg(target_os = "wasi")]
use std::os::wasi::ffi::{OsStrExt, OsStringExt};
#[cfg(feature = "longopts")]
pub(crate) mod longopts;

mod help_text;
pub use help_text::help_fmt;

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
    pub arch: Backend,
}

#[derive(Default)]
struct PartialRunConfig {
    out_mode: OutMode,
    optimize: bool,
    keep: bool,
    cont: bool,
    tape_blocks: Option<u64>,
    extension: Option<OsString>,
    source_files: Vec<OsString>,
    out_suffix: Option<OsString>,
    arch: Option<Backend>,
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
        if source_files.is_empty() {
            return Err((
                BFCompileError::basic(BFErrorID::NoSourceFiles, "No source files provided"),
                out_mode,
            ));
        }
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
    #[cfg(any(not(feature = "longopts"), test))]
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
                        format!("'-{}' is not a recognized argument", bad_arg.escape_ascii()),
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

    fn set_arch(&mut self, param: &OsStr) -> Result<(), (BFCompileError, OutMode)> {
        if self.arch.is_some() {
            return Err(self.gen_err(BFErrorID::MultipleArchitectures, "passed -a multiple times"));
        }
        self.arch = Some(
            param
                .to_string_lossy()
                .parse()
                .map_err(|e| (e, self.out_mode))?,
        );
        Ok(())
    }

    fn set_ext(&mut self, param: OsString) -> Result<(), (BFCompileError, OutMode)> {
        #[cfg(not(any(unix, target_os = "wasi")))]
        if !cfg!(any(unix, target_os = "wasi")) {
            let start = param
                .as_encoded_bytes()
                .utf8_chunks()
                .next()
                .expect("Non-empty suffix");
            if start.valid().is_empty() {
                return Err(self.gen_err(
                    BFErrorID::NonUTF8,
                    "Can't handle extension with non-unicode start",
                ));
            }
        }
        if self.extension.is_none() {
            self.extension = Some(param);
            Ok(())
        } else {
            Err(self.gen_err(BFErrorID::MultipleExtensions, "passed -e multiple times"))
        }
    }

    fn set_suffix(&mut self, suf: OsString) -> Result<(), (BFCompileError, OutMode)> {
        if self.out_suffix.is_none() {
            self.out_suffix = Some(suf);
            Ok(())
        } else {
            Err(self.gen_err(
                BFErrorID::MultipleOutputExtensions,
                "passed -s multiple times",
            ))
        }
    }

    fn set_tape_size(&mut self, param: OsString) -> Result<(), (BFCompileError, OutMode)> {
        use std::str::FromStr;
        if self.tape_blocks.is_some() {
            return Err(self.gen_err(
                BFErrorID::MultipleTapeBlockCounts,
                "passed -t multiple times",
            ));
        }
        let Ok(Ok(tape_size)) = param.into_string().map(|s| u64::from_str(&s)) else {
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
        // handle non-flag values
        if arg == "--" {
            pcfg.source_files.extend(args);
            break;
        }
        let arg_bytes: &[u8];
        #[cfg(any(unix, target_os = "wasi"))]
        {
            arg_bytes = arg.as_bytes();
        };
        #[cfg(not(any(unix, target_os = "wasi")))]
        {
            arg_bytes = arg.as_encoded_bytes();
        };
        if arg_bytes[0] != b'-' {
            pcfg.source_files.push(arg);
            continue;
        }

        let mut arg_byte_iter = arg_bytes[1..].iter().copied();

        while let Some(b) = arg_byte_iter.next() {
            match b {
                b'h' => return Ok(RunConfig::ShowHelp),
                b'V' => return Ok(RunConfig::ShowVersion),
                b'A' => return Ok(RunConfig::ListArches),
                b'a' | b'e' | b's' | b't' => {
                    let mut remainder: OsString;
                    #[cfg(any(unix, target_os = "wasi"))]
                    {
                        remainder = OsString::from_vec(arg_byte_iter.collect());
                    };
                    #[cfg(not(any(unix, target_os = "wasi")))]
                    {
                        // SAFETY: if this point is reached, then only ASCII characters will
                        // have been encountered, as all recognized arguments are ASCII, and
                        // non-ASCII characters would thus have triggered an UnknownArg error.
                        //
                        // Because of this, the fact that OsString encodings are a superset of
                        // UTF-8 where the non-UTF-8 chunks are opaque but the UTF-8 chunks
                        // aren't, and the fact that UTF-8 is a superset of ASCII, the
                        // remaining bytes are definitely valid OsString encoding bytes.
                        remainder = unsafe {
                            OsString::from_encoded_bytes_unchecked(arg_byte_iter.collect())
                        };
                    };
                    if remainder.is_empty() {
                        remainder = args.next().ok_or_else(|| {
                            pcfg.gen_err(
                                BFErrorID::MissingOperand,
                                format!("-{} requires an additional argument", char::from(b)),
                            )
                        })?;
                    }
                    match b {
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
mod tests {
    use super::*;

    // a more concise way to write OsString::from(a)
    #[cfg(not(tarpaulin_include))]
    fn arg(a: impl Into<OsString>) -> OsString {
        a.into()
    }

    // extract a standard run config
    #[cfg(not(tarpaulin_include))]
    fn parse_standard(args: Vec<OsString>) -> StandardRunConfig {
        let RunConfig::StandardRun(cfg) = parse_args(args.into_iter()).unwrap() else {
            panic!("test expected StandardRunConfig")
        };
        cfg
    }

    #[test]
    fn combined_args() {
        // ensure that combined arguments are processed properly
        let args_set_0 = vec![
            // should be interpreted identically to -k -j -e .brainfuck'
            arg("-kje.brainfuck"),
            arg("foo.brainfuck"),
            arg("bar.brainfuck"),
        ]
        .into_iter();
        let args_set_1 = vec![
            // should be interpreted identically to -kje.brainfuck'
            arg("-k"),
            arg("-j"),
            arg("-e"),
            arg(".brainfuck"),
            arg("foo.brainfuck"),
            arg("bar.brainfuck"),
        ]
        .into_iter();

        assert_eq!(
            parse_args(args_set_0).unwrap(),
            parse_args(args_set_1).unwrap()
        );
    }

    #[test]
    fn options_stop_on_double_dash() {
        let args_set = vec![arg("--"), arg("-j"), arg("-h"), arg("-e.notbf")];
        // ensure that -h, -j and -e.notbf are interpreted as the list of file names
        let parsed_args = parse_standard(args_set);
        assert_eq!(parsed_args.out_mode, OutMode::Basic);
        assert_eq!(
            parsed_args.source_files,
            vec![arg("-j"), arg("-h"), arg("-e.notbf"),]
        );
    }

    #[test]
    fn options_can_mix_with_files() {
        // ensure that -O isn't interpreted as a file name
        assert_eq!(
            parse_standard(vec![arg("e.bf"), arg("-O")]).source_files,
            vec![arg("e.bf")]
        );
    }

    #[test]
    fn help_returned() {
        let args_set = vec![arg("-h")].into_iter();
        assert_eq!(parse_args(args_set), Ok(RunConfig::ShowHelp));
    }

    #[test]
    fn version_returned() {
        let args_set = vec![arg("-V")].into_iter();
        assert_eq!(parse_args(args_set), Ok(RunConfig::ShowVersion));
    }

    #[test]
    fn handle_empty_args() {
        let (bf_err, _) = parse_args(vec![].into_iter()).unwrap_err();
        assert_eq!(bf_err.error_id(), BFErrorID::NoSourceFiles);
    }

    #[test]
    fn non_numeric_tape_size() {
        let (err, ..) = parse_args(vec![arg("-t"), arg("###")].into_iter()).unwrap_err();
        assert_eq!(err.error_id(), BFErrorID::TapeSizeNotNumeric);
    }

    #[test]
    fn multiple_tape_size() {
        let args_set = vec![arg("-t1"), arg("-t1024")].into_iter();
        let (err, ..) = parse_args(args_set).unwrap_err();
        assert_eq!(err.error_id(), BFErrorID::MultipleTapeBlockCounts);
    }

    #[test]
    fn tape_size_zero() {
        let args_set = vec![arg("-t0")].into_iter();
        let (err, ..) = parse_args(args_set).unwrap_err();
        assert_eq!(err.error_id(), BFErrorID::TapeSizeZero);
    }

    #[test]
    fn tape_too_large() {
        let args_set = vec![arg("-t9223372036854775807")].into_iter();
        let (err, ..) = parse_args(args_set).unwrap_err();
        assert_eq!(err.error_id(), BFErrorID::TapeTooLarge);
    }

    #[test]
    fn missing_operand() {
        let args_set = vec![arg("-t")].into_iter();
        let (err, ..) = parse_args(args_set).unwrap_err();
        assert_eq!(err.error_id(), BFErrorID::MissingOperand);
        let args_set = vec![arg("-e")].into_iter();
        let (err, ..) = parse_args(args_set).unwrap_err();
        assert_eq!(err.error_id(), BFErrorID::MissingOperand);
        let args_set = vec![arg("-a")].into_iter();
        let (err, ..) = parse_args(args_set).unwrap_err();
        assert_eq!(err.error_id(), BFErrorID::MissingOperand);
    }

    #[test]
    fn out_mode_options() {
        assert_eq!(
            parse_standard(vec![arg("-q"), arg("f.bf")]).out_mode,
            OutMode::Quiet
        );
        assert_eq!(
            parse_standard(vec![arg("-j"), arg("f.bf")]).out_mode,
            OutMode::Json
        );
        assert_eq!(
            parse_standard(vec![arg("-qj"), arg("f.bf")]).out_mode,
            OutMode::Json
        );
        assert_eq!(
            parse_standard(vec![arg("-jq"), arg("f.bf")]).out_mode,
            OutMode::Json
        );
    }

    #[test]
    fn single_args_parsed() {
        let args = parse_standard(vec![arg("-Ok"), arg("foo.bf")]);
        assert!(args.keep && args.optimize && !args.cont,);
        let args = parse_standard(vec![arg("-Ok"), arg("-c"), arg("foo.bf")]);
        assert!(args.keep && args.optimize && args.cont,);
        let args = parse_standard(vec![arg("-c"), arg("foo.bf")]);
        assert!(args.cont && !args.optimize && !args.keep,);
        let args = parse_standard(vec![arg("-Oc"), arg("foo.bf")]);
        assert!(args.cont && args.optimize && !args.keep,);
        let args = parse_standard(vec![arg("-kOccOk"), arg("foo.bf")]);
        assert!(args.keep && args.optimize && args.cont,);
        let args = parse_standard(vec![arg("foo.bf")]);
        assert!(!args.keep && !args.optimize && !args.cont,);
    }

    #[test]
    fn multiple_extensions_err() {
        assert!(
            parse_args(vec![arg("-e.brainfuck"), arg("-e"), arg(".bf")].into_iter())
                .is_err_and(|e| e.0.error_id() == BFErrorID::MultipleExtensions)
        );
    }

    #[test]
    fn bad_args_error_out() {
        assert!(
            parse_args(vec![arg("-u")].into_iter())
                .is_err_and(|e| e.0.error_id() == BFErrorID::UnknownArg)
        );
    }

    #[test]
    fn list_arch_processed() {
        assert_eq!(
            parse_args(vec![arg("-A")].into_iter()),
            Ok(RunConfig::ListArches)
        );
        assert_eq!(
            parse_args(vec![arg("-e"), arg(".b"), arg("-A")].into_iter()),
            Ok(RunConfig::ListArches)
        );
    }

    macro_rules! test_arch_args {
        ($arch: literal, $backend: ident, $($aliases: literal),*) => {
            for arch_id in [$arch, $($aliases,)*] {
                if cfg!(feature = $arch) {
                    #[cfg(feature = $arch)]
                    {
                        assert_eq!(
                            parse_standard(vec![arg("-a"), arg(arch_id), arg("foo.bf")]).arch,
                            Backend::$backend
                        );
                    }
                } else {
                    assert!(
                        parse_args(vec![arg("-a"), arg(arch_id), arg("foo.bf")].into_iter())
                            .is_err_and(|e| e.0.error_id() == BFErrorID::UnknownArch)
                    );
                }
            }
       }
    }

    #[test]
    fn arch_selection() {
        test_arch_args!("arm64", Arm64, "aarch64");
        test_arch_args!("i386", I386, "i486", "i586", "i686", "x86");
        test_arch_args!("riscv64", RiscV64, "riscv");
        test_arch_args!("s390x", S390x, "s390", "z/architecture");
        test_arch_args!("x86_64", X86_64, "x64", "amd64", "x86-64");
        assert!(
            parse_args(vec![arg("-apdp11"), arg("foo.bf")].into_iter())
                .is_err_and(|e| e.0.error_id() == BFErrorID::UnknownArch)
        );
    }

    #[test]
    fn multiple_arches_error() {
        if cfg!(all(feature = "x86_64", feature = "arm64")) {
            assert!(
                parse_args(vec![arg("-ax86_64"), arg("-aarm64"), arg("foo.bf")].into_iter())
                    .is_err_and(|e| e.0.error_id() == BFErrorID::MultipleArchitectures)
            );
        }
    }
}
