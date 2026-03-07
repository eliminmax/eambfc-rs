// SPDX-FileCopyrightText: 2024 - 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use crate::OutMode;
use crate::compile::backends::{Backend, BackendParseErr};
use std::borrow::Cow;
use std::convert::{TryFrom, TryInto};
use std::ffi::{OsStr, OsString};
use std::num::NonZeroU64;
use std::path::PathBuf;

pub(crate) mod err;
use err::ArgParseError;

use crate::compile::ElfClass;
mod help_text;
pub use help_text::help_fmt;

#[derive(PartialEq, Debug)]
pub(crate) struct StandardRunConfig {
    pub out_mode: OutMode,
    pub optimize: bool,
    pub keep: bool,
    pub cont: bool,
    pub tape_blocks: u64,
    pub extension: Cow<'static, OsStr>,
    pub source_files: Vec<PathBuf>,
    pub out_suffix: Option<OsString>,
    pub arch: Backend,
}

#[allow(
    clippy::struct_excessive_bools,
    reason = "bools best represent toggleable switches"
)]
#[derive(Default)]
struct PartialRunConfig {
    json: bool,
    quiet: bool,
    optimize: bool,
    keep: bool,
    cont: bool,
    tape_blocks: Option<NonZeroU64>,
    extension: Option<OsString>,
    source_files: Vec<PathBuf>,
    out_suffix: Option<OsString>,
    arch: Option<Backend>,
}

impl TryFrom<PartialRunConfig> for StandardRunConfig {
    type Error = ArgParseError;
    fn try_from(pcfg: PartialRunConfig) -> Result<Self, Self::Error> {
        let PartialRunConfig {
            json,
            quiet,
            optimize,
            keep,
            cont,
            tape_blocks,
            extension,
            source_files,
            out_suffix,
            arch,
        } = pcfg;
        let out_mode = match (json, quiet) {
            (true, true) => return Err(ArgParseError::SetBothOutModes),
            (true, false) => OutMode::Json,
            (false, true) => OutMode::Quiet,
            (false, false) => OutMode::Basic,
        };

        let extension = extension.map_or(Cow::Borrowed(".bf".as_ref()), Cow::Owned);
        let out_suffix = {
            if let Some(out_suffix) = out_suffix {
                if out_suffix == extension {
                    return Err(ArgParseError::InputIsOutput(out_suffix));
                }
                Some(out_suffix)
            } else {
                None
            }
        };

        if source_files.is_empty() {
            return Err(ArgParseError::NoSourceFiles);
        }
        let arch = arch.unwrap_or_default();
        let tape_blocks = tape_blocks.map_or(8, NonZeroU64::get);

        let max_tape_blocks = match arch.ei_class() {
            #[cfg(have_32bit_targets)]
            ElfClass::ELFClass32 => const { (u32::MAX / 0x1000) as u64 },
            #[cfg(have_64bit_targets)]
            ElfClass::ELFClass64 => const { u64::MAX / 0x1000 },
        };

        if tape_blocks > max_tape_blocks {
            return Err(ArgParseError::TapeTooLarge {
                class: arch.ei_class(),
                tape_blocks,
            });
        }

        Ok(StandardRunConfig {
            out_mode,
            optimize,
            keep,
            cont,
            tape_blocks,
            extension,
            source_files,
            out_suffix,
            arch,
        })
    }
}

impl PartialRunConfig {
    fn set_arch(&mut self, param: OsString) -> Result<(), ArgParseError> {
        let backend = if let Some(s) = param.to_str() {
            s.parse().map_err(|e| match e {
                #[cfg(not(have_all_targets))]
                BackendParseErr::DisabledBackend(db) => ArgParseError::DisabledBackend(db),
                BackendParseErr::UnknownBackend => ArgParseError::UnknownBackend(param),
            })
        } else {
            Err(ArgParseError::UnknownBackend(param))
        }?;
        if let Some(old) = self.arch {
            return Err(ArgParseError::MultipleArchitectures(old, backend));
        }
        self.arch = Some(backend);
        Ok(())
    }

    fn set_ext(&mut self, ext: OsString) -> Result<(), ArgParseError> {
        if let Some(old_ext) = self.extension.take() {
            return Err(ArgParseError::MultipleExtensions(old_ext, ext));
        }
        self.extension = Some(ext);
        Ok(())
    }

    fn set_suffix(&mut self, suf: OsString) -> Result<(), ArgParseError> {
        if let Some(old_suf) = self.out_suffix.take() {
            return Err(ArgParseError::MultipleOutputExtensions(old_suf, suf));
        }
        self.out_suffix = Some(suf);
        Ok(())
    }

    fn set_tape_size(&mut self, param: OsString) -> Result<(), ArgParseError> {
        let Some(p) = param.to_str() else {
            return Err(ArgParseError::TapeSizeNotNumeric(param));
        };
        let tape_size = match p.parse() {
            Ok(ts) => ts,
            Err(err) => return Err(ArgParseError::from_bad_tape_size(&err, param)),
        };

        if let Some(old_size) = self.tape_blocks
            && old_size != tape_size
        {
            return Err(ArgParseError::MultipleTapeSizes(
                old_size.get(),
                tape_size.get(),
            ));
        }
        self.tape_blocks = Some(tape_size);
        Ok(())
    }
}

#[derive(PartialEq, Debug)]
pub(crate) enum RunConfig {
    StandardRun(StandardRunConfig),
    ShowHelp,
    ShowVersion,
    ListArches,
}

pub(crate) fn parse_args(args: impl Iterator<Item = OsString>) -> Result<RunConfig, ArgParseError> {
    let mut args = args;
    let mut cfg = PartialRunConfig::default();

    while let Some(arg) = args.next() {
        match arg.as_encoded_bytes() {
            b"--" => {
                cfg.source_files.extend(args.map(PathBuf::from));
                break;
            }
            longopt @ [b'-', b'-', ..] => {
                let (opt, operand) = if let Some(i) = longopt.iter().position(|i| *i == b'=') {
                    // SAFETY: This function's safety documentation states that the encoded bytes
                    // can be split right before or right after a non-empty UTF-8 byte sequence,
                    // and &longopt[i..i + 1] is &[b'='], which is one such sequence.
                    let operand = unsafe { OsStr::from_encoded_bytes_unchecked(&longopt[i + 1..]) };
                    (&longopt[2..i], Some(operand))
                } else {
                    (&longopt[2..], None)
                };

                macro_rules! fail_with_operand {
                    ($action: stmt) => {{
                        if let Some(operand) = operand.map(OsStr::to_owned) {
                            return Err(ArgParseError::UnexpectedOperand { arg, operand });
                        }
                        $action
                    }};
                }

                macro_rules! pass_operand_to {
                    ($method: ident) => {
                        if let Some(o) = operand.map(OsStr::to_owned).or_else(|| args.next()) {
                            cfg.$method(o)
                        } else {
                            return Err(ArgParseError::MissingOperand(arg));
                        }
                    };
                }
                match opt {
                    b"help" => fail_with_operand!(return Ok(RunConfig::ShowHelp)),
                    b"version" => fail_with_operand!(return Ok(RunConfig::ShowVersion)),
                    b"list-targets" => {
                        fail_with_operand!(return Ok(RunConfig::ListArches));
                    }
                    b"json" => fail_with_operand!(cfg.json = true),
                    b"quiet" => fail_with_operand!(cfg.quiet = true),
                    b"optimize" => fail_with_operand!(cfg.optimize = true),
                    b"keep" | b"keep-failed" => fail_with_operand!(cfg.keep = true),
                    b"continue" => fail_with_operand!(cfg.cont = true),
                    b"target-arch" => pass_operand_to!(set_arch)?,
                    b"tape-size" => pass_operand_to!(set_tape_size)?,
                    b"source-extension" => pass_operand_to!(set_ext)?,
                    b"output-suffix" => pass_operand_to!(set_suffix)?,
                    _ => return Err(ArgParseError::UnknownLongOption(arg)),
                }
            }
            [b'-', shortopts @ ..] => {
                if shortopts.is_empty() {
                    return Err(ArgParseError::SingleDashArg);
                }
                let mut byte_iter = shortopts.iter().copied();
                macro_rules! use_method {
                    ($method: ident, $loop: tt) => {{
                        let operand: Vec<u8> = byte_iter.collect();
                        let operand = if !operand.is_empty() {
                            // SAFETY: the encoded bytes can be split before or after a non-UTF-8
                            // sequence. All valid arguments are ASCII (and thus UTF-8) letters,
                            // so this splits after a dash and any number of ASCII letters.
                            unsafe { OsString::from_encoded_bytes_unchecked(operand) }
                        } else if let Some(o) = args.next() {
                            o
                        } else {
                            return Err(ArgParseError::MissingOperand(arg));
                        };
                        cfg.$method(operand)?;
                        break $loop;
                    }};
                }

                'l: while let Some(b) = byte_iter.next() {
                    match b {
                        b'h' => return Ok(RunConfig::ShowHelp),
                        b'V' => return Ok(RunConfig::ShowVersion),
                        b'A' => return Ok(RunConfig::ListArches),
                        b'q' => cfg.quiet = true,
                        b'j' => cfg.json = true,
                        b'O' => cfg.optimize = true,
                        b'k' => cfg.keep = true,
                        b'c' => cfg.cont = true,
                        b't' => use_method!(set_tape_size, 'l),
                        b'e' => use_method!(set_ext, 'l),
                        b's' => use_method!(set_suffix, 'l),
                        b'a' => use_method!(set_arch, 'l),
                        _ => return Err(ArgParseError::UnknownShortOption(b)),
                    }
                }
            }
            _ => cfg.source_files.push(arg.into()),
        }
    }

    Ok(RunConfig::StandardRun(cfg.try_into()?))
}

#[cfg(test)]
mod tests {

    trait UnwrapStandard {
        fn unwrap_standard_cfg(self) -> StandardRunConfig;
    }

    #[cfg(not(tarpaulin_include))]
    impl UnwrapStandard for Result<RunConfig, ArgParseError> {
        fn unwrap_standard_cfg(self) -> StandardRunConfig {
            self.unwrap().unwrap_standard_cfg()
        }
    }

    #[cfg(not(tarpaulin_include))]
    impl UnwrapStandard for RunConfig {
        fn unwrap_standard_cfg(self) -> StandardRunConfig {
            let RunConfig::StandardRun(cfg) = self else {
                panic!("test expected StandardRunConfig")
            };
            cfg
        }
    }
    use super::*;

    // a more concise way to write OsString::from(a)
    #[cfg(not(tarpaulin_include))]
    fn arg(a: impl Into<OsString>) -> OsString {
        a.into()
    }

    macro_rules! args {
        [$($arg: expr),*] => {
            vec![$(OsString::from($arg)),*].into_iter()
        };
        [$($arg: expr),*,] => {
            vec![$(OsString::from($arg)),*].into_iter()
        };
    }

    #[test]
    fn combined_args() {
        // ensure that combined arguments are processed properly

        // should be interpreted identically to -k -j -e .brainfuck'
        let args_set_0 = args!["-kje.brainfuck", "foo.brainfuck", "bar.brainfuck"];

        // should be interpreted identically to -kje.brainfuck'
        let args_set_1 = args![
            "-k",
            "-j",
            "-e",
            ".brainfuck",
            "foo.brainfuck",
            "bar.brainfuck",
        ];

        assert_eq!(
            parse_args(args_set_0).unwrap(),
            parse_args(args_set_1).unwrap()
        );
    }

    #[test]
    fn options_stop_on_double_dash() {
        let args_set = args!["--", "-j", "-h", "-e.notbf"];
        // ensure that -h, -j and -e.notbf are interpreted as the list of file names
        let Ok(RunConfig::StandardRun(parsed_args)) = parse_args(args_set) else {
            panic!("test expected StandardRunConfig")
        };
        assert_eq!(parsed_args.out_mode, OutMode::Basic);
        assert_eq!(
            parsed_args.source_files,
            vec![arg("-j"), arg("-h"), arg("-e.notbf")]
        );
    }

    #[test]
    fn options_can_mix_with_files() {
        // ensure that -O isn't interpreted as a file name
        assert_eq!(
            parse_args(args!["e.bf", "-O"])
                .unwrap_standard_cfg()
                .source_files,
            vec![arg("e.bf")]
        );
    }

    #[test]
    fn static_info_returned() {
        assert_eq!(parse_args(args!["-h"]), Ok(RunConfig::ShowHelp));
        assert_eq!(parse_args(args!["-V"]), Ok(RunConfig::ShowVersion));
    }

    #[test]
    fn report_no_sources() {
        let err = parse_args(args![]).unwrap_err();
        assert_eq!(err, ArgParseError::NoSourceFiles);
        let err = parse_args(args!["-t32", "-q"]).unwrap_err();
        assert_eq!(err, ArgParseError::NoSourceFiles);
    }

    #[test]
    fn non_numeric_tape_size() {
        let err = parse_args(args!["-t", "###"]).unwrap_err();
        assert_eq!(err, ArgParseError::TapeSizeNotNumeric(arg("###")));
    }

    #[test]
    fn multiple_tape_size() {
        let args_set = args!["-t1", "-t1024"];
        let err = parse_args(args_set).unwrap_err();
        assert_eq!(err, ArgParseError::MultipleTapeSizes(1, 1024));
    }

    #[test]
    fn tape_size_zero() {
        let args_set = args!["-t0"];
        let err = parse_args(args_set).unwrap_err();
        assert_eq!(err, ArgParseError::TapeSizeZero);
    }

    #[test]
    fn tape_too_large() {
        let args_set = args!["-t9223372036854775807", "foo.bf"];
        let err = parse_args(args_set).unwrap_err();
        assert_eq!(
            err,
            ArgParseError::TapeTooLarge {
                class: Backend::default().ei_class(),
                tape_blocks: 9_223_372_036_854_775_807
            }
        );
    }

    #[test]
    fn missing_operand() {
        let err = parse_args(args!["-t"]).unwrap_err();
        assert_eq!(err, ArgParseError::MissingOperand(arg("-t")));
        let err = parse_args(args!["-e"]).unwrap_err();
        assert_eq!(err, ArgParseError::MissingOperand(arg("-e")));
        let args_set = args!["-a"];
        let err = parse_args(args_set).unwrap_err();
        assert_eq!(err, ArgParseError::MissingOperand(arg("-a")));
    }

    #[test]
    fn out_mode_options() {
        assert_eq!(
            parse_args(args!["-q", "f.bf"])
                .unwrap_standard_cfg()
                .out_mode,
            OutMode::Quiet
        );
        assert_eq!(
            parse_args(args!["-j", "f.bf"])
                .unwrap_standard_cfg()
                .out_mode,
            OutMode::Json
        );
        assert_eq!(
            parse_args(args!["-qj", "f.bf"]).unwrap_err(),
            ArgParseError::SetBothOutModes,
        );
        assert_eq!(
            parse_args(args!["-jq", "f.bf"]).unwrap_err(),
            ArgParseError::SetBothOutModes,
        );
    }

    #[test]
    fn single_args_parsed() {
        let args = parse_args(args!["-Ok", "foo.bf"]).unwrap_standard_cfg();
        assert!(args.keep && args.optimize && !args.cont,);
        let args = parse_args(args!["-Ok", "-c", "foo.bf"]).unwrap_standard_cfg();
        assert!(args.keep && args.optimize && args.cont,);
        let args = parse_args(args!["-c", "foo.bf"]).unwrap_standard_cfg();
        assert!(args.cont && !args.optimize && !args.keep,);
        let args = parse_args(args!["-Oc", "foo.bf"]).unwrap_standard_cfg();
        assert!(args.cont && args.optimize && !args.keep,);
        let args = parse_args(args!["-kOccOk", "foo.bf"]).unwrap_standard_cfg();
        assert!(args.keep && args.optimize && args.cont,);
        let args = parse_args(args!["foo.bf"]).unwrap_standard_cfg();
        assert!(!args.keep && !args.optimize && !args.cont,);
    }

    #[test]
    fn multiple_extensions_err() {
        assert_eq!(
            parse_args(args!["-e.brainfuck", "-e", ".bf"]).unwrap_err(),
            ArgParseError::MultipleExtensions(arg(".brainfuck"), arg(".bf")),
        );
    }

    #[test]
    fn multiple_output_extensions_err() {
        assert_eq!(
            parse_args(args!["-s.elf", "-s", "_bf"]).unwrap_err(),
            ArgParseError::MultipleOutputExtensions(arg(".elf"), arg("_bf")),
        );
    }

    #[test]
    fn bad_args_error_out() {
        assert_eq!(
            parse_args(args!["-u"]).unwrap_err(),
            ArgParseError::UnknownShortOption(b'u'),
        );
    }

    #[test]
    fn list_arch_processed() {
        assert_eq!(parse_args(args!["-A"]), Ok(RunConfig::ListArches));
        assert_eq!(
            parse_args(args!["-e", ".b", "-A"]),
            Ok(RunConfig::ListArches)
        );
    }

    macro_rules! test_arch_args {
        ($arch: literal, $backend: ident, $($aliases: literal),*) => {
            for arch_id in [$arch, $($aliases,)*] {
                let args = args!["-a", arg(arch_id), "foo.bf"];
                #[cfg(feature = $arch)]
                assert_eq!(parse_args(args).unwrap_standard_cfg().arch, Backend::$backend);
                #[cfg(not(feature = $arch))]
                {
                    use crate::compile::backends::DisabledBackend;
                    assert_eq!(
                        parse_args(args).unwrap_err(),
                        ArgParseError::DisabledBackend(DisabledBackend::$backend)
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
        assert_eq!(
            parse_args(args!["-apdp11", "foo.bf"]).unwrap_err(),
            ArgParseError::UnknownBackend(arg("pdp11"))
        );
    }

    #[test]
    fn multiple_arches_error() {
        let args = args![
            "-a",
            env!("EAMBFC_DEFAULT_ARCH"),
            format!("-a{}", env!("EAMBFC_DEFAULT_ARCH")),
            "foo.bf",
        ];
        assert_eq!(
            parse_args(args).unwrap_err(),
            ArgParseError::MultipleArchitectures(Backend::default(), Backend::default()),
        );
    }

    #[test]
    fn longopts_are_like_shortopts() {
        // For standalone options, make sure that they're handled identically in short and long
        // forms
        let pairs = vec![
            ("-h", "--help"),
            ("-V", "--version"),
            ("-q", "--quiet"),
            ("-j", "--json"),
            ("-O", "--optimize"),
            ("-k", "--keep-failed"),
            ("-c", "--continue"),
            ("-A", "--list-targets"),
        ];
        for (short_opt, long_opt) in pairs {
            assert_eq!(
                parse_args(args![arg(short_opt), "f.bf"]).unwrap(),
                parse_args(args![arg(long_opt), "f.bf"]).unwrap(),
            );
        }

        // For flags that take arguments, make sure that the forms `-a x86_64`,
        // `--target-arch x86_64`, `-ax86_64`, and `--target-arch=x86_64` are all processed
        // identically.
        let param_opts = vec![
            ("-a", "--target-arch", args![env!("EAMBFC_DEFAULT_ARCH")]),
            (
                "-t",
                "--tape-size",
                args!["1", "###", "0", arg(u64::MAX.to_string())],
            ),
            ("-e", "--source-extension", args![".beef"]),
            ("-s", "--output-suffix", args![".elf"]),
        ];
        for (short, long, test_params) in param_opts {
            for param in test_params {
                let mut joined_short = arg(short);
                joined_short.push(&param);
                let mut joined_long = arg(long);
                joined_long.push("=");
                joined_long.push(&param);
                let a = parse_args(args![arg(short), param.clone(), "f.bf"]);
                let b = parse_args(args![arg(long), param, "f.bf"]);
                let c = parse_args(args![joined_short, "f.bf"]);
                let d = parse_args(args![joined_long, "f.bf"]);
                assert_eq!(a, b);
                assert_eq!(a, c);
                assert_eq!(a, d);
            }
        }
    }

    #[test]
    fn unrecognized_longopts() {
        let err = parse_args(args!["--run-real-fast"]).unwrap_err();
        assert_eq!(
            err,
            ArgParseError::UnknownLongOption(arg("--run-real-fast"))
        );
    }

    #[test]
    fn err_when_input_is_output() {
        assert_eq!(
            parse_args(args!["-e.beef", "-s.beef", "file.beef"]).unwrap_err(),
            ArgParseError::InputIsOutput(arg(".beef"))
        );
        assert_eq!(
            parse_args(args!["-s.bf", "file.bf"]).unwrap_err(),
            ArgParseError::InputIsOutput(arg(".bf"))
        );
        assert_eq!(
            parse_args(args!["-e.bf", "-s.bf", "file.bf"]).unwrap_err(),
            ArgParseError::InputIsOutput(arg(".bf"))
        );
        // make sure that it does not return an error if extension is set afterwards
        assert_eq!(
            // if -e changes suffix after -s.bf, it shouldn't return an InputIsOutput error
            parse_args(args!["-s.bf", "-e.beef", "file.beef"]).unwrap_standard_cfg(),
            PartialRunConfig {
                extension: Some(arg(".beef")),
                source_files: vec!["file.beef".into()],
                out_suffix: Some(arg(".bf")),
                ..Default::default()
            }
            .try_into()
            .unwrap()
        );
    }
}
