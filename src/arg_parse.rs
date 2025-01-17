// SPDX-FileCopyrightText: 2024 - 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use super::elf_tools::ELFArch;
use super::err::{BFCompileError, BFErrorID};
use super::OutMode;
use std::convert::{TryFrom, TryInto};
use std::ffi::OsString;
use std::os::unix::ffi::{OsStrExt, OsStringExt};

#[derive(PartialEq, Debug)]
pub struct StandardRunConfig {
    pub out_mode: OutMode,
    pub optimize: bool,
    pub keep: bool,
    pub cont: bool,
    pub tape_blocks: u64,
    pub extension: OsString,
    pub source_files: Vec<OsString>,
    pub arch: ELFArch,
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
    arch: Option<ELFArch>,
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
            BFCompileError::basic(BFErrorID::NO_SOURCE_FILES, "No source files provided"),
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

#[derive(PartialEq, Debug)]
pub enum RunConfig {
    StandardRun(StandardRunConfig),
    ShowHelp,
    ShowVersion,
    ListArches,
}

pub fn parse_args<T: Iterator<Item = OsString>>(
    mut args: T,
) -> Result<RunConfig, (BFCompileError, OutMode)> {
    let mut pcfg = PartialRunConfig::default();

    macro_rules! error_out {
        ($error_type: ident, $msg: expr) => {{
            let err = BFCompileError::basic(BFErrorID::$error_type, $msg);
            return Err((err, pcfg.out_mode));
        }};
    }

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
        macro_rules! parameter_instr {
            ($flag: literal) => {{
                let remainder: Vec<_> = arg_byte_iter.collect();
                if remainder.is_empty() {
                    args.next().ok_or_else(|| {
                        (
                            BFCompileError::basic(
                                BFErrorID::MISSING_OPERAND,
                                format!(
                                    "-{} requires an additional argument",
                                    $flag.escape_ascii()
                                ),
                            ),
                            pcfg.out_mode,
                        )
                    })?
                } else {
                    OsString::from_vec(remainder)
                }
            }};
        }

        while let Some(b) = arg_byte_iter.next() {
            // if cfg.$var is none, set it to the result of evaluating $body, otherwise, error out
            // with error id BFErrorID::$error_id
            macro_rules! param_arg {
                ($var: ident, $error_id: ident, $body: expr) => {{
                    if pcfg.$var.is_some() {
                        error_out!(
                            $error_id,
                            format!("passed -{} multiple times", b.escape_ascii())
                        );
                    }
                    pcfg.$var = $body;
                    break;
                }};
            }
            match b {
                b'h' => return Ok(RunConfig::ShowHelp),
                b'V' => return Ok(RunConfig::ShowVersion),
                b'A' => return Ok(RunConfig::ListArches),
                b'j' => pcfg.out_mode.json(),
                b'q' => pcfg.out_mode.quiet(),
                b'O' => pcfg.optimize = true,
                b'k' => pcfg.keep = true,
                b'c' => pcfg.cont = true,
                b'a' => param_arg!(
                    arch,
                    MULTIPLE_ARCHES,
                    match parameter_instr!(b'a').as_bytes() {
                        #[cfg(feature = "x86_64")]
                        b"x86_64" | b"x64" | b"amd64" | b"x86-64" => Some(ELFArch::X86_64),
                        #[cfg(feature = "arm64")]
                        b"arm64" | b"aarch64" => Some(ELFArch::Arm64),
                        #[cfg(feature = "s390x")]
                        b"s390x" | b"s390" | b"z/architecture" => Some(ELFArch::S390x),
                        f => error_out!(
                            UNKNOWN_ARCH,
                            format!("{} is not a recognized architecture", f.escape_ascii())
                        ),
                    }
                ),
                b'e' => param_arg!(extension, MULTIPLE_EXTENSIONS, Some(parameter_instr!(b'e'))),
                b't' => param_arg!(
                    tape_blocks,
                    MULTIPLE_TAPE_BLOCK_COUNTS,
                    match parameter_instr!(b't').to_string_lossy().parse::<u64>() {
                        Ok(0) => error_out!(NO_TAPE, "Tape value for -t must be at least 1"),
                        Ok(i) if i >= u64::MAX >> 12 =>
                            error_out!(TAPE_TOO_LARGE, "tape size exceeds 64-bit integer limit"),
                        Ok(i) => Some(i),
                        Err(_) => error_out!(
                            NOT_NUMERIC,
                            "tape size could not be parsed as a numeric value"
                        ),
                    }
                ),
                c => return Err((BFCompileError::unknown_flag(c), pcfg.out_mode)),
            };
        }
    }
    Ok(RunConfig::StandardRun(pcfg.try_into()?))
}

#[cfg(test)]
impl Default for StandardRunConfig {
    fn default() -> Self {
        StandardRunConfig {
            out_mode: OutMode::Basic,
            optimize: false,
            keep: false,
            cont: false,
            tape_blocks: 8,
            extension: OsString::from(".bf"),
            source_files: Vec::<OsString>::new(),
            arch: ELFArch::default(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn combined_args() {
        // ensure that combined arguments are processed properly
        let args_set_0 = vec![
            // should be interpreted identically to -k -j -e .brainfuck'
            OsString::from("-kje.brainfuck"),
            OsString::from("foo.brainfuck"),
            OsString::from("bar.brainfuck"),
        ]
        .into_iter();
        let args_set_1 = vec![
            // should be interpreted identically to -kje.brainfuck'
            OsString::from("-k"),
            OsString::from("-j"),
            OsString::from("-e"),
            OsString::from(".brainfuck"),
            OsString::from("foo.brainfuck"),
            OsString::from("bar.brainfuck"),
        ]
        .into_iter();

        assert_eq!(
            parse_args(args_set_0).unwrap(),
            parse_args(args_set_1).unwrap()
        );
    }

    #[test]
    fn options_stop_on_double_dash() {
        let args_set = vec![
            OsString::from("--"),
            OsString::from("-j"),
            OsString::from("-h"),
            OsString::from("-e.notbf"),
        ]
        .into_iter();
        // ensure that -h, -j and -e.notbf are interpreted as the list of file names
        let RunConfig::StandardRun(parsed_args) = parse_args(args_set).unwrap() else {
            panic!("Arguments not parsed into StandardRunConfig!")
        };
        assert_eq!(parsed_args.out_mode, OutMode::Basic);
        assert_eq!(
            parsed_args.source_files,
            vec![
                OsString::from("-j"),
                OsString::from("-h"),
                OsString::from("-e.notbf"),
            ]
        );
    }

    #[test]
    fn options_dont_mix_with_files() {
        let args_set = vec![OsString::from("e.bf"), OsString::from("-h")].into_iter();
        // ensure that -h is interpreted as a file name
        let RunConfig::StandardRun(parsed_args) = parse_args(args_set).unwrap() else {
            panic!("Arguments not parsed into StandardRunConfig!")
        };
        assert_eq!(
            parsed_args.source_files,
            vec![OsString::from("e.bf"), OsString::from("-h"),]
        );
    }

    #[test]
    fn help_returned() {
        let args_set = vec![OsString::from("-h")].into_iter();
        assert_eq!(parse_args(args_set), Ok(RunConfig::ShowHelp));
    }

    #[test]
    fn version_returned() {
        let args_set = vec![OsString::from("-V")].into_iter();
        assert_eq!(parse_args(args_set), Ok(RunConfig::ShowVersion));
    }

    #[test]
    fn handle_empty_args() {
        let (bf_err, _) = parse_args(vec![].into_iter()).unwrap_err();
        assert_eq!(bf_err.kind, BFErrorID::NO_SOURCE_FILES);
    }

    #[test]
    fn arg0_contains_non_utf8() {
        let args_set = vec![OsString::from("-h")].into_iter();
        assert_eq!(parse_args(args_set), Ok(RunConfig::ShowHelp));
    }

    #[test]
    fn filename_contains_non_utf8() {
        let args_set = vec![OsString::from_vec(b"fil\xee.bf".into())].into_iter();
        assert_eq!(
            parse_args(args_set),
            Ok(RunConfig::StandardRun(StandardRunConfig {
                source_files: vec![OsString::from_vec(b"fil\xee.bf".into())],
                ..StandardRunConfig::default()
            }))
        );
    }

    #[test]
    fn non_numeric_tape_size() {
        let args_set = vec![
            OsString::from_vec(b"-t".into()),
            OsString::from_vec(b"###".into()),
        ]
        .into_iter();
        let (err, ..) = parse_args(args_set).unwrap_err();
        assert_eq!(err.kind, BFErrorID::NOT_NUMERIC);
    }

    #[test]
    fn multiple_tape_size() {
        let args_set = vec![
            OsString::from_vec(b"-t1".into()),
            OsString::from_vec(b"-t1024".into()),
        ]
        .into_iter();
        let (err, ..) = parse_args(args_set).unwrap_err();
        assert_eq!(err.kind, BFErrorID::MULTIPLE_TAPE_BLOCK_COUNTS);
    }

    #[test]
    fn tape_size_zero() {
        let args_set = vec![OsString::from_vec(b"-t0".into())].into_iter();
        let (err, ..) = parse_args(args_set).unwrap_err();
        assert_eq!(err.kind, BFErrorID::NO_TAPE);
    }

    #[test]
    fn missing_tape_size() {
        let args_set = vec![OsString::from_vec(b"-t".into())].into_iter();
        let (err, ..) = parse_args(args_set).unwrap_err();
        assert_eq!(err.kind, BFErrorID::MISSING_OPERAND);
    }
}
