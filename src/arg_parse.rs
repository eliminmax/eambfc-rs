// SPDX-FileCopyrightText: 2024 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use super::elf_tools::ELFArch;
use super::err::{BFCompileError, BFErrorID};
use super::OutMode;
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

#[derive(PartialEq, Debug)]
pub enum RunConfig {
    StandardRun(StandardRunConfig),
    ShowHelp,
    ShowVersion,
    ListArches,
}

fn parameter_instr<T: Iterator<Item = OsString>>(
    flag: u8,
    remainder: Vec<u8>,
    args: &mut T,
) -> Result<OsString, BFCompileError> {
    if remainder.is_empty() {
        args.next().ok_or_else(|| {
            BFCompileError::basic(
                BFErrorID::MISSING_OPERAND,
                format!("-{} requires an additional argument", flag.escape_ascii()),
            )
        })
    } else {
        Ok(OsString::from_vec(remainder))
    }
}

pub fn parse_args<T: Iterator<Item = OsString>>(
    mut args: T,
) -> Result<RunConfig, (BFCompileError, OutMode)> {

    let mut extension: Option<OsString> = None;
    let mut source_files: Option<Vec<OsString>> = None;
    let mut tape_blocks: Option<u64> = None;
    let mut arch: Option<ELFArch> = None;

    let mut out_mode = OutMode::Basic;
    // boolean flags
    let (mut optimize, mut keep, mut cont) = (false, false, false);


    macro_rules! error_out {
        ($error_type: ident, $msg: expr) => {{
            let err = BFCompileError::basic(BFErrorID::$error_type, $msg);
            return Err((err, out_mode));
        }};
    }

    while let Some(arg) = args.next() {
        // handle non-flag values
        if arg == "--" {
            source_files = Some(args.collect());
            break;
        }
        let arg_bytes = arg.into_vec();
        if arg_bytes[0] != b'-' {
            let mut sf = vec![OsString::from_vec(arg_bytes)];
            sf.extend(args);
            source_files = Some(sf);
            break;
        }

        let mut arg_byte_iter = arg_bytes.into_iter().skip(1);
        macro_rules! parameter_instr {
            ($flag: literal) => {{
                parameter_instr($flag, arg_byte_iter.collect(), &mut args)
                    .map_err(|e| (e, out_mode))?
            }};
        }

        while let Some(b) = arg_byte_iter.next() {
            macro_rules! param_arg {
                (($flag: literal, $var: ident, $error_type: ident), $body: expr) => {{
                    if $var.is_some() {
                        error_out!($error_type, concat!("passed -", $flag, "multiple times"));
                    }
                    $var = $body;
                    break;
                }};
            }
            match b {
                b'h' => return Ok(RunConfig::ShowHelp),
                b'V' => return Ok(RunConfig::ShowVersion),
                b'A' => return Ok(RunConfig::ListArches),
                b'j' => out_mode.json(),
                b'q' => out_mode.quiet(),
                b'O' => optimize = true,
                b'k' => keep = true,
                b'c' => cont = true,
                b'a' => param_arg!(
                    ('a', arch, MULTIPLE_ARCHES),
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
                b'e' => param_arg!(
                    ('e', extension, MULTIPLE_EXTENSIONS),
                    Some(parameter_instr!(b'e'))
                ),
                b't' => param_arg!(
                    ('t', tape_blocks, MULTIPLE_TAPE_BLOCK_COUNTS),
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
                c => return Err((BFCompileError::unknown_flag(c), out_mode)),
            };
        }
    }
    let Some(source_files) = source_files else {
        error_out!(NO_SOURCE_FILES, "No source files provided");
    };

    Ok(RunConfig::StandardRun(StandardRunConfig {
        out_mode,
        optimize,
        keep,
        cont,
        tape_blocks: tape_blocks.unwrap_or(8),
        extension: extension.unwrap_or(".bf".into()),
        source_files,
        arch: arch.unwrap_or_default(),
    }))
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
