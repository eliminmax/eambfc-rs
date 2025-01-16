// SPDX-FileCopyrightText: 2024 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use super::elf_tools::ELFArch;
use super::err::{BFCompileError, BFErrorID};
use super::OutMode;
use std::ffi::{OsStr, OsString};
use std::os::unix::ffi::{OsStrExt, OsStringExt};

#[derive(PartialEq, Debug)]
pub struct StandardRunConfig {
    pub progname: String,
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
    ShowHelp(String),
    ShowVersion(String),
    ShowArches(String),
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

#[allow(clippy::too_many_lines)]
pub fn parse_args<T: Iterator<Item = OsString>>(
    mut args: T,
) -> Result<RunConfig, (BFCompileError, String, OutMode)> {
    // argument 0 should be the name of the file.
    // if not present, it's sensible to fall back to a sane default of "eambfc-rs".
    let progname = args.next().unwrap_or(OsString::from("eambfc-rs"));
    let progname = progname.to_string_lossy().to_string();
    let mut extension: Option<OsString> = None;
    let mut source_files = Vec::<OsString>::new();
    let mut out_mode = OutMode::Basic;
    let mut optimize = false;
    let mut keep = false;
    let mut cont = false;
    let mut tape_blocks: Option<u64> = None;
    let mut arch: Option<ELFArch> = None;

    macro_rules! error_out {
        ($error_type: ident, $msg: expr) => {{
            return Err((
                BFCompileError::basic(BFErrorID::$error_type, $msg),
                progname,
                out_mode,
            ));
        }};
    }
    while let Some(arg) = args.next() {
        // handle non-flag values
        if arg == "--" {
            source_files.extend(args);
            break;
        }
        let arg_bytes = arg.into_vec();
        if arg_bytes[0] != b'-' {
            source_files.push(OsString::from_vec(arg_bytes));
            source_files.extend(args);
            break;
        }
        let mut arg_byte_iter = arg_bytes.into_iter().skip(1);
        while let Some(b) = arg_byte_iter.next() {
            macro_rules! parameter_instr {
                ($flag: literal) => {{
                    match parameter_instr($flag, arg_byte_iter.collect(), &mut args) {
                        Ok(o) => o,
                        Err(e) => return Err((e, progname, out_mode)),
                    }
                }};
            }
            match b {
                b'a' => {
                    if arch.is_some() {
                        error_out!(MULTIPLE_ARCHES, "passed -a multiple times");
                    }
                    arch = match parameter_instr!(b'a').as_bytes() {
                        #[cfg(feature = "x86_64")]
                        b"x86_64" | b"x64" | b"amd64" | b"x86-64" => Some(ELFArch::X86_64),
                        #[cfg(feature = "arm64")]
                        b"arm64" | b"aarch64" => Some(ELFArch::Arm64),
                        #[cfg(feature = "s390x")]
                        b"s390x" | b"s390" | b"z/architecture" => Some(ELFArch::S390x),
                        f => error_out!(
                            UNKNOWN_ARCH,
                            format!(
                                "{} is not a recognized architecture",
                                OsStr::from_bytes(f).to_string_lossy()
                            )
                        ),
                    };
                    break;
                }
                b'e' => {
                    if extension.is_some() {
                        error_out!(MULTIPLE_EXTENSIONS, "passed -e multiple times");
                    }
                    extension = Some(parameter_instr!(b'e'));
                    break;
                }
                b't' => {
                    if tape_blocks.is_some() {
                        error_out!(MULTIPLE_TAPE_BLOCK_COUNTS, "passed -t multiple times");
                    }
                    match parameter_instr!(b't').to_string_lossy().parse::<u64>() {
                        Ok(0) => error_out!(NO_TAPE, "Tape value for -t must be at least 1."),
                        Ok(i) if i >= u64::MAX >> 12 => error_out!(
                            TAPE_TOO_LARGE,
                            format!("{i} * 0x1000 exceeds the 64-bit integer limit.")
                        ),
                        Ok(i) => tape_blocks = Some(i),
                        Err(s) => error_out!(
                            NOT_NUMERIC,
                            format!("{s} could not be parsed as a numeric value")
                        ),
                    }
                    break;
                }
                b'h' => return Ok(RunConfig::ShowHelp(progname)),
                b'V' => return Ok(RunConfig::ShowVersion(progname)),
                b'A' => return Ok(RunConfig::ShowArches(progname)),
                b'j' => out_mode = OutMode::JSON,
                // for consistency with original C version, quiet doesn't override JSON mode
                b'q' => {
                    if out_mode == OutMode::Basic {
                        out_mode = OutMode::Quiet;
                    }
                }
                b'O' => optimize = true,
                b'k' => keep = true,
                b'c' => cont = true,
                c => return Err((BFCompileError::unknown_flag(c), progname, out_mode)),
            };
        }
    }
    if source_files.is_empty() {
        error_out!(NO_SOURCE_FILES, "No source files provided");
    }

    Ok(RunConfig::StandardRun(StandardRunConfig {
        progname,
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
            progname: String::from("eambfc-rs"),
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
    fn combined_args() -> Result<(), String> {
        // ensure that combined arguments are processed properly
        let args_set_0 = vec![
            OsString::from("eambfc-rs-test"),
            // should be interpreted identically to -k -j -e .brainfuck'
            OsString::from("-kje.brainfuck"),
            OsString::from("foo.brainfuck"),
            OsString::from("bar.brainfuck"),
        ]
        .into_iter();
        let args_set_1 = vec![
            OsString::from("eambfc-rs-test"),
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
        Ok(())
    }

    #[test]
    fn options_stop_on_double_dash() -> Result<(), String> {
        let args_set = vec![
            OsString::from("eambfc-rs-test"),
            OsString::from("--"),
            OsString::from("-j"),
            OsString::from("-h"),
            OsString::from("-e.notbf"),
        ]
        .into_iter();
        // ensure that -h, -j and -e.notbf are interpreted as the list of file names
        let parsed_args = match parse_args(args_set).unwrap() {
            RunConfig::StandardRun(rc) => rc,
            _ => panic!("Arguments not parsed into StandardRunConfig!"),
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
        Ok(())
    }

    #[test]
    fn options_dont_mix_with_files() -> Result<(), String> {
        let args_set = vec![
            OsString::from("eambfc-rs-test"),
            OsString::from("e.bf"),
            OsString::from("-h"),
        ]
        .into_iter();
        // ensure that -h is interpreted as a of file name
        let parsed_args = match parse_args(args_set).unwrap() {
            RunConfig::StandardRun(rc) => rc,
            _ => panic!("Arguments not parsed into StandardRunConfig!"),
        };
        assert_eq!(
            parsed_args.source_files,
            vec![OsString::from("e.bf"), OsString::from("-h"),]
        );
        Ok(())
    }

    #[test]
    fn help_includes_progname() -> Result<(), String> {
        let args_set =
            vec![OsString::from("not-eambfc-i-promise"), OsString::from("-h")].into_iter();
        assert_eq!(
            parse_args(args_set),
            Ok(RunConfig::ShowHelp(String::from("not-eambfc-i-promise")))
        );
        Ok(())
    }

    #[test]
    fn version_includes_progname() -> Result<(), String> {
        let args_set =
            vec![OsString::from("not-eambfc-i-promise"), OsString::from("-V")].into_iter();
        assert_eq!(
            parse_args(args_set),
            Ok(RunConfig::ShowVersion(String::from("not-eambfc-i-promise")))
        );
        Ok(())
    }

    #[test]
    fn fallback_for_empty_args() -> Result<(), String> {
        let (bf_err, name, _) = parse_args(vec![].into_iter()).unwrap_err();
        assert_eq!(name, String::from("eambfc-rs"));
        assert_eq!(bf_err.kind, BFErrorID::NO_SOURCE_FILES);

        Ok(())
    }

    #[test]
    fn arg0_contains_non_utf8() -> Result<(), String> {
        let args_set = vec![
            OsString::from_vec(b"not-\xeeambfc-i-promis\xee".into()),
            OsString::from("-h"),
        ]
        .into_iter();
        assert_eq!(
            parse_args(args_set),
            Ok(RunConfig::ShowHelp(String::from("not-�ambfc-i-promis�")))
        );
        Ok(())
    }

    #[test]
    fn filename_contains_non_utf8() -> Result<(), String> {
        let args_set = vec![
            OsString::from("eambfc-rs"),
            OsString::from_vec(b"fil\xee.bf".into()),
        ]
        .into_iter();
        assert_eq!(
            parse_args(args_set),
            Ok(RunConfig::StandardRun(StandardRunConfig {
                progname: String::from("eambfc-rs"),
                source_files: vec![OsString::from_vec(b"fil\xee.bf".into())],
                ..StandardRunConfig::default()
            }))
        );
        Ok(())
    }

    #[test]
    fn non_numeric_tape_size() -> Result<(), String> {
        let args_set = vec![
            OsString::from("eambfc-rs"),
            OsString::from_vec(b"-t".into()),
            OsString::from_vec(b"###".into()),
        ]
        .into_iter();
        let (err, ..) = parse_args(args_set).unwrap_err();
        assert_eq!(err.kind, BFErrorID::NOT_NUMERIC);
        Ok(())
    }

    #[test]
    fn multiple_tape_size() -> Result<(), String> {
        let args_set = vec![
            OsString::from("eambfc-rs"),
            OsString::from_vec(b"-t1".into()),
            OsString::from_vec(b"-t1024".into()),
        ]
        .into_iter();
        let (err, ..) = parse_args(args_set).unwrap_err();
        assert_eq!(err.kind, BFErrorID::MULTIPLE_TAPE_BLOCK_COUNTS);
        Ok(())
    }

    #[test]
    fn tape_size_zero() -> Result<(), String> {
        let args_set = vec![
            OsString::from("eambfc-rs"),
            OsString::from_vec(b"-t0".into()),
        ]
        .into_iter();
        let (err, ..) = parse_args(args_set).unwrap_err();
        assert_eq!(err.kind, BFErrorID::NO_TAPE);
        Ok(())
    }

    #[test]
    fn missing_tape_size() -> Result<(), String> {
        let args_set = vec![
            OsString::from("eambfc-rs"),
            OsString::from_vec(b"-t".into()),
        ]
        .into_iter();
        let (err, ..) = parse_args(args_set).unwrap_err();
        assert_eq!(err.kind, BFErrorID::MISSING_OPERAND);
        Ok(())
    }
}
