// SPDX-FileCopyrightText: 2024 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use super::err::BFCompileError;
use super::run_config::{OutMode, RunConfig, StandardRunConfig};
use std::ffi::OsString;
use std::os::unix::ffi::OsStringExt;

pub fn parse_args<T: Iterator<Item = OsString>>(
    mut args: T,
) -> Result<RunConfig, (BFCompileError, String, OutMode)> {
    // argument 0 should be the name of the file.
    // if not present, it's sensible to fall back to a sane default of "eambfc-rs".
    let progname = args.next().unwrap_or(OsString::from("eambfc-rs"));
    let progname = progname.to_string_lossy().to_string();

    let mut extension = OsString::new();
    let mut source_files = Vec::<OsString>::new();
    let mut out_mode = OutMode::Basic;
    let mut optimize = false;
    let mut keep = false;
    let mut cont = false;
    while let Some(arg) = args.next() {
        // some logic to treat anything after `--` as literal values
        if arg == "--" {
            source_files.extend(args);
            break;
        }
        let arg_bytes = arg.into_vec();
        if arg_bytes[0] == b'-' {
            let mut arg_byte_iter = arg_bytes.into_iter().skip(1);
            while let Some(b) = arg_byte_iter.next() {
                match b {
                    b'e' => {
                        if !extension.is_empty() {
                            return Err((
                                BFCompileError::Basic {
                                    id: "MULTIPLE_EXTENSIONS".to_string(),
                                    msg: "passed -e multiple times".to_string(),
                                },
                                progname,
                                out_mode,
                            ));
                        }
                        let remainder = arg_byte_iter.collect::<Vec<u8>>();
                        if remainder.is_empty() {
                            if let Some(new_extension) = args.next() {
                                extension = new_extension;
                            } else {
                                return Err((
                                    BFCompileError::Basic {
                                        id: "MISSING_OPERAND".to_string(),
                                        msg: "-e requires an additional argument".to_string(),
                                    },
                                    progname,
                                    out_mode,
                                ));
                            }
                        } else {
                            extension = OsString::from_vec(remainder);
                        }
                        break;
                    }
                    b'h' => return Ok(RunConfig::ShowHelp(progname.to_string())),
                    b'V' => return Ok(RunConfig::ShowVersion(progname.to_string())),
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
                    c => return Err((BFCompileError::UnknownFlag(c), progname, out_mode)),
                };
            }
        } else {
            // not an option flag, so convert back to OsString then save current and remaining args
            // as brainfuck source files.
            source_files.push(OsString::from_vec(arg_bytes));
            source_files.extend(args);
            break;
        }
    }
    if source_files.is_empty() {
        return Err((
            BFCompileError::Basic {
                id: "NO_SOURCE_FILES".to_string(),
                msg: "No source files provided".to_string(),
            },
            progname,
            out_mode,
        ));
    }
    // fall back to default extension if none was provided
    if extension.is_empty() {
        extension = OsString::from(".bf");
    }
    Ok(RunConfig::StandardRun(StandardRunConfig {
        progname,
        out_mode,
        optimize,
        keep,
        cont,
        extension,
        source_files,
    }))
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
        let err = parse_args(vec![].into_iter()).unwrap_err();
        match err {
            (BFCompileError::Basic { id, msg: _ }, name, _) => {
                assert_eq!(name, String::from("eambfc-rs"));
                assert_eq!(id, "NO_SOURCE_FILES");
            }
            _ => panic!(),
        }

        Ok(())
    }
}
