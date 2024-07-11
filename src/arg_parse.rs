// SPDX-FileCopyrightText: 2024 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use super::err::BFCompileError;
use super::run_config::{OutMode, RunType, StandardRunConfig};
use std::env;
use std::ffi::OsString;
use std::os::unix::ffi::OsStringExt;

#[derive(Debug)]
pub enum ArgParseError {
    MultipleExtensions,
    UnknownFlag(u8),
    NoFiles,
    MissingParameter,
}

pub fn parse_args() -> Result<RunType, (BFCompileError, OutMode)> {
    let mut args = env::args_os();
    // argument 0 should be the name of the file.
    // if not present, it's sensible to fall back to a sane default of "eambfc-rs".
    let progname = args.next().unwrap_or(OsString::from("eambfs-rs"));
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
                                    out_mode,
                                ));
                            }
                        } else {
                            extension = OsString::from_vec(remainder);
                        }
                        break;
                    }
                    b'h' => return Ok(RunType::ShowHelp(progname.to_string())),
                    b'V' => return Ok(RunType::ShowVersion(progname.to_string())),
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
                    c => return Err((BFCompileError::UnknownFlag(c), out_mode)),
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
            out_mode,
        ));
    }
    // fall back to default extension if none was provided
    if extension.is_empty() {
        extension = OsString::from(".bf");
    }
    Ok(RunType::StandardRun(StandardRunConfig {
        progname,
        out_mode,
        optimize,
        keep,
        cont,
        extension,
        source_files,
    }))
}
