// SPDX-FileCopyrightText: 2024 - 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

pub mod arch_inter;
pub mod arg_parse;
#[cfg(feature = "arm64")]
pub mod backend_arm64;
#[cfg(feature = "s390x")]
pub mod backend_s390x;
#[cfg(feature = "x86_64")]
pub mod backend_x86_64;
pub mod compile;
pub mod elf_tools;
pub mod err;
pub mod optimize;

use arg_parse::RunConfig;
use compile::BFCompile;
use elf_tools::ELFArch;
pub use err::OutMode;
use err::{BFCompileError, BFErrorID};
use std::borrow::Cow;
use std::env::args_os;
use std::ffi::{OsStr, OsString};
use std::fs::{remove_file, File, OpenOptions};
use std::os::unix::ffi::{OsStrExt, OsStringExt};
use std::os::unix::fs::OpenOptionsExt;
use std::process::ExitCode;

// architecture interfaces
#[cfg(feature = "arm64")]
use backend_arm64::Arm64Inter;
#[cfg(feature = "s390x")]
use backend_s390x::S390xInter;
#[cfg(feature = "x86_64")]
use backend_x86_64::X86_64Inter;

// if filename ends with extension, return Ok(f), where f is the filename without the extension
// otherwise, return Err(filename)
fn rm_ext<'a>(filename: &'a OsStr, extension: &OsStr) -> Result<OsString, &'a OsStr> {
    let name_len: usize = filename.as_bytes().len();
    let ext_len: usize = extension.as_bytes().len();
    if filename
        .to_os_string()
        .into_vec()
        .ends_with(extension.as_bytes())
    {
        let mut noext = filename.to_os_string().into_vec();
        noext.truncate(name_len - ext_len);
        Ok(OsString::from_vec(noext))
    } else {
        Err(filename)
    }
}

// wrapper around the compilation of a specific file
fn compile_wrapper<Compiler: BFCompile>(
    _compiler: Compiler,
    file_name: &OsStr,
    extension: &OsStr,
    optimize: bool,
    keep: bool,
    tape_blocks: u64,
) -> Result<(), Vec<BFCompileError>> {
    let outfile_name = rm_ext(file_name, extension).map_err(|e| {
        vec![BFCompileError::basic(
            BFErrorID::BAD_EXTENSION,
            format!(
                "Filename \"{}\" does not end with expected extension \"{}\"",
                e.to_string_lossy(),
                extension.to_string_lossy()
            ),
        )]
    })?;
    let mut open_options = OpenOptions::new();
    open_options
        .write(true)
        .create(true)
        .truncate(true)
        .mode(0o755);
    let infile = File::open(file_name).map_err(|_| {
        vec![BFCompileError::basic(
            BFErrorID::OPEN_R_FAILED,
            format!(
                "Failed to open {} for reading.",
                file_name.to_string_lossy()
            ),
        )]
    })?;
    let outfile = open_options.open(&outfile_name).map_err(|_| {
        vec![BFCompileError::basic(
            BFErrorID::OPEN_W_FAILED,
            format!(
                "Failed to open {} for writing.",
                outfile_name.to_string_lossy()
            ),
        )]
    })?;
    if let Err(e) = Compiler::compile(Box::new(infile), Box::new(outfile), optimize, tape_blocks) {
        if !keep {
            // try to delete the file
            #[allow(
                clippy::let_underscore_must_use,
                reason = "if file can't be deleted, there's nothing to do"
            )]
            let _ = remove_file(outfile_name);
        }
        Err(e)
    } else {
        Ok(())
    }
}

fn main() -> ExitCode {
    let mut exit_code = ExitCode::SUCCESS;
    let mut args = args_os();
    // if not present, it's sensible to fall back to a sane default of "eambfc-rs".
    let progname = args.next().map_or(Cow::Borrowed("eambfc-rs"), |c| {
        Cow::Owned(c.to_string_lossy().to_string())
    });
    match arg_parse::parse_args(args) {
        Ok(RunConfig::ListArches) => {
            println!("This build of {progname} supports the following architectures:\n");
            #[cfg(feature = "x86_64")]
            println!("- x86_64 (aliases: x64, amd64, x86-64)");
            #[cfg(feature = "arm64")]
            println!("- arm64 (aliases: aarch64)");
            #[cfg(feature = "s390x")]
            println!("- s390x (aliases: s390, z/architecure)");
            println!(
                "\nIf no architecure is specified, it defaults to {}.",
                ELFArch::default()
            );
        }
        Ok(RunConfig::ShowHelp) => {
            println!(
                include_str!("text_assets/help_template.txt"),
                progname,
                ELFArch::default()
            );
        }
        Ok(RunConfig::StandardRun(rc)) => {
            for f in rc.source_files {
                #[allow(
                    unreachable_patterns,
                    reason = "Pattern is only unreachable if all backends are compiled in"
                )]
                let comp_result = match rc.arch {
                    #[cfg(feature = "arm64")]
                    ELFArch::Arm64 => compile_wrapper(
                        Arm64Inter,
                        &f,
                        &rc.extension,
                        rc.optimize,
                        rc.keep,
                        rc.tape_blocks,
                    ),
                    #[cfg(feature = "s390x")]
                    ELFArch::S390x => compile_wrapper(
                        S390xInter,
                        &f,
                        &rc.extension,
                        rc.optimize,
                        rc.keep,
                        rc.tape_blocks,
                    ),
                    #[cfg(feature = "x86_64")]
                    ELFArch::X86_64 => compile_wrapper(
                        X86_64Inter,
                        &f,
                        &rc.extension,
                        rc.optimize,
                        rc.keep,
                        rc.tape_blocks,
                    ),
                    _ => unreachable!(), // if architecture is disabled, it won't be included here
                };
                if let Err(errs) = comp_result {
                    errs.into_iter().for_each(|e| e.report(rc.out_mode));
                    if !rc.cont {
                        return ExitCode::FAILURE;
                    }
                    exit_code = ExitCode::FAILURE;
                }
            }
        }
        Ok(RunConfig::ShowVersion) => {
            println!(
                include_str!("text_assets/version_template.txt"),
                progname,
                env!("CARGO_PKG_VERSION"),
                env!("EAMBFC_RS_GIT_COMMIT")
            );
            return exit_code;
        }
        Err((err, out_mode)) => {
            err.report(out_mode);
            if out_mode == OutMode::Basic {
                eprintln!(
                    include_str!("text_assets/help_template.txt"),
                    progname,
                    ELFArch::default()
                );
            }
        }
    }
    exit_code
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rmext_success_ascii() {
        assert_eq!(
            rm_ext(OsStr::from_bytes(b"foobar"), OsStr::from_bytes(b"bar")),
            Ok(OsString::from("foo"))
        );
    }

    #[test]
    fn rmext_success_non_ascii() {
        assert_eq!(
            rm_ext(OsStr::from_bytes(b"\xee.e"), OsStr::from_bytes(b".e")),
            Ok(OsString::from_vec(vec![0xee]))
        );
    }

    #[test]
    fn rmext_fail_ascii() {
        assert_eq!(
            rm_ext(OsStr::from_bytes(b"foobar"), OsStr::from_bytes(b"baz")),
            Err(OsStr::from_bytes(b"foobar"))
        );
    }

    #[test]
    fn rmext_fail_non_ascii() {
        assert_eq!(
            rm_ext(OsStr::from_bytes(b"\xee.e"), OsStr::from_bytes(b".bf")),
            Err(OsStr::from_bytes(b"\xee.e"))
        );
    }
}
