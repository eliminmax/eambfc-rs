// SPDX-FileCopyrightText: 2024 Eli Array Minkoff
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
use err::{BFCompileError, BFErrorID};
use std::env::args_os;
use std::ffi::{OsStr, OsString};
use std::fs::{remove_file, File, OpenOptions};
use std::os::unix::ffi::{OsStrExt, OsStringExt};
use std::os::unix::fs::OpenOptionsExt;
use std::{io, process};

// architecture interfaces
#[cfg(feature = "arm64")]
use backend_arm64::Arm64Inter;
#[cfg(feature = "s390x")]
use backend_s390x::S390xInter;
#[cfg(feature = "x86_64")]
use backend_x86_64::X86_64Inter;

#[derive(PartialEq, Debug, Clone, Copy)]
pub enum OutMode {
    Basic,
    JSON,
    Quiet,
}

fn show_help(outfile: &mut dyn io::Write, progname: &str) {
    let help_text = format!(
        "Usage: {progname} [options] <program.bf> [<program2.bf> ...]

 -h        - display this help text and exit
 -V        - print version information and exit
 -j        - print errors in JSON format
 -q        - don't print errors unless -j was passed
 -O        - enable optimization*.
 -k        - keep files that failed to compile (for debugging)
 -c        - continue to the next file instead of quitting if a
             file fails to compile
 -t count  - allocate <count> 4-KiB blocks for the tape
             (defaults to 8 if not specified)**
 -e ext    - use 'ext' as the extension for source files instead of '.bf'
             (This program will remove this at the end of the input
             file to create the output file name)**
 -a arch   - compile for specified architecture
             (defaults to {} if not specified)**
 -A        - list supported architectures and exit

* Optimization can make error reporting less precise.
** -a, -t and -e can only be passed at most once each.

Remaining options are treated as source file names. If they don't
end with '.bf' (or the extension specified with '-e'), the program
will raise an error.
",
        ELFArch::default(),
    );
    outfile
        .write_all(help_text.as_bytes())
        .expect("Failed to write help text - things are truly borked.");
}

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
    file_name: &OsString,
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

fn main() {
    let mut stdout = io::stdout();
    let mut stderr = io::stderr();

    let mut exit_code = 0;
    match arg_parse::parse_args(args_os()) {
        Ok(RunConfig::ShowArches(progname)) => {
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
        Ok(RunConfig::ShowHelp(progname)) => show_help(&mut stdout, &progname),
        Ok(RunConfig::StandardRun(rc)) => {
            rc.source_files.iter().for_each(|f| {
                #[allow(
                    unreachable_patterns,
                    reason = "Pattern is only unreachable if all backends are compiled in"
                )]
                let comp_result = match rc.arch {
                    #[cfg(feature = "arm64")]
                    ELFArch::Arm64 => compile_wrapper(
                        Arm64Inter,
                        f,
                        &rc.extension,
                        rc.optimize,
                        rc.keep,
                        rc.tape_blocks,
                    ),
                    #[cfg(feature = "s390x")]
                    ELFArch::S390x => compile_wrapper(
                        S390xInter,
                        f,
                        &rc.extension,
                        rc.optimize,
                        rc.keep,
                        rc.tape_blocks,
                    ),
                    #[cfg(feature = "x86_64")]
                    ELFArch::X86_64 => compile_wrapper(
                        X86_64Inter,
                        f,
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
                        process::exit(1);
                    }
                    exit_code = 1;
                }
            });
        }
        Ok(RunConfig::ShowVersion(progname)) => {
            println!(
                "{progname}: eambfc-rs version {}

Copyright (c) 2024 Eli Array Minkoff
License: GNU GPL version 3 <https://gnu.org/licenses/gpl.html>
This is free software: you are free to change and redistribute it.
There is NO WARRANTY, to the extent permitted by law.

{}",
                env!("CARGO_PKG_VERSION"),
                env!("EAMBFC_RS_GIT_COMMIT")
            );
            process::exit(exit_code);
        }
        Err((err, progname, out_mode)) => {
            err.report(out_mode);
            if out_mode == OutMode::Basic {
                show_help(&mut stderr, &progname);
            }
        }
    }
    process::exit(exit_code);
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
            Ok(OsString::from_vec(vec![0xeeu8]))
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
