// SPDX-FileCopyrightText: 2024 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

pub mod arg_parse;
pub mod eam_compile;
pub mod elf_tools;
pub mod err;
pub mod optimize;
pub mod run_config;
pub mod x86_64_encoders;
pub use x86_64_encoders as instr_encoders;

use eam_compile::bf_compile;
use err::{BFCompileError, BfErrDisplay};
use run_config::{OutMode, RunConfig};
use std::env::args_os;
use std::ffi::{OsStr, OsString};
use std::fs::{remove_file, File, OpenOptions};
use std::os::unix::ffi::{OsStrExt, OsStringExt};
use std::os::unix::fs::OpenOptionsExt;
use std::{io, process};

fn show_help<T: io::Write>(outfile: &mut T, progname: &str) {
    let help_text = format!(
        "Usage: {} [options] <program.bf> [<program2.bf> ...]

 -h        - display this help text and exit
 -V        - print version information and exit
 -j        - print errors in JSON format
 -q        - don't print errors unless -j was passed
 -O        - enable optimization*.
 -k        - keep files that failed to compile (for debugging)
 -c        - continue to the next file instead of quitting if a
             file fails to compile
 -e ext    - (only provide once) use 'ext' as the extension for
             source files instead of '.bf'
             (This program will remove this at the end of the input
             file to create the output file name)

* Optimization can make error reporting less precise.

Remaining options are treated as source file names. If they don't
end with '.bf' (or the extension specified with '-e'), the program
will raise an error.
",
        progname
    );
    let _ = outfile.write(help_text.as_bytes());
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
fn compile_wrapper(
    file_name: &OsString,
    extension: &OsStr,
    optimize: bool,
) -> Result<(), BFCompileError> {
    let outfile_name = rm_ext(file_name, extension).map_err(|e| BFCompileError::Basic {
        id: String::from("BAD_EXTENSION"),
        msg: format!(
            "Filename {} does not end with expected extension.",
            e.to_string_lossy()
        ),
    })?;
    let mut open_options = OpenOptions::new();
    open_options.write(true).create(true).mode(0o755);
    let infile = File::open(file_name).map_err(|_| BFCompileError::Basic {
        id: String::from("OPEN_R_FAILED"),
        msg: format!(
            "Failed to open {} for reading.",
            file_name.to_string_lossy().to_string()
        ),
    })?;
    let outfile = open_options
        .open(&outfile_name)
        .map_err(|_| BFCompileError::Basic {
            id: String::from("OPEN_W_FAILED"),
            msg: format!(
                "Failed to open {} for writing.",
                outfile_name.to_string_lossy().to_string()
            ),
        })?;
    bf_compile(infile, outfile, optimize)
}

fn main() {
    let mut stdout = io::stdout();
    let mut stderr = io::stderr();

    let mut exit_code = 0;
    match arg_parse::parse_args(args_os()) {
        Ok(RunConfig::ShowHelp(progname)) => show_help(&mut stdout, &progname),
        Ok(RunConfig::StandardRun(rc)) => {
            rc.source_files.iter().for_each(|f| {
                match compile_wrapper(&f, &rc.extension, rc.optimize) {
                    Ok(_) => {}
                    Err(e) => {
                        e.report(&rc.out_mode);
                        if !rc.keep {
                            // try to delete the file
                            let _ =
                                remove_file(rm_ext(f, &rc.extension).unwrap_or(OsString::from("")));
                        }
                        if !rc.cont {
                            process::exit(1);
                        } else {
                            exit_code = 1;
                        }
                    }
                }
            });
        }
        Ok(RunConfig::ShowVersion(progname)) => {
            println!(
                "{}: eambfc-rs version {}

Copyright (c) 2024 Eli Array Minkoff
License: GNU GPL version 3
<https://gnu.org/licenses/gpl.html>
This is free software:
you are free to change and redistribute it.
There is NO WARRANTY, to the extent permitted by law.",
                progname, "0.0.0-pre"
            );
            process::exit(exit_code);
        }
        Err((err, progname, out_mode)) => {
            err.report(&out_mode);
            if out_mode == OutMode::Basic {
                show_help(&mut stderr, &progname)
            }
        }
    }
    process::exit(exit_code);
}
