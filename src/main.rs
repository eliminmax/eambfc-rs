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

use err::BfErrDisplay;
use run_config::{OutMode, RunConfig};
use std::ffi::{OsStr, OsString};
#[allow(unused_imports)]
use std::fs::File;
#[allow(unused_imports)]
use std::io::Write;
#[allow(unused_imports)]
use std::os::unix::{fs::PermissionsExt, ffi::OsStrExt, ffi::OsStringExt};
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
    if filename.to_os_string().into_vec().ends_with(extension.as_bytes()) {
        let mut noext = filename.to_os_string().into_vec();
        noext.truncate(name_len - ext_len);
        Ok(OsString::from_vec(noext))
    } else {
        Err(filename)
    }
}

fn main() {
    let mut stdout = io::stdout();
    match arg_parse::parse_args() {
        Ok(RunConfig::ShowHelp(progname)) => show_help(&mut stdout, &progname),
        Ok(RunConfig::StandardRun(rc)) => {
            println!("Not yet implemented, but arguments parsed were:");
            println!("Program name: {}", rc.progname);
            println!(
                "Output mode: {}",
                match rc.out_mode {
                    OutMode::Basic => "Basic",
                    OutMode::JSON => "JSON",
                    OutMode::Quiet => "Quiet",
                }
            );
            println!("Optimize: {}", rc.optimize);
            println!("Keep failed compilation output: {}", rc.keep);
            println!("Continue after failed compilation: {}", rc.cont);
            println!(
                "File extension: {}",
                rc.extension.to_string_lossy().to_string()
            );
            rc.source_files.iter().for_each(|f| {
                println!(
                    "- compile {} to {}",
                    f.to_string_lossy().to_string(),
                    rm_ext(&f, &rc.extension).unwrap().to_string_lossy().to_string()
                )
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
            process::exit(0);
        }
        Err((err, out_mode)) => err.report(out_mode),
    }
}
