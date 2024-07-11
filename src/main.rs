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

use std::ffi::{OsStr, OsString};
#[allow(unused_imports)]
use std::fs::File;
#[allow(unused_imports)]
use std::os::unix::fs::PermissionsExt;
use std::{io, process};

#[allow(unused_imports)]
use run_config::{OutMode, RunType, StandardRunConfig};

#[allow(dead_code)]
fn get_perms() -> u32 {
    todo!("get_perms");
}

#[allow(dead_code, unused_variables)]
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

#[allow(dead_code, unused_variables)]
fn rm_ext(filename: &OsString, extension: &OsStr) -> OsString {
    todo!("rm_ext");
}

fn main() {
    let mut stdout = io::stdout();
    match arg_parse::parse_args().unwrap() {
        RunType::ShowHelp(progname) => show_help(&mut stdout, &progname),
        RunType::StandardRun(rc) => {
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
            rc.source_files
                .iter()
                .for_each(|f| println!("- compile: {}", f.to_string_lossy().to_string()));
        }
        RunType::ShowVersion(progname) => {
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
    }
}
