// SPDX-FileCopyrightText: 2024 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

#[allow(unused_imports)]
use std::fs::File;
#[allow(unused_imports)]
use std::os::unix::fs::PermissionsExt;
use std::{env, io};

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
 -j        - print errors in JSON format*
             (assumes file names are UTF-8-encoded.)
 -q        - don't print errors unless -j was passed*
 -O        - enable optimization**.
 -k        - keep files that failed to compile (for debugging)
 -c        - continue to the next file instead of quitting if a
             file fails to compile
 -e ext    - (only provide once) use 'ext' as the extension for
             source files instead of '.bf'
             (This program will remove this at the end of the input
             file to create the output file name)

* -q and -j will not affect arguments passed before they were.

** Optimization can make error reporting less precise.

Remaining options are treated as source file names. If they don't
end with '.bf' (or the extension specified with '-e'), the program
will raise an error.
",
        progname
    );
    let _ = outfile.write(help_text.as_bytes());
}

#[allow(dead_code, unused_variables)]
fn rm_ext(filename: &String, extension: &str) -> String {
    todo!("rm_ext");
}

fn main() {
    let mut args = env::args();
    let progname: String = args.next().unwrap_or(String::from("eambfc"));
    show_help(&mut io::stdout(), progname.as_str());
    todo!("main");
}
