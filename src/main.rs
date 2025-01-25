// SPDX-FileCopyrightText: 2024 - 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

mod arch_inter;
mod arg_parse;
mod backends;
mod compile;
mod elf_tools;
mod err;
mod optimize;

use std::borrow::Cow;
use std::env::args_os;
use std::process::ExitCode;

use crate::arg_parse::RunConfig;
use crate::compile::BFCompile;
use crate::elf_tools::ElfArch;
use crate::err::OutMode;

// architecture interfaces
#[cfg(feature = "arm64")]
use crate::backends::arm64::Arm64Inter;
#[cfg(feature = "s390x")]
use crate::backends::s390x::S390xInter;
#[cfg(feature = "x86_64")]
use crate::backends::x86_64::X86_64Inter;

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
                ElfArch::default()
            );
        }
        Ok(RunConfig::ShowHelp) => {
            println!(
                include_str!("text_assets/help_template.txt"),
                progname,
                ElfArch::default()
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
                    ElfArch::Arm64 => Arm64Inter::compile_file(
                        f.as_ref(),
                        &rc.extension,
                        rc.optimize,
                        rc.keep,
                        rc.tape_blocks,
                    ),
                    #[cfg(feature = "s390x")]
                    ElfArch::S390x => S390xInter::compile_file(
                        f.as_ref(),
                        &rc.extension,
                        rc.optimize,
                        rc.keep,
                        rc.tape_blocks,
                    ),
                    #[cfg(feature = "x86_64")]
                    ElfArch::X86_64 => X86_64Inter::compile_file(
                        f.as_ref(),
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
                    ElfArch::default()
                );
            }
        }
    }
    exit_code
}
