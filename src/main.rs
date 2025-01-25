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
pub mod fsutil;

use arg_parse::RunConfig;
use compile::BFCompile;
use elf_tools::ELFArch;
pub use err::OutMode;
use std::borrow::Cow;
use std::env::args_os;
use std::process::ExitCode;

// architecture interfaces
#[cfg(feature = "arm64")]
use backend_arm64::Arm64Inter;
#[cfg(feature = "s390x")]
use backend_s390x::S390xInter;
#[cfg(feature = "x86_64")]
use backend_x86_64::X86_64Inter;

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
                    ELFArch::Arm64 => Arm64Inter::compile_file(
                        f.as_ref(),
                        &rc.extension,
                        rc.optimize,
                        rc.keep,
                        rc.tape_blocks,
                    ),
                    #[cfg(feature = "s390x")]
                    ELFArch::S390x => S390xInter::compile_file(
                        f.as_ref(),
                        &rc.extension,
                        rc.optimize,
                        rc.keep,
                        rc.tape_blocks,
                    ),
                    #[cfg(feature = "x86_64")]
                    ELFArch::X86_64 => X86_64Inter::compile_file(
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
                    ELFArch::default()
                );
            }
        }
    }
    exit_code
}
