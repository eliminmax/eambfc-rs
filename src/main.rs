// SPDX-FileCopyrightText: 2024 - 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

//! An (optionally) optimizing brainfuck compiler targeting `arm64`, `s390x`, and `x86_64` Linux
//! systems\*.
//!
//! \* Each supported platform has an associated feature, and will only be compiled in if that
//! feature is enabled. By default, all backends are enabled*

mod arg_parse;
mod compile;
mod err;

use std::borrow::Cow;
use std::env::args_os;
use std::process::ExitCode;

use crate::arg_parse::RunConfig;
use crate::compile::elf_tools::ElfArch;
use crate::compile::BFCompile;
use crate::err::OutMode;

// architecture interfaces
#[cfg(feature = "arm64")]
use crate::compile::backends::Arm64Inter;
#[cfg(feature = "s390x")]
use crate::compile::backends::S390xInter;
#[cfg(feature = "x86_64")]
use crate::compile::backends::X86_64Inter;

fn main() -> ExitCode {
    let mut exit_code = ExitCode::SUCCESS;
    let mut args = args_os();
    // if args[0] is not present, it's sensible to fall back to the name cargo is using
    let progname: Cow<'static, str> = args.next().map_or(env!("CARGO_BIN_NAME").into(), |c| {
        c.to_string_lossy().to_string().into()
    });
    match arg_parse::parse_args(args) {
        Ok(RunConfig::ListArches) => {
            println!(concat!(
                "This build of ",
                env!("CARGO_PKG_NAME"),
                " supports the following architectures:\n"
            ));
            #[cfg(feature = "x86_64")]
            println!("- x86_64 (aliases: x64, amd64, x86-64)");
            #[cfg(feature = "arm64")]
            println!("- arm64 (aliases: aarch64)");
            #[cfg(feature = "s390x")]
            println!("- s390x (aliases: s390, z/architecture)");
            println!(concat!(
                "\nIf no architecture is specified, it defaults to ",
                env!("EAMBFC_DEFAULT_ARCH"),
                '.'
            ));
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
                macro_rules! compile_with {
                    ($inter: ident) => {{
                        $inter::compile_file(
                            f.as_ref(),
                            &rc.extension,
                            rc.optimize,
                            rc.keep,
                            rc.tape_blocks,
                        )
                    }};
                }
                let comp_result = match rc.arch {
                    #[cfg(feature = "arm64")]
                    ElfArch::Arm64 => compile_with!(Arm64Inter),
                    #[cfg(feature = "s390x")]
                    ElfArch::S390x => compile_with!(S390xInter),
                    #[cfg(feature = "x86_64")]
                    ElfArch::X86_64 => compile_with!(X86_64Inter),
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
                env!("CARGO_PKG_NAME"),
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
