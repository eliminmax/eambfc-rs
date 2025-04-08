// SPDX-FileCopyrightText: 2024 - 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

//! An (optionally) optimizing brainfuck compiler targeting 64-bit Linux systems\*.
//!
//! * The following backends exist currently:
//! * `arm64`
//! * `riscv64`
//! * `s390x`
//! * `x86_64`
//!
//! \* Each supported platform has an associated feature, and will only be compiled in if that
//! feature is enabled. By default, all backends are enabled through the `all_backends` feature*

mod arg_parse;
mod compile;
mod err;

use std::borrow::Cow;
use std::env::args_os;
use std::process::ExitCode;

use arg_parse::{RunConfig, help_fmt};
use compile::{BFCompile, elf_tools::Backend};
use err::OutMode;

// architecture interfaces
#[cfg(feature = "arm64")]
use crate::compile::backends::Arm64Inter;
#[cfg(feature = "riscv64")]
use crate::compile::backends::RiscV64Inter;
#[cfg(feature = "s390x")]
use crate::compile::backends::S390xInter;
#[cfg(feature = "x86_64")]
use crate::compile::backends::X86_64Inter;

fn main() -> ExitCode {
    let mut args = args_os();
    // if args[0] is not present, it's sensible to fall back to the name cargo is using
    let progname: Cow<'static, str> = args.next().map_or(env!("CARGO_BIN_NAME").into(), |c| {
        c.to_string_lossy().to_string().into()
    });
    #[cfg(not(feature = "longopts"))]
    let rc = arg_parse::parse_args(args);
    #[cfg(feature = "longopts")]
    // SAFETY: this function is safe as long as it's in a single-threaded environment, and no
    // threads have been spawned thus far
    let rc = arg_parse::longopts::parse_args_long(args);
    match rc {
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
            #[cfg(feature = "riscv64")]
            println!("- riscv64 (aliases: riscv)");
            #[cfg(feature = "s390x")]
            println!("- s390x (aliases: s390, z/architecture)");
            println!(concat!(
                "\nIf no architecture is specified, it defaults to ",
                env!("EAMBFC_DEFAULT_ARCH"),
                '.'
            ));
            ExitCode::SUCCESS
        }
        Ok(RunConfig::ShowHelp) => {
            println!("{}", help_fmt(&progname));
            ExitCode::SUCCESS
        }
        Ok(RunConfig::StandardRun(rc)) => {
            let mut exit_code = ExitCode::SUCCESS;
            for f in rc.source_files {
                macro_rules! compile_with {
                    ($inter: ident) => {{
                        $inter::compile_file(
                            f.as_ref(),
                            &rc.extension,
                            rc.optimize,
                            rc.keep,
                            rc.tape_blocks,
                            rc.out_suffix.as_deref(),
                        )
                    }};
                }
                let comp_result = match rc.arch {
                    #[cfg(feature = "arm64")]
                    Backend::Arm64 => compile_with!(Arm64Inter),
                    #[cfg(feature = "riscv64")]
                    Backend::RiscV64 => compile_with!(RiscV64Inter),
                    #[cfg(feature = "s390x")]
                    Backend::S390x => compile_with!(S390xInter),
                    #[cfg(feature = "x86_64")]
                    Backend::X86_64 => compile_with!(X86_64Inter),
                };
                if let Err(errs) = comp_result {
                    errs.into_iter().for_each(|e| e.report(rc.out_mode));
                    if !rc.cont {
                        return ExitCode::FAILURE;
                    }
                    exit_code = ExitCode::FAILURE;
                }
            }
            exit_code
        }
        Ok(RunConfig::ShowVersion) => {
            println!(
                include_str!("text_assets/version_template.txt"),
                progname,
                env!("CARGO_PKG_NAME"),
                env!("CARGO_PKG_VERSION"),
                env!("EAMBFC_RS_GIT_COMMIT")
            );
            ExitCode::SUCCESS
        }
        Err((err, out_mode)) => {
            err.report(out_mode);
            if out_mode == OutMode::Basic {
                eprintln!("{}", help_fmt(&progname));
            }
            ExitCode::FAILURE
        }
    }
}
