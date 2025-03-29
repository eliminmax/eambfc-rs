// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only
use super::RunConfig;
use crate::err::{BFCompileError, BFErrorID};
use crate::OutMode;
use std::ffi::OsString;
use std::os::unix::ffi::{OsStrExt, OsStringExt};

pub(crate) fn parse_args_long(
    args: impl Iterator<Item = OsString>,
) -> Result<RunConfig, (BFCompileError, OutMode)> {
    use lexopt::prelude::*;
    let mut pcfg = super::PartialRunConfig::default();
    let mut parser = lexopt::Parser::from_args(args);
    loop {
        match parser.next() {
            Ok(None) => break,
            Ok(Some(Short('h') | Long("help"))) => return Ok(RunConfig::ShowHelp),
            Ok(Some(Short('V') | Long("version"))) => return Ok(RunConfig::ShowVersion),
            Ok(Some(Short('q') | Long("quiet"))) => pcfg.out_mode.quiet(),
            Ok(Some(Short('j') | Long("json"))) => pcfg.out_mode.json(),
            Ok(Some(Short('O') | Long("optimize"))) => pcfg.optimize = true,
            Ok(Some(Short('k') | Long("keep-failed"))) => pcfg.keep = true,
            Ok(Some(Short('c') | Long("continue"))) => pcfg.cont = true,
            Ok(Some(Short('A') | Long("list-targets"))) => return Ok(RunConfig::ListArches),
            Ok(Some(Short('a') | Long("target-arch"))) => {
                if let Ok(val) = parser.value() {
                    pcfg.set_arch(val.as_bytes())?;
                } else {
                    return Err(pcfg.gen_err(
                        BFErrorID::MissingOperand,
                        "-a requires an additional argument",
                    ));
                }
            }
            Ok(Some(Short('t') | Long("tape-size"))) => {
                if let Ok(val) = parser.value() {
                    pcfg.set_tape_size(val.into_vec())?;
                } else {
                    return Err(pcfg.gen_err(
                        BFErrorID::MissingOperand,
                        "-t requires an additional argument",
                    ));
                }
            }
            Ok(Some(Short('e') | Long("source-suffix"))) => {
                if let Ok(val) = parser.value() {
                    pcfg.set_ext(val.into_vec())?;
                } else {
                    return Err(pcfg.gen_err(
                        BFErrorID::MissingOperand,
                        "-e requires an additional argument",
                    ));
                }
            }
            Ok(Some(Short('s') | Long("output-suffix"))) => {
                if let Ok(val) = parser.value() {
                    pcfg.set_suffix(val.into_vec())?;
                } else {
                    return Err(pcfg.gen_err(
                        BFErrorID::MissingOperand,
                        "-s requires an additional argument",
                    ));
                }
            }
            Ok(Some(Short(c))) => {
                return Err(pcfg.gen_err(
                    BFErrorID::UnknownArg,
                    format!("'-{c}' is not a recognized argument"),
                ))
            }
            Ok(Some(Long(l))) => {
                return Err(pcfg.gen_err(
                    BFErrorID::UnknownArg,
                    format!("\"--{l}\" is not a recognized argument"),
                ))
            }
            Ok(Some(Value(v))) => pcfg.source_files.push(v),
            Err(lexopt::Error::UnexpectedValue { option, .. }) => {
                return Err(pcfg.gen_err(
                    BFErrorID::UnexpectedArgValue,
                    format!("Option {option} doesn't take a value"),
                ));
            }
            Err(lexopt::Error::MissingValue { option: None }) => {
                // I don't see how this could be reached - how could a nonexistent option be
                // missing an argument?
                return Err(pcfg.gen_err(BFErrorID::MissingOperand, "additional argument required"));
            }
            Err(lexopt::Error::MissingValue {
                option: Some(option),
            }) => {
                return Err(pcfg.gen_err(
                    BFErrorID::MissingOperand,
                    format!("{option} requires an additional argument"),
                ));
            }
            Err(_) => unreachable!("Remaining variants would require unused lexopt functionality"),
        }
    }
    Ok(RunConfig::StandardRun(pcfg.try_into()?))
}

#[cfg(test)]
mod tests {
    use super::super::*;
    use super::parse_args_long;

    // a more concise way to write OsString::from(a)
    #[cfg(not(tarpaulin_include))]
    fn arg(a: impl Into<OsString>) -> OsString {
        a.into()
    }

    #[test]
    fn longopts_are_like_shortopts() {
        // For standalone options, make sure that they're handled identically in short and long
        // forms
        let pairs = vec![
            ("-h", "--help"),
            ("-V", "--version"),
            ("-q", "--quiet"),
            ("-j", "--json"),
            ("-O", "--optimize"),
            ("-k", "--keep-failed"),
            ("-c", "--continue"),
            ("-A", "--list-targets"),
        ];
        for (short_opt, long_opt) in pairs {
            assert_eq!(
                parse_args_long(vec![arg(short_opt), arg("f.bf")].into_iter()),
                parse_args_long(vec![arg(long_opt), arg("f.bf")].into_iter()),
            );
        }

        // For flags that take arguments, make sure that the forms `-a x86_64`,
        // `--target-arch x86_64`, `-ax86_64`, and `--target-arch=x86_64` are all processed
        // identically.
        let param_opts = vec![
            (
                "-a",
                "--target-arch",
                vec![arg(env!("EAMBFC_DEFAULT_ARCH"))],
            ),
            (
                "-t",
                "--tape-size",
                vec![arg("1"), arg("###"), arg("0"), arg(u64::MAX.to_string())],
            ),
            ("-e", "--source-suffix", vec![arg(".beef")]),
            ("-s", "--output-suffix", vec![arg(".elf")]),
        ];
        for (short, long, test_params) in param_opts {
            for param in test_params {
                let mut joined_short = arg(short);
                joined_short.push(&param);
                let mut joined_long = arg(long);
                joined_long.push("=");
                joined_long.push(&param);
                let a = parse_args_long(vec![arg(short), param.clone(), arg("f.bf")].into_iter());
                let b = parse_args_long(vec![arg(long), param, arg("f.bf")].into_iter());
                let c = parse_args_long(vec![joined_short, arg("f.bf")].into_iter());
                let d = parse_args_long(vec![joined_long, arg("f.bf")].into_iter());
                assert_eq!(a, b);
                assert_eq!(a, c);
                assert_eq!(a, d);
            }
        }
    }

    #[test]
    fn behaves_like_parse_args() {
        // test args copied from every unit test for the original parse_args except for
        // `options_dont_mix_with_files`, to make sure they're processed identically to
        // `parse_args`. (getopt_long does allow options to mix with files as long as the
        // environment variable POSIXLY_CORRECT is not set).
        let arg_groups = vec![
            vec![
                // should be interpreted identically to -k -j -e .brainfuck'
                arg("-kje.brainfuck"),
                arg("foo.brainfuck"),
                arg("bar.brainfuck"),
            ],
            vec![
                // should be interpreted identically to -kje.brainfuck'
                arg("-k"),
                arg("-j"),
                arg("-e"),
                arg(".brainfuck"),
                arg("foo.brainfuck"),
                arg("bar.brainfuck"),
            ],
            vec![arg("--"), arg("-j"), arg("-h"), arg("-e.notbf")],
            vec![arg("-h")],
            vec![arg("-V")],
            vec![],
            vec![arg("-t"), arg("###")],
            vec![arg("-t1"), arg("-t1024")],
            vec![arg("-t0")],
            vec![arg("-t9223372036854775807")],
            vec![arg("-t")],
            vec![arg("-e")],
            vec![arg("-a")],
            vec![arg("-q"), arg("f.bf")],
            vec![arg("-j"), arg("f.bf")],
            vec![arg("-qj"), arg("f.bf")],
            vec![arg("-jq"), arg("f.bf")],
            vec![arg("-Ok"), arg("foo.bf")],
            vec![arg("-Ok"), arg("-c"), arg("foo.bf")],
            vec![arg("-c"), arg("foo.bf")],
            vec![arg("-Oc"), arg("foo.bf")],
            vec![arg("-kOccOk"), arg("foo.bf")],
            vec![arg("foo.bf")],
            vec![arg("-e.brainfuck"), arg("-e"), arg(".bf")],
            vec![arg("-u")],
            vec![arg("-A")],
            vec![arg("-e"), arg(".b"), arg("-A")],
            vec![arg("-aarm64"), arg("foo.bf")],
            vec![arg("-aaarch64"), arg("foo.bf")],
            vec![arg("-ariscv64"), arg("foo.bf")],
            vec![arg("-ariscv"), arg("foo.bf")],
            vec![arg("-as390x"), arg("foo.bf")],
            vec![arg("-as390"), arg("foo.bf")],
            vec![arg("-az/architecture"), arg("foo.bf")],
            vec![arg("-ax86_64"), arg("foo.bf")],
            vec![arg("-ax64"), arg("foo.bf")],
            vec![arg("-aamd64"), arg("foo.bf")],
            vec![arg("-ax86-64"), arg("foo.bf")],
            vec![arg("-apdp11"), arg("foo.bf")],
            vec![arg("-ax86_64"), arg("-aarm64"), arg("foo.bf")],
        ];

        for args in arg_groups {
            assert_eq!(
                parse_args(args.clone().into_iter()),
                parse_args_long(args.clone().into_iter()),
                "{args:?} were parsed differently by parse_args and parse_args_long"
            );
        }
    }

    #[test]
    fn options_can_mix_with_files() {
        use std::env::var_os;
        let cfg = parse_args_long(vec![arg("e.bf"), arg("-h")].into_iter()).unwrap();
        if var_os("POSIXLY_CORRECT").is_some() {
            let RunConfig::StandardRun(StandardRunConfig { source_files, .. }) = cfg else {
                panic!("Expected standard run config")
            };
            assert_eq!(source_files, ["e.bf", "-h"]);
        } else {
            // ensure that -h is not interpreted as a file name (unlike parse_args)
            assert_eq!(cfg, RunConfig::ShowHelp);
        }
    }

    #[test]
    fn unrecognized_longopts() {
        let a = parse_args_long(vec![arg("-R")].into_iter()).unwrap_err();
        let b = parse_args_long(vec![arg("--run-real-fast")].into_iter()).unwrap_err();
        assert_eq!(a.0.error_id(), b.0.error_id());
        assert_eq!(a.0.error_id(), BFErrorID::UnknownArg);
        assert_ne!(a.0, b.0);
    }
}
