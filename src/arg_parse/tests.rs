// SPDX-FileCopyrightText: 2024 - 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use super::*;

// a more consice way to write OsString::from(a)
#[cfg(not(tarpaulin_include))]
fn arg(a: impl Into<OsString>) -> OsString {
    a.into()
}

// extract a standard run config
#[cfg(not(tarpaulin_include))]
fn parse_standard(args: Vec<OsString>) -> StandardRunConfig {
    let RunConfig::StandardRun(cfg) = parse_args(args.into_iter()).unwrap() else {
        panic!("test expected StandardRunConfig")
    };
    cfg
}

#[test]
fn combined_args() {
    // ensure that combined arguments are processed properly
    let args_set_0 = vec![
        // should be interpreted identically to -k -j -e .brainfuck'
        arg("-kje.brainfuck"),
        arg("foo.brainfuck"),
        arg("bar.brainfuck"),
    ]
    .into_iter();
    let args_set_1 = vec![
        // should be interpreted identically to -kje.brainfuck'
        arg("-k"),
        arg("-j"),
        arg("-e"),
        arg(".brainfuck"),
        arg("foo.brainfuck"),
        arg("bar.brainfuck"),
    ]
    .into_iter();

    assert_eq!(
        parse_args(args_set_0).unwrap(),
        parse_args(args_set_1).unwrap()
    );
}

#[test]
fn options_stop_on_double_dash() {
    let args_set = vec![arg("--"), arg("-j"), arg("-h"), arg("-e.notbf")];
    // ensure that -h, -j and -e.notbf are interpreted as the list of file names
    let parsed_args = parse_standard(args_set);
    assert_eq!(parsed_args.out_mode, OutMode::Basic);
    assert_eq!(
        parsed_args.source_files,
        vec![arg("-j"), arg("-h"), arg("-e.notbf"),]
    );
}

#[test]
fn options_dont_mix_with_files() {
    // ensure that -h is interpreted as a file name
    assert_eq!(
        parse_standard(vec![arg("e.bf"), arg("-h")]).source_files,
        vec![arg("e.bf"), arg("-h"),]
    );
}

#[test]
fn help_returned() {
    let args_set = vec![arg("-h")].into_iter();
    assert_eq!(parse_args(args_set), Ok(RunConfig::ShowHelp));
}

#[test]
fn version_returned() {
    let args_set = vec![arg("-V")].into_iter();
    assert_eq!(parse_args(args_set), Ok(RunConfig::ShowVersion));
}

#[test]
fn handle_empty_args() {
    let (bf_err, _) = parse_args(vec![].into_iter()).unwrap_err();
    assert_eq!(bf_err.error_id(), BFErrorID::NoSourceFiles);
}

#[test]
fn non_numeric_tape_size() {
    let (err, ..) = parse_args(vec![arg("-t"), arg("###")].into_iter()).unwrap_err();
    assert_eq!(err.error_id(), BFErrorID::NotNumeric);
}

#[test]
fn multiple_tape_size() {
    let args_set = vec![arg("-t1"), arg("-t1024")].into_iter();
    let (err, ..) = parse_args(args_set).unwrap_err();
    assert_eq!(err.error_id(), BFErrorID::MultipleTapeBlockCounts);
}

#[test]
fn tape_size_zero() {
    let args_set = vec![arg("-t0")].into_iter();
    let (err, ..) = parse_args(args_set).unwrap_err();
    assert_eq!(err.error_id(), BFErrorID::NoTape);
}

#[test]
fn tape_too_large() {
    let args_set = vec![arg("-t9223372036854775807")].into_iter();
    let (err, ..) = parse_args(args_set).unwrap_err();
    assert_eq!(err.error_id(), BFErrorID::TapeTooLarge);
}

#[test]
fn missing_operand() {
    let args_set = vec![arg("-t")].into_iter();
    let (err, ..) = parse_args(args_set).unwrap_err();
    assert_eq!(err.error_id(), BFErrorID::MissingOperand);
    let args_set = vec![arg("-e")].into_iter();
    let (err, ..) = parse_args(args_set).unwrap_err();
    assert_eq!(err.error_id(), BFErrorID::MissingOperand);
    let args_set = vec![arg("-a")].into_iter();
    let (err, ..) = parse_args(args_set).unwrap_err();
    assert_eq!(err.error_id(), BFErrorID::MissingOperand);
}

#[test]
fn out_mode_options() {
    assert_eq!(
        parse_standard(vec![arg("-q"), arg("f.bf")]).out_mode,
        OutMode::Quiet
    );
    assert_eq!(
        parse_standard(vec![arg("-j"), arg("f.bf")]).out_mode,
        OutMode::Json
    );
    assert_eq!(
        parse_standard(vec![arg("-qj"), arg("f.bf")]).out_mode,
        OutMode::Json
    );
    assert_eq!(
        parse_standard(vec![arg("-jq"), arg("f.bf")]).out_mode,
        OutMode::Json
    );
}

#[test]
fn single_args_parsed() {
    let args = parse_standard(vec![arg("-Ok"), arg("foo.bf")]);
    assert!(args.keep && args.optimize && !args.cont,);
    let args = parse_standard(vec![arg("-Ok"), arg("-c"), arg("foo.bf")]);
    assert!(args.keep && args.optimize && args.cont,);
    let args = parse_standard(vec![arg("-c"), arg("foo.bf")]);
    assert!(args.cont && !args.optimize && !args.keep,);
    let args = parse_standard(vec![arg("-Oc"), arg("foo.bf")]);
    assert!(args.cont && args.optimize && !args.keep,);
    let args = parse_standard(vec![arg("-kOccOk"), arg("foo.bf")]);
    assert!(args.keep && args.optimize && args.cont,);
    let args = parse_standard(vec![arg("foo.bf")]);
    assert!(!args.keep && !args.optimize && !args.cont,);
}

#[test]
fn multiple_extensions_err() {
    assert!(
        parse_args(vec![arg("-e.brainfuck"), arg("-e"), arg(".bf")].into_iter())
            .is_err_and(|e| e.0.error_id() == BFErrorID::MultipleExtensions)
    );
}

#[test]
fn bad_args_error_out() {
    assert!(parse_args(vec![arg("-u")].into_iter())
        .is_err_and(|e| e.0.error_id() == BFErrorID::UnknownArg));
}

#[test]
fn list_arch_processed() {
    assert_eq!(
        parse_args(vec![arg("-A")].into_iter()),
        Ok(RunConfig::ListArches)
    );
    assert_eq!(
        parse_args(vec![arg("-e"), arg(".b"), arg("-A")].into_iter()),
        Ok(RunConfig::ListArches)
    );
}

#[test]
fn arch_selection() {
    // use these ugly double-checking constructs to avoid trying to construct nonexisttent enum
    // variants when architectures are disabled.
    if cfg!(feature = "arm64") {
        #[cfg(feature = "arm64")]
        {
            assert_eq!(
                parse_standard(vec![arg("-aarm64"), arg("foo.bf")]).arch,
                ElfArch::Arm64
            );
            assert_eq!(
                parse_standard(vec![arg("-aaarch64"), arg("foo.bf")]).arch,
                ElfArch::Arm64
            );
        };
    } else {
        assert!(parse_args(vec![arg("-aarm64"), arg("foo.bf")].into_iter())
            .is_err_and(|e| e.0.error_id() == BFErrorID::UnknownArch));
    }
    if cfg!(feature = "s390x") {
        #[cfg(feature = "s390x")]
        {
            assert_eq!(
                parse_standard(vec![arg("-as390x"), arg("foo.bf")]).arch,
                ElfArch::S390x
            );
            assert_eq!(
                parse_standard(vec![arg("-as390"), arg("foo.bf")]).arch,
                ElfArch::S390x
            );
            assert_eq!(
                parse_standard(vec![arg("-az/architecture"), arg("foo.bf")]).arch,
                ElfArch::S390x
            );
        };
    } else {
        assert!(parse_args(vec![arg("-as390x"), arg("foo.bf")].into_iter())
            .is_err_and(|e| e.0.error_id() == BFErrorID::UnknownArch));
    }
    if cfg!(feature = "x86_64") {
        #[cfg(feature = "x86_64")]
        {
            assert_eq!(
                parse_standard(vec![arg("-ax86_64"), arg("foo.bf")]).arch,
                ElfArch::X86_64
            );
            assert_eq!(
                parse_standard(vec![arg("-ax64"), arg("foo.bf")]).arch,
                ElfArch::X86_64
            );
            assert_eq!(
                parse_standard(vec![arg("-aamd64"), arg("foo.bf")]).arch,
                ElfArch::X86_64
            );
            assert_eq!(
                parse_standard(vec![arg("-ax86-64"), arg("foo.bf")]).arch,
                ElfArch::X86_64
            );
        };
    } else {
        assert!(parse_args(vec![arg("-ax86_64"), arg("foo.bf")].into_iter())
            .is_err_and(|e| e.0.error_id() == BFErrorID::UnknownArch));
    }
    assert!(parse_args(vec![arg("-apdp11"), arg("foo.bf")].into_iter())
        .is_err_and(|e| e.0.error_id() == BFErrorID::UnknownArch));
}

#[test]
fn multiple_arches_error() {
    if cfg!(all(feature = "x86_64", feature = "arm64")) {
        assert!(
            parse_args(vec![arg("-ax86_64"), arg("-aarm64"), arg("foo.bf")].into_iter())
                .is_err_and(|e| e.0.error_id() == BFErrorID::MultipleArches)
        );
    }
}
