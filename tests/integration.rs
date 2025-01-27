// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

#[cfg(test)]
mod integration_tests {
    extern crate serde;
    extern crate serde_json;
    use serde::Deserialize;
    use std::process::Command;

    const PATH: &str = "./target/debug/eambfc-rs";

    macro_rules! eambfc_with_args {
        () => {
            Command::new(PATH)
        };
        ($arg:literal) => {
            eambfc_with_args!().arg($arg)
        };
        ($arg:literal  $($args:literal )+) => {
            eambfc_with_args!(eambfc_with_args!().arg($arg), $($args )+)
        };
        ($cmd:expr, $arg:literal) => {
            $cmd.arg($arg)
        };
        ($cmd:expr, $arg:literal  $($args:literal )+) => {
            eambfc_with_args!($cmd.arg($arg), $($args )+)
        };
    }

    #[allow(
        non_snake_case,
        reason = "Match de-facto JSON schema used within the output"
    )]
    #[derive(Deserialize, Debug, PartialEq, Clone)]
    struct ErrorMsg {
        #[deny(unused)]
        errorId: String,
        message: String,
        instruction: Option<String>,
        line: Option<usize>,
        column: Option<usize>,
    }

    impl ErrorMsg {
        fn expected_formatting(errs: &[Self]) -> String {
            use std::fmt::Write;

            let mut s: String = String::new();
            for err in errs {
                write!(s, "Error {}", err.errorId).unwrap();
                if let Some(instr) = err.instruction.as_ref() {
                    write!(s, " when compiling '{}'", instr.as_bytes().escape_ascii()).unwrap();
                }
                if let (Some(line), Some(col)) = (err.line, err.column) {
                    write!(s, " at line {line} column {col}").unwrap();
                }
                writeln!(s, ": {}", err.message).unwrap();
            }
            s = s.trim().to_string();
            s
        }

        fn validate_formatting(errs: &[Self], cmd: &mut Command) {
            let mut output = String::from_utf8(cmd.output().unwrap().stderr).unwrap();
            output = output.replace(
                &format!(
                    include_str!("../src/text_assets/help_template.txt"),
                    PATH, "x86_64"
                ),
                "",
            );
            output = output.trim().to_string();
            assert_eq!(Self::expected_formatting(errs), output,);
        }
    }

    macro_rules! test_err {
        ($first_err: literal, $($args: literal )*) => {
            let errors = String::from_utf8(
                eambfc_with_args!("-j" $($args )*).output().unwrap().stdout
                ).unwrap().lines().map(|e| serde_json::from_str(&e).unwrap()).collect::<Vec<_>>();
            ErrorMsg::validate_formatting(
                &errors,
                eambfc_with_args!($($args )*)
            );
            assert_eq!(errors[0].errorId, $first_err);
        };
    }

    #[test]
    fn test_simple_errors() {
        test_err!("MULTIPLE_EXTENSIONS", "-e" ".bf" "-e" ".b");
        test_err!("MULTIPLE_TAPE_BLOCK_COUNTS", "-t" "32" "-t" "76");
        test_err!("MISSING_OPERAND", "-t");
        test_err!("UNKNOWN_ARG", "-r");
        test_err!("NO_SOURCE_FILES", "-k");
        test_err!("BAD_EXTENSION", "e");
        test_err!("NO_TAPE", "-t" "0");
        test_err!("TAPE_TOO_LARGE", "-t9223372036854775807");
        test_err!("NOT_NUMERIC", "-t" "hello");
        test_err!("OPEN_R_FAILED", "nonexistent.bf");
        test_err!("UNKNOWN_ARCH", "-a" "pdp10.99999");
        test_err!("MULTIPLE_ARCHES", "-a" "amd64" "-aarm64");
    }

    #[test]
    fn quiet_means_quiet() {
        let cmd_output = eambfc_with_args!("-q" "these" "are" "quite" "bad" "args" "-t0")
            .output()
            .unwrap();
        assert!(cmd_output.stdout.is_empty());
        assert!(cmd_output.stderr.is_empty());
    }
}
