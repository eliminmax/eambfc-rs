// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

#[allow(unused_attributes, reason = "tests can be skipped for multiple reasons")]
#[cfg(test)]
mod cli_tests {
    extern crate serde;
    extern crate serde_json;
    extern crate tempfile;
    use serde::Deserialize;
    use tempfile::TempDir;

    use std::path::{Path, PathBuf};
    use std::process::{Command, Stdio};
    use std::{fs, io};
    trait TempDirExt {
        fn join(&self, file: impl AsRef<Path>) -> PathBuf;
    }

    impl TempDirExt for TempDir {
        fn join(&self, file: impl AsRef<Path>) -> PathBuf {
            self.path().join(file)
        }
    }

    const PATH: &str = env!("CARGO_BIN_EXE_eambfc-rs");

    const TEST_FILES: [&str; 9] = [
        "colortest.bf",
        "dead_code.bf",
        "hello.bf",
        "loop.bf",
        "null.bf",
        "rw.bf",
        "truthmachine.bf",
        "wrap2.bf",
        "wrap.bf",
    ];

    fn source_file(file: impl AsRef<Path>) -> PathBuf {
        Path::new("test_assets/bf_sources").join(file)
    }

    fn working_dir() -> TempDir {
        tempfile::tempdir_in(env!("CARGO_TARGET_TMPDIR")).unwrap()
    }

    /// Consumes its arguments, constructing a `std::process::Command` prepared to invoke the
    /// target binary with those arguments
    macro_rules! eambfc_with_args {
        // internal variant
        (with_cmd $cmd:expr, $arg:expr) => {
            $cmd.arg($arg)
        };
        // internal variant
        (with_cmd $cmd:expr, $arg:expr, $($args:expr),*) => {
            eambfc_with_args!(with_cmd $cmd.arg($arg), $($args),*)
        };
        ($arg:expr) => {
            Command::new(PATH).arg($arg)
        };
        ($arg:expr, $($args:expr),*) => {
            eambfc_with_args!(with_cmd Command::new(PATH).arg($arg), $($args),*)
        };
    }

    macro_rules! invoke {
        ($cmd: expr) => {
            assert!($cmd.status().unwrap().success())
        };
        (expect_failure, $cmd: expr) => {
            assert!(!$cmd.status().unwrap().success())
        };
    }

    macro_rules! checked_output {
        ($cmd: expr) => {{
            let output = $cmd.output().unwrap();
            assert!(output.status.success());
            output.stdout
        }};
        (expect_failure, $cmd: expr, $stream: ident) => {{
            let output = $cmd.output().unwrap();
            assert!(!output.status.success());
            output.$stream
        }};
        (expect_failure, $cmd: expr) => {{
            checked_output!(expect_failure, $cmd, stdout)
        }};
    }

    macro_rules! help_text {
        ($progname: expr) => {{
            format!(
                concat!(include_str!("../src/text_assets/help_template.txt"), '\n'),
                $progname,
                env!("EAMBFC_DEFAULT_ARCH")
            )
        }};
        () => {{
            help_text!(PATH)
        }};
    }

    #[derive(Deserialize, PartialEq, Clone)]
    struct ErrorMsg {
        #[serde(rename = "errorId")]
        error_id: String,
        message: String,
        instruction: Option<String>,
        line: Option<usize>,
        column: Option<usize>,
    }

    impl ErrorMsg {
        fn expected_formatting(errs: &[Self]) -> String {
            use std::fmt::Write;

            let mut s = String::new();
            for err in errs {
                write!(s, "Error {}", err.error_id).unwrap();
                if let Some(instr) = err.instruction.as_ref() {
                    write!(s, " when compiling '{}'", instr.as_bytes().escape_ascii()).unwrap();
                }
                if let (Some(line), Some(col)) = (err.line, err.column) {
                    write!(s, " at line {line} column {col}").unwrap();
                }
                writeln!(s, ": {}", err.message).unwrap();
            }
            s
        }
    }

    macro_rules! test_err {
        ($first_err: expr) => {
            let errors = String::from_utf8(
                checked_output!(expect_failure, eambfc_with_args!("-j"))
            ).unwrap()
            .lines()
            .map(|e| serde_json::from_str(&e).unwrap()).collect::<Vec<_>>();
            assert_eq!(
                ErrorMsg::expected_formatting(&errors).trim(),
                String::from_utf8(
                    checked_output!(expect_failure, Command::new(PATH), stderr)
                ).unwrap().replace(&help_text!(), "").trim()
            );
            assert_eq!(errors[0].error_id, $first_err);
        };
        ($first_err: expr, $($args:expr),+) => {
            let errors = String::from_utf8(
                eambfc_with_args!("-j", $($args),+).output().unwrap().stdout
            ).unwrap()
            .lines()
            .map(|e| serde_json::from_str(&e).unwrap()).collect::<Vec<_>>();
            let output = checked_output!(expect_failure, eambfc_with_args!($($args),+), stderr);
            assert_eq!(
                ErrorMsg::expected_formatting(&errors).trim(),
                String::from_utf8(output).unwrap().replace(&help_text!(), "").trim()
            );
            assert_eq!(errors[0].error_id, $first_err);
        };
    }

    #[test]
    fn test_simple_errors() {
        test_err!("MULTIPLE_EXTENSIONS", "-e", ".bf", "-e", ".b");
        test_err!("MULTIPLE_TAPE_BLOCK_COUNTS", "-t", "32", "-t", "76");
        test_err!("MISSING_OPERAND", "-t");
        test_err!("UNKNOWN_ARG", "-r");
        test_err!("NO_SOURCE_FILES");
        test_err!("BAD_EXTENSION", "e");
        test_err!("NO_TAPE", "-t", "0");
        test_err!("TAPE_TOO_LARGE", "-t9223372036854775807");
        test_err!("NOT_NUMERIC", "-t", "hello");
        test_err!("OPEN_R_FAILED", "nonexistent.bf");
        test_err!("UNKNOWN_ARCH", "-a", "pdp10.99999");
        test_err!(
            "MULTIPLE_ARCHES",
            "-a",
            env!("EAMBFC_DEFAULT_ARCH"),
            "-a",
            env!("EAMBFC_DEFAULT_ARCH")
        );

        let unmatched_open = source_file("unmatched_open.bf");
        let unmatched_close = source_file("unmatched_close.bf");
        test_err!("UNMATCHED_OPEN", &unmatched_open);
        test_err!("UNMATCHED_CLOSE", &unmatched_close);
        // optimization mode uses a separate dedicated check for unbalanced loops, so check again
        test_err!("UNMATCHED_OPEN", "-O", &unmatched_open);
        test_err!("UNMATCHED_CLOSE", "-O", &unmatched_close);
    }

    #[test]
    fn arch_list() {
        use std::fmt::Write;
        let mut expected = format!(
            "This build of {} supports the following architectures:\n\n",
            env!("CARGO_PKG_NAME")
        );
        if cfg!(feature = "x86_64") {
            writeln!(expected, "- x86_64 (aliases: x64, amd64, x86-64)").unwrap();
        }
        if cfg!(feature = "arm64") {
            writeln!(expected, "- arm64 (aliases: aarch64)").unwrap();
        }
        if cfg!(feature = "s390x") {
            writeln!(expected, "- s390x (aliases: s390, z/architecture)").unwrap();
        }
        writeln!(
            expected,
            "\nIf no architecture is specified, it defaults to {}.",
            env!("EAMBFC_DEFAULT_ARCH")
        )
        .unwrap();
        let cmd_output = checked_output!(eambfc_with_args!("-A"));
        assert_eq!(String::from_utf8(cmd_output), Ok(expected));
    }

    #[test]
    fn quiet_means_quiet() {
        let cmd_output = eambfc_with_args!("-q", "these", "are", "quite", "bad", "args", "-t0")
            .output()
            .unwrap();
        assert!(!cmd_output.status.success());
        assert!(cmd_output.stdout.is_empty());
        assert!(cmd_output.stderr.is_empty());
    }

    #[cfg_attr(not(unix), ignore = "Can't test Unix permissions on non-Unix platform")]
    #[test]
    fn permission_error_test() {
        // function still needs to be compilable for non-unix targets, so use conditional
        // compilation to make that possible
        #[cfg(unix)]
        {
            use fs::OpenOptions;

            use std::os::unix::fs::OpenOptionsExt;

            let dir = working_dir();
            let mut open_options = OpenOptions::new();
            open_options
                .write(true)
                .create(true)
                .truncate(false)
                .mode(0o044);
            let unreadable_src = dir.join("unreadable.bf");
            drop(open_options.open(&unreadable_src).unwrap());

            test_err!("OPEN_R_FAILED", &unreadable_src);

            let unwritable_dest = dir.join("unwritable");
            let unwritable_src = unwritable_dest.with_extension("bf");
            fs::copy(source_file("hello.bf"), &unwritable_src).unwrap();

            let mut open_options = OpenOptions::new();
            open_options
                .write(true)
                .create(true)
                .truncate(false)
                .mode(0o555);
            drop(open_options.open(&unwritable_dest).unwrap());
            test_err!("OPEN_W_FAILED", &unwritable_src);
        }
    }

    /// test that both `file` and `file.as_ref().with_extension("unopt")` output `expected` when
    /// invoked
    fn test_compiled_pair(file: impl AsRef<Path>, expected: &[u8]) {
        let file = file.as_ref().canonicalize().unwrap();
        assert_eq!(checked_output!(Command::new(&file)), expected);
        assert_eq!(
            checked_output!(Command::new(file.with_extension("unopt"))),
            expected
        );
    }

    fn test_rw_cmd(rw: impl AsRef<Path>) {
        use io::Write;
        for byte in u8::MIN..=u8::MAX {
            let mut child = Command::new(rw.as_ref())
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .spawn()
                .unwrap();
            child.stdin.take().unwrap().write_all(&[byte]).unwrap();
            let output = child.wait_with_output().unwrap();
            assert!(output.status.success());
            assert_eq!(output.stdout, &[byte]);
        }
    }

    fn test_truthmachine_cmd(truthmachine: impl AsRef<Path>) {
        use io::{Read, Write};

        macro_rules! spawn_tm {
            ($binding: ident, $input: literal) => {
                let mut $binding = Command::new(truthmachine.as_ref())
                    .stdin(Stdio::piped())
                    .stdout(Stdio::piped())
                    .spawn()
                    .unwrap();
                let write_result = $binding.stdin.take().unwrap().write($input);
                assert!(write_result.is_ok_and(|sz| sz == 1));
            };
        }

        spawn_tm!(cmd_0, b"0");
        let output = cmd_0.wait_with_output().unwrap();
        assert!(output.status.success());
        assert_eq!(output.stdout, b"0");

        spawn_tm!(cmd_1, b"1");
        let mut output = cmd_1.stdout.take().unwrap();
        let mut read_buf: [u8; 16] = [0; 16];
        output.read_exact(&mut read_buf).unwrap();
        assert_eq!(read_buf, [b'1'; 16]);
        cmd_1.kill().and_then(|()| cmd_1.wait()).unwrap();
    }

    fn test_arch(arch: &str) {
        let dir = working_dir();
        for file in TEST_FILES.iter().copied() {
            fs::copy(source_file(file), dir.join(file)).unwrap();
        }

        invoke!(eambfc_with_args!("-a", arch).args(TEST_FILES.iter().map(|f| dir.join(f))));
        for file in TEST_FILES {
            let path = dir.join(file).with_extension("");
            fs::rename(&path, path.with_extension("unopt")).unwrap();
        }

        invoke!(eambfc_with_args!("-O", "-a", arch).args(TEST_FILES.iter().map(|f| dir.join(f))));

        test_compiled_pair(dir.join("hello"), b"Hello, world!\n");
        test_compiled_pair(dir.join("null"), b"");
        test_compiled_pair(dir.join("loop"), b"!");
        test_compiled_pair(dir.join("wrap2"), b"0000");
        test_compiled_pair(dir.join("wrap"), "🧟".as_bytes());
        test_compiled_pair(
            dir.join("colortest"),
            include_bytes!("../test_assets/colortest_output"),
        );
        test_rw_cmd(dir.join("rw"));
        test_rw_cmd(dir.join("rw.unopt"));
        test_truthmachine_cmd(dir.join("truthmachine"));
        test_truthmachine_cmd(dir.join("truthmachine.unopt"));
    }

    #[test]
    fn test_optimization() {
        let dir = working_dir();
        let dead_code = dir.join("dead_code.bf");
        let null = dir.join("null.bf");
        fs::copy(source_file("dead_code.bf"), &dead_code).unwrap();
        fs::copy(source_file("null.bf"), &null).unwrap();
        invoke!(eambfc_with_args!("-O", &dead_code, &null));
        // make sure that the optimized build of dead_code and the optimized build of null are
        // byte-for-byte identical
        assert_eq!(
            fs::read(dir.join("dead_code")).unwrap(),
            fs::read(dir.join("null")).unwrap()
        );
    }

    #[cfg_attr(not(feature = "bintests"), ignore = "test requires feature = \"bintests\"")]
    #[cfg_attr(not(feature = "arm64"), ignore = "arm64 support disabled")]
    #[cfg_attr(
        any(target_os = "windows", not(can_run_arm64)),
        ignore = "can't run arm64 Linux ELF binaries"
    )]
    #[test]
    fn test_arm64() {
        test_arch("arm64");
    }

    #[cfg_attr(not(feature = "bintests"), ignore = "test requires feature = \"bintests\"")]
    #[cfg_attr(not(feature = "s390x"), ignore = "s390x support disabled")]
    #[cfg_attr(
        any(target_os = "windows", not(can_run_s390x)),
        ignore = "can't run s390x Linux ELF binaries"
    )]
    #[test]
    fn test_s390x() {
        test_arch("s390x");
    }

    #[cfg_attr(not(feature = "bintests"), ignore = "test requires feature = \"bintests\"")]
    #[cfg_attr(not(feature = "x86_64"), ignore = "x86_64 support disabled")]
    #[cfg_attr(
        any(target_os = "windows", not(can_run_x86_64)),
        ignore = "can't run x86_64 Linux ELF binaries"
    )]
    #[test]
    fn test_x86_64() {
        test_arch("x86_64");
    }

    #[test]
    fn continue_and_keep_flags() {
        let dir = working_dir();
        let ok_src = dir.join("ok.bf");
        let ok_file = ok_src.with_extension("");
        let err_src = dir.join("err.bf");
        let err_file = err_src.with_extension("");
        fs::copy(source_file("unmatched_close.bf"), &err_src).unwrap();
        fs::copy(source_file("hello.bf"), &ok_src).unwrap();

        // make sure that exit code is failure and ok.bf isn't compiled if -c wasn't passed
        invoke!(expect_failure, eambfc_with_args!("-q", &err_src, &ok_src));
        assert!(!ok_file.exists() && !err_file.exists());

        // make sure that ok.bf is still compiled with -c even though err.bf failed
        invoke!(
            expect_failure,
            eambfc_with_args!("-q", "-c", &err_src, &ok_src)
        );
        // because -k was not passed, err should have been deleted
        assert!(ok_file.exists() && !err_file.exists());

        // try compiling err.bf again with -k
        invoke!(expect_failure, eambfc_with_args!("-q", "-k", err_src));
        // now, the file should exist even though compilation failed
        assert!(err_file.exists());
    }

    #[test]
    fn alternative_extension() {
        let dir = working_dir();
        let outfile = dir.join("hello");
        let path = outfile.with_extension("brnfck");
        let hello_path = outfile.with_extension("bf");

        fs::copy(source_file("hello.bf"), &hello_path).unwrap();
        invoke!(eambfc_with_args!(&hello_path));
        let expected = fs::read(&outfile).unwrap();

        fs::rename(hello_path, &path).unwrap();
        invoke!(eambfc_with_args!("-e.brnfck", path));
        assert_eq!(expected, fs::read(&outfile).unwrap());
    }

    #[test]
    fn test_version_output() {
        let expected = format!(
            concat!(
                include_str!("../src/text_assets/version_template.txt"),
                '\n'
            ),
            PATH,
            env!("CARGO_PKG_NAME"),
            env!("CARGO_PKG_VERSION"),
            env!("EAMBFC_RS_GIT_COMMIT"),
        );
        let output = checked_output!(eambfc_with_args!("-V"));
        assert_eq!(output, expected.as_bytes());
    }

    #[test]
    fn test_help_output() {
        let expected = format!(
            concat!(include_str!("../src/text_assets/help_template.txt"), '\n'),
            PATH,
            env!("EAMBFC_DEFAULT_ARCH"),
        );
        let output = checked_output!(eambfc_with_args!("-h"));
        assert_eq!(output, expected.as_bytes());
    }

    #[test]
    #[cfg_attr(not(unix), ignore = "CommandExt::arg0 is unix-only")]
    fn test_alt_argv0_help() {
        // need cfg(unix) here so that CommandExt isn't checked on non-unix targets
        #[cfg(unix)]
        {
            use std::os::unix::process::CommandExt;
            let expected_help = format!(
                concat!(include_str!("../src/text_assets/help_template.txt"), '\n'),
                "bfc",
                env!("EAMBFC_DEFAULT_ARCH"),
            );
            let output = checked_output!(eambfc_with_args!("-h").arg0("bfc"));
            assert_eq!(output, expected_help.as_bytes());
        }
    }
}
