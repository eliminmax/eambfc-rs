// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only
#![cfg(test)]

#[path = "../src/arg_parse/help_text.rs"]
mod help_text;
use help_text::help_fmt;

extern crate tempfile;
use tempfile::TempDir;

extern crate serde;
extern crate serde_json;
use serde::Deserialize;

extern crate test_macros;
use test_macros::{bin_test, unix_test};

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::{fs, io};

const EXEC_PATH: &str = env!("CARGO_BIN_EXE_eambfc-rs");

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

trait TempDirExt {
    fn join(&self, file: impl AsRef<Path>) -> PathBuf;
}

impl TempDirExt for TempDir {
    fn join(&self, file: impl AsRef<Path>) -> PathBuf {
        self.path().join(file)
    }
}

/// return a `tempfile::TempDir` within `CARGO_TARGET_TMPDIR` that can be used for
fn working_dir() -> io::Result<TempDir> {
    tempfile::tempdir_in(env!("CARGO_TARGET_TMPDIR"))
}

fn source_file(file: impl AsRef<Path>) -> PathBuf {
    Path::new("test_assets/bf_sources").join(file)
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
        Command::new(EXEC_PATH).arg($arg)
    };
    ($arg:expr, $($args:expr),*) => {
        eambfc_with_args!(with_cmd Command::new(EXEC_PATH).arg($arg), $($args),*)
    };
}

/// Invoke a `std::process::Command` (or something with a similar API), ignoring output and
/// panicking if the command fails.
///
/// Alternatively, if the command is preceded with `expect_failure, `, then it panics if the
/// command succeeds.
///
/// # Examples:
/// ```no_run
/// invoke!(Command::new("touch file"));
/// invoke!(expect_failure, Command::new("dd").arg("if=/dev/zero").arg("of=/dev/full"));
/// ```
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
    (expect_failure, $cmd: expr) => {{ checked_output!(expect_failure, $cmd, stdout) }};
}

macro_rules! help_text {
    ($progname: expr) => {{ format!("{}\n", help_fmt($progname)) }};
    () => {{ help_text!(EXEC_PATH) }};
}

#[derive(Deserialize, PartialEq, Clone)]
struct ErrorMsg {
    #[serde(rename = "errorId")]
    error_id: String,
    message: String,
    instruction: Option<String>,
    line: Option<usize>,
    column: Option<usize>,
    file: Option<String>,
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
            if let Some(file) = err.file.as_ref() {
                write!(s, " in file {file}").unwrap();
            }
            if let (Some(line), Some(col)) = (err.line, err.column) {
                write!(s, " at line {line} column {col}").unwrap();
            }
            writeln!(s, ": {}", err.message).unwrap();
        }
        s
    }
}

fn get_errs(eambfc_cmd: &mut Command) -> Vec<ErrorMsg> {
    String::from_utf8(checked_output!(expect_failure, eambfc_cmd))
        .unwrap()
        .lines()
        .map(serde_json::from_str)
        .collect::<Result<Vec<_>, _>>()
        .unwrap()
}

macro_rules! test_err {
    ($first_err: expr) => {
        let errors = get_errs(eambfc_with_args!("-j"));
        assert_eq!(
            ErrorMsg::expected_formatting(&errors).trim(),
            String::from_utf8(
                checked_output!(expect_failure, Command::new(EXEC_PATH), stderr)
            ).unwrap().replace(&help_text!(), "").trim()
        );
        assert_eq!(errors[0].error_id, $first_err);
    };
    ($first_err: expr, $($args:expr),+) => {
        let errors = get_errs(eambfc_with_args!("-j", $($args),+));
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
    test_err!("MultipleExtensions", "-e", ".bf", "-e", ".b");
    test_err!("MultipleOutputExtensions", "-s", ".elf", "-s", ".out");
    test_err!("MultipleTapeBlockCounts", "-t", "32", "-t", "76");
    test_err!("MissingOperand", "-t");
    test_err!("UnknownArg", "-r");
    test_err!("NoSourceFiles");
    test_err!("BadSourceExtension", "e");
    test_err!("TapeSizeZero", "-t", "0");
    test_err!("TapeTooLarge", "-t9223372036854775807");
    test_err!("TapeSizeNotNumeric", "-t", "hello");
    test_err!("OpenReadFailed", "nonexistent.bf");
    test_err!("UnknownArch", "-a", "pdp10.99999");
    test_err!(
        "MultipleArchitectures",
        "-a",
        env!("EAMBFC_DEFAULT_ARCH"),
        "-a",
        env!("EAMBFC_DEFAULT_ARCH")
    );

    test_err!("InputIsOutput", "-s.bf");
    test_err!("InputIsOutput", "-s.b", "-e.b");
    // if -e changes suffix after -s.bf, error shouldn't be InputIsOutput
    test_err!("NoSourceFiles", "-s.bf", "-e.b");

    let unmatched_open = source_file("unmatched_open.bf");
    let unmatched_close = source_file("unmatched_close.bf");
    test_err!("UnmatchedOpen", &unmatched_open);
    test_err!("UnmatchedClose", &unmatched_close);
    // optimization mode uses a separate dedicated check for unbalanced loops, so check again
    test_err!("UnmatchedOpen", "-O", &unmatched_open);
    test_err!("UnmatchedClose", "-O", &unmatched_close);
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
    if cfg!(feature = "riscv64") {
        writeln!(expected, "- riscv64 (aliases: riscv)").unwrap();
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
fn out_suffix() -> io::Result<()> {
    let dir = working_dir()?;
    let src = dir.join("hello.bf");
    fs::copy(source_file("hello.bf"), &src)?;
    invoke!(eambfc_with_args!("-s", ".elf", "--", &src));
    assert!(fs::exists(dir.join("hello.elf"))? && !fs::exists(dir.join("hello"))?);
    Ok(())
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

#[unix_test("PermissionsExt, OpenOptionsExt")]
fn executable_bit_set() -> io::Result<()> {
    use fs::OpenOptions;
    use std::os::unix::fs::{OpenOptionsExt, PermissionsExt};
    let dir = working_dir()?;
    let target = dir.join("null");
    let source = target.with_extension("bf");
    fs::copy(source_file("null.bf"), &source)?;
    invoke!(eambfc_with_args!(&source));
    let mode = fs::metadata(target)?.permissions().mode();

    // create a new file with 777 permissions to check the default mode
    let testfile_path = dir.join(".testfile");
    drop(
        OpenOptions::new()
            .mode(0o777)
            .write(true)
            .create_new(true)
            .open(&testfile_path)?,
    );
    let default_mode = fs::metadata(testfile_path)?.permissions().mode();

    // make sure that the mode matches 0o755 & `mask`
    assert_eq!(mode & 0o777, default_mode & 0o755);
    Ok(())
}

#[unix_test("OpenOptionsExt::mode")]
fn permission_error_test() -> io::Result<()> {
    use fs::OpenOptions;

    use std::os::unix::fs::OpenOptionsExt;

    let dir = working_dir()?;
    let mut open_options = OpenOptions::new();
    open_options
        .write(true)
        .create(true)
        .truncate(false)
        .mode(0o044);
    let unreadable_src = dir.join("unreadable.bf");
    drop(open_options.open(&unreadable_src)?);

    test_err!("OpenReadFailed", &unreadable_src);

    let unwritable_dest = dir.join("unwritable");
    let unwritable_src = unwritable_dest.with_extension("bf");
    fs::copy(source_file("hello.bf"), &unwritable_src)?;

    let mut open_options = OpenOptions::new();
    open_options
        .write(true)
        .create(true)
        .truncate(false)
        .mode(0o555);
    drop(open_options.open(&unwritable_dest)?);
    test_err!("OpenWriteFailed", &unwritable_src);
    Ok(())
}

/// test that both `file` and `file.as_ref().with_extension("unopt")` output `expected` when
/// invoked
fn test_compiled_pair(file: impl AsRef<Path>, expected: &[u8]) -> io::Result<()> {
    let file = file.as_ref().canonicalize()?;
    assert_eq!(checked_output!(Command::new(&file)), expected);
    assert_eq!(
        checked_output!(Command::new(file.with_extension("unopt"))),
        expected
    );
    Ok(())
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

fn test_arch(arch: &str) -> io::Result<()> {
    let dir = working_dir()?;
    for file in TEST_FILES.iter().copied() {
        fs::copy(source_file(file), dir.join(file))?;
    }

    invoke!(eambfc_with_args!("-a", arch).args(TEST_FILES.iter().map(|f| dir.join(f))));
    for file in TEST_FILES {
        let path = dir.join(file).with_extension("");
        fs::rename(&path, path.with_extension("unopt"))?;
    }

    invoke!(eambfc_with_args!("-O", "-a", arch).args(TEST_FILES.iter().map(|f| dir.join(f))));

    test_compiled_pair(dir.join("hello"), b"Hello, world!\n")?;
    test_compiled_pair(dir.join("null"), b"")?;
    test_compiled_pair(dir.join("loop"), b"!")?;
    test_compiled_pair(dir.join("wrap2"), b"0000")?;
    test_compiled_pair(dir.join("wrap"), "🧟".as_bytes())?;
    test_compiled_pair(
        dir.join("colortest"),
        include_bytes!("../test_assets/colortest_output"),
    )?;
    test_rw_cmd(dir.join("rw"));
    test_rw_cmd(dir.join("rw.unopt"));
    test_truthmachine_cmd(dir.join("truthmachine"));
    test_truthmachine_cmd(dir.join("truthmachine.unopt"));
    Ok(())
}

#[test]
fn test_optimization() -> io::Result<()> {
    let dir = working_dir()?;
    let dead_code = dir.join("dead_code.bf");
    let null = dir.join("null.bf");
    fs::copy(source_file("dead_code.bf"), &dead_code)?;
    fs::copy(source_file("null.bf"), &null)?;
    invoke!(eambfc_with_args!("-O", &dead_code, &null));
    // make sure that the optimized build of dead_code and the optimized build of null are
    // byte-for-byte identical
    assert_eq!(
        fs::read(dir.join("dead_code"))?,
        fs::read(dir.join("null"))?
    );
    Ok(())
}

#[bin_test(arm64)]
fn test_arm64() -> io::Result<()> {
    test_arch("arm64")
}

#[bin_test(riscv64)]
fn test_riscv64() -> io::Result<()> {
    test_arch("riscv64")
}

#[bin_test(s390x)]
fn test_s390x() -> io::Result<()> {
    test_arch("s390x")
}

#[bin_test(x86_64)]
fn test_x86_64() -> io::Result<()> {
    test_arch("x86_64")
}

#[test]
fn continue_and_keep_flags() -> io::Result<()> {
    let dir = working_dir()?;
    let ok_src = dir.join("ok.bf");
    let ok_file = ok_src.with_extension("");
    let err_src = dir.join("err.bf");
    let err_file = err_src.with_extension("");
    fs::copy(source_file("unmatched_close.bf"), &err_src)?;
    fs::copy(source_file("hello.bf"), &ok_src)?;

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
    Ok(())
}

#[test]
fn alternative_extension() -> io::Result<()> {
    let dir = working_dir()?;
    let outfile = dir.join("hello");
    let path = outfile.with_extension("brnfck");
    let hello_path = outfile.with_extension("bf");

    fs::copy(source_file("hello.bf"), &hello_path)?;
    invoke!(eambfc_with_args!(&hello_path));
    let expected = fs::read(&outfile)?;

    fs::rename(hello_path, &path)?;
    invoke!(eambfc_with_args!("-e.brnfck", path));
    assert_eq!(expected, fs::read(&outfile)?);
    Ok(())
}

#[test]
fn test_version_output() {
    let expected = format!(
        concat!(
            include_str!("../src/text_assets/version_template.txt"),
            '\n'
        ),
        EXEC_PATH,
        env!("CARGO_PKG_NAME"),
        env!("CARGO_PKG_VERSION"),
        env!("EAMBFC_RS_GIT_COMMIT"),
    );
    let output = checked_output!(eambfc_with_args!("-V"));
    assert_eq!(output, expected.as_bytes());
}

#[test]
fn test_help_output() {
    let output = checked_output!(eambfc_with_args!("-h"));
    assert_eq!(output, help_text!().as_bytes());
}

#[unix_test("CommandExt::arg0")]
fn test_alt_argv0_help() {
    use std::os::unix::process::CommandExt;
    let output = checked_output!(eambfc_with_args!("-h").arg0("bfc"));
    assert_eq!(String::from_utf8(output).unwrap(), help_text!("bfc"));
}

#[test]
fn code_position_reporting() -> io::Result<()> {
    use io::Write;
    let dir = working_dir()?;
    let codepos = dir.join("codepos.bf");
    fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&codepos)?
        .write_all(b"\n+++++++++++++++++++++++++++++++[\n[")?;
    let errors = get_errs(eambfc_with_args!("-j", codepos));
    assert_eq!(errors[0].line, Some(2));
    assert_eq!(errors[0].column, Some(32));
    assert_eq!(errors[0].error_id, "UnmatchedOpen");
    assert_eq!(errors[1].line, Some(3));
    assert_eq!(errors[1].column, Some(1));
    assert_eq!(errors[1].error_id, "UnmatchedOpen");
    Ok(())
}

#[test]
fn non_utf8_code_position_reporting() {
    let errors = get_errs(eambfc_with_args!(
        "-j",
        source_file("non_ascii_positions.bf")
    ));
    assert_eq!(errors[0].error_id, "UnmatchedClose");
    assert_eq!(errors[0].line, Some(6));
    assert_eq!(errors[0].column, Some(11));
    assert_eq!(errors[1].error_id, "UnmatchedOpen");
    assert_eq!(errors[1].line, Some(7));
    assert_eq!(errors[1].column, Some(1));
    assert_eq!(errors[2].error_id, "UnmatchedOpen");
    assert_eq!(errors[2].line, Some(8));
    assert_eq!(errors[2].column, Some(3));
}
