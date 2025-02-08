// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

#[cfg(not(unix))]
trait FakeOpenOptionsExt {
    fn mode(&self, _perms: u32) {}
}
#[cfg(not(unix))]
impl FakeOpenOptionsExt for std::fs::OpenOptions {}
#[cfg(test)]
mod cli_tests {
    extern crate serde;
    extern crate serde_json;
    extern crate tempfile;
    use serde::Deserialize;
    use static_init::dynamic;
    use tempfile::TempDir;

    use std::path::{Path, PathBuf};
    use std::process::{Command, Stdio};
    use std::sync::OnceLock;
    use std::{fs, io};

    const PATH: &str = env!("CARGO_BIN_EXE_eambfc-rs");

    const TEST_FILES: [&str; 10] = [
        "alternative_extension.brnfck",
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

    struct IsInit;
    static INIT: OnceLock<IsInit> = OnceLock::new();
    /// Return the working directory. The first time it's called, it's initialized with `TempDir`,
    /// and subdirectories for each testable arches are created, with the source files for each test
    /// copied into them.
    fn working_dir() -> impl std::ops::Deref<Target = TempDir> {
        #[dynamic(lazy, drop)]
        static mut WORKING_DIR: TempDir =
            tempfile::tempdir_in(env!("CARGO_TARGET_TMPDIR")).unwrap();
        fn init_arch_dir(dst: impl AsRef<Path>) {
            fs::create_dir(&dst).unwrap();
            for file in TEST_FILES.iter().copied() {
                fs::copy(
                    PathBuf::from("./test_assets/templates").join(file),
                    dst.as_ref().join(file),
                )
                .unwrap();
            }
        }
        INIT.get_or_init(|| {
            #[cfg(can_run_arm64)]
            init_arch_dir(WORKING_DIR.read().path().join("arm64"));
            #[cfg(can_run_s390x)]
            init_arch_dir(WORKING_DIR.read().path().join("s390x"));
            #[cfg(can_run_x86_64)]
            init_arch_dir(WORKING_DIR.read().path().join("x86_64"));
            IsInit
        });
        WORKING_DIR.read()
    }

    fn temp_asset(sub_path: impl AsRef<Path>) -> PathBuf {
        working_dir().path().join(sub_path)
    }

    macro_rules! eambfc_with_args {
        (with_cmd $cmd:expr, $arg:expr) => {
            $cmd.arg($arg)
        };
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
            s = s.trim().to_string();
            s
        }

        fn validate_formatting(errs: &[Self], cmd: &mut Command) {
            let mut output = String::from_utf8(cmd.output().unwrap().stderr).unwrap();
            output = output.replace(
                &format!(
                    include_str!("../src/text_assets/help_template.txt"),
                    PATH,
                    env!("EAMBFC_DEFAULT_ARCH")
                ),
                "",
            );
            output = output.trim().to_string();
            assert_eq!(Self::expected_formatting(errs), output,);
        }
    }

    macro_rules! test_err {
        ($first_err: expr) => {
            let errors = String::from_utf8(eambfc_with_args!("-j").output().unwrap().stdout)
            .unwrap()
            .lines()
            .map(|e| serde_json::from_str(&e).unwrap()).collect::<Vec<_>>();
            ErrorMsg::validate_formatting(
                &errors,
                &mut Command::new(PATH),
            );
            assert_eq!(errors[0].error_id, $first_err);
        };
        ($first_err: expr, $($args:expr),+) => {
            let errors = String::from_utf8(
                eambfc_with_args!("-j", $($args),+).output().unwrap().stdout
            ).unwrap()
            .lines()
            .map(|e| serde_json::from_str(&e).unwrap()).collect::<Vec<_>>();
            ErrorMsg::validate_formatting(
                &errors,
                eambfc_with_args!($($args),+)
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
        test_err!("UNMATCHED_OPEN", "./test_assets/unmatched_open.bf");
        test_err!("UNMATCHED_CLOSE", "./test_assets/unmatched_close.bf");
        // optimization mode uses a separate dedicated check for unbalanced loops, so check again
        test_err!("UNMATCHED_OPEN", "-O", "./test_assets/unmatched_open.bf");
        test_err!("UNMATCHED_CLOSE", "-O", "./test_assets/unmatched_close.bf");
    }

    #[test]
    fn quiet_means_quiet() {
        let cmd_output = eambfc_with_args!("-q", "these", "are", "quite", "bad", "args", "-t0")
            .output()
            .unwrap();
        assert!(cmd_output.stdout.is_empty());
        assert!(cmd_output.stderr.is_empty());
    }

    #[cfg_attr(not(unix), ignore = "Can't test Unix permissions on non-Unix platform")]
    #[test]
    fn permission_error_test() -> io::Result<()> {
        use fs::{copy as copy_file, OpenOptions};

        // function still needs to be compilable for non-unix targets, so use conditional
        // compilation to make that possible
        #[cfg(unix)]
        use std::os::unix::fs::OpenOptionsExt;
        // for non-unix targets, implement a dummy trait with a do-nothing "mode" function
        #[cfg(not(unix))]
        use super::FakeOpenOptionsExt;

        let mut open_options = OpenOptions::new();
        open_options
            .write(true)
            .create(true)
            .truncate(false)
            .mode(0o044);
        let unreadable_src = temp_asset("unreadable.bf");
        drop(open_options.open(&unreadable_src)?);
        test_err!(
            "OPEN_R_FAILED",
            unreadable_src.as_os_str().to_str().unwrap()
        );

        let unwritable_dest = temp_asset("unwritable");
        let unwritable_src = temp_asset("unwritable.bf");
        copy_file(
            "test_assets/templates/hello.bf",
            temp_asset("unwritable.bf"),
        )?;
        let mut open_options = OpenOptions::new();
        open_options
            .write(true)
            .create(true)
            .truncate(false)
            .mode(0o555);
        drop(open_options.open(&unwritable_dest)?);
        test_err!(
            "OPEN_W_FAILED",
            unwritable_src.as_os_str().to_str().unwrap()
        );
        Ok(())
    }

    fn test_fixed_output(file: impl AsRef<Path>, expected: &[u8]) {
        let result = Command::new(file.as_ref()).output().unwrap();
        assert!(result.status.success());
        assert_eq!(result.stdout, expected, "{}", expected.escape_ascii());
        let result = Command::new(file.as_ref().with_extension("unopt"))
            .output()
            .unwrap();
        assert!(result.status.success());
        assert_eq!(result.stdout, expected, "{}", expected.escape_ascii());
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
        use fs::File;
        use io::Read;
        let base_dir = working_dir().path().join(arch);
        let alt_ext_result = Command::new(PATH)
            .args(["-a", arch])
            .arg("-e.brnfck")
            .arg(base_dir.join("alternative_extension.brnfck"))
            .status()
            .unwrap();
        assert!(alt_ext_result.success());
        let general_result = Command::new(PATH)
            .args(["-a", arch])
            .args(TEST_FILES[1..].iter().map(|f| base_dir.join(f)))
            .status()
            .unwrap();
        assert!(general_result.success());
        for file in TEST_FILES {
            let path = base_dir.join(file).with_extension("");
            fs::rename(&path, path.with_extension("unopt")).unwrap();
        }
        let alt_ext_optimized_result = Command::new(PATH)
            .args(["-O", "-a", arch])
            .arg("-e.brnfck")
            .arg(base_dir.join("alternative_extension.brnfck"))
            .status()
            .unwrap();
        assert!(alt_ext_optimized_result.success());
        let optimized_result = Command::new(PATH)
            .arg("-O")
            .args(TEST_FILES[1..].iter().map(|f| base_dir.join(f)))
            .status()
            .unwrap();
        assert!(optimized_result.success());

        test_fixed_output(base_dir.join("alternative_extension"), b"Hello, world!\n");
        test_fixed_output(base_dir.join("hello"), b"Hello, world!\n");
        test_fixed_output(base_dir.join("dead_code"), b"");
        test_fixed_output(base_dir.join("null"), b"");
        test_fixed_output(base_dir.join("loop"), b"!");
        test_fixed_output(base_dir.join("wrap2"), b"0000");
        test_fixed_output(base_dir.join("wrap"), "🧟".as_bytes());
        test_fixed_output(
            base_dir.join("colortest"),
            include_bytes!("../test_assets/colortest_output"),
        );
        test_rw_cmd(base_dir.join("rw"));
        test_rw_cmd(base_dir.join("rw.unopt"));

        // make sure that the optimized build of dead_code and the optimized build of null are
        // byte-for-byte identical
        let mut dead_code_elf_bytes = Vec::new();
        let mut null_elf_bytes = Vec::new();
        let dead_code_elf_size = File::open(base_dir.join("dead_code"))
            .unwrap()
            .read_to_end(&mut dead_code_elf_bytes)
            .unwrap();
        let null_elf_size = File::open(base_dir.join("null"))
            .unwrap()
            .read_to_end(&mut null_elf_bytes)
            .unwrap();
        assert_eq!(
            (dead_code_elf_size, dead_code_elf_bytes),
            (null_elf_size, null_elf_bytes)
        );
        test_truthmachine_cmd(base_dir.join("truthmachine"));
        test_truthmachine_cmd(base_dir.join("truthmachine.unopt"));
    }

    #[cfg_attr(not(feature = "arm64"), ignore = "arm64 support disabled")]
    #[cfg_attr(
        any(target_os = "windows", not(can_run_arm64)),
        ignore = "can't run arm64 Linux ELF binaries"
    )]
    #[test]
    fn test_arm64() {
        test_arch("arm64");
    }

    #[cfg_attr(not(feature = "s390x"), ignore = "s390x support disabled")]
    #[cfg_attr(
        any(target_os = "windows", not(can_run_s390x)),
        ignore = "can't run s390x Linux ELF binaries"
    )]
    #[test]
    fn test_s390x() {
        test_arch("s390x");
    }

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
        let output = eambfc_with_args!("-V").output().unwrap();
        assert!(output.status.success());
        assert_eq!(
            output.stdout,
            expected.as_bytes(),
            "\n\n{:?}\n\n{expected:?}\n\n",
            output.stdout.escape_ascii().to_string()
        );
    }

    #[test]
    fn test_help_output() {
        let expected = format!(
            concat!(include_str!("../src/text_assets/help_template.txt"), '\n'),
            PATH,
            env!("EAMBFC_DEFAULT_ARCH"),
        );
        let output = eambfc_with_args!("-h").output().unwrap();
        assert!(output.status.success());
        assert_eq!(output.stdout, expected.as_bytes());
    }

    #[test]
    #[cfg_attr(not(unix), ignore = "CommandExt::arg0 is unix-only")]
    fn test_alt_argv0_help() {
        #[cfg(unix)] {
            use std::os::unix::process::CommandExt;
            let expected_help = format!(
                concat!(include_str!("../src/text_assets/help_template.txt"), '\n'),
                "bfc",
                env!("EAMBFC_DEFAULT_ARCH"),
            );
            let output = eambfc_with_args!("-h").arg0("bfc").output().unwrap();
            assert!(output.status.success());
            assert_eq!(output.stdout, expected_help.as_bytes());
        }
    }
}
