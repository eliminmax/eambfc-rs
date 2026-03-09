// SPDX-FileCopyrightText: 2024 - 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

#![cfg(not(tarpaulin_include))]

//! This build script is used to set the default architecture and set various `cfg` values -
//! primarily those used with the macros in the internal `test_macros` crate

use std::env;
use std::error::Error;
use std::fmt::{self, Debug, Display};
use std::fs;
use std::io::ErrorKind;
use std::path::Path;
use std::process::Command;

macro_rules! have {
    ($arch: literal) => {
        cfg!(feature = $arch)
    };
    ($grouper: tt ($($arch: literal),+)) => {
        cfg!($grouper($(feature = $arch),+))
    };
}

const ARCHES: [&str; 5] = ["x86_64", "arm64", "riscv64", "s390x", "i386"];

/// If `EAMBFC_DEFAULT_ARCH` is set at compile time, ensure that it's an enabled architecture, and
/// use it as the default. Otherwise, try to match architecture that eambfc-rs is compiled for,
/// falling back to the first enabled backend in a fallback list
fn default_arch() -> &'static str {
    macro_rules! first_enabled {
        ($next_up: literal, $($priority_list: tt),+) => {{
            if have!($next_up) {
                $next_up
            } else {
                first_enabled!($($priority_list),+)
            }
        }};
        ($last: expr) => {{
            $last
        }}
    }

    macro_rules! arch_check {
        ($arch: literal) => {{
            if !have!($arch) {
                println!(
                    "cargo::error=Can't default to {} unless it's enabled",
                    $arch
                );
            }
            $arch
        }};
    }

    let fallback = first_enabled!("x86_64", "arm64", "i386", "riscv64", "s390x");

    match env::var("EAMBFC_DEFAULT_ARCH").as_deref() {
        Ok("arm64") => arch_check!("arm64"),
        Ok("riscv64") => arch_check!("riscv64"),
        Ok("i386") => arch_check!("i386"),
        Ok("s390x") => arch_check!("s390x"),
        Ok("x86_64") => arch_check!("x86_64"),
        Ok(unknown) => {
            println!("cargo::error=Can't default to {unknown} as no such backend exists");
            // still need to return something
            first_enabled!(fallback)
        }
        Err(env::VarError::NotUnicode(nonutf8)) => {
            println!(
                "cargo::error=Can't default to {} as no such backend exists",
                nonutf8.display()
            );
            // still need to return something
            first_enabled!(fallback)
        }
        Err(env::VarError::NotPresent) => {
            match env::var("CARGO_CFG_TARGET_ARCH").unwrap().as_str() {
                "aarch64" => first_enabled!("arm64", fallback),
                "i386" | "i486" | "i586" | "i686" => first_enabled!("i386", "x86_64", fallback),
                "s390x" => first_enabled!("s390x", fallback),
                "riscv64" => first_enabled!("riscv64", fallback),
                "x86_64" => first_enabled!("x86_64", "i386", fallback),
                _ => first_enabled!(fallback),
            }
        }
    }
}

fn can_run_bintests(arch: &str) -> bool {
    have!("bintests")
        && Command::new(&(String::from("./test_assets/exec_support/") + arch))
            .status()
            .is_ok_and(|s| s.success())
}

fn metavalue(cond: bool, value: &str) {
    println!("cargo::rustc-check-cfg=cfg({value})");
    if cond {
        println!("cargo::rustc-cfg={value}");
    }
}

/// The following cfgs are set are set in the following cases:
///
/// * `cross_compiled`: Set when the build.rs `HOST` and `TARGET` values differ - used to skip
///   tests which may have issues when running through compatibility layers like wine
///     * If it's set, and any of the tests that would be skipped are enabled, it will direct Cargo
///       to issue a warning
/// * `have_64bit_targets`: Set when at least one 64-bit backend is enabled
/// * `have_32bit_targets`: Set when at least one 32-bit backend is enabled
/// * `have_le_targets`: Set when at least one little-endian backend is enabled
/// * `have_be_targets`: Set when at least one big-endian backend is enabled
/// * `can_run_default`: Set when the default backend executables can be run
/// * `can_run_{arch}`: used when the `{arch}` backend executables can be run
fn set_cfg_metavalues() {
    let cross_compiled = env::var("HOST") != env::var("TARGET");
    metavalue(cross_compiled, "cross_compiled");
    if cross_compiled {
        macro_rules! warn_skipped {
            ($feature_str: literal) => {{
                println!(
                    "cargo::warning=tests enabled by {} are skipped when cross-compiling",
                    $feature_str
                );
            }};
        }
        if cfg!(test) {
            match (have!("bintests"), have!("disasmtests")) {
                (false, false) => warn_skipped!("\"bintests\" and \"disasmtests\" features"),
                (false, true) => warn_skipped!("\"bintests\" feature"),
                (true, false) => warn_skipped!("\"disasmtests\" feature"),
                (true, true) => (),
            }
        }
    }

    metavalue(
        have!(any("x86_64", "arm64", "riscv64", "s390x")),
        "have_64bit_targets",
    );
    metavalue(have!("i386"), "have_32bit_targets");
    metavalue(
        have!(any("x86_64", "arm64", "riscv64", "i386")),
        "have_le_targets",
    );
    metavalue(have!("s390x"), "have_be_targets");
    metavalue(
        have!(all("x86_64", "arm64", "riscv64", "s390x", "i386")),
        "have_all_targets",
    );
    let default_arch = default_arch();
    println!("cargo::rustc-cfg=eambfc_default_arch={default_arch:?}");
    println!(concat!(
        "cargo::rustc-check-cfg=cfg(eambfc_default_arch, values(",
        r#""arm64", "i386", "riscv64", "s390x", "x86_64""#,
        "))"
    ));

    let mut hit_default = false;
    for arch in ARCHES {
        let can_run = can_run_bintests(arch);
        metavalue(can_run, &format!("can_run_{arch}"));
        if arch == default_arch {
            hit_default = true;
            metavalue(can_run, "can_run_default");
        }
    }
    if !hit_default {
        println!("cargo::rustc-check-cfg=cfg(can_run_default)");
    }
}

struct ErrMsg(Box<dyn Error>);

impl Debug for ErrMsg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self}")
    }
}

impl Display for ErrMsg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{}\n\n--\n\n{:?}", self.0, self.0)
    }
}

impl<T: Error + 'static> From<T> for ErrMsg {
    fn from(err: T) -> Self {
        ErrMsg(Box::from(err))
    }
}

fn main() -> Result<(), ErrMsg> {
    println!("cargo::rerun-if-changed=.git/index");
    println!("cargo::rerun-if-changed=.commitinfo");
    println!("cargo::rerun-if-env-changed=EAMBFC_DEFAULT_ARCH");
    if !have!(any("x86_64", "arm64", "riscv64", "s390x", "i386")) {
        println!("cargo::error=No backends enabled");
    }
    set_cfg_metavalues();

    if !Path::new(".git").exists() {
        fs::write(".commitinfo", "\nNot built from git repository")?;
        return Ok(());
    }

    if Command::new("git")
        .spawn()
        .is_err_and(|e| e.kind() == ErrorKind::NotFound)
    {
        println!("cargo::warning:Building from git repo, but git is not available at build time");
        // truncate commit info
        fs::write(".commitinfo", "")?;
        return Ok(());
    }

    let cmd_output = Command::new("git")
        .args(["log", "-n1", "--pretty=format:built from git commit: %h"])
        .output()?;
    assert!(
        cmd_output.status.success(),
        "Could not determine commit hash: {}",
        cmd_output.stderr.escape_ascii()
    );
    let mut commit_info = String::from_utf8(cmd_output.stdout)?;

    if !Command::new("git")
        .args(["status", "--short"])
        .output()?
        .stdout
        .is_empty()
    {
        commit_info += " (with local changes)";
    }

    fs::write(".commitinfo", commit_info)?;
    Ok(())
}
