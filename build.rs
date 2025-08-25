// SPDX-FileCopyrightText: 2024 - 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only
#![cfg(not(tarpaulin_include))]

// This build script is used to do 3 things:
// 1. check that at least one architecture is enabled
// 2. set the default architecture
// 3. set `cfg` values used for conditional compilation, primarily those used with the proc macros
//    in the internal `test_macros` crate
//
// The level of complexity of those tasks varies greatly.

use std::io::ErrorKind;
use std::path::PathBuf;
use std::process::Command;

// 1. check that at least one architecture is enabled

#[cfg(not(any(
    feature = "x86_64",
    feature = "arm64",
    feature = "riscv64",
    feature = "s390x",
    feature = "i386",
)))]
compile_error!("Must have at least one architecture enabled");

// 2. set the default architecture

/// If `EAMBFC_DEFAULT_ARCH` is set at compile time, check that it's an enabled architecture, then
/// use it as the default. Otherwise, try to match architecture that eambfc-rs is compiled for,
/// falling back to the first enabled backend in a list ordered in descending likelihood of being
/// the desired choice
fn set_default_arch() {
    macro_rules! choose_default {
        ($next_up: literal, $($priority_list: tt),+) => {{
            if cfg!(feature = $next_up) {
                $next_up
            } else {
                choose_default!($($priority_list),+)
            }
        }};
        ($last: expr) => {{
            $last
        }};
    }
    let fallback = choose_default!("x86_64", "arm64", "i386", "riscv64", "s390x");

    macro_rules! arch_check {
        ($arch: literal) => {{
            assert!(
                cfg!(feature = $arch),
                concat!("Can't default to ", $arch, " unless it's enabled")
            );
            $arch
        }};
    }
    let arch = match std::env::var("EAMBFC_DEFAULT_ARCH").ok().as_deref() {
        Some("arm64") => arch_check!("arm64"),
        Some("riscv64") => arch_check!("riscv64"),
        Some("i386") => arch_check!("i386"),
        Some("s390x") => arch_check!("s390x"),
        Some("x86_64") => arch_check!("x86_64"),
        Some(bad_arch) => panic!("Can't default to {bad_arch} as no backend exists"),
        None => match std::env::var("CARGO_CFG_TARGET_ARCH").unwrap().as_str() {
            "aarch64" => choose_default!("arm64", fallback),
            "i386" | "i486" | "i586" | "i686" => choose_default!("i386", "x86_64", fallback),
            "s390x" => choose_default!("s390x", fallback),
            "riscv64" => choose_default!("riscv64", fallback),
            "x86_64" => choose_default!("x86_64", "i386", fallback),
            _ => fallback,
        },
    };
    println!("cargo::rustc-env=EAMBFC_DEFAULT_ARCH={arch}");
    println!("cargo::rustc-cfg=eambfc_default_arch={arch:?}");
    println!(
        "cargo::rustc-check-cfg=cfg(eambfc_default_arch, values({}))",
        stringify!("arm64", "i386", "riscv64", "s390x", "x86_64")
    );

    println!("cargo::rustc-check-cfg=cfg(can_run_default)");
    macro_rules! check_exec_support {
        ($platform: literal) => {
            println!("cargo::rustc-check-cfg=cfg(can_run_{})", $platform);
            #[cfg(feature = "bintests")]
            if Command::new(concat!("./test_assets/exec_support/", $platform))
                .status()
                .is_ok_and(|status| status.success())
            {
                println!(concat!("cargo::rustc-cfg=can_run_", $platform));
                if $platform == arch {
                    println!("cargo:rustc-cfg=can_run_default");
                }
            }
        };
    }
    check_exec_support!("arm64");
    check_exec_support!("i386");
    check_exec_support!("riscv64");
    check_exec_support!("s390x");
    check_exec_support!("x86_64");
}

// 3. set `cfg` values used for conditional compilation, ...
/// The following cfgs are set are set in the following cases:
///
/// * `cross_compiled`: Set when the build.rs `HOST` and `TARGET` values differ - used to skip
///   tests which have issues when running through compatibility layers like wine
///     * If it's set, and any of the tests that would be skipped are enabled, it will direct Cargo
///       to issue a warning
///
/// * `have_64bit_targets`: Set when at least one 64-bit backend is enabled
/// * `have_32bit_targets`: Set when at least one 32-bit backend is enabled
/// * `have_le_targets`: Set when at least one little-endian backend is enabled
/// * `have_be_targets`: Set when at least one big-endian backend is enabled
fn set_cfg_metavalues() {
    println!("cargo::rustc-check-cfg=cfg(cross_compiled)");
    if std::env::var("HOST") != std::env::var("TARGET") {
        println!("cargo::rustc-cfg=cross_compiled");
        macro_rules! warn_skipped {
            ($feature_str: literal) => {{
                println!(concat!(
                    "cargo::warning=Skipping tests enabled by ",
                    $feature_str,
                    " as they're unsupported when cross-compiling"
                ));
            }};
        }
        if cfg!(test) {
            match (cfg!(feature = "bintests"), cfg!(feature = "disasmtests")) {
                (true, true) => warn_skipped!("\"bintests\" and \"disasmtests\" features"),
                (true, false) => warn_skipped!("\"bintests\" feature"),
                (false, true) => warn_skipped!("\"disasmtests\" feature"),
                (false, false) => (),
            }
        }
    }
    println!("cargo::rustc-check-cfg=cfg(have_64bit_targets)");
    if cfg!(any(
        feature = "arm64",
        feature = "riscv64",
        feature = "s390x",
        feature = "x86_64"
    )) {
        println!("cargo::rustc-cfg=have_64bit_targets");
    }

    println!("cargo::rustc-check-cfg=cfg(have_32bit_targets)");
    if cfg!(feature = "i386") {
        println!("cargo::rustc-cfg=have_32bit_targets");
    }

    println!("cargo::rustc-check-cfg=cfg(have_le_targets)");
    if cfg!(any(
        feature = "arm64",
        feature = "i386",
        feature = "riscv64",
        feature = "x86_64"
    )) {
        println!("cargo::rustc-cfg=have_le_targets");
    }

    println!("cargo::rustc-check-cfg=cfg(have_be_targets)");
    if cfg!(feature = "s390x") {
        println!("cargo::rustc-cfg=have_be_targets");
    }
}

fn main() {
    println!("cargo::rerun-if-changed=.git/index");
    println!("cargo::rerun-if-env-changed=EAMBFC_DEFAULT_ARCH");
    set_cfg_metavalues();
    set_default_arch();

    if !PathBuf::from(".git").exists() {
        println!("cargo::rustc-env=EAMBFC_RS_GIT_COMMIT=unknown: not built from git repository");
        return;
    }

    if Command::new("git")
        .spawn()
        .is_err_and(|e| e.kind() == ErrorKind::NotFound)
    {
        println!("cargo::rustc-env=EAMBFC_RS_GIT_COMMIT=unknown: git not available at build time");
        return;
    }

    let git_invocation = Command::new("git")
        .args(["log", "-n1", "--pretty=format:built from git commit: %h"])
        .output()
        .unwrap();
    assert!(
        git_invocation.status.success(),
        "git command exists, and .git present, but could not determine commit hash"
    );

    let version_text = String::from_utf8(git_invocation.stdout)
        .expect("{e:?} is non-utf8, but git_invocation output is ASCII");

    println!("cargo::rustc-env=EAMBFC_RS_GIT_COMMIT={version_text}");
}
