// SPDX-FileCopyrightText: 2024-2025 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD
#![cfg(not(tarpaulin_include))]

#[cfg(feature = "bintests")]
use std::collections::HashSet;
use std::io::ErrorKind;
use std::path::PathBuf;
use std::process::Command;

#[cfg(not(any(
    feature = "x86_64",
    feature = "arm64",
    feature = "riscv64",
    feature = "s390x"
)))]
compile_error!("Must have at least one architecture enabled");

fn set_default_arch() {
    #[cfg(feature = "bintests")]
    let mut runnable_arches: HashSet<&'static str> = HashSet::new();
    macro_rules! check_exec_support {
        ($platform: literal) => {
            #[cfg(feature = "bintests")]
            if Command::new(concat!("./test_assets/exec_support/", $platform))
                .status()
                .is_ok_and(|status| status.success())
            {
                runnable_arches.insert($platform);
                println!(concat!("cargo::rustc-cfg=can_run_", $platform));
            }
        };
    }

    check_exec_support!("arm64");
    check_exec_support!("riscv64");
    check_exec_support!("s390x");
    check_exec_support!("x86_64");

    macro_rules! arch_check {
        ($arch: literal) => {{
            assert!(
                cfg!(feature = $arch),
                concat!("Can't default to ", $arch, " unless it's enabled")
            );
            $arch
        }};
    }

    // set default arch
    let fallback = if cfg!(feature = "x86_64") {
        "x86_64"
    } else if cfg!(feature = "arm64") {
        "arm64"
    } else if cfg!(feature = "riscv64") {
        "riscv64"
    } else {
        assert!(
            cfg!(feature = "s390x"),
            "must have at least one arch enabled"
        );
        "s390x"
    };
    let arch = match std::env::var("EAMBFC_DEFAULT_ARCH").ok().as_deref() {
        Some("arm64") => arch_check!("arm64"),
        Some("riscv64") => arch_check!("riscv64"),
        Some("s390x") => arch_check!("s390x"),
        Some("x86_64") => arch_check!("x86_64"),
        Some(bad_arch) => panic!("Can't default to {bad_arch} as no backend exists"),
        None => match std::env::var("CARGO_CFG_TARGET_ARCH").unwrap().as_str() {
            "aarch64" => {
                if cfg!(feature = "arm64") {
                    "arm64"
                } else {
                    fallback
                }
            }
            "s390x" => {
                if cfg!(feature = "s390x") {
                    "s390x"
                } else {
                    fallback
                }
            }
            "riscv64" => {
                if cfg!(feature = "riscv64") {
                    "riscv64"
                } else {
                    fallback
                }
            }
            "x86_64" => {
                if cfg!(feature = "x86_64") {
                    "x86_64"
                } else {
                    fallback
                }
            }
            _ => fallback,
        },
    };
    println!("cargo::rustc-env=EAMBFC_DEFAULT_ARCH={arch}");
    println!("cargo::rustc-cfg=eambfc_default_arch={arch:?}");

    #[cfg(feature = "bintests")]
    if runnable_arches.contains(&arch) {
        println!("cargo::rustc-cfg=can_run_default");
    }
}

fn main() {
    println!("cargo::rerun-if-changed=.git/index");
    println!("cargo::rerun-if-env-changed=EAMBFC_DEFAULT_ARCH");
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
        .unwrap_or_else(|e| unreachable!("{e:?} is non-utf8, but git_invocation output is ASCII"));

    println!("cargo::rustc-env=EAMBFC_RS_GIT_COMMIT={version_text}");
}
