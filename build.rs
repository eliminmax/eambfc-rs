// SPDX-FileCopyrightText: 2024-2025 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

use std::io::ErrorKind;
use std::path::PathBuf;
use std::process::Command;

#[cfg(not(any(feature = "x86_64", feature = "arm64", feature = "s390x")))]
compile_error!("Must have at least one architecture enabled");
fn main() {
    macro_rules! check_exec_support {
        ($platform: literal) => {
            if cfg!(feature = $platform)
                && Command::new(concat!("./test_assets/exec_support/", $platform))
                    .output()
                    .is_ok_and(|res| res.status.success())
            {
                println!(concat!("cargo::rustc-cfg=can_run_", $platform));
            }
        };
    }

    check_exec_support!("arm64");
    check_exec_support!("s390x");
    check_exec_support!("x86_64");

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

    println!("cargo::rerun-if-changed=.git/index");
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
