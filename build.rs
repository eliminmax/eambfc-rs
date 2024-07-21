// SPDX-FileCopyrightText: NONE
//
// SPDX-License-Identifier: 0BSD

use std::path::PathBuf;
use std::process::{Command, Output};

#[cfg(not(unix))]
compiler_error!("Unsupported platform! This program relies on std::os::unix!");

#[inline]
fn git_found() -> bool {
    match Command::new("/bin/sh")
        .args(["-c", "command -v git"])
        .output()
    {
        Ok(Output { status, .. }) => status.success(),
        Err(_) => false,
    }
}

fn main() {
    println!("cargo::rerun-if-changed=.git/index");
    let git_invocation = Command::new("git")
        .args(["log", "-n1", "--pretty=format:built from git commit: %h"])
        .output();

    let commit_id = if git_found() && PathBuf::from(".git").exists() {
        match git_invocation {
            Ok(Output { stdout, status, .. }) if status.success() => {
                let mut s =
                    String::from_utf8(stdout).expect("Failed to parse bytes {stdout:?} as UTF-8");
                let git_status = Command::new("git")
                    .args(["status", "--short"])
                    .output()
                    .expect("Failed to determine whether or not local changes were made");
                if !git_status.stdout.is_empty() {
                    s.push_str(" (with local changes)");
                }

                s
            }
            _ => panic!("`git` is installed .git present, but could not determine commit hash!"),
        }
    } else {
        String::from("not built from git repository")
    };

    println!("cargo::rustc-env=EAMBFC_RS_GIT_COMMIT={commit_id}");
}
