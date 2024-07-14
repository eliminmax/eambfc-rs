// SPDX-FileCopyrightText: 2024 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use std::ffi::OsString;

#[derive(PartialEq, Debug)]
pub enum OutMode {
    Basic,
    JSON,
    Quiet,
}

#[derive(PartialEq, Debug)]
pub struct StandardRunConfig {
    pub progname: String,
    pub out_mode: OutMode,
    pub optimize: bool,
    pub keep: bool,
    pub cont: bool,
    pub extension: OsString,
    pub source_files: Vec<OsString>,
}

#[derive(PartialEq, Debug)]
pub enum RunConfig {
    StandardRun(StandardRunConfig),
    ShowHelp(String),
    ShowVersion(String),
}
