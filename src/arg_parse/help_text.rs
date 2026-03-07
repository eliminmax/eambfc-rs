// SPDX-FileCopyrightText: 2025 - 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

pub fn help_fmt(progname: &str) -> String {
    format!(
        include_str!("../text_assets/help_template.txt"),
        progname = progname,
        default_arch = env!("EAMBFC_DEFAULT_ARCH")
    )
}
