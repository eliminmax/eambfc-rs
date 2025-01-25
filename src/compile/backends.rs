// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

#[cfg(feature = "arm64")]
pub mod arm64;
#[cfg(feature = "s390x")]
pub mod s390x;
#[cfg(feature = "x86_64")]
pub mod x86_64;
