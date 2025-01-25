// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

#[cfg(feature = "arm64")]
mod arm64;
#[cfg(feature = "arm64")]
pub (crate) use arm64::Arm64Inter;

#[cfg(feature = "s390x")]
mod s390x;
#[cfg(feature = "s390x")]
pub (crate) use s390x::S390xInter;
#[cfg(feature = "x86_64")]
mod x86_64;
#[cfg(feature = "x86_64")]
pub (crate) use x86_64::X86_64Inter;

use super::arch_inter;
use super::elf_tools;
