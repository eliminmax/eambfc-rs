// SPDX-FileCopyrightText: 2025 - 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

#[cfg(not(have_all_targets))]
use crate::compile::backends::DisabledBackend;
use crate::compile::backends::{Backend, ElfClass};

use std::error::Error;
use std::ffi::OsString;
use std::fmt::{self, Display};
use std::num::{IntErrorKind, ParseIntError};

#[derive(PartialEq, Clone, Debug)]
pub(crate) enum ArgParseError {
    #[cfg(not(have_all_targets))]
    DisabledBackend(DisabledBackend),
    InputIsOutput(OsString),
    MissingOperand(OsString),
    MultipleArchitectures(Backend, Backend),
    MultipleExtensions(OsString, OsString),
    MultipleOutputExtensions(OsString, OsString),
    MultipleTapeSizes(u64, u64),
    NoSourceFiles,
    SetBothOutModes,
    SingleDashArg,
    TapeSizeNotNumeric(OsString),
    TapeSizeOverflow(OsString),
    TapeSizeZero,
    TapeTooLarge {
        class: ElfClass,
        tape_blocks: u64,
    },
    UnexpectedOperand {
        arg: OsString,
        operand: OsString,
    },
    UnknownBackend(OsString),
    UnknownLongOption(OsString),
    UnknownShortOption(u8),
}

impl ArgParseError {
    pub(super) fn from_bad_tape_size(err: &ParseIntError, param: OsString) -> Self {
        match err.kind() {
            IntErrorKind::Zero => Self::TapeSizeZero,
            IntErrorKind::Empty => {
                panic!("Internal error: tape size parameter empty");
            }
            IntErrorKind::PosOverflow => Self::TapeSizeOverflow(param),
            _ => Self::TapeSizeNotNumeric(param),
        }
    }
}

impl Display for ArgParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InputIsOutput(ext) => {
                write!(
                    f,
                    "extension {} is used for both source and output files",
                    ext.display()
                )
            }
            Self::MissingOperand(arg) => {
                write!(f, "argument {} requires an operand", arg.display())
            }
            Self::MultipleArchitectures(a, b) => {
                write!(f, "provided multiple backends: {a} and {b}")
            }
            Self::MultipleExtensions(a, b) => {
                write!(
                    f,
                    "provided multiple extensions for source files: {} and {}",
                    a.display(),
                    b.display()
                )
            }
            Self::MultipleOutputExtensions(a, b) => {
                write!(
                    f,
                    "provided multiple extensions for output files: {} and {}",
                    a.display(),
                    b.display()
                )
            }
            Self::MultipleTapeSizes(a, b) => {
                if a == b {
                    write!(f, "tape size {a} provided multiple times")
                } else {
                    write!(f, "both {a} and {b} provided as tape size")
                }
            }
            Self::NoSourceFiles => write!(f, "no source files provided"),
            Self::TapeSizeNotNumeric(param) => {
                write!(f, "non-numeric tape size {} provided", param.display())
            }
            Self::TapeSizeZero => write!(f, "tape size cannot be zero pages"),
            Self::TapeTooLarge { class, tape_blocks } => write!(
                f,
                "{tape_blocks} 4KiB-blocks can't fit in {}-bit address space",
                class.bits()
            ),
            Self::UnknownLongOption(opt) => write!(f, "unknown option: {}", opt.display()),
            Self::UnexpectedOperand { arg, operand } => {
                let arg = arg.display();
                let operand = operand.display();
                write!(f, "option {arg} was provided unexpected operand {operand}")
            }
            #[cfg(not(have_all_targets))]
            Self::DisabledBackend(db) => write!(f, "backend {db} is disabled"),
            Self::UnknownBackend(param) => {
                write!(f, "unknown backend: {}", param.display())
            }
            Self::UnknownShortOption(b) => write!(f, "unknown option: -{}", b.escape_ascii()),
            Self::SingleDashArg => write!(
                f,
                "`-` as a standalone arg is not supported. Use `--` as a terminal argument instead."
            ),
            Self::TapeSizeOverflow(param) => write!(
                f,
                "overflow parsing {} as a 64-bit unsigned int",
                param.display()
            ),
            Self::SetBothOutModes => write!(f, "attempted to set both quiet and json output"),
        }
    }
}

impl Error for ArgParseError {}
