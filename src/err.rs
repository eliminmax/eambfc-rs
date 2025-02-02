// SPDX-FileCopyrightText: 2024 - 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use std::borrow::Cow;
use std::fmt::Write;

#[derive(PartialEq, Debug, Clone, Copy, Default)]
pub(crate) enum OutMode {
    #[default]
    Basic,
    Json,
    Quiet,
}

impl OutMode {
    /// Set `self` to `OutMode::Json`
    pub fn json(&mut self) {
        *self = OutMode::Json;
    }
    /// If `self` is not `OutMode::Json`, sets `self` to `OutMode::Quiet`
    /// for consistency with original C version, quiet doesn't override JSON mode
    pub fn quiet(&mut self) {
        if *self == OutMode::Basic {
            *self = OutMode::Quiet;
        }
    }
}

#[non_exhaustive]
#[derive(PartialEq, Clone, Copy)]
pub(crate) enum BFErrorID {
    BadExtension,
    FailedRead,
    FailedWrite,
    JumpTooLong,
    MissingOperand,
    MultipleArches,
    MultipleExtensions,
    MultipleTapeBlockCounts,
    NoSourceFiles,
    NoTape,
    NotNumeric,
    OpenReadFailed,
    OpenWriteFailed,
    TapeTooLarge,
    UnknownArch,
    UnknownArg,
    UnmatchedClose,
    UnmatchedOpen,
}

impl std::fmt::Debug for BFErrorID {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                BFErrorID::BadExtension => "BAD_EXTENSION",
                BFErrorID::FailedRead => "FAILED_READ",
                BFErrorID::FailedWrite => "FAILED_WRITE",
                BFErrorID::JumpTooLong => "JUMP_TOO_LONG",
                BFErrorID::MissingOperand => "MISSING_OPERAND",
                BFErrorID::MultipleArches => "MULTIPLE_ARCHES",
                BFErrorID::MultipleExtensions => "MULTIPLE_EXTENSIONS",
                BFErrorID::MultipleTapeBlockCounts => "MULTIPLE_TAPE_BLOCK_COUNTS",
                BFErrorID::NoSourceFiles => "NO_SOURCE_FILES",
                BFErrorID::NoTape => "NO_TAPE",
                BFErrorID::NotNumeric => "NOT_NUMERIC",
                BFErrorID::OpenReadFailed => "OPEN_R_FAILED",
                BFErrorID::OpenWriteFailed => "OPEN_W_FAILED",
                BFErrorID::TapeTooLarge => "TAPE_TOO_LARGE",
                BFErrorID::UnknownArch => "UNKNOWN_ARCH",
                BFErrorID::UnknownArg => "UNKNOWN_ARG",
                BFErrorID::UnmatchedClose => "UNMATCHED_CLOSE",
                BFErrorID::UnmatchedOpen => "UNMATCHED_OPEN",
            }
        )
    }
}

type ErrMsg = Cow<'static, str>;

#[derive(Debug, PartialEq)]
pub(crate) struct BFCompileError {
    pub(crate) kind: BFErrorID,
    msg: ErrMsg,
    instr: Option<u8>,
    loc: Option<CodePosition>,
}

impl BFCompileError {
    /// Construct a new `BFCompileError` with the provided information.
    #[must_use]
    pub fn new<M: Into<ErrMsg>>(
        kind: BFErrorID,
        msg: M,
        instr: Option<u8>,
        loc: Option<CodePosition>,
    ) -> Self {
        Self {
            kind,
            msg: msg.into(),
            instr,
            loc,
        }
    }

    /// Construct a new `BFCompileError` with the provided information.
    #[must_use]
    pub fn basic<M: Into<ErrMsg>>(kind: BFErrorID, msg: M) -> Self {
        Self {
            kind,
            msg: msg.into(),
            instr: None,
            loc: None,
        }
    }

    fn report_basic(&self) {
        let mut report_string = format!("Error {:?}", self.kind);
        if let Some(instr) = self.instr {
            write!(report_string, " when compiling '{}'", instr.escape_ascii())
                .unwrap_or_else(|_| panic!("Failed to write! to String"));
        }
        if let Some(loc) = self.loc {
            write!(report_string, " at line {} column {}", loc.line, loc.col)
                .unwrap_or_else(|_| panic!("Failed to write! to String"));
        }
        eprintln!("{report_string}: {}", self.msg);
    }

    fn report_json(&self) {
        let mut report_string = format!("{{\"errorId\":\"{:?}\"", self.kind);
        if let Some(instr) = self.instr {
            report_string.push_str(",\"instruction\":\"");
            match instr {
                // characters with special backslash escapes in JSON but not Rust
                0x08 => report_string.push_str("\\b"),
                0x0c => report_string.push_str("\\f"),
                // single quote doesn't need to be escaped for JSON, but Rust escapes it
                b'\'' => report_string.push('\''),
                c => report_string.push_str(&c.escape_ascii().to_string()),
            }
            report_string.push('\"');
        }
        if let Some(CodePosition { line, col }) = self.loc {
            write!(report_string, ",\"line\":{line},\"column\":{col}")
                .unwrap_or_else(|_| panic!("Failed to write! to String"));
        }
        println!("{report_string},\"message\":\"{}\"}}", self.msg);
    }

    /// Report error to user in manner determined by `out_mode`.
    ///
    /// * If it's `OutMode::Quiet`, then it does nothing
    /// * If it's `OutMode::Basic`, then it prints a human-readable message to stderr
    /// * If it's `OutMode::Json`, then it prints a JSON object to stdout, suitable to pipe into
    ///   tools like `jq`. It has the following structure:
    ///   ```plain
    ///   {
    ///     "errorId": string,
    ///     "message": string,
    ///     "instruction": string,
    ///     "line": int,
    ///     "column": int
    ///   }
    ///   ```
    ///   * "instruction" will be omitted if `self.instr` is `None`,
    ///   * "line" and "column" will be omitted if `self.loc` is `None`,
    ///
    pub fn report(&self, out_mode: OutMode) {
        match out_mode {
            OutMode::Quiet => (),
            OutMode::Basic => self.report_basic(),
            OutMode::Json => self.report_json(),
        }
    }
}

impl From<BFCompileError> for Vec<BFCompileError> {
    fn from(err: BFCompileError) -> Self {
        vec![err]
    }
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub(crate) struct CodePosition {
    pub line: usize,
    pub col: usize,
}
