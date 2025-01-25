// SPDX-FileCopyrightText: 2024 - 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use std::borrow::Cow;
use std::fmt::Write;

#[derive(PartialEq, Debug, Clone, Copy, Default)]
pub enum OutMode {
    #[default]
    Basic,
    Json,
    Quiet,
}

impl OutMode {
    pub fn json(&mut self) {
        *self = OutMode::Json;
    }
    pub fn quiet(&mut self) {
        // for consistency with original C version, quiet doesn't override JSON mode
        if *self == OutMode::Basic {
            *self = OutMode::Quiet;
        }
    }
}

#[derive(Debug, PartialEq, Clone, Copy)]
#[allow(
    non_camel_case_types,
    reason = "matches error IDs from C version, and allows derived Debug to be sufficient"
)]
pub enum BFErrorID {
    BAD_EXTENSION,
    FAILED_READ,
    FAILED_WRITE,
    JUMP_TOO_LONG,
    MISSING_OPERAND,
    MULTIPLE_ARCHES,
    MULTIPLE_EXTENSIONS,
    MULTIPLE_TAPE_BLOCK_COUNTS,
    NO_SOURCE_FILES,
    NO_TAPE,
    NOT_NUMERIC,
    OPEN_R_FAILED,
    OPEN_W_FAILED,
    TAPE_TOO_LARGE,
    UNKNOWN_ARCH,
    UNKNOWN_ARG,
    UNMATCHED_CLOSE,
    UNMATCHED_OPEN,
}

#[derive(Debug, PartialEq)]
pub struct BFCompileError {
    pub kind: BFErrorID,
    msg: Cow<'static, str>,
    instr: Option<u8>,
    loc: Option<CodePosition>,
}

type ErrMsg = Cow<'static, str>;

impl BFCompileError {
    #[must_use]
    pub fn basic<M: Into<ErrMsg>>(kind: BFErrorID, msg: M) -> Self {
        Self {
            kind,
            msg: msg.into(),
            instr: None,
            loc: None,
        }
    }
    #[must_use]
    pub fn instruction<M: Into<ErrMsg>>(kind: BFErrorID, msg: M, instr: u8) -> Self {
        Self {
            kind,
            msg: msg.into(),
            instr: Some(instr),
            loc: None,
        }
    }
    #[must_use]
    pub fn positional<M: Into<ErrMsg>>(
        kind: BFErrorID,
        msg: M,
        instr: u8,
        loc: CodePosition,
    ) -> Self {
        Self {
            kind,
            msg: msg.into(),
            instr: Some(instr),
            loc: Some(loc),
        }
    }
    #[must_use]
    pub fn unknown_flag(flag: u8) -> Self {
        Self {
            kind: BFErrorID::UNKNOWN_ARG,
            msg: Cow::from(format!(
                "'{}' is not a recognized argument",
                flag.escape_ascii()
            )),
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
pub struct CodePosition {
    pub line: usize,
    pub col: usize,
}
