// SPDX-FileCopyrightText: 2024 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use super::OutMode;
use std::borrow::Cow;

#[derive(Debug, PartialEq, Clone, Copy)]
#[allow(non_camel_case_types)]
pub enum BFErrorID {
    BAD_EXTENSION,
    FAILED_READ,
    FAILED_WRITE,
    IMMEDIATE_TOO_LARGE,
    INVALID_JUMP_ADDRESS,
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
    pub fn basic<M: Into<ErrMsg>>(kind: BFErrorID, msg: M) -> Self {
        Self {
            kind,
            msg: msg.into(),
            instr: None,
            loc: None,
        }
    }
    pub fn instruction<M: Into<ErrMsg>>(kind: BFErrorID, msg: M, instr: u8) -> Self {
        Self {
            kind,
            msg: msg.into(),
            instr: Some(instr),
            loc: None,
        }
    }
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
            report_string.push_str(&format!(" when compiling '{}'", instr.escape_ascii()));
        }
        if let Some(loc) = self.loc {
            report_string.push_str(&format!(" at line {} column {}", loc.line, loc.col));
        }
        eprintln!("{report_string}: {}", self.msg);
    }

    fn report_json(&self) {
        let mut report_string = format!("{{\"errorId\":\"{:?}\",", self.kind);
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
            report_string.push_str(&format!(",\"line\":{line},\"column\":{col}"));
        }
        println!("{report_string},\"msg\":{}}}", self.msg);
    }

    pub fn report(&self, out_mode: OutMode) {
        match out_mode {
            OutMode::Quiet => (),
            OutMode::Basic => self.report_basic(),
            OutMode::JSON => self.report_json(),
        }
    }
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub struct CodePosition {
    pub line: usize,
    pub col: usize,
}
