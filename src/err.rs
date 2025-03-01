// SPDX-FileCopyrightText: 2024 - 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use std::borrow::Cow;
use std::ffi::OsStr;
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
#[derive(PartialEq, Clone, Copy, Debug)]
pub(crate) enum BFErrorID {
    BadSourceExtension,
    FailedRead,
    FailedWrite,
    InputIsOutput,
    JumpTooLong,
    MissingOperand,
    MultipleArchitectures,
    MultipleExtensions,
    MultipleOutputExtensions,
    MultipleTapeBlockCounts,
    NoSourceFiles,
    TapeSizeZero,
    TapeSizeNotNumeric,
    OpenReadFailed,
    OpenWriteFailed,
    TapeTooLarge,
    UnknownArch,
    UnknownArg,
    UnmatchedClose,
    UnmatchedOpen,
    #[cfg(not(any(unix, target_os = "wasi")))]
    NonUTF8,
}

type ErrMsg = Cow<'static, str>;

#[derive(Debug, PartialEq)]
pub(crate) struct BFCompileError {
    kind: BFErrorID,
    msg: ErrMsg,
    instr: Option<u8>,
    loc: Option<CodePosition>,
    file: Option<Box<OsStr>>,
}

fn json_escape(s: &str) -> String {
    let mut construct = String::new();
    s.chars().for_each(|c| {
        if c.is_ascii_control() || matches!(c, '"' | '\\') {
            json_escape_byte(c as u8, &mut construct);
        } else {
            construct.push(c);
        }
    });
    construct
}

fn json_escape_byte(b: u8, target: &mut String) {
    match b {
        // characters with special backslash escapes in JSON but not Rust
        0x08 => target.push_str("\\b"),
        0x0c => target.push_str("\\f"),
        b'\n' | b'\r' | b'\t' | b'\\' | b'"' => write!(target, "{}", b.escape_ascii())
            .unwrap_or_else(|_| unreachable!("Won't fail to write! to String")),
        ..0b10_000 => write!(target, "\\u{b:04x}")
            .unwrap_or_else(|_| unreachable!("Won't fail to write! to String")),
        0b10_000..0b1000_0000 => target.push(char::from(b)),
        _ => target.push('�'),
    }
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
            file: None,
        }
    }
    pub fn set_file(&mut self, file: &OsStr) {
        self.file = Some(Box::from(file));
    }

    /// Construct a new `BFCompileError` with the provided information.
    #[must_use]
    pub fn basic<M: Into<ErrMsg>>(kind: BFErrorID, msg: M) -> Self {
        Self {
            kind,
            msg: msg.into(),
            instr: None,
            loc: None,
            file: None,
        }
    }

    fn report_basic(&self) {
        let mut report_string = format!("Error {:?}", self.kind);
        if let Some(instr) = self.instr {
            if instr > 0x7f {
                write!(report_string, " when compiling '�' (byte value {instr})")
            } else {
                write!(report_string, " when compiling '{}'", instr.escape_ascii())
            }
            .unwrap_or_else(|_| unreachable!("Won't fail to `write!` to String"));
        }
        if let Some(file) = self.file.as_ref() {
            write!(report_string, " in file {}", file.to_string_lossy())
                .unwrap_or_else(|_| unreachable!("Won't fail to `write!` to string"));
        }
        if let Some(loc) = self.loc {
            write!(report_string, " at line {} column {}", loc.line, loc.col)
                .unwrap_or_else(|_| unreachable!("Won't fail to write! to String"));
        }
        eprintln!("{report_string}: {}", self.msg);
    }

    fn report_json(&self) {
        let mut report_string = format!("{{\"errorId\":\"{:?}\"", self.kind);
        if let Some(instr) = self.instr {
            report_string.push_str(",\"instruction\":\"");
            json_escape_byte(instr, &mut report_string);
            report_string.push('\"');
        }
        if let Some(file) = self.file.as_ref() {
            write!(
                report_string,
                ",\"file\":\"{}\"",
                json_escape(&file.to_string_lossy())
            )
            .unwrap_or_else(|_| unreachable!("Won't fail to `write!` to string"));
        }
        if let Some(CodePosition { line, col }) = self.loc {
            write!(report_string, ",\"line\":{line},\"column\":{col}")
                .unwrap_or_else(|_| unreachable!("Won't fail to write! to String"));
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

    /// Return the error ID of `self` (a `BFErrorID`)
    /// (Used for internal unit testing only, thus the `#[cfg(test)]`
    #[cfg(test)]
    pub fn error_id(&self) -> BFErrorID {
        self.kind
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

#[cfg(test)]
#[test]
fn test_json_escape() {
    let mut s = String::new();
    for b in 0x00..0x10 {
        json_escape_byte(b, &mut s);
    }
    // make sure control characters are properly escaped
    assert_eq!(
        s,
        concat!(
            "\\u0000\\u0001\\u0002\\u0003\\u0004\\u0005\\u0006\\u0007",
            "\\b\\t\\n\\u000b\\f\\r\\u000e\\u000f"
        )
    );
    s.clear();
    json_escape_byte(b'"', &mut s);
    json_escape_byte(b'\'', &mut s);
    json_escape_byte(b'\\', &mut s);
    assert_eq!(s, "\\\"'\\\\");
    s.clear();
    for b in b" \x90" {
        json_escape_byte(*b, &mut s);
    }
    assert_eq!(s, " �");
}
