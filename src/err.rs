// SPDX-FileCopyrightText: 2024 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

// enable quiet mode - this does not print error messages to stderr. Does not
// affect JSON messages printed to stdout.
pub fn quiet_mode() {
    todo!("quiet_mode");
}

// enable JSON display mode - this prints JSON-formatted error messagess to
// stdout instead of printing human-readable error messages to stderr.
pub fn json_mode() {
    todo!("json_mode");
}


pub enum EambfcOutMode {
    JSON,
    Quiet,
    Basic
}

impl Default for EambfcOutMode {
    fn default() -> Self {
        EambfcOutMode::Basic
    }
}

pub enum CompileError {
    Basic {
        id: &'static str,
        msg: &'static str,
    },
    Instruction {
        id: &'static str,
        msg: &'static str,
        instr: char,
    },
    Position {
        id: &'static str,
        msg: &'static str,
        instr: char,
        line: usize,
        col: usize,
    },
}

// functions to display error messages, depending on the current error mode.

// special handling for malloc/realloc failure error messages, which avoids any
// further use of malloc/realloc for purposes like generating JSON-escaped
// strings.
pub fn alloc_err() {
    todo!("alloc_err");
}

// a generic error message
pub fn basic_err(id: &str, msg: &str) {
    todo!("basic_err");
}

// an error message related to a specific instruction
pub fn instr_err(id: &str, msg: &str, instr: char) {
    todo!("instr_err");
}

// an error message related to a specific instruction at a specific location
pub fn position_err(id: &str, msg: &str, instr: char, line: usize, col: usize) {
    todo!("position_err");
}

// replaces first instance of "{}" within proto with arg, then passes it as msg
// to basic_err
pub fn param_err(id: &str, proto: String, arg: &str) {
    todo!("param_err");
}
