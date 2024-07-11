// SPDX-FileCopyrightText: 2024 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use super::run_config::OutMode;

pub enum BFCompileError {
    Basic {
        id: String,
        msg: String,
    },
    Instruction {
        id: String,
        msg: String,
        instr: char,
    },
    Position {
        id: String,
        msg: String,
        instr: char,
        line: usize,
        col: usize,
    },
    UnknownFlag(u8), // flag is a c character
}

#[allow(unused_variables)]
pub trait BfErrDisplay {
    fn report(&self, out_mode: OutMode);
}

impl BfErrDisplay for BFCompileError {
    fn report(&self, out_mode: OutMode) {
        if out_mode == OutMode::Quiet {
            return;
        }
        match &self {
            BFCompileError::Basic { id, msg } => {
                if out_mode == OutMode::Basic {
                    eprintln!("Error {}: {}", id, msg);
                } else {
                    println!(
                        "{{\"errorId\": \"{}\", \"message\":\"{}\"}}",
                        json_str(id),
                        json_str(msg)
                    );
                }
            }
            BFCompileError::Instruction { id, msg, instr } => {
                if out_mode == OutMode::Basic {
                    eprintln!("Error {} when compiling {}: {}", id, instr, msg);
                } else {
                    println!(
                        "{{\"errorId\": \"{}\", \"message\":\"{}\", \"instruction\": \"{}\"}}",
                        json_str(id),
                        json_str(msg),
                        json_str(&instr.to_string())
                    );
                }
            }
            BFCompileError::Position {
                id,
                msg,
                instr,
                line,
                col,
            } => {
                if out_mode == OutMode::Basic {
                    eprintln!(
                        "Error {} when compiling {} at line {}, colunm {}: {}",
                        id, instr, line, col, msg
                    );
                } else {
                    println!(
                        "{{\"errorId\": \"{}\", \"message\":\"{}\", \"instruction\": \"{}\",\
                        \"line\": {}, \"column\": {}}}",
                        json_str(id),
                        json_str(msg),
                        json_str(&instr.to_string()),
                        line,
                        col
                    );
                }
            }
            BFCompileError::UnknownFlag(c) => BFCompileError::Basic {
                id: "UNKNOWN_ARG".to_string(),
                msg: format!(
                    "Unknown argument: {}",
                    match *c {
                        n if n < 0x80_u8 => (*c as char).to_string(),
                        _ => format!("\\x{:x}", *c),
                    }
                ),
            }
            .report(out_mode),
        }
    }
}

fn json_str(s: &str) -> String {
    s.chars()
        .map(|c| match c {
            '\n' => "\\n".to_string(),
            '\r' => "\\r".to_string(),
            '\x0c' => "\\f".to_string(),
            '\t' => "\\t".to_string(),
            '\x08' => "\\x08".to_string(),
            '\\' => "\\\\".to_string(),
            '"' => "\\\"".to_string(),
            n if n < '\x20' => format!("\\u00{:02x}", n as u32),
            _ => (c.to_string()),
        })
        .collect::<Vec<String>>()
        .join("")
}