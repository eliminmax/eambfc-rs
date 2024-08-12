// SPDX-FileCopyrightText: 2024 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use super::OutMode;

#[derive(Debug, PartialEq)]
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
    Positional {
        id: String,
        msg: String,
        instr: u8,
        line: usize,
        col: usize,
    },
    UnknownFlag(u8), // flag is a c character
}

pub trait BfErrDisplay {
    fn report(&self, out_mode: &OutMode);
}

impl BfErrDisplay for BFCompileError {
    fn report(&self, out_mode: &OutMode) {
        if *out_mode == OutMode::Quiet {
            return;
        }
        match &self {
            BFCompileError::Basic { id, msg } => {
                if *out_mode == OutMode::Basic {
                    eprintln!("Error {}: {}", id, msg);
                } else {
                    println!(
                        "{{\"errorId\":\"{}\",\"message\":\"{}\"}}",
                        json_str(id),
                        json_str(msg)
                    );
                }
            }
            BFCompileError::Instruction { id, msg, instr } => {
                if *out_mode == OutMode::Basic {
                    eprintln!("Error {} when compiling {}: {}", id, instr, msg);
                } else {
                    println!(
                        "{{\"errorId\":\"{}\",\"message\":\"{}\",\"instruction\":\"{}\"}}",
                        json_str(id),
                        json_str(msg),
                        json_str(&instr.to_string())
                    );
                }
            }
            BFCompileError::Positional {
                id,
                msg,
                instr,
                line,
                col,
            } => {
                if *out_mode == OutMode::Basic {
                    eprintln!(
                        "Error {} when compiling {} at line {}, colunm {}: {}",
                        id, instr, line, col, msg
                    );
                } else {
                    println!(
                        "{{\"errorId\":\"{}\",\"message\":\"{}\",\"instruction\":\"{}\",\
                        \"line\":{},\"column\":{}}}",
                        json_str(id),
                        json_str(msg),
                        json_str(&instr.to_string()),
                        line,
                        col
                    );
                }
            }
            BFCompileError::UnknownFlag(c) => {
                if *out_mode == OutMode::Basic {
                    eprintln!(
                        "Error UNKNOWN_ARG: {} is not a recognized argument.",
                        match *c {
                            n if n < 0x80_u8 => (*c as char).to_string(),
                            _ => format!("non-ASCII byte char 0x{c:02x}"),
                        }
                    );
                } else {
                    println!(
                        "{{\"errorId\":\"UNKNOWN_ARG\",\
                        \"message\":\"{} is not a recognized argument\"}}",
                        match *c {
                            n if n < 0x80_u8 => json_str(&(*c as char).to_string()),
                            _ => format!("non-ASCII byte char 0x{c:02x}"),
                        }
                    );
                }
            }
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
            '\x08' => "\\b".to_string(),
            '\\' => "\\\\".to_string(),
            '"' => "\\\"".to_string(),
            n if n < '\x20' => format!("\\u00{:02x}", n as u32),
            _ => c.to_string(),
        })
        .collect::<Vec<String>>()
        .join("")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn json_str_no_escapes() -> Result<(), String> {
        assert_eq!(json_str("foo bar baz"), String::from("foo bar baz"));
        Ok(())
    }

    #[test]
    fn json_str_special_escapes() -> Result<(), String> {
        assert_eq!(
            json_str("\n\r\x0c\t\x08\\\""),
            String::from("\\n\\r\\f\\t\\b\\\\\\\"")
        );
        Ok(())
    }
}
