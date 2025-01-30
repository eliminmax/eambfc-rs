// SPDX-FileCopyrightText: 2024 - 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use crate::err::{BFCompileError, BFErrorID};
use std::io::Read;

/// Read `file` into a Vec<u8>, omitting dead code.
///
/// NOTE: uses `std::io::Read::bytes` internally, which is "inefficient for data that's not in
/// memory". It's best to either pass `&[u8]` or `std::io::BufReader`
pub(super) fn filtered_read(
    file: impl Read,
) -> Result<Vec<u8>, BFCompileError> {
    let mut code_buf: Vec<u8> = file
        .bytes()
        .filter_map(|res| match res {
            Ok(b) if b"+-<>,.[]".contains(&b) => Some(Ok(b)),
            Ok(_) => None,
            Err(_) => Some(Err(BFCompileError::basic(
                BFErrorID::FailedRead,
                "Failed to read file into buffer",
            ))),
        })
        .collect::<Result<_, _>>()?;
    loops_match(code_buf.as_slice())?;
    strip_dead_code(&mut code_buf);
    while let Some(i) = set_zero_code(&code_buf) {
        code_buf[i] = b'@';
        code_buf.drain(i+1..=i+2);
    }

    Ok(code_buf)
}

fn loops_match(code_bytes: &[u8]) -> Result<(), BFCompileError> {
    let mut nest_level: usize = 0;
    for b in code_bytes {
        match b {
            b'[' => nest_level += 1,
            b']' => {
                if nest_level == 0 {
                    return Err(BFCompileError::basic(
                        BFErrorID::UnmatchedClose,
                        "Found an unmatched ']' while preparing for optimization. \
                            Compile without -O for more information.",
                    ));
                }
                nest_level -= 1;
            }
            _ => (),
        }
    }
    if nest_level > 0 {
        Err(BFCompileError::basic(
            BFErrorID::UnmatchedOpen,
            "Found an unmatched '[' while preparing for optimization. \
                    Compile without -O for more information.",
        ))
    } else {
        Ok(())
    }
}

#[derive(PartialEq)]
enum CancellingCodeIndex {
    CancellingPair(usize),
    OverflowingArith(usize),
}

fn find_cancelling_code(code_bytes: &[u8]) -> Option<CancellingCodeIndex> {
    const SMALL_PATTERNS: [&[u8]; 4] = [
        b"+-".as_slice(),
        b"-+".as_slice(),
        b"<>".as_slice(),
        b"><".as_slice(),
    ];
    for (i, window) in code_bytes.windows(2).enumerate() {
        if SMALL_PATTERNS.contains(&window) {
            return Some(CancellingCodeIndex::CancellingPair(i));
        }
    }
    for (i, window) in code_bytes.windows(256).enumerate() {
        if [[b'-'; 256].as_slice(), [b'+'; 256].as_slice()].contains(&window) {
            return Some(CancellingCodeIndex::OverflowingArith(i));
        }
    }
    None
}

fn find_dead_loop(code_bytes: &[u8]) -> Option<usize> {
    if code_bytes.is_empty() {
        return None;
    }
    if code_bytes[0] == b'[' {
        return Some(0);
    }
    for (index, window) in code_bytes.windows(2).enumerate() {
        if window == b"][" {
            return Some(index + 1);
        }
    }
    None
}

fn set_zero_code(code_bytes: &[u8]) -> Option<usize> {
    for (i, window) in code_bytes.windows(3).enumerate() {
        if matches!(window, [b'[', b'-' | b'+', b']']) {
            return Some(i);
        }
    }
    None
}

fn strip_dead_code(filtered_bytes: &mut Vec<u8>) {
    // alternate between finding and removing code that cancels itself out, and finding and
    // removing loops that can never run. Return the remaining code once both steps complete
    // without changing any code
    loop {
        let mut unchanged = true;
        // first, remove sequences within bf_bytes that cancel out.
        while let Some(cancelling_code) = find_cancelling_code(filtered_bytes) {
            unchanged = false;
            match cancelling_code {
                CancellingCodeIndex::CancellingPair(i) => {
                    let _ = filtered_bytes.drain(i..i + 2);
                }
                CancellingCodeIndex::OverflowingArith(i) => {
                    let _ = filtered_bytes.drain(i..i + 256);
                }
            }
        }

        // find and remove dead loops later in the program
        while let Some(index) = find_dead_loop(filtered_bytes) {
            unchanged = false;
            let mut nest_level = 0;
            for (i, b) in filtered_bytes[index..].iter().enumerate() {
                if *b == b'[' {
                    nest_level += 1;
                } else if *b == b']' {
                    nest_level -= 1;
                }
                if nest_level == 0 {
                    filtered_bytes.drain(index..=index + i);
                    break;
                }
            }
        }

        // finally, check if any of the above changed anything. If not, break out of the loop.
        if unchanged {
            break;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn strip_dead_code_test() {
        let mut code = Vec::from(b"[+++++]><+---+++-[-][,[-][+>-<]]-+[-+]-+[]+-[]");
        code.extend(b"+".repeat(256));
        code.extend_from_slice(b"[+-]>");
        code.extend(b"-".repeat(256));
        code.extend_from_slice(b"[->+<][,.]");
        strip_dead_code(&mut code);
        assert_eq!(code, Vec::from(b">[->+<]"));
    }

    use std::io::ErrorKind;
    struct Unreadable;
    impl Read for Unreadable {
        fn read(&mut self, _buf: &mut [u8]) -> std::io::Result<usize> {
            Err(std::io::Error::new(ErrorKind::Unsupported, "Unreadable"))
        }
    }

    #[test]
    fn read_failure_handled() {
        let unreadable = Unreadable;

        assert!(filtered_read(unreadable).is_err_and(|e| e.kind == BFErrorID::FailedRead));
    }

    #[test]
    fn unmatched_loops_detected() {
        assert_eq!(
            loops_match(b"[").unwrap_err().kind,
            BFErrorID::UnmatchedOpen,
        );
        assert_eq!(
            loops_match(b"]").unwrap_err().kind,
            BFErrorID::UnmatchedClose,
        );
    }
}
