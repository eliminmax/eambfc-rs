// SPDX-FileCopyrightText: 2024 - 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use crate::err::{BFCompileError, BFErrorID};
use std::io::Read;

/// Read `file` into a `Vec<u8>`, omitting dead code and non-brainfuck instructions, and replacing
/// `b"[-]"` and `b"[+]"` with `b"@"`, which is EAMBFC's internal "`zero_byte`" extra instruction.
///
/// NOTE: uses `std::io::Read::bytes` internally, which is "inefficient for data that's not in
/// memory". It's best if `file` implements `std::io::BufRead`.
pub(super) fn filtered_read(file: impl Read) -> Result<Vec<u8>, BFCompileError> {
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
    // because strip_dead_code was called, code_buf[0] can't be `b'['`, so skip it.
    let mut search_start: usize = 1;
    while let Some(i) = set_zero_code(&code_buf, search_start) {
        code_buf[i] = b'@';
        code_buf.drain(i + 1..=i + 2);
        // start the next search right after the replaced byte
        search_start = i + 1;
    }

    Ok(code_buf)
}

/// Return an `Err` if `code_bytes` has a `b']'` instruction outside of any loops, or if it has a
/// `b'['` instruction that is never closed by a `b']'` instruction.
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

/// This function does a few things repeatedly.
///
/// first, it strips out any occurrences of `b"+-"`, `b"-+"`, `b"<>"`, and `b"><"`, as those
/// instructions directly cancel themselves out. Once it can't find any of them, it tries to strip
/// out any sequences of exactly 256 consecutive `b'+'` or `b'-'` instructions, as those would
/// overflow back to where they started.
///
/// Once none of those sequences were found, it searches for any conditional loop blocks that can be
/// trivially determined never to execute, either because they are at the start of the program,
/// when all cells are zero, or because they start right after another loop ends, meaning that the
/// current cell must be zero.
///
/// If any code was removed during that process, it goes through it again. Otherwise, it returns.
fn strip_dead_code(filtered_bytes: &mut Vec<u8>) {
    // alternate between finding and removing code that cancels itself out, and finding and
    // removing loops that can never run. Return the remaining code once both steps complete
    // without changing any code
    loop {
        let mut unchanged = true;
        // remove pairs of instructions cancel out.
        let mut search_start = 0;
        while let Some(index) = find_cancelling_pairs(filtered_bytes, search_start) {
            unchanged = false;
            search_start = index;
            filtered_bytes.drain(index..index + 2);
        }

        // find and remove wrapping arithmetic
        search_start = 0;
        while let Some(index) = find_wrapping_arith(filtered_bytes, search_start) {
            unchanged = false;
            search_start = index;
            filtered_bytes.drain(index..index + 256);
        }

        // find and remove dead loops later in the program
        search_start = 0;
        while let Some(index) = find_dead_loop(filtered_bytes, search_start) {
            unchanged = false;
            search_start = index;
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

/// Search for a cancelling pair in `code_bytes[search_start..]`, and return `Some(i)`, where `i` is
/// its starting index within `code_bytes`, once found.
///
/// Returns `None` if it reaches the end of the slice without finding a match
fn find_cancelling_pairs(code_bytes: &[u8], search_start: usize) -> Option<usize> {
    for (i, window) in code_bytes[search_start..].windows(2).enumerate() {
        if matches!(window, b"+-" | b"-+" | b"<>" | b"><") {
            return Some(search_start + i);
        }
    }
    None
}

/// Search for 256 consecutive `b'-'` or `b'+'` instructions within `code_bytes[search_start..]`,
/// and returns `Some(i)`, where `i` is its starting index within `code_bytes`, once found.
///
/// Returns `None` if it reaches the end of the slice without finding a match
fn find_wrapping_arith(code_bytes: &[u8], search_start: usize) -> Option<usize> {
    for (i, window) in code_bytes[search_start..].windows(256).enumerate() {
        if window == [b'-'; 256] || window == [b'+'; 256] {
            return Some(search_start + i);
        }
    }
    None
}

/// Search for a dead loop that can be trivially determined never to run within
/// `code_bytes[search_start..]` and returns `Some(i)`, where `i` is its starting index within
/// `code_bytes`.
///
/// Returns `None` if it reaches the end of the slice without finding a match
fn find_dead_loop(code_bytes: &[u8], search_start: usize) -> Option<usize> {
    if code_bytes.is_empty() {
        return None;
    }
    if search_start == 0 && code_bytes[0] == b'[' {
        return Some(0);
    }
    for (index, window) in code_bytes[search_start.saturating_sub(1)..]
        .windows(2)
        .enumerate()
    {
        if window == b"][" {
            return Some(search_start + index);
        }
    }
    None
}

/// Try to find a `b"[-]"` or `b"[+]"` sequence to zero out the current byte. If one is found,
/// returns `Some(i)`, where `i` is the index of the `b'['` within the sequence.
/// Otherwise, it returns `None`.
///
/// searching starts from `search_start`, so code known not to be part of such a sequence can be
/// skipped over.
fn set_zero_code(code_bytes: &[u8], search_start: usize) -> Option<usize> {
    if code_bytes.is_empty() {
        return None;
    }
    for (i, window) in code_bytes[search_start..].windows(3).enumerate() {
        if matches!(window, [b'[', b'-' | b'+', b']']) {
            return Some(search_start + i);
        }
    }
    None
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
