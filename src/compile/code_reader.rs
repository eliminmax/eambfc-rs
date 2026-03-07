// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use super::FilteredInstr;
use crate::err::{BFCompileError, BFErrorID, CodePosition};

use std::io::{BufRead, Read};

/// An iterator that returns `FilteredInstr`uctions read from a reader that implements `BufRead`,
/// tracking code position
pub(super) struct CodeReader<R: BufRead> {
    byte_reader: std::io::Bytes<R>,
    pos: CodePosition,
}

impl<B: BufRead> CodeReader<B> {
    pub(super) fn new(inner_reader: B) -> Self {
        Self {
            byte_reader: inner_reader.bytes(),
            pos: CodePosition { line: 1, col: 0 },
        }
    }
}

impl<R: Read + BufRead> Iterator for CodeReader<R> {
    type Item = Result<FilteredInstr, BFCompileError>;
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(byte) = self.byte_reader.by_ref().next() {
            match byte {
                Ok(b'\n') => {
                    self.pos.col = 0;
                    self.pos.line += 1;
                }
                // This comparison that a byte isn't a continuation byte within a UTF-8 multi-byte
                // sequence, so if it's either a new UTF-8 codepoint or invalid UTF-8, this will
                // increment the column counter, but it won't if it's a byte that's a valid
                // continuation of a UTF-8 sequence
                Ok(b) if b & 0xc0 != 0x80 => {
                    self.pos.col += 1;
                    if let Some(fi) = FilteredInstr::from_byte(b) {
                        return Some(Ok(fi));
                    }
                }
                // Either a non-UTF-8 byte or a UTF-8 continuation byte. Either way, don't
                // increment the counter, and don't bother checking if it's valid bf - it's not
                Ok(_) => (),
                Err(err) => {
                    return Some(Err(BFCompileError::new(
                        BFErrorID::FailedRead,
                        format!("An I/O error occurred reading from file: {err:?}"),
                        None,
                        Some(self.pos),
                    )));
                }
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn read_success() {
        const TEST_CODE: &[u8] = b"+[-<]>.,".as_slice();
        let mut cr = CodeReader::new(TEST_CODE);
        assert_eq!(cr.next(), Some(Ok(FilteredInstr::Add)));
        assert_eq!(cr.next(), Some(Ok(FilteredInstr::LoopOpen)));
        assert_eq!(cr.next(), Some(Ok(FilteredInstr::Sub)));
        assert_eq!(cr.next(), Some(Ok(FilteredInstr::MoveL)));
        assert_eq!(cr.next(), Some(Ok(FilteredInstr::LoopClose)));
        assert_eq!(cr.next(), Some(Ok(FilteredInstr::MoveR)));
        assert_eq!(cr.next(), Some(Ok(FilteredInstr::Write)));
        assert_eq!(cr.next(), Some(Ok(FilteredInstr::Read)));
        assert_eq!(cr.next(), None);
    }

    #[test]
    fn read_fail() {
        struct FailingReader;
        impl Read for FailingReader {
            fn read(&mut self, _buf: &mut [u8]) -> std::io::Result<usize> {
                Err(std::io::Error::other("can't read from FailingReader"))
            }
        }
        let mut cr = CodeReader::new(std::io::BufReader::new(FailingReader));
        assert!(
            cr.next()
                .unwrap()
                .is_err_and(|e| e.error_id() == BFErrorID::FailedRead)
        );
    }
}
