use crate::err::{BFCompileError, BFErrorID, CodePosition};
use super::FilteredInstr;

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
        while let Some(b) = self.byte_reader.by_ref().next() {
            let b = match b {
                Ok(ok) => ok,
                Err(err) => {
                    return Some(Err(BFCompileError::new(
                        BFErrorID::FailedRead,
                        format!("An I/O error occurred reading from file: {err:?}"),
                        None,
                        Some(self.pos),
                    )));
                }
            };
            // This comparison that a byte isn't a continuation byte within a UTF-8 multi-byte
            // sequence, so if it's either a new UTF-8 codepoint or invalid UTF-8, this will
            // increment the column counter, but it won't if it's a byte that's typically a
            // continuatio of a UTF-8 sequence
            if b & 0xc0 != 0x80 {
                self.pos.col += 1;
            }
            if let Some(fi) = FilteredInstr::from_byte(b) {
                return Some(Ok(fi));
            }
            if b == b'\n' {
                self.pos.col = 0;
                self.pos.line += 1;
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

}
