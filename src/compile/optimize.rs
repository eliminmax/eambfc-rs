// SPDX-FileCopyrightText: 2024 - 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use crate::err::{BFCompileError, BFErrorID};
use std::collections::VecDeque;
use std::io::Read;
use std::num::NonZeroUsize;

#[derive(Debug, PartialEq, Clone, Copy)]
pub(super) enum CondensedInstruction {
    BFInstruction(u8),
    RepeatMoveR(NonZeroUsize),
    RepeatMoveL(NonZeroUsize),
    RepeatAdd(NonZeroUsize),
    RepeatSub(NonZeroUsize),
    SetZero,
}

#[derive(PartialEq, Clone, Copy)]
enum InstructionTag {
    BFAdd,
    BFSub,
    BFMoveR,
    BFMoveL,
    BFRead,
    BFWrite,
    BFLoopStart,
    BFLoopEnd,
    RepeatAdd,
    RepeatSub,
    RepeatMoveL,
    RepeatMoveR,
    SetZero,
}

struct CondensedInstructions {
    instructions: VecDeque<InstructionTag>,
    repeat_counts: VecDeque<NonZeroUsize>,
}

impl CondensedInstructions {
    fn new() -> Self {
        Self {
            instructions: VecDeque::new(),
            repeat_counts: VecDeque::new(),
        }
    }

    fn bulk_push_uncondensed(&mut self, tag: InstructionTag, count: usize) {
        self.instructions.extend([tag].repeat(count));
    }
    fn repeat_push(
        &mut self,
        single_tag: InstructionTag,
        repeat_tag: InstructionTag,
        count: usize,
    ) {
        if count == 1 {
            self.instructions.push_back(single_tag);
        } else {
            let count = NonZeroUsize::new(count).expect("count is nonzero");
            self.instructions.push_back(repeat_tag);
            self.repeat_counts.push_back(count);
        }
    }
    fn push(&mut self, instr: u8, count: usize) {
        match instr {
            b'\0' => (),
            b'[' => self.bulk_push_uncondensed(InstructionTag::BFLoopStart, count),
            b']' => self.bulk_push_uncondensed(InstructionTag::BFLoopEnd, count),
            b',' => self.bulk_push_uncondensed(InstructionTag::BFRead, count),
            b'.' => self.bulk_push_uncondensed(InstructionTag::BFWrite, count),
            b'@' => self.instructions.push_back(InstructionTag::SetZero),
            b'+' => self.repeat_push(InstructionTag::BFAdd, InstructionTag::RepeatAdd, count),
            b'-' => self.repeat_push(InstructionTag::BFSub, InstructionTag::RepeatSub, count),
            b'<' => self.repeat_push(InstructionTag::BFMoveL, InstructionTag::RepeatMoveL, count),
            b'>' => self.repeat_push(InstructionTag::BFMoveR, InstructionTag::RepeatMoveR, count),
            i => panic!(
                "instruction {} is invalid and should've been filtered",
                i.escape_ascii()
            ),
        }
    }

    fn get_count(&mut self) -> NonZeroUsize {
        self.repeat_counts
            .pop_front()
            .expect("CondensedInstructions will always have exactly enough repeat_counts")
    }
}

impl Iterator for CondensedInstructions {
    type Item = CondensedInstruction;
    fn next(&mut self) -> Option<Self::Item> {
        self.instructions.pop_front().map(|i| match i {
            InstructionTag::BFAdd => CondensedInstruction::BFInstruction(b'+'),
            InstructionTag::BFSub => CondensedInstruction::BFInstruction(b'-'),
            InstructionTag::BFMoveR => CondensedInstruction::BFInstruction(b'>'),
            InstructionTag::BFMoveL => CondensedInstruction::BFInstruction(b'<'),
            InstructionTag::BFRead => CondensedInstruction::BFInstruction(b','),
            InstructionTag::BFWrite => CondensedInstruction::BFInstruction(b'.'),
            InstructionTag::BFLoopStart => CondensedInstruction::BFInstruction(b'['),
            InstructionTag::BFLoopEnd => CondensedInstruction::BFInstruction(b']'),
            InstructionTag::RepeatAdd => CondensedInstruction::RepeatAdd(self.get_count()),
            InstructionTag::RepeatSub => CondensedInstruction::RepeatSub(self.get_count()),
            InstructionTag::RepeatMoveR => CondensedInstruction::RepeatMoveR(self.get_count()),
            InstructionTag::RepeatMoveL => CondensedInstruction::RepeatMoveL(self.get_count()),
            InstructionTag::SetZero => CondensedInstruction::SetZero,
        })
    }
}

pub(super) fn to_condensed(
    mut file: impl Read,
) -> Result<impl Iterator<Item = CondensedInstruction>, BFCompileError> {
    let mut code_buf = Vec::<u8>::new();
    let _ = file.read_to_end(&mut code_buf).map_err(|_| {
        BFCompileError::basic(BFErrorID::FailedRead, "Failed to read file into buffer")
    })?;
    code_buf.retain(|b| b"+-<>,.[]".contains(b));
    loops_match(code_buf.as_slice())?;
    strip_dead_code(&mut code_buf);
    Ok(condense(code_buf))
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
    let small_patterns: [&[u8]; 4] = [
        b"+-".as_slice(),
        b"-+".as_slice(),
        b"<>".as_slice(),
        b"><".as_slice(),
    ];
    for (i, window) in code_bytes.windows(2).enumerate() {
        if small_patterns.contains(&window) {
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

fn condense(stripped_bytes: Vec<u8>) -> CondensedInstructions {
    let mut condensed_instrs = CondensedInstructions::new();
    let mut prev_instr = b'\0';
    let mut count: usize = 0;
    let instr_string = String::from_utf8(stripped_bytes)
        .expect("non-bf bytes shouldn't have appeared!")
        .replace("[-]", "@")
        .replace("[+]", "@");

    let instr_chars = instr_string.bytes();

    for current_instr in instr_chars {
        if current_instr == prev_instr {
            count += 1;
        } else {
            condensed_instrs.push(prev_instr, count);
            count = 1;
            prev_instr = current_instr;
        }
    }
    condensed_instrs.push(prev_instr, count);
    condensed_instrs
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

    #[test]
    fn to_condensed_test() {
        assert_eq!(
            to_condensed(b"e+[+]++[-],.....".as_slice())
                .unwrap()
                .collect::<Vec<_>>(),
            vec![
                CondensedInstruction::BFInstruction(b'+'),
                CondensedInstruction::SetZero,
                CondensedInstruction::RepeatAdd(const { NonZeroUsize::new(2).unwrap() }),
                CondensedInstruction::SetZero,
                CondensedInstruction::BFInstruction(b','),
                CondensedInstruction::BFInstruction(b'.'),
                CondensedInstruction::BFInstruction(b'.'),
                CondensedInstruction::BFInstruction(b'.'),
                CondensedInstruction::BFInstruction(b'.'),
                CondensedInstruction::BFInstruction(b'.'),
            ]
        );
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

        assert!(to_condensed(unreadable).is_err_and(|e| e.kind == BFErrorID::FailedRead));
    }

    #[test]
    #[should_panic(expected = "instruction i is invalid and should've been filtered")]
    fn unfiltered_bf_panics() {
        let mut ci = CondensedInstructions::new();
        ci.push(b'i', 32);
    }

    #[test]
    // throw a whole bunch of instructions at the wall and ensure they all stick
    fn all_instructons_work() {
        let mut ci = CondensedInstructions::new();
        ci.push(b'>', 1);
        ci.push(b'+', 1);
        ci.push(b'<', 1);
        ci.push(b'-', 1);
        ci.push(b'>', 32);
        ci.push(b'+', 32);
        ci.push(b'<', 32);
        ci.push(b'-', 32);
        ci.push(b'@', 2);
        ci.push(b'[', 3);
        ci.push(b'-', 101);
        ci.push(b']', 3);
        ci.push(b',', 3);
        ci.push(b',', 1);
        ci.push(b'.', 3);
        ci.push(b'.', 1);
        let instructions: Vec<CondensedInstruction> = ci.collect();
        assert_eq!(
            instructions,
            vec![
                CondensedInstruction::BFInstruction(b'>'),
                CondensedInstruction::BFInstruction(b'+'),
                CondensedInstruction::BFInstruction(b'<'),
                CondensedInstruction::BFInstruction(b'-'),
                CondensedInstruction::RepeatMoveR(NonZeroUsize::new(32).unwrap()),
                CondensedInstruction::RepeatAdd(NonZeroUsize::new(32).unwrap()),
                CondensedInstruction::RepeatMoveL(NonZeroUsize::new(32).unwrap()),
                CondensedInstruction::RepeatSub(NonZeroUsize::new(32).unwrap()),
                CondensedInstruction::SetZero,
                CondensedInstruction::BFInstruction(b'['),
                CondensedInstruction::BFInstruction(b'['),
                CondensedInstruction::BFInstruction(b'['),
                CondensedInstruction::RepeatSub(NonZeroUsize::new(101).unwrap()),
                CondensedInstruction::BFInstruction(b']'),
                CondensedInstruction::BFInstruction(b']'),
                CondensedInstruction::BFInstruction(b']'),
                CondensedInstruction::BFInstruction(b','),
                CondensedInstruction::BFInstruction(b','),
                CondensedInstruction::BFInstruction(b','),
                CondensedInstruction::BFInstruction(b','),
                CondensedInstruction::BFInstruction(b'.'),
                CondensedInstruction::BFInstruction(b'.'),
                CondensedInstruction::BFInstruction(b'.'),
                CondensedInstruction::BFInstruction(b'.'),
            ]
        );
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
