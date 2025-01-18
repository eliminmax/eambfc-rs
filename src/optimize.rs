// SPDX-FileCopyrightText: 2024 - 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use super::err::{BFCompileError, BFErrorID};
use std::collections::VecDeque;
use std::io::Read;
use std::num::NonZeroUsize;

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum CondensedInstruction {
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

    fn push(&mut self, instr: u8, count: usize) {
        macro_rules! bulk_push_uncondensed {
            ($id: ident) => {{
                self.instructions
                    .extend([InstructionTag::$id].repeat(count));
            }};
        }
        macro_rules! repeat_push {
            ($single: ident, $multi: ident) => {{
                if count == 1 {
                    self.instructions.push_back(InstructionTag::$single)
                } else {
                    let count = NonZeroUsize::new(count).expect("count is nonzero");
                    self.instructions.push_back(InstructionTag::$multi);
                    self.repeat_counts.push_back(count);
                }
            }};
        }

        match instr {
            b'\0' => (),
            b'[' => bulk_push_uncondensed!(BFLoopStart),
            b']' => bulk_push_uncondensed!(BFLoopEnd),
            b',' => bulk_push_uncondensed!(BFRead),
            b'.' => bulk_push_uncondensed!(BFWrite),
            b'@' => self.instructions.push_back(InstructionTag::SetZero),
            b'+' => repeat_push!(BFAdd, RepeatAdd),
            b'-' => repeat_push!(BFSub, RepeatSub),
            b'<' => repeat_push!(BFMoveL, RepeatMoveL),
            b'>' => repeat_push!(BFMoveR, RepeatMoveR),
            i => panic!(
                "instruction {} is invalid and should've been filtered",
                i.escape_ascii()
            ),
        }
    }
}

impl Iterator for CondensedInstructions {
    type Item = CondensedInstruction;
    fn next(&mut self) -> Option<Self::Item> {
        macro_rules! get_count {
            () => {
                self.repeat_counts
                    .pop_front()
                    .expect("CondensedInstructions must have valid internal state")
            };
        }
        self.instructions.pop_front().map(|i| match i {
            InstructionTag::BFAdd => CondensedInstruction::BFInstruction(b'+'),
            InstructionTag::BFSub => CondensedInstruction::BFInstruction(b'-'),
            InstructionTag::BFMoveR => CondensedInstruction::BFInstruction(b'>'),
            InstructionTag::BFMoveL => CondensedInstruction::BFInstruction(b'<'),
            InstructionTag::BFRead => CondensedInstruction::BFInstruction(b','),
            InstructionTag::BFWrite => CondensedInstruction::BFInstruction(b'.'),
            InstructionTag::BFLoopStart => CondensedInstruction::BFInstruction(b'['),
            InstructionTag::BFLoopEnd => CondensedInstruction::BFInstruction(b']'),
            InstructionTag::RepeatAdd => CondensedInstruction::RepeatAdd(get_count!()),
            InstructionTag::RepeatSub => CondensedInstruction::RepeatSub(get_count!()),
            InstructionTag::RepeatMoveR => CondensedInstruction::RepeatMoveR(get_count!()),
            InstructionTag::RepeatMoveL => CondensedInstruction::RepeatMoveL(get_count!()),
            InstructionTag::SetZero => CondensedInstruction::SetZero,
        })
    }
}

pub fn to_condensed(
    mut file: Box<dyn Read>,
) -> Result<impl Iterator<Item = CondensedInstruction>, BFCompileError> {
    let mut code_buf = Vec::<u8>::new();
    let _ = file.read_to_end(&mut code_buf).map_err(|_| {
        BFCompileError::basic(BFErrorID::FAILED_READ, "Failed to read file into buffer")
    })?;
    code_buf.retain(|b| b"+-<>,.[]".contains(b));
    loops_match(code_buf.as_slice())?;
    let stripped_bytes = strip_dead_code(code_buf);
    Ok(condense(stripped_bytes))
}

fn loops_match(code_bytes: &[u8]) -> Result<(), BFCompileError> {
    let mut ret: Result<(), ()> = Ok(());
    let mut nest_level: usize = 0;
    code_bytes.iter().for_each(|b| match b {
        b'[' => nest_level += 1,
        b']' => {
            if nest_level == 0 {
                ret = Err(());
            } else {
                nest_level -= 1;
            }
        }
        _ => {}
    });
    if nest_level > 0 {
        Err(BFCompileError::basic(
            BFErrorID::UNMATCHED_OPEN,
            "Found an unmatched '[' while preparing for optimization. \
                    Compile without -O for more information.",
        ))
    } else {
        ret.map_err(|()| {
            BFCompileError::basic(
                BFErrorID::UNMATCHED_CLOSE,
                "Found an unmatched ']' while preparing for optimization. \
                    Compile without -O for more information.",
            )
        })
    }
}

fn remove_loop_at(index: usize, target: &mut Vec<u8>) {
    if target.get(index).unwrap_or(&b'_') != &b'[' {
        // early return - maybe removed if nested inside of another loop removed in an earlier run
        // through this function, and vec.split_off(at) panics if out-of-bounds
        return;
    }
    let split_holder = target.split_off(index);
    let mut nest_level = 0;
    let mut index = 0;
    let mut split_holder = split_holder
        .into_iter()
        .skip_while(|b| {
            if b == &b'[' {
                nest_level += 1;
            } else if b == &b']' {
                nest_level -= 1;
            }

            index += 1;
            nest_level > 0
        })
        .skip(1)
        .collect::<Vec<u8>>();

    target.append(&mut split_holder);
}

fn strip_dead_code(mut filtered_bytes: Vec<u8>) -> Vec<u8> {
    // loop through 3 steps until they leave things unchanged
    assert!(filtered_bytes.is_ascii());
    let mut old_filtered: String;
    loop {
        old_filtered =
            String::from_utf8(filtered_bytes).expect("non-bf bytes shouldn't have appeared!");
        // first, replace sequences within the bf_bytes String that cancel out.
        let mut new_filtered = old_filtered
            .replace("+-", "")
            .replace("-+", "")
            .replace("<>", "")
            .replace("><", "")
            .replace(&"-".repeat(256), "")
            .replace(&"+".repeat(256), "")
            .into_bytes();

        // remove leading dead loop
        if new_filtered.starts_with(b"[") {
            remove_loop_at(0, &mut new_filtered);
        }
        // find location of dead loop that may exist later in the program
        let mut dead_loop_starts = new_filtered
            .as_slice()
            .windows(2)
            .enumerate()
            .filter(|(_, val)| (val == b"]["))
            .map(|(i, _)| i + 1);

        if let Some(index) = dead_loop_starts.next() {
            remove_loop_at(index, &mut new_filtered);
        }
        // finally, check if any of the above changed anything. If not, break out of the loop.
        if old_filtered.as_bytes() == new_filtered.as_slice() {
            return new_filtered;
        }
        filtered_bytes = new_filtered;
    }
}

fn condense(stripped_bytes: Vec<u8>) -> CondensedInstructions {
    let mut condensed_instrs = CondensedInstructions::new();
    let mut prev_instr = b'\0';
    let mut count = 0usize;
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
        assert_eq!(strip_dead_code(code), Vec::from(b">[->+<]"));
    }

    #[test]
    fn to_condensed_test() {
        assert_eq!(
            to_condensed(Box::new(b"e+[+]++[-],.....".as_slice()))
                .unwrap()
                .collect::<Vec<_>>(),
            vec![
                CondensedInstruction::BFInstruction(b'+'),
                CondensedInstruction::SetZero,
                CondensedInstruction::RepeatAdd(const { NonZeroUsize::new(2usize).unwrap() }),
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
        let unreadable = Box::new(Unreadable {});

        assert!(to_condensed(unreadable).is_err_and(|e| e.kind == BFErrorID::FAILED_READ));
    }

    #[test]
    fn unmatched_loops_detected() {
        assert_eq!(
            loops_match(b"[").unwrap_err().kind,
            BFErrorID::UNMATCHED_OPEN,
        );
        assert_eq!(
            loops_match(b"]").unwrap_err().kind,
            BFErrorID::UNMATCHED_CLOSE,
        );
    }
}
