// SPDX-FileCopyrightText: 2024 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use super::err::BFCompileError;
use std::io::Read;

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum CondensedInstruction {
    BFInstruction(u8),
    RepeatMoveR(usize),
    RepeatMoveL(usize),
    RepeatAdd(usize),
    RepeatSub(usize),
    SetZero,
}

pub fn to_condensed<R: Read>(mut file: R) -> Result<Vec<CondensedInstruction>, BFCompileError> {
    let mut source_file_bytes = Vec::<u8>::new();
    let _ = file
        .read_to_end(&mut source_file_bytes)
        .map_err(|_| BFCompileError::Basic {
            id: String::from("FAILED_READ"),
            msg: String::from("Failed to read file into buffer"),
        })?;
    let filtered_bytes = filter_non_bf(source_file_bytes)?;
    let stripped_bytes = strip_dead_code(filtered_bytes);
    Ok(condense(stripped_bytes))
}

#[derive(Debug, PartialEq)]
enum LoopsMatched {
    Balanced,
    UnmatchedOpen,
    UnmatchedClose,
}

fn filter_non_bf(source_file_bytes: Vec<u8>) -> Result<Vec<u8>, BFCompileError> {
    // first, filter out non-bf characters
    let filtered_bytes = source_file_bytes
        .into_iter()
        .filter(|b| b"+-<>,.[]".contains(b))
        .collect::<Vec<u8>>();
    match loops_match(filtered_bytes.as_slice()) {
        LoopsMatched::Balanced => Ok(filtered_bytes),
        LoopsMatched::UnmatchedOpen => Err(BFCompileError::Basic {
            id: String::from("UNMATCHED_OPEN"),
            msg: String::from(
                "Found an unmatched '[' while preparing for optimization. \
                    Compile without -O for more information.",
            ),
        }),
        LoopsMatched::UnmatchedClose => Err(BFCompileError::Basic {
            id: String::from("UNMATCHED_CLOSE"),
            msg: String::from(
                "Found an unmatched ']' while preparing for optimization. \
                    Compile without -O for more information.",
            ),
        }),
    }
}

fn loops_match(code_bytes: &[u8]) -> LoopsMatched {
    let mut ret: LoopsMatched = LoopsMatched::Balanced;
    let mut nest_level: usize = 0;
    code_bytes.iter().for_each(|b| match b {
        b'[' => nest_level += 1,
        b']' => {
            if nest_level == 0 {
                ret = LoopsMatched::UnmatchedClose;
            } else {
                nest_level -= 1
            }
        }
        _ => {}
    });
    if nest_level > 0 {
        LoopsMatched::UnmatchedOpen
    } else {
        ret
    }
}

fn remove_loop_at(index: usize, target: &mut Vec<u8>) {
    if target.get(index).unwrap_or(&b'_') != &b'[' {
        // early return - maybe removed if nested inside of another loop removed in an earlier run
        // through this function, and vec.split_off(at) panics if at > vec.len.
        return;
    }
    let split_holder = target.split_off(index);
    let mut nest_level = 0;
    let mut index = 0;
    let mut split_holder = split_holder
        .into_iter()
        .skip_while(|b| {
            if b == &b'[' {
                nest_level += 1
            } else if b == &b']' {
                nest_level -= 1
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
            .filter_map(|(i, val)| if val == b"][" { Some(i + 1) } else { None });

        if let Some(index) = dead_loop_starts.next() {
            remove_loop_at(index, &mut new_filtered);
        }
        // finally, check if any of the above changed anything. If not, break out of the loop.
        if old_filtered.as_bytes() == new_filtered.as_slice() {
            return new_filtered;
        } else {
            filtered_bytes = new_filtered;
        }
    }
}

#[inline]
fn condense_instr(instr: u8, count: usize) -> Vec<CondensedInstruction> {
    macro_rules! condense_to {
        ($condensed_instr:expr) => {{
            if count == 1 {
                vec![CondensedInstruction::BFInstruction(instr)]
            } else {
                vec![$condensed_instr(count)]
            }
        }};
    }
    match instr {
        b'\0' => vec![], // null char used as a placeholder
        b'[' | b'.' | b']' | b',' => [CondensedInstruction::BFInstruction(instr)].repeat(count),
        b'@' => [CondensedInstruction::SetZero].repeat(count),
        b'+' => condense_to!(CondensedInstruction::RepeatAdd),
        b'-' => condense_to!(CondensedInstruction::RepeatSub),
        b'<' => condense_to!(CondensedInstruction::RepeatMoveL),
        b'>' => condense_to!(CondensedInstruction::RepeatMoveR),
        b => panic!("Invalid byte value: {b}"),
    }
}

fn condense(stripped_bytes: Vec<u8>) -> Vec<CondensedInstruction> {
    let mut condensed_instrs = Vec::<CondensedInstruction>::new();
    let mut prev_instr = b'\0';
    let mut count = 0usize;
    let instr_string = String::from_utf8(stripped_bytes)
        .expect("non-bf bytes shouldn't have appeared!")
        .replace("[-]", "@")
        .replace("[+]", "@");

    let instr_chars = instr_string.bytes();

    for current_instr in instr_chars {
        if current_instr == prev_instr {
            count += 1
        } else {
            condensed_instrs.append(&mut condense_instr(prev_instr, count));
            count = 1;
            prev_instr = current_instr;
        }
    }
    condensed_instrs.append(&mut condense_instr(prev_instr, count));
    condensed_instrs
}

#[cfg(test)]
mod tests {
    use super::*;

    #[inline]
    fn error_thrown(err: BFCompileError) -> String {
        match err {
            BFCompileError::UnknownFlag(_) => String::from("UNKNOWN_ARG"),
            BFCompileError::Basic { id, .. }
            | BFCompileError::Instruction { id, .. }
            | BFCompileError::Position { id, .. } => id,
        }
    }

    #[test]
    fn strip_dead_code_test() -> Result<(), String> {
        let code = filter_non_bf(
            b"[+++++]><+---+++-[-][,[-][+>-<]]-+[-+]-+[]+-[]\
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\
[+-]>\
----------------------------------------------------------------\
----------------------------------------------------------------\
----------------------------------------------------------------\
----------------------------------------------------------------\
[->+<][,.]"
                .to_vec(),
        )
        .unwrap();
        assert_eq!(strip_dead_code(code), Vec::from(b">[->+<]"));
        Ok(())
    }

    #[test]
    fn to_condensed_test() -> Result<(), String> {
        assert_eq!(
            to_condensed(b"e+[+]++[-],.....".as_slice()).unwrap(),
            vec![
                CondensedInstruction::BFInstruction(b'+'),
                CondensedInstruction::SetZero,
                CondensedInstruction::RepeatAdd(2usize),
                CondensedInstruction::SetZero,
                CondensedInstruction::BFInstruction(b','),
                CondensedInstruction::BFInstruction(b'.'),
                CondensedInstruction::BFInstruction(b'.'),
                CondensedInstruction::BFInstruction(b'.'),
                CondensedInstruction::BFInstruction(b'.'),
                CondensedInstruction::BFInstruction(b'.'),
            ]
        );
        Ok(())
    }

    use std::io::ErrorKind;
    struct Unreadable {}
    impl Read for Unreadable {
        fn read(&mut self, _buf: &mut [u8]) -> std::io::Result<usize> {
            Err(std::io::Error::new(ErrorKind::Unsupported, "Unreadable"))
        }
    }

    #[test]
    fn read_failure_handled() -> Result<(), String> {
        let unreadable = Unreadable {};
        match to_condensed(unreadable) {
            Ok(_) => {
                return Err(String::from(
                    "Did not see error when trying to read from unreadable",
                ))
            }
            Err(e) => assert_eq!(error_thrown(e), String::from("FAILED_READ")),
        };
        Ok(())
    }


    #[test]
    fn unmatched_loops_detected() -> Result<(), String> {
        assert_eq!(loops_match(b"["), LoopsMatched::UnmatchedOpen);
        assert_eq!(loops_match(b"]"), LoopsMatched::UnmatchedClose);
        Ok(())
    }
}
