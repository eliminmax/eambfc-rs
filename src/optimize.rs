// SPDX-FileCopyrightText: 2024 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use super::err::{BFCompileError, BFErrorID};
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

pub fn to_condensed(mut file: Box<dyn Read>) -> Result<Vec<CondensedInstruction>, BFCompileError> {
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
            .filter_map(|(i, val)| if val == b"][" { Some(i + 1) } else { None });

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

fn condense_instr(instr: u8, count: usize, condensed: &mut Vec<CondensedInstruction>) {
    macro_rules! condense_to {
        ($condensed_instr: ident) => {{
            if count == 1 {
                condensed.push(CondensedInstruction::BFInstruction(instr));
            } else {
                condensed.push(CondensedInstruction::$condensed_instr(count));
            }
        }};
    }
    match instr {
        b'\0' => (), // null char used as a placeholder
        b'[' | b'.' | b']' | b',' => {
            condensed.extend([CondensedInstruction::BFInstruction(instr)].repeat(count))
        }
        b'@' => condensed.extend([CondensedInstruction::SetZero].repeat(count)),
        b'+' => condense_to!(RepeatAdd),
        b'-' => condense_to!(RepeatSub),
        b'<' => condense_to!(RepeatMoveL),
        b'>' => condense_to!(RepeatMoveR),
        _ => unreachable!("Non-bf byte values are already purged"),
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
            count += 1;
        } else {
            condense_instr(prev_instr, count, &mut condensed_instrs);
            count = 1;
            prev_instr = current_instr;
        }
    }
    condense_instr(prev_instr, count, &mut condensed_instrs);
    condensed_instrs
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn strip_dead_code_test() -> Result<(), String> {
        let mut code = Vec::from(b"[+++++]><+---+++-[-][,[-][+>-<]]-+[-+]-+[]+-[]");
        code.extend(b"+".repeat(256));
        code.extend_from_slice(b"[+-]>");
        code.extend(b"-".repeat(256));
        code.extend_from_slice(b"[->+<][,.]");
        assert_eq!(strip_dead_code(code), Vec::from(b">[->+<]"));
        Ok(())
    }

    #[test]
    fn to_condensed_test() -> Result<(), String> {
        assert_eq!(
            to_condensed(Box::new(b"e+[+]++[-],.....".as_slice())).unwrap(),
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
        let unreadable = Box::new(Unreadable {});
        match to_condensed(unreadable) {
            Ok(_) => {
                return Err(String::from(
                    "Did not see error when trying to read from unreadable",
                ))
            }
            Err(e) => assert_eq!(e.kind, BFErrorID::FAILED_READ),
        };
        Ok(())
    }

    #[test]
    fn unmatched_loops_detected() -> Result<(), String> {
        assert_eq!(
            loops_match(b"[").unwrap_err().kind,
            BFErrorID::UNMATCHED_OPEN,
        );
        assert_eq!(
            loops_match(b"]").unwrap_err().kind,
            BFErrorID::UNMATCHED_CLOSE,
        );
        Ok(())
    }
}
