// SPDX-FileCopyrightText: 2024 - 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use super::FilteredInstr;
use crate::err::{BFCompileError, BFErrorID};
use std::io::BufRead;
use std::num::NonZero;

/// Represents one or more instructions, in an intemediate form that's easier to optimize.
#[derive(Clone, Copy, PartialEq)]
#[cfg_attr(any(test, debug_assertions), derive(Debug))]
enum InstrSequence {
    /// A brainfuck `[`
    LoopOpen,
    /// A brainfuck `]`
    LoopClose,
    /// A brainfuck `,`
    Read,
    /// A brainfuck `.`
    Write,
    /// One or more consecutive brainfuck `+` or `-` instructions
    ModifyCell(NonZero<i8>),
    /// One or more consecutive brainfuck `<` or `>` instructions
    ModifyPtr(NonZero<i64>),
    /// `SetCell(0)` replaces a loop that always sets the current cell to 0 with no side effects.
    /// In addition, `SetCell(0)` followed by `ModifyCell(n)` can then be replaced with
    /// `SetCell(n.get() as u8)`.
    SetCell(u8),
}

/// the intermediate representation instructions produced by the optimization process
#[derive(Clone, Copy, PartialEq)]
#[cfg_attr(test, derive(Debug))]
pub(super) enum CombinedInstruction {
    LoopOpen,
    LoopClose,
    Read,
    Write,
    Add(u8),
    Sub(u8),
    MoveRight(u64),
    MoveLeft(u64),
    SetCell(u8),
}

impl From<InstrSequence> for CombinedInstruction {
    fn from(is: InstrSequence) -> Self {
        match is {
            InstrSequence::LoopOpen => Self::LoopOpen,
            InstrSequence::LoopClose => Self::LoopClose,
            InstrSequence::Read => Self::Read,
            InstrSequence::Write => Self::Write,
            InstrSequence::SetCell(imm) => Self::SetCell(imm),
            InstrSequence::ModifyCell(imm) => {
                if imm.get() > 0 {
                    Self::Add(imm.get().unsigned_abs())
                } else {
                    Self::Sub(imm.get().unsigned_abs())
                }
            }
            InstrSequence::ModifyPtr(imm) => {
                if imm.get() > 0 {
                    Self::MoveRight(imm.get().unsigned_abs())
                } else {
                    Self::MoveLeft(imm.get().unsigned_abs())
                }
            }
        }
    }
}

impl InstrSequence {
    fn try_joining(self, other: Self) -> CombinationOutcome {
        match (self, other) {
            (IS::ModifyPtr(na), IS::ModifyPtr(nb)) => {
                if let Some(n) = NonZero::new(na.get().wrapping_add(nb.get())) {
                    CombinationOutcome::CombineInto(Self::ModifyPtr(n))
                } else {
                    CombinationOutcome::CancelOut
                }
            }
            (IS::ModifyCell(na), IS::ModifyCell(nb)) => {
                if let Some(n) = NonZero::new(na.get().wrapping_add(nb.get())) {
                    CombinationOutcome::CombineInto(Self::ModifyCell(n))
                } else {
                    CombinationOutcome::CancelOut
                }
            }
            _ => CombinationOutcome::DontCombine,
        }
    }
}

#[derive(Clone, Copy, PartialEq)]
#[cfg_attr(test, derive(Debug))]
enum CombinationOutcome {
    CancelOut,
    CombineInto(InstrSequence),
    DontCombine,
}

impl From<FilteredInstr> for InstrSequence {
    fn from(fi: FilteredInstr) -> Self {
        match fi {
            FilteredInstr::Sub => InstrSequence::ModifyCell(const { NonZero::new(-1).unwrap() }),
            FilteredInstr::Add => InstrSequence::ModifyCell(const { NonZero::new(1).unwrap() }),
            FilteredInstr::MoveL => InstrSequence::ModifyPtr(const { NonZero::new(-1).unwrap() }),
            FilteredInstr::MoveR => InstrSequence::ModifyPtr(const { NonZero::new(1).unwrap() }),
            FilteredInstr::LoopOpen => InstrSequence::LoopOpen,
            FilteredInstr::LoopClose => InstrSequence::LoopClose,
            FilteredInstr::Read => InstrSequence::Read,
            FilteredInstr::Write => InstrSequence::Write,
        }
    }
}

use FilteredInstr as FI;
use InstrSequence as IS;

fn recheck_mergable(ir: &mut Vec<IS>, mut index: usize) {
    while let (Some(instr), Some(next_instr)) = (ir.get(index).copied(), ir.get(index + 1).copied())
    {
        match instr.try_joining(next_instr) {
            CombinationOutcome::CombineInto(new) => {
                ir[index] = new;
                ir.remove(index + 1);
            }
            CombinationOutcome::CancelOut => {
                ir.drain(index..=index + 1);
                if index == 0 {
                    return;
                }
                index -= 1;
            }
            CombinationOutcome::DontCombine => return,
        }
    }
}

/// Scan `ir` for dead loops - that is, loops that are immediately after other loops, or are before
/// any read, add, or sub instructions, and thus will never run.
fn drop_dead_loops(ir: &mut Vec<IS>) -> Result<(), BFCompileError> {
    // Start on LoopClose to eliminate opening loops from the very start of the code
    let mut can_elim = true;
    // Until `IS::ModifyCell` or `IS::Read` is found, all cell values can be known to be zero, as
    // long as this function is called before `join_set_cells`.
    let mut known_all_zeroes = true;
    let mut i = 0;
    'outer: while let Some(instr) = ir.get(i).copied() {
        debug_assert!(
            !matches!(instr, IS::SetCell(_)),
            "`drop_dead_loops` should be called before set_sequences are handled"
        );
        if instr == IS::LoopOpen && can_elim {
            let mut ii = i + 1;
            let mut nest_level: usize = 1;
            while let Some(inner_instr) = ir.get(ii).copied() {
                match inner_instr {
                    IS::LoopOpen => nest_level += 1,
                    IS::LoopClose => {
                        nest_level -= 1;
                        if nest_level == 0 {
                            ir.drain(i..=ii);
                            // check if the removal of the dead loop results in a newly-exposed
                            // mergeable instruction pair
                            if i > 0 {
                                recheck_mergable(ir, i - 1);
                            }
                            continue 'outer;
                        }
                    }
                    _ => (),
                }
                ii += 1;
            }
            return Err(BFCompileError::new(
                BFErrorID::UnmatchedOpen,
                "Could not optimize properly due to unmatched loop open",
                Some(b'['),
                None,
            ));
        } else if matches!(instr, IS::Read | IS::ModifyCell(_)) {
            known_all_zeroes = false;
        }
        can_elim = known_all_zeroes || instr == IS::LoopClose;
        i += 1;
    }
    Ok(())
}

/// append one or more `InstrSequence`s to `dest` to represent `count` consecutive `instr`s
fn append_counted_instrs(dest: &mut Vec<InstrSequence>, count: usize, instr: FilteredInstr) {
    /// 4 nearly-identical pranches can be implemented with this macro - `$variant` is the
    ///   identifier for the `CombinedInstruction` enum variant, and `$count_expr` is the
    ///   expression to get the value from `count`.
    macro_rules! condense_to {
        ($variant: ident, $count_expr: expr) => {{
            if let Some(ct) = NonZero::new($count_expr) {
                dest.push(IS::$variant(ct));
            }
        }};
    }
    match instr {
        FI::Add => condense_to!(ModifyCell, count.to_le_bytes()[0].cast_signed()),
        FI::Sub => condense_to!(
            ModifyCell,
            count.to_le_bytes()[0].cast_signed().wrapping_neg()
        ),
        FI::MoveR => condense_to!(ModifyPtr, count.cast_signed() as i64),
        FI::MoveL => condense_to!(ModifyPtr, (count.cast_signed() as i64).wrapping_neg()),
        prev => dest.resize(dest.len() + count, prev.into()),
    }
}

/// Combine filtered instructions from `filtered_instrs` into a vec of `InstrSequence`s, returning
/// an `Err(BFCompileError)` on read failure.
fn combine_filtered(
    filtered_instrs: impl IntoIterator<Item = Result<FI, BFCompileError>>,
) -> Result<Vec<InstrSequence>, BFCompileError> {
    let mut count: usize = 0;
    let mut previous: Option<FI> = None;
    let mut combined = Vec::<IS>::new();
    let mut filtered_instrs = filtered_instrs.into_iter();
    while let Some(instr) = filtered_instrs.next().transpose()? {
        match previous {
            None => {
                previous = Some(instr);
                count = 1;
            }
            Some(prev) if prev == instr => count += 1,
            Some(prev) => {
                append_counted_instrs(&mut combined, count, prev);
                count = 1;
                previous = Some(instr);
            }
        }
    }
    if let Some(final_instr) = previous {
        append_counted_instrs(&mut combined, count, final_instr);
    }
    Ok(combined)
}

/// Join adjacent `ModifyCell` or `ModifyPtr` sequences, removing any that cancel out
fn join_adjacent_arith(insns: &mut Vec<InstrSequence>) {
    let mut i = 0;
    while i < insns.len().saturating_sub(1) {
        match insns[i].try_joining(insns[i + 1]) {
            CombinationOutcome::CombineInto(combined) => {
                insns.remove(i);
                insns[i] = combined;
            }
            CombinationOutcome::CancelOut => drop(insns.drain(i..=i + 1)),
            CombinationOutcome::DontCombine => i += 1,
        }
    }
}

fn join_set_cells(ir: &mut Vec<InstrSequence>) {
    // Try to find sequences that set the current cell to a predetermined value, by zeroing it out
    // then optionally adding or subtracting any number of times (including 0), and replace with
    // `IS::SetCell`.

    let mut search_start = 0;
    'outer: loop {
        for (i, window) in ir.windows(3).enumerate().skip(search_start) {
            if window[0] == IS::LoopOpen
                && matches!(window[1], IS::ModifyCell(ct) if ct.get().abs() % 2 == 1)
                && window[2] == IS::LoopClose
            {
                ir.drain(i + 1..=i + 2);
                match ir.get(i + 1) {
                    Some(IS::ModifyCell(n)) => {
                        ir[i] = IS::SetCell(n.get().cast_unsigned());
                        ir.remove(i + 1);
                    }
                    _ => ir[i] = IS::SetCell(0),
                }
                continue 'outer;
            }
            search_start += 1;
        }
        break 'outer;
    }
}

use super::CodeReader;
/// Collect `instructions` into a `Vec<CombinedInstruction>`, performing various optimizations in
/// the process.
pub(super) fn combine_instructions(
    instructions: CodeReader<impl BufRead>,
) -> Result<Vec<CombinedInstruction>, BFCompileError> {
    let mut combined = combine_filtered(instructions)?;
    join_adjacent_arith(&mut combined);

    drop_dead_loops(&mut combined)?;
    join_set_cells(&mut combined);

    // drop trailing instructions other than `]`, `,`, or `.`, as other instructiosn will have no
    // externally-visible effects if no I/O instructions will be run afterwards.
    while combined
        .last()
        .is_some_and(|l| !matches!(l, IS::Read | IS::Write | IS::LoopClose))
    {
        combined.remove(combined.len() - 1);
    }
    Ok(combined.into_iter().map(From::from).collect())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn translate_between_levels() {
        let instrs: Vec<_> = Vec::from(b"+-<>[],.")
            .into_iter()
            .filter_map(|b| FilteredInstr::from_byte(b).map(InstrSequence::from))
            .collect();
        assert_eq!(
            instrs,
            [
                InstrSequence::ModifyCell(NonZero::new(1).unwrap()),
                InstrSequence::ModifyCell(NonZero::new(-1).unwrap()),
                InstrSequence::ModifyPtr(NonZero::new(-1).unwrap()),
                InstrSequence::ModifyPtr(NonZero::new(1).unwrap()),
                InstrSequence::LoopOpen,
                InstrSequence::LoopClose,
                InstrSequence::Read,
                InstrSequence::Write,
            ]
        );
        let instrs: Vec<_> = instrs.into_iter().map(CombinedInstruction::from).collect();
        assert_eq!(
            instrs,
            [
                CombinedInstruction::Add(1),
                CombinedInstruction::Sub(1),
                CombinedInstruction::MoveLeft(1),
                CombinedInstruction::MoveRight(1),
                CombinedInstruction::LoopOpen,
                CombinedInstruction::LoopClose,
                CombinedInstruction::Read,
                CombinedInstruction::Write,
            ]
        );
        // Original implementation swapped left and right terminology, so make sure to catch that.
        assert_eq!(
            CombinedInstruction::from(InstrSequence::from(FilteredInstr::from_byte(b'>').unwrap())),
            CombinedInstruction::MoveRight(1)
        );
        assert_eq!(
            CombinedInstruction::from(InstrSequence::from(FilteredInstr::from_byte(b'<').unwrap())),
            CombinedInstruction::MoveLeft(1)
        );
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic = "`drop_dead_loops` should be called before set_sequences are handled"]
    fn combined_called_out_of_order() {
        #[allow(
            clippy::let_underscore_must_use,
            reason = "checking for debug_assert_eq anyway"
        )]
        let _ = drop_dead_loops(&mut vec![InstrSequence::SetCell(0)]);
    }

    #[test]
    fn combination_logic_works() {
        assert_eq!(
            IS::try_joining(
                IS::ModifyPtr(NonZero::new(32).unwrap()),
                IS::ModifyCell(NonZero::new(32).unwrap())
            ),
            CombinationOutcome::DontCombine
        );
        assert_eq!(
            IS::try_joining(
                IS::ModifyPtr(NonZero::new(-32).unwrap()),
                IS::ModifyPtr(NonZero::new(-32).unwrap())
            ),
            CombinationOutcome::CombineInto(IS::ModifyPtr(NonZero::new(-64).unwrap()))
        );
        assert_eq!(
            IS::try_joining(
                IS::ModifyPtr(NonZero::new(32).unwrap()),
                IS::ModifyPtr(NonZero::new(32).unwrap())
            ),
            CombinationOutcome::CombineInto(IS::ModifyPtr(NonZero::new(64).unwrap()))
        );
        assert_eq!(
            IS::try_joining(
                IS::ModifyPtr(NonZero::new(32).unwrap()),
                IS::ModifyPtr(NonZero::new(-32).unwrap())
            ),
            CombinationOutcome::CancelOut
        );
    }
    #[test]
    fn combination_test() {
        let mut code = Vec::from(b"[+++++]><+---+++-[-][,[-][+>-<]]-+[-+]-+[]+-[]");
        code.extend([b'+'; 256]);
        code.extend(b"[+-]>>+<");
        code.extend([b'-'; 256]);
        code.extend(b"[->+<][,.]");
        code.extend(b"+++");
        let combined = combine_instructions(CodeReader::new(code.as_slice())).unwrap();

        // Should be reduced by dead code removal to the equivalent of ">>+<[->+<]"
        assert_eq!(
            combined,
            [
                CombinedInstruction::MoveRight(2),
                CombinedInstruction::Add(1),
                CombinedInstruction::MoveLeft(1),
                CombinedInstruction::LoopOpen,
                CombinedInstruction::Sub(1),
                CombinedInstruction::MoveRight(1),
                CombinedInstruction::Add(1),
                CombinedInstruction::MoveLeft(1),
                CombinedInstruction::LoopClose
            ]
        );
    }
    #[test]
    fn zeroing_code_caught() {
        // Using `,` before each loop prevents the optimizer from concluding the loops are dead,
        // and the trailing `,` prevents it from removing the last SetCell as side-effect-free.
        // Even numbers of adds or subs may loop forever or set zero, but odd numbers will always
        // set zero.
        let code = combine_instructions(CodeReader::new(
            b",[-],[--],[---],[+++],[++],[+],".as_slice(),
        ))
        .unwrap();
        assert_eq!(
            code,
            [
                CombinedInstruction::Read,       // b","
                CombinedInstruction::SetCell(0), // b"[-]"
                CombinedInstruction::Read,       // b","
                CombinedInstruction::LoopOpen,   // b"["
                CombinedInstruction::Sub(2),     // b"--"
                CombinedInstruction::LoopClose,  // b"]"
                CombinedInstruction::Read,       // b","
                CombinedInstruction::SetCell(0), // b"[---]"
                CombinedInstruction::Read,       // b","
                CombinedInstruction::SetCell(0), // b"[+++]"
                CombinedInstruction::Read,       // b","
                CombinedInstruction::LoopOpen,   // b"["
                CombinedInstruction::Add(2),     // b"++"
                CombinedInstruction::LoopClose,  // b"]"
                CombinedInstruction::Read,       // b","
                CombinedInstruction::SetCell(0), // b"[+]"
                CombinedInstruction::Read,       // b","
            ]
        );
    }
}
