// SPDX-FileCopyrightText: 2024 - 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use super::FilteredInstr;
use crate::err::{BFCompileError, BFErrorID};
use std::io::BufRead;
use std::num::NonZero;

/// Represents one or more instructions, in an intemediate form that's easier to optimize.
#[derive(Clone, Copy, PartialEq)]
#[cfg_attr(debug_assertions, derive(Debug))]
enum InstrSequence {
    LoopOpen,
    LoopClose,
    Read,
    Write,
    ModifyCell(NonZero<i8>),
    ModifyPtr(NonZero<i64>),
    SetCell(u8),
}

/// the intermediate representation instructions produced by the optimization process
#[derive(Clone, Copy, PartialEq)]
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

/// Scan `ir` for dead loops - that is, loops that are immediately after other loops, or
fn drop_dead_loops(ir: &mut Vec<IS>) -> Result<(), BFCompileError> {
    // Start on LoopClose to eliminate opening loops from the very start of the code
    let mut can_elim = true;
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
        }
        i += 1;
        can_elim = instr == IS::LoopClose;
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
        FI::Add => condense_to!(ModifyCell, count as i8),
        FI::Sub => condense_to!(ModifyCell, (count as i8).wrapping_neg()),
        FI::MoveR => condense_to!(ModifyPtr, count as i64),
        FI::MoveL => condense_to!(ModifyPtr, (count as i64).wrapping_neg()),
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
                debug_assert_eq!(
                    0, count,
                    "nonzero count makes no sense without previous instr."
                );
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

use super::CodeReader;
/// Collect `instructions` into a `Vec<CombinedInstruction>`, performing various optimizations in
/// the process.
pub(super) fn combine_instructions(
    instructions: CodeReader<impl BufRead>,
) -> Result<Vec<CombinedInstruction>, BFCompileError> {
    let mut combined = combine_filtered(instructions)?;
    join_adjacent_arith(&mut combined);

    // Try to find sequences that set the current cell to a predetermined value, by zeroing it out
    // then optionally adding or subtracting any number of times (including 0), and replace with
    // `IS::SetCell`.
    let mut search_start = 0;
    drop_dead_loops(&mut combined)?;

    'outer: loop {
        for (i, window) in combined.windows(3).enumerate().skip(search_start) {
            if window[0] == IS::LoopOpen
                && matches!(window[1], IS::ModifyCell(ct) if ct.get() % 2 == 1)
                && window[2] == IS::LoopClose
            {
                combined.drain(i + 1..=i + 2);
                match combined.get(i + 1) {
                    Some(IS::ModifyPtr(n)) => {
                        combined[i] = IS::SetCell(n.get() as u8);
                        combined.remove(i + 1);
                    }
                    _ => combined[i] = IS::SetCell(0),
                }
                continue 'outer;
            }
            search_start += 1;
        }
        break 'outer;
    }
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
