//! Borrowed array elements. A loop over an array copies each element into
//! a register, which costs a count increment, and its release at the end
//! of the pass a decrement, both on the element's allocation. Where the
//! array register holds the array all the while (it is live wherever the
//! element's register is, and nothing writes it there), the array keeps
//! the element alive, so compiled code reads it without counting and
//! never releases it (`ArrayGetReg`'s `borrow`; the interpreter copies
//! as before). The register must only ever hold such elements: written
//! by nothing else but `Release`/`ClearRegs` (nil), never moved out
//! (`live::mark_moves` leaves it alone), never returned or raised, and
//! kept to itself by register sharing. Functions with handlers are left
//! as they are (an unwind enters them with every register owned).
//! Runs before `regshare` and `mark_moves`.

use rustc_hash::FxHashMap as HashMap;

use quarz_ir::*;

pub fn mark_borrows(functions: &mut [Function]) {
    for f in functions.iter_mut() {
        mark_in(f);
    }
}

fn mark_in(f: &mut Function) {
    // The element registers and the array each reads.
    let mut arrays: HashMap<Reg, Option<Reg>> = HashMap::default();
    for blk in &f.blocks {
        for inst in &blk.insts {
            if let Inst::ArrayGetReg { dst, arr, .. } = inst {
                let e = arrays.entry(*dst).or_insert(Some(*arr));
                if *e != Some(*arr) {
                    *e = None;
                }
            }
        }
    }
    if arrays.is_empty() || f.blocks.iter().any(|b| b.handler.is_some()) {
        return;
    }
    // What else writes or consumes them.
    for blk in &f.blocks {
        for inst in &blk.insts {
            let consumed = match inst {
                Inst::ArrayGetReg { .. } | Inst::Release { .. } | Inst::ClearRegs { .. } => {
                    Vec::new()
                }
                Inst::OwnedCall {
                    recv: VarLoc::Reg(r),
                    ..
                } => vec![*r],
                Inst::ArrayPush { arr, .. } => vec![*arr],
                Inst::Take { src, .. } => vec![*src],
                _ => Vec::new(),
            };
            let written = match inst {
                Inst::ArrayGetReg { .. } | Inst::Release { .. } | Inst::ClearRegs { .. } => {
                    Vec::new()
                }
                _ => inst.defs(),
            };
            for r in consumed.iter().chain(&written) {
                arrays.remove(r);
            }
        }
        if let Term::Return(r)
        | Term::Raise(r)
        | Term::BreakOut(r)
        | Term::ReturnOut(r)
        | Term::Resume(r) = blk.term
        {
            arrays.remove(&r);
        }
    }
    arrays.retain(|_, a| a.is_some());
    if arrays.is_empty() {
        return;
    }
    // The array holds the element wherever the element is read later.
    let live = live::liveness(f);
    for (blk, live) in f.blocks.iter().zip(&live) {
        for (ii, here) in live.iter().enumerate() {
            let inst = blk.insts.get(ii);
            arrays.retain(|&b, a| {
                let a = a.expect("an array");
                !here[b as usize]
                    || (here[a as usize] && inst.is_none_or(|i| {
                        !i.defs().contains(&a)
                            && !matches!(i, Inst::ArrayPush { arr, .. } if *arr == a)
                            && !matches!(i, Inst::OwnedCall { recv: VarLoc::Reg(r), .. } if *r == a)
                    }))
            });
        }
    }
    for blk in f.blocks.iter_mut() {
        for inst in blk.insts.iter_mut() {
            if let Inst::ArrayGetReg { dst, borrow, .. } = inst {
                if arrays.contains_key(dst) {
                    *borrow = true;
                }
            }
        }
    }
}
