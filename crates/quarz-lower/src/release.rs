//! Releases nothing can tell from an earlier one. A variable whose
//! release may be observed lives to the end of its scope (`Inst::Release`)
//! instead of moving out at its last use; but when nothing between that
//! use and the end could run code or look at the value (number
//! arithmetic, copies of other registers), releasing it there instead is
//! the same to the program, and moving it into the call that last uses
//! it saves a count update (Swift's "deinit barriers"). Such a `Release`
//! is dropped, and `live::mark_moves` then moves the value at its last
//! use. Runs before `mark_moves`.

use rustc_hash::FxHashSet as HashSet;

use quarz_ir::*;

/// Drop the `Release`s of every function that nothing can tell from a
/// move at the last use.
pub fn drop_unobserved(functions: &mut [Function], methods: &[RtMethod], builtin: &RtBuiltin) {
    for f in functions.iter_mut() {
        drop_in(f, methods, builtin);
    }
}

/// Whether `inst` can neither run code nor look at a register other than
/// its operands (between a last use and a `Release`, it lets the release
/// move up).
fn transparent(inst: &Inst, methods: &[RtMethod], builtin: &RtBuiltin) -> bool {
    match inst {
        Inst::LoadConst { .. }
        | Inst::Move { .. }
        | Inst::Take { .. }
        | Inst::IsNil { .. }
        | Inst::Not { .. }
        | Inst::ClassIs { .. }
        | Inst::ClassIsA { .. }
        | Inst::Len { .. }
        | Inst::ClearRegs { .. } => true,
        // Arithmetic and comparisons the runtime does itself.
        Inst::BinOp {
            method: Some(m), ..
        } => methods
            .get(*m as usize)
            .is_some_and(|m| m.owner == builtin.int || m.owner == builtin.float),
        _ => false,
    }
}

/// Whether `inst` reads `r` where it can move it into a call (its
/// receiver or an argument), which releases it before it returns, unless
/// it keeps it. (A copy would only move it into another register, which
/// may hold it longer.)
fn moves_out(inst: &Inst, r: Reg) -> bool {
    // (Read twice, it is not moved.)
    if inst.uses().iter().filter(|u| **u == r).count() != 1 {
        return false;
    }
    match inst {
        Inst::Call {
            recv,
            args,
            splat: false,
            ..
        } => *recv == Some(r) || args.iter().take(15).any(|a| *a == r),
        _ => false,
    }
}

/// An instruction: block and index.
type Site = (usize, usize);

fn drop_in(f: &mut Function, methods: &[RtMethod], builtin: &RtBuiltin) {
    let has_release = f
        .blocks
        .iter()
        .any(|b| b.insts.iter().any(|i| matches!(i, Inst::Release { .. })));
    if !has_release {
        return;
    }
    let mut preds: Vec<Vec<BlockId>> = vec![Vec::new(); f.blocks.len()];
    for (bi, b) in f.blocks.iter().enumerate() {
        for s in live::successors(b) {
            preds[s as usize].push(bi as BlockId);
        }
    }
    let mut gone: HashSet<Site> = HashSet::default();
    for (bi, b) in f.blocks.iter().enumerate() {
        for (ii, inst) in b.insts.iter().enumerate() {
            let Inst::Release { src: r } = *inst else {
                continue;
            };
            // Walk back over what cannot tell, within the block and then
            // into a lone predecessor that jumps here: control goes from
            // the use straight to the `Release`, so the register is dead
            // after the use once the `Release` is gone. (A handler could be
            // entered on the way and read it: not through one.)
            let (mut cb, mut ci) = (bi, ii);
            let mut steps = 0;
            let found = loop {
                if f.blocks[cb].handler.is_some() {
                    break false;
                }
                if ci == 0 {
                    let p = &preds[cb];
                    steps += 1;
                    if steps > f.blocks.len()
                        || p.len() != 1
                        || f.blocks[p[0] as usize].term != Term::Jump(cb as BlockId)
                    {
                        break false;
                    }
                    cb = p[0] as usize;
                    ci = f.blocks[cb].insts.len();
                    continue;
                }
                ci -= 1;
                let at = &f.blocks[cb].insts[ci];
                if at.uses().contains(&r) {
                    break moves_out(at, r);
                }
                if at.defs().contains(&r) || !transparent(at, methods, builtin) {
                    break false;
                }
            };
            if found {
                gone.insert((bi, ii));
            }
        }
    }
    if gone.is_empty() {
        return;
    }
    for (bi, blk) in f.blocks.iter_mut().enumerate() {
        if !(0..blk.insts.len()).any(|ii| gone.contains(&(bi, ii))) {
            continue;
        }
        let insts = std::mem::take(&mut blk.insts);
        let lines = std::mem::take(&mut blk.lines);
        for (ii, (inst, line)) in insts.into_iter().zip(lines).enumerate() {
            if !gone.contains(&(bi, ii)) {
                blk.insts.push(inst);
                blk.lines.push(line);
            }
        }
    }
}
