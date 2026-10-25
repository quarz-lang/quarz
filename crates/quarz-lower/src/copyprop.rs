//! Copy propagation: a `Move { dst, src }` whose destination is only
//! ever read while both registers still hold what the move copied is
//! removed, the reads going to the source instead. Every copy of a heap
//! value costs a reference-count increment and, later, a decrement with
//! their tag tests; inlining and parameter binding produce many such
//! copies (`Move 37 <- 20; FieldGet 38 = 37.@pos`).
//!
//! Registers are mutable, so the pass works on reaching definitions
//! (shared with the scalar replacement): a read of `dst` is redirected
//! only when the move is the one definition reaching it and `src` has
//! the same definitions there as at the move. A read that updates the
//! register in place (`xs = xs.push(v)`, an `ArrayPush`) keeps its
//! copy: the source must not see the change. A `Release` of the copy
//! (the end of an inlined `self`'s scope, say) goes with it: the source
//! still holds the value, so no deinitializer can run there.

use rustc_hash::FxHashSet as HashSet;

use quarz_ir::*;

use crate::sroa::{defs_at, reaching, Holds, Site};

pub fn propagate_copies(functions: &mut [Function]) {
    for f in functions.iter_mut() {
        // Moves chain (`Move 45 <- 41; Move 46 <- 45`); each round
        // shortens the chains by one. A later round looks only at the
        // copies of registers the previous one changed: for the others,
        // the writes and reads it judges by are as they were.
        let mut changed = None;
        for _ in 0..6 {
            match propagate_in(f, changed.as_ref()) {
                Some(regs) => changed = Some(regs),
                None => break,
            }
        }
    }
}

/// Whether reading register `r` in `inst` consumes or changes it.
fn consumes(inst: &Inst, r: Reg) -> bool {
    match inst {
        Inst::OwnedCall {
            recv: VarLoc::Reg(q),
            ..
        } => *q == r,
        Inst::ArrayPush { arr, .. } => *arr == r,
        // It releases what it reads: redirected, it releases the copy's
        // source (see `propagate_in`).
        Inst::Release { src } => *src == r,
        _ => false,
    }
}

/// One round, over the copies of registers in `only` (all at first).
/// The registers whose writes or reads it changed (the copies removed
/// and their sources), or `None` when it changed nothing.
fn propagate_in(f: &mut Function, only: Option<&HashSet<Reg>>) -> Option<HashSet<Reg>> {
    let moves: Vec<(Site, Reg, Reg)> = f
        .blocks
        .iter()
        .enumerate()
        .flat_map(|(bi, blk)| {
            blk.insts
                .iter()
                .enumerate()
                .filter_map(move |(ii, inst)| match inst {
                    Inst::Move { dst, src } if dst != src => Some(((bi, ii), *dst, *src)),
                    _ => None,
                })
        })
        .filter(|(_, dst, src)| only.is_none_or(|o| o.contains(dst) || o.contains(src)))
        .collect();
    if moves.is_empty() {
        return None;
    }
    let reach = reaching(f);
    let (uses, term_uses) = (&reach.uses, &reach.term_uses);
    let mut delete: HashSet<Site> = HashSet::default();
    // (site, dst, src): redirect the reads of `dst` at `site` to `src`.
    let mut redirect: Vec<(Site, Reg, Reg)> = Vec::new();
    let mut term_redirect: Vec<(usize, Reg, Reg)> = Vec::new();
    // The copies removed this round and their sources: a chain's later
    // links wait for the next round, so the reaching definitions stay
    // valid (removing a copy changes its destination's definitions, which
    // a copy from it relied on). Copies of one source go together: the
    // reads redirected to it leave its definitions as they were.
    let mut removed: HashSet<Reg> = HashSet::default();
    let mut sources: HashSet<Reg> = HashSet::default();
    for (site, dst, src) in moves {
        if removed.contains(&dst) || sources.contains(&dst) || removed.contains(&src) {
            continue;
        }
        let src_defs = defs_at(&reach, site.0, site.1, src);
        let mut holds = Holds::new(&reach, site, &[dst, src]);
        let mut ok = true;
        let mut reads: Vec<Site> = Vec::new();
        let mut term_reads: Vec<usize> = Vec::new();
        let mut drops: Vec<Site> = Vec::new();
        // A read in a handler (entered from anywhere in its region) may
        // see the copy: it stays.
        if reach.read_unknown(f, dst) {
            continue;
        }
        let (dst_reads, dst_terms) = reach.reads_of(f, site, dst);
        for (ubi, uii) in dst_reads {
            let here = defs_at(&reach, ubi, uii, dst);
            let inst = &f.blocks[ubi].insts[uii];
            // A `Release` of the copy may release the source instead when
            // the copy is all that reads the source (the variable a loop
            // element goes into, say).
            let is_release = matches!(inst, Inst::Release { .. });
            let releases_only_src =
                is_release && uses[src as usize].len() == 1 && term_uses[src as usize].is_empty();
            if here.len() != 1
                || (consumes(inst, dst) && !is_release)
                || defs_at(&reach, ubi, uii, src) != src_defs
            {
                ok = false;
                break;
            }
            if !holds.at(ubi, uii) {
                ok = false;
                break;
            }
            if is_release && !releases_only_src {
                // Otherwise the source still holds the value: releasing the
                // copy only lowers its count, which nothing can tell; it
                // goes with the copy.
                drops.push((ubi, uii));
            } else {
                reads.push((ubi, uii));
            }
        }
        if ok {
            for bi in dst_terms {
                let n = f.blocks[bi].insts.len();
                let here = defs_at(&reach, bi, n, dst);
                if here.len() != 1 || defs_at(&reach, bi, n, src) != src_defs {
                    ok = false;
                    break;
                }
                if !holds.at(bi, n) {
                    ok = false;
                    break;
                }
                term_reads.push(bi);
            }
        }
        if !ok {
            continue;
        }
        removed.insert(dst);
        sources.insert(src);
        delete.insert(site);
        delete.extend(drops);
        redirect.extend(reads.into_iter().map(|s| (s, dst, src)));
        term_redirect.extend(term_reads.into_iter().map(|b| (b, dst, src)));
    }
    if delete.is_empty() {
        return None;
    }
    for ((bi, ii), dst, src) in redirect {
        f.blocks[bi].insts[ii].map_uses(&mut |r| if r == dst { src } else { r });
    }
    for (bi, dst, src) in term_redirect {
        f.blocks[bi]
            .term
            .map_uses(&mut |r| if r == dst { src } else { r });
    }
    for (bi, blk) in f.blocks.iter_mut().enumerate() {
        let insts = std::mem::take(&mut blk.insts);
        let lines = std::mem::take(&mut blk.lines);
        for (ii, (inst, line)) in insts.into_iter().zip(lines).enumerate() {
            if delete.contains(&(bi, ii)) {
                continue;
            }
            blk.insts.push(inst);
            blk.lines.push(line);
        }
    }
    removed.extend(sources);
    Some(removed)
}
