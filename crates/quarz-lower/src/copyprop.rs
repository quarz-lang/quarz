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
//! copy: the source must not see the change.

use rustc_hash::FxHashSet as HashSet;

use quarz_ir::*;

use crate::sroa::{defs_at, reaching, Site, UNKNOWN};

pub fn propagate_copies(functions: &mut [Function]) {
    for f in functions.iter_mut() {
        // Moves chain (`Move 45 <- 41; Move 46 <- 45`); each round
        // shortens the chains by one.
        for _ in 0..6 {
            if !propagate_in(f) {
                break;
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

fn propagate_in(f: &mut Function) -> bool {
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
        .collect();
    if moves.is_empty() {
        return false;
    }
    let reach = reaching(f);
    // Where every register is read.
    let mut uses: Vec<Vec<Site>> = vec![Vec::new(); f.nregs as usize];
    let mut term_uses: Vec<Vec<usize>> = vec![Vec::new(); f.nregs as usize];
    for (bi, blk) in f.blocks.iter().enumerate() {
        for (ii, inst) in blk.insts.iter().enumerate() {
            for r in inst.uses() {
                uses[r as usize].push((bi, ii));
            }
        }
        if let Some(r) = blk.term.uses() {
            term_uses[r as usize].push(bi);
        }
    }
    let mut delete: HashSet<Site> = HashSet::default();
    // (site, dst, src): redirect the reads of `dst` at `site` to `src`.
    let mut redirect: Vec<(Site, Reg, Reg)> = Vec::new();
    let mut term_redirect: Vec<(usize, Reg, Reg)> = Vec::new();
    // Registers already rewritten this round: a chain's later links wait
    // for the next round, so the reaching definitions stay valid.
    let mut touched: HashSet<Reg> = HashSet::default();
    for (site, dst, src) in moves {
        if touched.contains(&dst) || touched.contains(&src) {
            continue;
        }
        let src_defs = defs_at(&reach, f, site.0, site.1, src);
        let mut ok = true;
        let mut reads: Vec<Site> = Vec::new();
        let mut term_reads: Vec<usize> = Vec::new();
        for &(ubi, uii) in &uses[dst as usize] {
            let here = defs_at(&reach, f, ubi, uii, dst);
            // A read in a handler (entered from anywhere in its region)
            // may see the copy: it stays.
            if here.contains(&UNKNOWN) {
                ok = false;
                break;
            }
            if !here.contains(&site) {
                continue;
            }
            let inst = &f.blocks[ubi].insts[uii];
            // A `Release` of the copy may release the source instead when
            // the copy is all that reads the source (the variable a loop
            // element goes into, say).
            let releases_only_src = matches!(inst, Inst::Release { .. })
                && uses[src as usize].len() == 1
                && term_uses[src as usize].is_empty();
            if here.len() != 1
                || (consumes(inst, dst) && !releases_only_src)
                || defs_at(&reach, f, ubi, uii, src) != src_defs
            {
                ok = false;
                break;
            }
            reads.push((ubi, uii));
        }
        if ok {
            for &bi in &term_uses[dst as usize] {
                let n = f.blocks[bi].insts.len();
                let here = defs_at(&reach, f, bi, n, dst);
                if here.contains(&UNKNOWN) {
                    ok = false;
                    break;
                }
                if !here.contains(&site) {
                    continue;
                }
                if here.len() != 1 || defs_at(&reach, f, bi, n, src) != src_defs {
                    ok = false;
                    break;
                }
                term_reads.push(bi);
            }
        }
        if !ok {
            continue;
        }
        touched.insert(dst);
        touched.insert(src);
        delete.insert(site);
        redirect.extend(reads.into_iter().map(|s| (s, dst, src)));
        term_redirect.extend(term_reads.into_iter().map(|b| (b, dst, src)));
    }
    if delete.is_empty() {
        return false;
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
    true
}
