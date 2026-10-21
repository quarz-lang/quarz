//! Register liveness over QIR, and the reads that are a register's
//! last: where its value can be moved out instead of copied (no count
//! increment now, no release later), so that a collection passed on
//! stays uniquely referenced and is updated in place. Lowering writes
//! the moves into the code (`mark_moves`: `Take`, `Call::moved`) for
//! the interpreter, which cannot afford a lookup per instruction; the
//! compiled backends also use `last_reads` directly. A call's callee
//! takes the parameters out of an argument list the call owns (see
//! `Activation::args_owned` in the VM).

use crate::{Block, BlockId, Function, Inst, Reg, Term};

/// The blocks control can go to from `b` (its handler included: it can
/// be entered from any of its instructions).
pub fn successors(b: &Block) -> Vec<BlockId> {
    let mut v = match &b.term {
        Term::Jump(t) => vec![*t],
        Term::Branch { then, els, .. } => vec![*then, *els],
        _ => vec![],
    };
    if let Some(h) = b.handler {
        v.push(h.block);
    }
    v
}

/// Liveness: `result[b][i][r]` says whether register `r` may be read
/// before being written from instruction `i` of block `b` on (index
/// `insts.len()` stands for the terminator). A block's handler can be
/// entered from any of its instructions, so what the handler reads is
/// live throughout the block.
pub fn liveness(f: &Function) -> Vec<Vec<Vec<bool>>> {
    let nregs = f.nregs as usize;
    let nblocks = f.blocks.len();
    let mut live_in: Vec<Vec<bool>> = vec![vec![false; nregs]; nblocks];
    let uses_defs: Vec<Vec<(Vec<Reg>, Vec<Reg>)>> = f
        .blocks
        .iter()
        .map(|blk| blk.insts.iter().map(|i| (i.uses(), i.defs())).collect())
        .collect();
    let or_into = |live: &mut [bool], other: &[bool]| {
        for (l, v) in live.iter_mut().zip(other) {
            *l |= *v;
        }
    };
    // The live set at the end of a block, then stepping backwards.
    let walk = |bi: usize, live_in: &[Vec<bool>], visit: &mut dyn FnMut(&[bool])| {
        let blk = &f.blocks[bi];
        let mut live = vec![false; nregs];
        for s in successors(blk) {
            or_into(&mut live, &live_in[s as usize]);
        }
        if let Some(r) = blk.term.uses() {
            live[r as usize] = true;
        }
        let handler: Option<&Vec<bool>> = blk.handler.map(|h| &live_in[h.block as usize]);
        visit(&live);
        for (u, d) in uses_defs[bi].iter().rev() {
            for r in d {
                live[*r as usize] = false;
            }
            for r in u {
                live[*r as usize] = true;
            }
            if let Some(h) = handler {
                or_into(&mut live, h);
            }
            visit(&live);
        }
    };
    let mut changed = true;
    while changed {
        changed = false;
        for bi in (0..nblocks).rev() {
            let mut last = vec![false; nregs];
            walk(bi, &live_in, &mut |l| last.clone_from_slice(l));
            if last != live_in[bi] {
                live_in[bi] = last;
                changed = true;
            }
        }
    }
    (0..nblocks)
        .map(|bi| {
            let mut per_inst = Vec::with_capacity(f.blocks[bi].insts.len() + 1);
            walk(bi, &live_in, &mut |l| per_inst.push(l.to_vec()));
            per_inst.reverse();
            per_inst
        })
        .collect()
}

/// For each instruction (`result[b][i]`), the registers it reads for the
/// last time: it reads them once, and nothing reads them after it before
/// they are written again. Such a value can be moved out of its register.
pub fn last_reads_from(f: &Function, live: &[Vec<Vec<bool>>]) -> Vec<Vec<Vec<Reg>>> {
    f.blocks
        .iter()
        .enumerate()
        .map(|(bi, blk)| {
            blk.insts
                .iter()
                .enumerate()
                .map(|(ii, inst)| {
                    let uses = inst.uses();
                    let after = &live[bi][ii + 1];
                    let mut out: Vec<Reg> = uses
                        .iter()
                        .copied()
                        .filter(|r| {
                            !after[*r as usize] && uses.iter().filter(|u| *u == r).count() == 1
                        })
                        .collect();
                    out.sort_unstable();
                    out.dedup();
                    out
                })
                .collect()
        })
        .collect()
}

/// `last_reads_from` with its own liveness.
pub fn last_reads(f: &Function) -> Vec<Vec<Vec<Reg>>> {
    last_reads_from(f, &liveness(f))
}

/// The natives that update a uniquely referenced receiver in place
/// (`OwnedCall`'s fast paths in the interpreter and the compiled code).
pub const IN_PLACE_NATIVES: [&str; 6] = [
    "Array#push",
    "Array#set",
    "Hash#put",
    "Hash#delete",
    "Set#add",
    "Set#delete",
];

/// A call to one of the `IN_PLACE_NATIVES` that reads its receiver
/// register for the last time becomes an `OwnedCall` on it: the
/// collection moves into the call and is updated in place (`xs.push(v)`
/// as a method's result, say). The register is written back, but it is
/// dead. Run after `mark_moves`.
pub fn own_dying_receivers(f: &mut Function, in_place: &[bool]) {
    for blk in f.blocks.iter_mut() {
        for inst in blk.insts.iter_mut() {
            let Inst::Call {
                dst,
                kind: crate::CallKind::Method(mid),
                recv: Some(r),
                args,
                splat: false,
                kw,
                kw_splat: None,
                block: None,
                moved,
            } = inst
            else {
                continue;
            };
            if *moved & (1 << 15) == 0 || !in_place.get(*mid as usize).copied().unwrap_or(false) {
                continue;
            }
            *inst = Inst::OwnedCall {
                dst: *dst,
                method: *mid,
                recv: crate::VarLoc::Reg(*r),
                args: std::mem::take(args),
                kw: std::mem::take(kw),
            };
        }
    }
}

/// Write the moves into the function, for the interpreter and the
/// compiled backends alike: a `Move` that is its source's last read
/// becomes a `Take`, and a call records which of its receiver and
/// arguments it reads for the last time (`Inst::Call::moved`). Run once,
/// after the optimizations that move instructions around.
///
/// The same answer as `last_reads`, computed with bit sets per block
/// rather than a set per instruction: this runs on every function of
/// every program, the prelude's included, at each start.
pub fn mark_moves(f: &mut Function) {
    let nblocks = f.blocks.len();
    let words = (f.nregs as usize).div_ceil(64);
    let set = |s: &mut [u64], r: Reg| s[r as usize / 64] |= 1 << (r % 64);
    let unset = |s: &mut [u64], r: Reg| s[r as usize / 64] &= !(1 << (r % 64));
    let has = |s: &[u64], r: Reg| s[r as usize / 64] & (1 << (r % 64)) != 0;
    // Per block: the registers read before any write (`up`) and those
    // written (`kill`); then the live sets at entry to a fixed point:
    // in = up | (out & !kill) | handler's in (the handler can be entered
    // from any instruction).
    let mut up = vec![vec![0u64; words]; nblocks];
    let mut kill = vec![vec![0u64; words]; nblocks];
    // Each instruction's reads and writes, kept for the second walk.
    let ud: Vec<Vec<(Vec<Reg>, Vec<Reg>)>> = f
        .blocks
        .iter()
        .map(|blk| blk.insts.iter().map(|i| (i.uses(), i.defs())).collect())
        .collect();
    for (bi, blk) in f.blocks.iter().enumerate() {
        if let Some(r) = blk.term.uses() {
            set(&mut up[bi], r);
        }
        for (uses, defs) in ud[bi].iter().rev() {
            for r in defs {
                unset(&mut up[bi], *r);
                set(&mut kill[bi], *r);
            }
            for r in uses {
                set(&mut up[bi], *r);
            }
        }
    }
    let succ: Vec<Vec<BlockId>> = f.blocks.iter().map(successors).collect();
    let mut live_in = vec![vec![0u64; words]; nblocks];
    let out_of = |bi: usize, live_in: &[Vec<u64>]| {
        let mut out = vec![0u64; words];
        for s in &succ[bi] {
            for (o, v) in out.iter_mut().zip(&live_in[*s as usize]) {
                *o |= v;
            }
        }
        out
    };
    let mut changed = true;
    while changed {
        changed = false;
        for bi in (0..nblocks).rev() {
            let out = out_of(bi, &live_in);
            let blk = &f.blocks[bi];
            let mut new: Vec<u64> = (0..words)
                .map(|w| up[bi][w] | (out[w] & !kill[bi][w]))
                .collect();
            if let (Some(h), false) = (blk.handler, blk.insts.is_empty()) {
                for (n, v) in new.iter_mut().zip(&live_in[h.block as usize]) {
                    *n |= v;
                }
            }
            if new != live_in[bi] {
                live_in[bi] = new;
                changed = true;
            }
        }
    }
    // Each block backwards from its end: `live` is what is read after
    // the instruction at hand.
    for (bi, (blk, ud)) in f.blocks.iter_mut().zip(&ud).enumerate() {
        let mut live = out_of(bi, &live_in);
        let handler = blk.handler.map(|h| live_in[h.block as usize].clone());
        if let Some(r) = blk.term.uses() {
            set(&mut live, r);
        }
        for (inst, (uses, defs)) in blk.insts.iter_mut().zip(ud).rev() {
            let dying = |r: Reg| !has(&live, r) && uses.iter().filter(|u| **u == r).count() == 1;
            match inst {
                Inst::Move { dst, src } if dst != src && dying(*src) => {
                    *inst = Inst::Take {
                        dst: *dst,
                        src: *src,
                    };
                }
                Inst::Call {
                    recv,
                    args,
                    splat: false,
                    moved,
                    ..
                } => {
                    let mut bits = 0u16;
                    for (i, a) in args.iter().enumerate().take(15) {
                        if dying(*a) {
                            bits |= 1 << i;
                        }
                    }
                    if recv.is_some_and(dying) {
                        bits |= 1 << 15;
                    }
                    *moved = bits;
                }
                _ => {}
            }
            for r in defs {
                unset(&mut live, *r);
            }
            for r in uses {
                set(&mut live, *r);
            }
            if let Some(h) = &handler {
                for (l, v) in live.iter_mut().zip(h) {
                    *l |= v;
                }
            }
        }
    }
}
