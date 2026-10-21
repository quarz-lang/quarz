//! Register liveness over QIR, and the reads that are a register's
//! last: where its value can be moved out instead of copied (no count
//! increment now, no release later). Both compiled backends take their
//! moves from here. The interpreter does not look them up per
//! instruction: measured, the lookup and the extra argument cost it
//! more (4-11% on the benchmarks) than the count operations it saves;
//! it moves a function's result out when it returns.

use crate::{Block, BlockId, Function, Reg, Term};

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
