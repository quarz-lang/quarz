//! Register sharing: registers whose values are never live at the same
//! time get one number. Lowering gives every variable and temporary its
//! own register, and inlining adds the callee's on top, so a method can
//! end up with a hundred registers of which a dozen are live at once.
//! The interpreter fills and empties every register on each call, and
//! the compiled code gives each a home, so fewer is cheaper on both.
//!
//! Two registers interfere when one is written while the other is live
//! (a handler's live set counts throughout its region), and an
//! instruction's result never shares with its own operands. A move's source
//! does not interfere with its destination: when they end up sharing,
//! the move is dropped. Registers are numbered greedily in order of
//! appearance, preferring a number a move partner already has, and only
//! among registers of one kind: those that may hold a counted value and
//! those that never do (`live::heap_possible`).
//! A `ClearRegs` keeps the registers read after it and those that may
//! hold a counted value (dead numbers need no clearing), renumbered and
//! split into the runs the new numbers form.

use quarz_ir::live::successors;
use quarz_ir::*;

use crate::inline::rewrite_with;

/// Which registers may share.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Sharing {
    /// Any two that do not interfere, of the same kind. What the
    /// interpreter, which fills and empties every register per call,
    /// gains most from; LLVM too.
    All,
    /// Only those that never hold a counted value. Cranelift's code is
    /// slower when counted values share homes (dispatch +12%, objects +8%
    /// measured) and no faster when numbers do not.
    Numbers,
}

pub fn share_registers(functions: &mut [Function], methods: &[RtMethod], sharing: Sharing) {
    for f in functions.iter_mut() {
        share_in(f, methods, sharing);
    }
}

/// A set of registers, one bit each.
#[derive(Clone)]
struct Bits(Vec<u64>);

impl Bits {
    fn new(n: usize) -> Bits {
        Bits(vec![0; n.div_ceil(64)])
    }
    fn set(&mut self, r: Reg) {
        self.0[r as usize / 64] |= 1 << (r % 64);
    }
    fn unset(&mut self, r: Reg) {
        self.0[r as usize / 64] &= !(1 << (r % 64));
    }
    fn has(&self, r: Reg) -> bool {
        self.0[r as usize / 64] & (1 << (r % 64)) != 0
    }
    fn or(&mut self, other: &Bits) {
        for (a, b) in self.0.iter_mut().zip(&other.0) {
            *a |= b;
        }
    }
    fn meets(&self, other: &Bits) -> bool {
        self.0.iter().zip(&other.0).any(|(a, b)| a & b != 0)
    }
    fn iter(&self) -> impl Iterator<Item = Reg> + '_ {
        self.0.iter().enumerate().flat_map(|(w, word)| {
            (0..64)
                .filter(move |b| word & (1 << b) != 0)
                .map(move |b| (w * 64 + b) as Reg)
        })
    }
}

fn share_in(f: &mut Function, methods: &[RtMethod], sharing: Sharing) {
    let n = f.nregs as usize;
    if n <= 1 {
        return;
    }
    // Registers that may hold a counted value share only among
    // themselves: compiled code releases by register (a number's
    // register sharing with a call result's would be released too).
    let heap = quarz_ir::live::heap_possible(f, methods);
    let nblocks = f.blocks.len();
    let ud: Vec<Vec<(Vec<Reg>, Vec<Reg>)>> = f
        .blocks
        .iter()
        .map(|b| b.insts.iter().map(|i| (i.uses(), i.defs())).collect())
        .collect();
    // Liveness at block entry (as in `live::mark_moves`).
    let mut up = vec![Bits::new(n); nblocks];
    let mut kill = vec![Bits::new(n); nblocks];
    for (bi, blk) in f.blocks.iter().enumerate() {
        if let Some(r) = blk.term.uses() {
            up[bi].set(r);
        }
        for (uses, defs) in ud[bi].iter().rev() {
            for r in defs {
                up[bi].unset(*r);
                kill[bi].set(*r);
            }
            for r in uses {
                up[bi].set(*r);
            }
        }
    }
    let succ: Vec<Vec<BlockId>> = f.blocks.iter().map(successors).collect();
    let mut live_in = vec![Bits::new(n); nblocks];
    let out_of = |bi: usize, live_in: &[Bits]| {
        let mut out = Bits::new(n);
        for s in &succ[bi] {
            out.or(&live_in[*s as usize]);
        }
        out
    };
    let mut changed = true;
    while changed {
        changed = false;
        for bi in (0..nblocks).rev() {
            let out = out_of(bi, &live_in);
            let mut new = Bits::new(n);
            for w in 0..new.0.len() {
                new.0[w] = up[bi].0[w] | (out.0[w] & !kill[bi].0[w]);
            }
            if let (Some(h), false) = (f.blocks[bi].handler, f.blocks[bi].insts.is_empty()) {
                new.or(&live_in[h.block as usize]);
            }
            if new.0 != live_in[bi].0 {
                live_in[bi] = new;
                changed = true;
            }
        }
    }
    // Interference: a write against what is live after it.
    let mut interf = vec![Bits::new(n); n];
    let mut edge = |a: Reg, b: Reg| {
        if a != b {
            interf[a as usize].set(b);
            interf[b as usize].set(a);
        }
    };
    // Move partners, for the preference.
    let mut partners: Vec<Vec<Reg>> = vec![Vec::new(); n];
    // What each `ClearRegs` must still clear: the registers read after
    // it (as nil), and those that may hold a counted value, whose release
    // is the point (a stale reference left in a dead register would keep
    // a collection shared, and copied on its next update). A dead number
    // needs nothing.
    let mut cleared: Vec<Vec<Vec<Reg>>> = f
        .blocks
        .iter()
        .map(|b| vec![Vec::new(); b.insts.len()])
        .collect();
    for (bi, blk) in f.blocks.iter().enumerate() {
        let mut live = out_of(bi, &live_in);
        if let Some(r) = blk.term.uses() {
            live.set(r);
        }
        let handler = blk.handler.map(|h| live_in[h.block as usize].clone());
        for (ii, (inst, (uses, defs))) in blk.insts.iter().zip(&ud[bi]).enumerate().rev() {
            if let Inst::ClearRegs { .. } = inst {
                let keep: Vec<Reg> = defs
                    .iter()
                    .copied()
                    .filter(|r| live.has(*r) || heap[*r as usize])
                    .collect();
                for d in &keep {
                    for l in live.iter() {
                        edge(*d, l);
                    }
                }
                for r in defs {
                    live.unset(*r);
                }
                if let Some(h) = &handler {
                    live.or(h);
                }
                cleared[bi][ii] = keep;
                continue;
            }
            let copy_src = match inst {
                Inst::Move { dst, src } | Inst::Take { dst, src } => {
                    partners[*dst as usize].push(*src);
                    partners[*src as usize].push(*dst);
                    Some(*src)
                }
                _ => None,
            };
            for d in defs {
                for l in live.iter() {
                    if Some(l) != copy_src {
                        edge(*d, l);
                    }
                }
            }
            // An instruction's own results are distinct, and distinct
            // from what it reads even when that dies there: the compiled
            // code may release a result register before reading the
            // operands (a move, which then disappears, excepted).
            for (i, a) in defs.iter().enumerate() {
                for b in &defs[i + 1..] {
                    edge(*a, *b);
                }
                if copy_src.is_none() {
                    for u in uses {
                        edge(*a, *u);
                    }
                }
            }
            for r in defs {
                live.unset(*r);
            }
            for r in uses {
                live.set(*r);
            }
            if let Some(h) = &handler {
                live.or(h);
            }
        }
    }
    // Order of appearance: the first definition or use.
    let mut order: Vec<Reg> = Vec::with_capacity(n);
    let mut seen = Bits::new(n);
    let mut note = |r: Reg, order: &mut Vec<Reg>| {
        if !seen.has(r) {
            seen.set(r);
            order.push(r);
        }
    };
    for (bi, blk) in f.blocks.iter().enumerate() {
        for (uses, defs) in &ud[bi] {
            for r in uses.iter().chain(defs) {
                note(*r, &mut order);
            }
        }
        if let Some(r) = blk.term.uses() {
            note(r, &mut order);
        }
    }
    // Registers never mentioned keep nothing; give them the first number.
    let mut color: Vec<Option<Reg>> = vec![None; n];
    let mut members: Vec<Bits> = Vec::new();
    let mut heap_color: Vec<bool> = Vec::new();
    for r in order {
        let fits = |c: usize, members: &[Bits]| {
            heap_color[c] == heap[r as usize]
                && !(sharing == Sharing::Numbers && heap[r as usize])
                && !interf[r as usize].meets(&members[c])
        };
        let preferred = partners[r as usize]
            .iter()
            .filter_map(|p| color[*p as usize])
            .find(|c| fits(*c as usize, &members));
        let c = preferred.or_else(|| {
            (0..members.len())
                .find(|c| fits(*c, &members))
                .map(|c| c as Reg)
        });
        let c = match c {
            Some(c) => c,
            None => {
                members.push(Bits::new(n));
                heap_color.push(heap[r as usize]);
                (members.len() - 1) as Reg
            }
        };
        members[c as usize].set(r);
        color[r as usize] = Some(c);
    }
    let new_n = members.len().max(1) as u32;
    if new_n >= f.nregs {
        return;
    }
    let map = |r: Reg| color[r as usize].unwrap_or(0);
    for (bi, blk) in f.blocks.iter_mut().enumerate() {
        let insts = std::mem::take(&mut blk.insts);
        let lines = std::mem::take(&mut blk.lines);
        for (ii, (inst, line)) in insts.into_iter().zip(lines).enumerate() {
            match &inst {
                Inst::ClearRegs { .. } => {
                    // The new numbers of what is still cleared, as runs.
                    let mut regs: Vec<Reg> = cleared[bi][ii].iter().map(|r| map(*r)).collect();
                    regs.sort_unstable();
                    regs.dedup();
                    let mut i = 0;
                    while i < regs.len() {
                        let start = regs[i];
                        let mut end = start + 1;
                        while i + 1 < regs.len() && regs[i + 1] == end {
                            i += 1;
                            end += 1;
                        }
                        blk.insts.push(Inst::ClearRegs {
                            from: start,
                            to: end,
                        });
                        blk.lines.push(line);
                        i += 1;
                    }
                }
                _ => {
                    let new = rewrite_with(&inst, &map, &|c| c);
                    // A move between registers that now share is gone.
                    if let Inst::Move { dst, src } | Inst::Take { dst, src } = &new {
                        if dst == src {
                            continue;
                        }
                    }
                    blk.insts.push(new);
                    blk.lines.push(line);
                }
            }
        }
        blk.term.map_uses(&mut |r| map(r));
    }
    f.nregs = new_n;
}
