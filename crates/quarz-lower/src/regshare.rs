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

pub fn share_registers(functions: &mut [Function], methods: &[RtMethod]) {
    for f in functions.iter_mut() {
        share_in(f, methods);
    }
}

/// A set of registers: a list to go through and a flag per register,
/// so that adding, removing and testing are constant time and going
/// through it costs what it holds, not the number of registers.
struct Live {
    list: Vec<Reg>,
    pos: Vec<u32>,
}

const ABSENT: u32 = u32::MAX;

impl Live {
    fn new(n: usize) -> Live {
        Live {
            list: Vec::new(),
            pos: vec![ABSENT; n],
        }
    }
    fn set(&mut self, r: Reg) {
        if self.pos[r as usize] == ABSENT {
            self.pos[r as usize] = self.list.len() as u32;
            self.list.push(r);
        }
    }
    fn unset(&mut self, r: Reg) {
        let at = self.pos[r as usize];
        if at != ABSENT {
            self.list.swap_remove(at as usize);
            if let Some(moved) = self.list.get(at as usize) {
                self.pos[*moved as usize] = at;
            }
            self.pos[r as usize] = ABSENT;
        }
    }
    fn has(&self, r: Reg) -> bool {
        self.pos[r as usize] != ABSENT
    }
    fn clear(&mut self) {
        for r in self.list.drain(..) {
            self.pos[r as usize] = ABSENT;
        }
    }
    fn extend(&mut self, regs: &[Reg]) {
        for r in regs {
            self.set(*r);
        }
    }
}

fn share_in(f: &mut Function, methods: &[RtMethod]) {
    let n = f.nregs as usize;
    if n <= 1 {
        return;
    }
    // Registers that may hold a counted value share only among
    // themselves: compiled code releases by register (a number's
    // register sharing with a call result's would be released too).
    let heap = quarz_ir::live::heap_possible(f, methods);
    // A borrowed element's register is its own (compiled code never
    // releases it: a number sharing it would hold another value).
    let borrowed = quarz_ir::live::borrowed_regs(f);
    let kind = |r: Reg| -> usize {
        if borrowed[r as usize] {
            2 + r as usize
        } else {
            usize::from(heap[r as usize])
        }
    };
    let nblocks = f.blocks.len();
    let ud: Vec<Vec<(Regs, Regs)>> = f
        .blocks
        .iter()
        .map(|b| b.insts.iter().map(|i| (i.uses(), i.defs())).collect())
        .collect();
    // Liveness at block entry (as in `live::mark_moves`), register by
    // register: from the blocks that read it before writing it, back
    // through the predecessors that do not write it. A block's handler
    // may be entered from any of its instructions: what is live entering
    // the handler is live entering the block (one with instructions).
    // Each block's list holds only what is live there, where a set of
    // every register per block would grow as blocks times registers.
    let succ: Vec<Vec<BlockId>> = f.blocks.iter().map(successors).collect();
    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); nblocks];
    let mut protected: Vec<Vec<usize>> = vec![Vec::new(); nblocks];
    for (bi, blk) in f.blocks.iter().enumerate() {
        for s in &succ[bi] {
            preds[*s as usize].push(bi);
        }
        if let (Some(h), false) = (blk.handler, blk.insts.is_empty()) {
            protected[h.block as usize].push(bi);
        }
    }
    // By register: the blocks reading it before any write there, and
    // those writing it.
    let mut ups: Vec<Vec<usize>> = vec![Vec::new(); n];
    let mut kills: Vec<Vec<usize>> = vec![Vec::new(); n];
    {
        let mut up = Live::new(n);
        let mut kill = Live::new(n);
        for (bi, blk) in f.blocks.iter().enumerate() {
            if let Some(r) = blk.term.uses() {
                up.set(r);
            }
            for (uses, defs) in ud[bi].iter().rev() {
                for r in defs {
                    up.unset(*r);
                    kill.set(*r);
                }
                up.extend(uses);
            }
            for r in &up.list {
                ups[*r as usize].push(bi);
            }
            for r in &kill.list {
                kills[*r as usize].push(bi);
            }
            up.clear();
            kill.clear();
        }
    }
    let mut live_in: Vec<Vec<Reg>> = vec![Vec::new(); nblocks];
    {
        // `marked[b] == r + 1`: `r` is live entering `b`.
        let mut marked: Vec<u32> = vec![0; nblocks];
        let mut work: Vec<usize> = Vec::new();
        for r in 0..n {
            let stamp = r as u32 + 1;
            for &b in &ups[r] {
                if marked[b] != stamp {
                    marked[b] = stamp;
                    work.push(b);
                }
            }
            while let Some(b) = work.pop() {
                live_in[b].push(r as Reg);
                for &p in &preds[b] {
                    if marked[p] != stamp && kills[r].binary_search(&p).is_err() {
                        marked[p] = stamp;
                        work.push(p);
                    }
                }
                for &p in &protected[b] {
                    if marked[p] != stamp {
                        marked[p] = stamp;
                        work.push(p);
                    }
                }
            }
        }
    }
    // Interference: a write against what is live after it. Each
    // register's list, sorted and without duplicates at the end.
    let mut interf: Vec<Vec<Reg>> = vec![Vec::new(); n];
    let mut edge = |a: Reg, b: Reg| {
        if a != b {
            interf[a as usize].push(b);
            interf[b as usize].push(a);
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
    let mut live = Live::new(n);
    for (bi, blk) in f.blocks.iter().enumerate() {
        live.clear();
        for s in &succ[bi] {
            live.extend(&live_in[*s as usize]);
        }
        if let Some(r) = blk.term.uses() {
            live.set(r);
        }
        let handler = blk.handler.map(|h| &live_in[h.block as usize]);
        for (ii, (inst, (uses, defs))) in blk.insts.iter().zip(&ud[bi]).enumerate().rev() {
            if let Inst::ClearRegs { .. } = inst {
                let keep: Vec<Reg> = defs
                    .iter()
                    .copied()
                    .filter(|r| live.has(*r) || heap[*r as usize])
                    .collect();
                for d in &keep {
                    for &l in &live.list {
                        edge(*d, l);
                    }
                }
                for r in defs {
                    live.unset(*r);
                }
                if let Some(h) = handler {
                    live.extend(h);
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
                for &l in &live.list {
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
            live.extend(uses);
            if let Some(h) = handler {
                live.extend(h);
            }
        }
    }
    for list in interf.iter_mut() {
        list.sort_unstable();
        list.dedup();
    }
    // Order of appearance: the first definition or use.
    let mut order: Vec<Reg> = Vec::with_capacity(n);
    let mut seen = vec![false; n];
    let mut note = |r: Reg, order: &mut Vec<Reg>| {
        if !seen[r as usize] {
            seen[r as usize] = true;
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
    // A number fits a register of its kind that interferes with none of
    // the registers it holds; the numbers of each kind, in order.
    let mut color: Vec<Option<Reg>> = vec![None; n];
    let mut kind_color: Vec<usize> = Vec::new();
    let mut of_kind: std::collections::HashMap<usize, Vec<Reg>> = Default::default();
    // `taken[c] == r + 1`: an interfering register of `r`'s holds `c`.
    let mut taken: Vec<u32> = Vec::new();
    for r in order {
        let stamp = r + 1;
        for nb in &interf[r as usize] {
            if let Some(c) = color[*nb as usize] {
                taken[c as usize] = stamp;
            }
        }
        let k = kind(r);
        let fits = |c: Reg| kind_color[c as usize] == k && taken[c as usize] != stamp;
        let preferred = partners[r as usize]
            .iter()
            .filter_map(|p| color[*p as usize])
            .find(|c| fits(*c));
        let numbers = of_kind.entry(k).or_default();
        let c = preferred.or_else(|| numbers.iter().copied().find(|c| fits(*c)));
        let c = match c {
            Some(c) => c,
            None => {
                let c = kind_color.len() as Reg;
                kind_color.push(k);
                taken.push(0);
                numbers.push(c);
                c
            }
        };
        color[r as usize] = Some(c);
    }
    let new_n = kind_color.len().max(1) as u32;
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
