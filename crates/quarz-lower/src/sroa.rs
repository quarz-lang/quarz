//! Scalar replacement of data objects that do not escape: a `data`
//! value built in a function and only ever read field by field (after
//! inlining, `Vec2.new(x * k, y * k)` consumed by `+`) is never
//! allocated; each field read becomes a move from the register that
//! held the constructor argument.
//!
//! Registers are mutable, so the pass works on reaching definitions: a
//! use of a register is attributed to the construction only when that
//! construction is the one definition reaching it, and the argument
//! registers must still hold their values there.

use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};

use quarz_ir::*;

/// Replace what can be replaced in every function.
pub fn scalar_replace(functions: &mut [Function], methods: &[RtMethod], classes: &[RtClass]) {
    for f in functions.iter_mut() {
        replace_in(f, methods, classes);
    }
}

/// A definition site: instruction `inst` of block `block`.
pub(crate) type Site = (usize, usize);

/// The sites that may have written a register last, in order (a few at
/// most).
pub(crate) type Sites = Vec<Site>;

/// Reaching definitions per block entry: for each register (by number),
/// the sites that may have written it last.
pub(crate) struct Reaching {
    entry: Vec<Vec<Sites>>,
    /// Blocks entered from an exception: nothing definite is known there.
    handlers: HashSet<BlockId>,
    /// What each instruction writes (`written`), computed once.
    writes: Vec<Vec<Vec<Reg>>>,
}

/// The set of one site.
pub(crate) fn one(site: Site) -> HashSet<Site> {
    let mut s = HashSet::default();
    s.insert(site);
    s
}

pub(crate) fn successors(b: &Block) -> Vec<BlockId> {
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

/// The "any definition" marker: a handler block may be entered from the
/// middle of its region, so nothing definite is known there.
pub(crate) const UNKNOWN: Site = (usize::MAX, usize::MAX);

/// What an instruction writes, for the reaching definitions: its
/// defined registers, and the array an `ArrayPush` or `ArrayPushWord`
/// appends to (changed in place, so a copy taken before no longer equals
/// it).
pub(crate) fn written(inst: &Inst) -> Vec<Reg> {
    let mut v = inst.defs();
    if let Inst::ArrayPush { arr, .. } | Inst::ArrayPushWord { arr, .. } = inst {
        v.push(*arr);
    }
    v
}

pub(crate) fn reaching(f: &Function) -> Reaching {
    let n = f.blocks.len();
    let nregs = f.nregs as usize;
    let mut entry: Vec<Vec<Sites>> = vec![vec![Vec::new(); nregs]; n];
    let writes: Vec<Vec<Vec<Reg>>> = f
        .blocks
        .iter()
        .map(|b| b.insts.iter().map(written).collect())
        .collect();
    let handlers: HashSet<BlockId> = f
        .blocks
        .iter()
        .filter_map(|b| b.handler.map(|h| h.block))
        .collect();
    // The entry block: every register is nil (no site: "not written
    // here"). A handler is entered from anywhere: UNKNOWN for all.
    // A block is (re)visited when what enters it has grown.
    let mut queued = vec![true; n];
    let mut work: std::collections::VecDeque<usize> = (0..n).collect();
    let mut state: Vec<Sites> = Vec::with_capacity(nregs);
    while let Some(bi) = work.pop_front() {
        queued[bi] = false;
        {
            state.clone_from(&entry[bi]);
            if handlers.contains(&(bi as BlockId)) {
                for s in state.iter_mut() {
                    s.clear();
                    s.push(UNKNOWN);
                }
            }
            for (ii, w) in writes[bi].iter().enumerate() {
                for r in w {
                    let s = &mut state[*r as usize];
                    s.clear();
                    s.push((bi, ii));
                }
            }
            for s in successors(&f.blocks[bi]) {
                let s = s as usize;
                let mut grew = false;
                for (dst, sites) in entry[s].iter_mut().zip(&state) {
                    for site in sites {
                        if let Err(at) = dst.binary_search(site) {
                            dst.insert(at, *site);
                            grew = true;
                        }
                    }
                }
                if grew && !queued[s] {
                    queued[s] = true;
                    work.push_back(s);
                }
            }
        }
    }
    Reaching {
        entry,
        handlers,
        writes,
    }
}

/// Where what `site` made (a copy, `dst <- src`; an object built from
/// argument registers) still holds on entry to each block: on every path
/// from `site`, none of `regs` was written again, and no path from the
/// function's entry or a handler gets there without passing `site`.
/// Reaching definitions cannot tell this across a loop: a use reached by
/// `site` in the previous pass, while one of `regs` was written again by
/// the same instruction in this one, has the same definitions as at
/// `site`, but not the same values.
pub(crate) fn holds_on_entry(f: &Function, site: Site, regs: &[Reg]) -> Vec<bool> {
    let n = f.blocks.len();
    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (bi, blk) in f.blocks.iter().enumerate() {
        for s in successors(blk) {
            preds[s as usize].push(bi);
        }
    }
    let handlers: HashSet<usize> = f
        .blocks
        .iter()
        .filter_map(|b| b.handler.map(|h| h.block as usize))
        .collect();
    // What each block does, found once: it makes it (`site`, with no
    // write after it there), ends it (a write of one of `regs`, after
    // `site` if any), or leaves it as it came.
    #[derive(Clone, Copy)]
    enum Effect {
        Makes,
        Ends,
        Keeps,
    }
    let effect: Vec<Effect> = f
        .blocks
        .iter()
        .enumerate()
        .map(|(bi, blk)| {
            let mut e = Effect::Keeps;
            for (ii, inst) in blk.insts.iter().enumerate() {
                if (bi, ii) == site {
                    e = Effect::Makes;
                } else if writes_any(inst, regs) {
                    e = Effect::Ends;
                }
            }
            e
        })
        .collect();
    let at_end = |bi: usize, holds: bool| -> bool {
        match effect[bi] {
            Effect::Makes => true,
            Effect::Ends => false,
            Effect::Keeps => holds,
        }
    };
    // Optimistic start, lowered to a fixed point: the entry block and
    // handlers hold nothing.
    let mut entry: Vec<bool> = (0..n).map(|b| b != 0 && !handlers.contains(&b)).collect();
    let mut exit: Vec<bool> = (0..n).map(|b| at_end(b, entry[b])).collect();
    loop {
        let mut changed = false;
        for b in 1..n {
            if handlers.contains(&b) {
                continue;
            }
            let e = !preds[b].is_empty() && preds[b].iter().all(|&p| exit[p]);
            if e != entry[b] {
                entry[b] = e;
                changed = true;
            }
            let x = at_end(b, e);
            if x != exit[b] {
                exit[b] = x;
                changed = true;
            }
        }
        if !changed {
            return entry;
        }
    }
}

fn writes_any(inst: &Inst, regs: &[Reg]) -> bool {
    written(inst).iter().any(|r| regs.contains(r))
}

/// Whether what `site` made still holds before instruction `ii` of its
/// own block, after it: nothing between writes one of `regs`.
pub(crate) fn unwritten_between(f: &Function, site: Site, ii: usize, regs: &[Reg]) -> bool {
    f.blocks[site.0].insts[site.1 + 1..ii]
        .iter()
        .all(|inst| !writes_any(inst, regs))
}

/// Whether what `site` made still holds before instruction `ii` of block
/// `bi` (`ii` the instruction count: before the terminator), `entry`
/// being `holds_on_entry`'s answer.
pub(crate) fn holds_at(
    f: &Function,
    entry: &[bool],
    site: Site,
    regs: &[Reg],
    bi: usize,
    ii: usize,
) -> bool {
    let mut holds = entry[bi];
    for (k, inst) in f.blocks[bi].insts[..ii].iter().enumerate() {
        if (bi, k) == site {
            holds = true;
        } else if writes_any(inst, regs) {
            holds = false;
        }
    }
    holds
}

/// The definitions of `r` reaching instruction `ii` of block `bi`
/// (`None` = never written on this path, i.e. still nil).
pub(crate) fn defs_at(reach: &Reaching, f: &Function, bi: usize, ii: usize, r: Reg) -> Sites {
    let _ = f;
    // The last write before `ii` in the block, else what enters it.
    if let Some(k) = reach.writes[bi][..ii].iter().rposition(|w| w.contains(&r)) {
        return vec![(bi, k)];
    }
    if reach.handlers.contains(&(bi as BlockId)) {
        vec![UNKNOWN]
    } else {
        reach.entry[bi][r as usize].clone()
    }
}

fn replace_in(f: &mut Function, methods: &[RtMethod], classes: &[RtClass]) {
    // Candidate constructions.
    let mut sites: Vec<(Site, ClassId, Vec<Reg>, Reg)> = Vec::new();
    for (bi, blk) in f.blocks.iter().enumerate() {
        for (ii, inst) in blk.insts.iter().enumerate() {
            if let Inst::Call {
                dst,
                kind:
                    CallKind::Construct {
                        class,
                        init: Some(init),
                    },
                args,
                splat: false,
                kw,
                kw_splat: None,
                block: None,
                ..
            } = inst
            {
                let Some(m) = methods.get(*init as usize) else {
                    continue;
                };
                let Some(c) = classes.get(*class as usize) else {
                    continue;
                };
                if kw.is_empty()
                    && m.synth == RtSynth::DataInit
                    && matches!(c.kind, RtClassKind::Data | RtClassKind::Variant)
                    && args.len() == c.fields.len()
                    && blk.handler.is_none()
                {
                    sites.push(((bi, ii), *class, args.clone(), *dst));
                }
            }
        }
    }
    if sites.is_empty() {
        return;
    }
    let reach = reaching(f);
    // Where every register is used (instructions and terminators).
    let mut uses: HashMap<Reg, Vec<Site>> = HashMap::default();
    let mut term_uses: HashMap<Reg, Vec<usize>> = HashMap::default();
    for (bi, blk) in f.blocks.iter().enumerate() {
        for (ii, inst) in blk.insts.iter().enumerate() {
            for r in inst.uses() {
                uses.entry(r).or_default().push((bi, ii));
            }
        }
        if let Some(r) = blk.term.uses() {
            term_uses.entry(r).or_default().push(bi);
        }
    }
    let mut delete: HashSet<Site> = HashSet::default();
    let mut rewrite: HashMap<Site, Inst> = HashMap::default();
    for (site, class, args, dst) in sites {
        let arg_defs: Vec<Sites> = args
            .iter()
            .map(|a| defs_at(&reach, f, site.0, site.1, *a))
            .collect();
        // Aliases of the object: the register each definition writes.
        let mut aliases: Vec<(Reg, Site)> = vec![(dst, site)];
        let mut seen: HashSet<Site> = one(site);
        let mut to_delete: Vec<Site> = vec![site];
        let mut to_rewrite: Vec<(Site, Inst)> = Vec::new();
        let mut ok = true;
        let mut k = 0;
        while ok && k < aliases.len() {
            let (q, def) = aliases[k];
            k += 1;
            // A use in a handler (entered from anywhere in its region:
            // `UNKNOWN`) may see the object; so does a terminator.
            if term_uses.get(&q).is_some_and(|bs| {
                bs.iter().any(|bi| {
                    let n = f.blocks[*bi].insts.len();
                    let here = defs_at(&reach, f, *bi, n, q);
                    here.contains(&def) || here.contains(&UNKNOWN)
                })
            }) {
                ok = false;
                break;
            }
            for &(ubi, uii) in uses.get(&q).map(|v| v.as_slice()).unwrap_or(&[]) {
                let here = defs_at(&reach, f, ubi, uii, q);
                if here.contains(&UNKNOWN) {
                    ok = false;
                    break;
                }
                if !here.contains(&def) {
                    continue;
                }
                if here.len() != 1 {
                    ok = false;
                    break;
                }
                match &f.blocks[ubi].insts[uii] {
                    Inst::Move { dst: m, src } if *src == q => {
                        if seen.insert((ubi, uii)) {
                            aliases.push((*m, (ubi, uii)));
                            to_delete.push((ubi, uii));
                        }
                    }
                    Inst::FieldGet {
                        dst: d,
                        obj,
                        index,
                        class: c,
                    } if *obj == q && *c == class && (*index as usize) < args.len() => {
                        let a = args[*index as usize];
                        // The argument still holds what the object was
                        // built from: same definitions, and not written
                        // since on any path (a pass of a loop may write
                        // it and leave before building again).
                        let still = if ubi == site.0 && uii > site.1 {
                            unwritten_between(f, site, uii, &[a])
                        } else {
                            holds_at(f, &holds_on_entry(f, site, &[a]), site, &[a], ubi, uii)
                        };
                        if defs_at(&reach, f, ubi, uii, a) != arg_defs[*index as usize] || !still {
                            ok = false;
                            break;
                        }
                        to_rewrite.push(((ubi, uii), Inst::Move { dst: *d, src: a }));
                    }
                    _ => {
                        ok = false;
                        break;
                    }
                }
            }
        }
        if ok {
            delete.extend(to_delete);
            rewrite.extend(to_rewrite);
        }
    }
    if delete.is_empty() {
        return;
    }
    for (bi, blk) in f.blocks.iter_mut().enumerate() {
        let insts = std::mem::take(&mut blk.insts);
        let lines = std::mem::take(&mut blk.lines);
        for (ii, (inst, line)) in insts.into_iter().zip(lines).enumerate() {
            if delete.contains(&(bi, ii)) {
                continue;
            }
            let inst = rewrite.remove(&(bi, ii)).unwrap_or(inst);
            blk.insts.push(inst);
            blk.lines.push(line);
        }
    }
}
