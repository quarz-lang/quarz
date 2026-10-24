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
            if term_uses.get(&q).is_some_and(|bs| {
                bs.iter().any(|bi| {
                    let n = f.blocks[*bi].insts.len();
                    defs_at(&reach, f, *bi, n, q).contains(&def)
                })
            }) {
                ok = false;
                break;
            }
            for &(ubi, uii) in uses.get(&q).map(|v| v.as_slice()).unwrap_or(&[]) {
                let here = defs_at(&reach, f, ubi, uii, q);
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
                        if defs_at(&reach, f, ubi, uii, a) != arg_defs[*index as usize] {
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
