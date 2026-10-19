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

use std::collections::{HashMap, HashSet};

use quarz_ir::*;

/// Replace what can be replaced in every function.
pub fn scalar_replace(functions: &mut [Function], methods: &[RtMethod], classes: &[RtClass]) {
    for f in functions.iter_mut() {
        replace_in(f, methods, classes);
    }
}

/// A definition site: instruction `inst` of block `block`.
pub(crate) type Site = (usize, usize);

/// Reaching definitions per block entry: for each register, the set of
/// sites that may have written it last.
pub(crate) struct Reaching {
    entry: Vec<HashMap<Reg, HashSet<Site>>>,
    /// Blocks entered from an exception: nothing definite is known there.
    handlers: HashSet<BlockId>,
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
/// defined registers, and the array an `ArrayPush` appends to (changed
/// in place, so a copy taken before no longer equals it).
pub(crate) fn written(inst: &Inst) -> Vec<Reg> {
    let mut v = inst.defs();
    if let Inst::ArrayPush { arr, .. } = inst {
        v.push(*arr);
    }
    v
}

pub(crate) fn reaching(f: &Function) -> Reaching {
    let n = f.blocks.len();
    let mut entry: Vec<HashMap<Reg, HashSet<Site>>> = vec![HashMap::new(); n];
    let handlers: HashSet<BlockId> = f
        .blocks
        .iter()
        .filter_map(|b| b.handler.map(|h| h.block))
        .collect();
    // The entry block: every register is nil (site UNKNOWN stands for
    // "not written here").
    let mut changed = true;
    while changed {
        changed = false;
        for bi in 0..n {
            let mut state = entry[bi].clone();
            if handlers.contains(&(bi as BlockId)) {
                for r in 0..f.nregs {
                    state.insert(r, HashSet::from([UNKNOWN]));
                }
            }
            for (ii, inst) in f.blocks[bi].insts.iter().enumerate() {
                for r in written(inst) {
                    state.insert(r, HashSet::from([(bi, ii)]));
                }
            }
            for s in successors(&f.blocks[bi]) {
                let target = &mut entry[s as usize];
                for (r, sites) in &state {
                    let dst = target.entry(*r).or_default();
                    for site in sites {
                        if dst.insert(*site) {
                            changed = true;
                        }
                    }
                }
            }
        }
    }
    Reaching { entry, handlers }
}

/// The definitions of `r` reaching instruction `ii` of block `bi`
/// (`None` = never written on this path, i.e. still nil).
pub(crate) fn defs_at(
    reach: &Reaching,
    f: &Function,
    bi: usize,
    ii: usize,
    r: Reg,
) -> HashSet<Site> {
    let mut sites = if reach.handlers.contains(&(bi as BlockId)) {
        HashSet::from([UNKNOWN])
    } else {
        reach.entry[bi].get(&r).cloned().unwrap_or_default()
    };
    for (k, inst) in f.blocks[bi].insts[..ii].iter().enumerate() {
        if written(inst).contains(&r) {
            sites = HashSet::from([(bi, k)]);
        }
    }
    sites
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
    let mut uses: HashMap<Reg, Vec<Site>> = HashMap::new();
    let mut term_uses: HashMap<Reg, Vec<usize>> = HashMap::new();
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
    let mut delete: HashSet<Site> = HashSet::new();
    let mut rewrite: HashMap<Site, Inst> = HashMap::new();
    for (site, class, args, dst) in sites {
        let arg_defs: Vec<HashSet<Site>> = args
            .iter()
            .map(|a| defs_at(&reach, f, site.0, site.1, *a))
            .collect();
        // Aliases of the object: the register each definition writes.
        let mut aliases: Vec<(Reg, Site)> = vec![(dst, site)];
        let mut seen: HashSet<Site> = HashSet::from([site]);
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
