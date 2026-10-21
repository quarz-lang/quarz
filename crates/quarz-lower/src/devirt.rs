//! Speculative devirtualization: a call to a method that some class
//! overrides, when the classes that can receive it are few and each
//! runs a known small method, becomes a chain of exact class tests on
//! the receiver, each leading to a direct call of that class's method
//! (which the inliner then copies in), with the dispatched call kept as
//! the fallback. `area` on a `Shape` with three implementations costs
//! a tag test, a class comparison and the inlined body.
//!
//! The classes come from the whole program (class hierarchy analysis,
//! as the inliner already assumes); a method reached through an
//! extension, with defaults or a block, or whose receivers are many,
//! keeps its dispatch.

use rustc_hash::FxHashSet as HashSet;

use quarz_ir::*;

/// The most receiver classes a call site is split for.
const MAX_CLASSES: usize = 6;

pub fn devirtualize(functions: &mut [Function], world: &RtWorld) {
    for f in functions.iter_mut() {
        devirt_in(f, world);
    }
}

/// The classes a method call on `owner` may dispatch to, each with the
/// method it runs; `None` when the site is better left alone.
fn receivers(world: &RtWorld, mid: MethodId) -> Option<Vec<(ClassId, MethodId)>> {
    let m = &world.methods[mid as usize];
    let mut out = Vec::new();
    for (cid, c) in world.classes.iter().enumerate() {
        let cid = cid as ClassId;
        if !matches!(
            c.kind,
            RtClassKind::Class | RtClassKind::Data | RtClassKind::Variant
        ) || c.is_abstract
        {
            continue;
        }
        if cid != m.owner && !c.ancestors.contains(&m.owner) {
            continue;
        }
        if let Some(impl_) = resolve(world, cid, mid)? {
            out.push((cid, impl_));
        }
        if out.len() > MAX_CLASSES {
            return None;
        }
    }
    (!out.is_empty()).then_some(out)
}

/// The method class `cid` runs for `m`: `Ok(None)` when it has none
/// (an abstract one, so the class has no instances), `Err` when the
/// answer is not simple (an extension, overloads, a native).
fn resolve(world: &RtWorld, cid: ClassId, mid: MethodId) -> Option<Option<MethodId>> {
    let m = &world.methods[mid as usize];
    let class = &world.classes[cid as usize];
    let chain: Vec<ClassId> = if class.ancestors.first() == Some(&cid) {
        class.ancestors.clone()
    } else {
        std::iter::once(cid)
            .chain(class.ancestors.iter().copied())
            .collect()
    };
    for anc in chain {
        if world.extensions.iter().any(|e| {
            e.target == anc
                && e.methods.contains_key(&m.name)
                && world.extension_dispatches(e, m.owner)
        }) {
            return None;
        }
        let Some(ids) = world.classes[anc as usize].methods.get(&m.name) else {
            continue;
        };
        let matching: Vec<MethodId> = ids
            .iter()
            .copied()
            .filter(|id| {
                let c = &world.methods[*id as usize];
                c.synth == RtSynth::None
                    && c.params.len() == m.params.len()
                    && c.has_block == m.has_block
                    && c.params
                        .iter()
                        .all(|p| p.kind == RtParamKind::Positional && !p.has_default)
                    // The method itself or an override of it: a method of
                    // the same name that accepts less is an overload.
                    && (*id == mid
                        || c.overrides.contains(&mid)
                        || c.params.iter().zip(&m.params).all(|(p, q)| {
                            p.ty == q.ty || p.ty.is_none() || q.ty.is_none()
                        }))
            })
            .collect();
        let [one] = matching.as_slice() else {
            return None;
        };
        let c = &world.methods[*one as usize];
        if c.is_abstract {
            return Some(None);
        }
        if c.func.is_none() || c.native_key.is_some() {
            return None;
        }
        return Some(Some(*one));
    }
    None
}

struct Site {
    block: usize,
    index: usize,
    recv: Reg,
    receivers: Vec<(ClassId, MethodId)>,
}

fn find_site(f: &Function, world: &RtWorld, done: &HashSet<usize>) -> Option<Site> {
    for (bi, blk) in f.blocks.iter().enumerate() {
        if done.contains(&bi) {
            continue;
        }
        for (ii, inst) in blk.insts.iter().enumerate() {
            let Inst::Call {
                kind: CallKind::Method(mid),
                recv: Some(recv),
                args,
                splat: false,
                kw,
                kw_splat: None,
                block: None,
                ..
            } = inst
            else {
                continue;
            };
            if !kw.is_empty() {
                continue;
            }
            let m = &world.methods[*mid as usize];
            let virtual_ = m.overridden
                && !m.singleton
                && !m.is_extension
                && m.native_key.is_none()
                && m.synth == RtSynth::None
                && !m.has_block
                && m.params.len() == args.len()
                && m.params
                    .iter()
                    .all(|p| p.kind == RtParamKind::Positional && !p.has_default);
            if !virtual_ {
                continue;
            }
            let Some(receivers) = receivers(world, *mid) else {
                continue;
            };
            return Some(Site {
                block: bi,
                index: ii,
                recv: *recv,
                receivers,
            });
        }
    }
    None
}

fn devirt_in(f: &mut Function, world: &RtWorld) {
    // The blocks a split creates are not split again: the fallback
    // holds the dispatched call, and a branch's direct call may be to a
    // method that is itself overridden further down.
    let mut done: HashSet<usize> = HashSet::default();
    while let Some(site) = find_site(f, world, &done) {
        let bi = site.block;
        let handler = f.blocks[bi].handler;
        let rest_insts = f.blocks[bi].insts.split_off(site.index);
        let rest_lines = f.blocks[bi].lines.split_off(site.index);
        let mut rest = rest_insts.into_iter();
        let mut rest_lines = rest_lines.into_iter();
        let call = rest.next().expect("the call");
        let line = rest_lines.next().expect("its line");
        let term = std::mem::take(&mut f.blocks[bi].term);
        let term_line = f.blocks[bi].term_line;
        // The continuation: the rest of the block.
        let cont = f.blocks.len() as BlockId;
        f.blocks.push(Block {
            insts: rest.collect(),
            lines: rest_lines.collect(),
            term,
            term_line,
            handler,
        });
        // One test block per receiver class, then the fallback.
        let n = site.receivers.len();
        let first_test = f.blocks.len() as BlockId;
        let first_call = first_test + n as BlockId;
        let fallback = first_call + n as BlockId;
        f.blocks[bi].term = Term::Jump(first_test);
        f.blocks[bi].term_line = line;
        for (k, (cid, _)) in site.receivers.iter().enumerate() {
            let t = f.nregs;
            f.nregs += 1;
            let next = if k + 1 < n {
                first_test + k as BlockId + 1
            } else {
                fallback
            };
            f.blocks.push(Block {
                insts: vec![Inst::ClassIs {
                    dst: t,
                    src: site.recv,
                    class: *cid,
                }],
                lines: vec![line],
                term: Term::Branch {
                    cond: t,
                    then: first_call + k as BlockId,
                    els: next,
                },
                term_line: line,
                handler,
            });
        }
        for k in 0..n {
            done.insert(first_test as usize + k);
            done.insert(first_call as usize + k);
        }
        for (_, impl_) in &site.receivers {
            let mut direct = call.clone();
            if let Inst::Call { kind, .. } = &mut direct {
                *kind = CallKind::Method(*impl_);
            }
            f.blocks.push(Block {
                insts: vec![direct],
                lines: vec![line],
                term: Term::Jump(cont),
                term_line: line,
                handler,
            });
        }
        done.insert(fallback as usize);
        f.blocks.push(Block {
            insts: vec![call],
            lines: vec![line],
            term: Term::Jump(cont),
            term_line: line,
            handler,
        });
    }
}
