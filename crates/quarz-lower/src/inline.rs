//! Inlining of small methods into their callers, on the QIR.
//!
//! A call bound statically to a small, simple method (no frame, no
//! handlers, no blocks) is replaced by a copy of the method's body: its
//! registers are renumbered after the caller's, `Arg` reads become moves
//! from the argument registers, `self` becomes the receiver register,
//! and `return` becomes a jump to the rest of the caller. Every function
//! is expanded from the functions as they were before the pass, so the
//! code grows by one level only (a recursive method gets one level of
//! itself). The lines of the copied instructions point at the function's
//! `inlined` table, so backtraces still show the callee's frame.
//!
//! **A method that yields, with the literal block it is given (#1223).**
//! A call passing a literal block (`MakeBlock`, its register read by the
//! call alone) to a method that yields is inlined with the block: each
//! `yield` becomes a copy of the block's body, and the `MakeBlock` goes.
//! Neither a closure nor a block call is left. It is done only when:
//! - the callee is bound statically (`Dispatch::Static`: no dynamic
//!   dispatch, no module-typed receiver), as for any inlined call;
//! - the callee uses its block only by `yield` (`yield_callee`: its
//!   `BlockParam` read by nothing but the `Release` that ends its scope,
//!   so its block is neither passed on nor stored nor tested), has no
//!   handler (`rescue`, `ensure`), no frame, at most `MAX_YIELDS`
//!   yields, each with plain positional arguments;
//! - the block (`block_inlinable`) is no lambda and does not destructure,
//!   takes exactly as many positional parameters as each `yield` gives
//!   (so binding them is a move each: arity adaptation, destructuring,
//!   defaults and splats stay a block call, `BlockCaller`), has no frame
//!   of its own, no handler, no `MakeBlock`, `BlockParam`, `yield` or
//!   `super` of its own, and does not call the callee again (a callee
//!   recursive through its block makes a block itself, refused above; a
//!   nested use, `w.with { w.with { 1 } }`, is inlined level by level,
//!   the passes of `inline_calls` bounding the depth);
//! - the callee's size plus the block's once per `yield` is at most
//!   `MAX_WITH_BLOCKS`, the block alone at most `MAX_BLOCK_INSTS`.
//!
//! The block's body runs in the caller's context, as its closure would
//! have: its `self` and method block are the caller's (`SelfRef`,
//! implicit-self calls kept as they are), and its `FrameGet`/`FrameSet`
//! read the caller's frame at the same depth. A block's depth 0 is the
//! frame its closure holds (`Closure::frame`, `act.frame` where the
//! `MakeBlock` ran), which is the depth 0 of the code around the
//! `MakeBlock`, the caller's. Its `return v` (`Term::Return`, `next v`
//! included) is the `yield`'s value; its `break v` (`BreakOut`) ends
//! the call with `v`. Its `return` from its own method (`ReturnOut`) is
//! the caller's `Return` when the caller is that method and the call is
//! in no handler's block, and stays a `ReturnOut` in a caller that is a
//! block itself (the block's closure carries the same method's tag, and
//! a block's `ReturnOut` unwinds through its handlers as any). A block
//! with a `return` is not inlined anywhere else:
//! - under a handler (`rescue`, `ensure`) in the method: the lowering
//!   runs an `ensure` on a plain `return` by copying its code before the
//!   `Return`, never through the handler, so a `Return` there would skip
//!   it; and a `ReturnOut` is no method's own terminator (compiled code's
//!   direct call of a method does not catch a return aimed at it);
//! - in a file's top level or an initializer.
//!
//! Its lines chain
//! through the `yield`'s, so a backtrace shows the block, the callee and
//! the caller, as the calls did.

use rustc_hash::FxHashMap as HashMap;

use quarz_ir::*;

/// The largest body (in instructions) worth inlining.
const MAX_INSTS: usize = 40;
/// The largest block inlined at a `yield`, the most `yield`s of a callee
/// inlined with its block, and the largest callee and block together
/// (the block counted once per `yield`).
const MAX_BLOCK_INSTS: usize = 40;
const MAX_YIELDS: usize = 3;
const MAX_WITH_BLOCKS: usize = 100;

/// Inline the eligible calls of every function in `functions` (indexed
/// by `FuncId`), `passes` levels deep.
pub fn inline_calls(
    functions: &mut [Function],
    methods: &[RtMethod],
    native_objects: bool,
    passes: usize,
) {
    // In a program with a `deinitialize`, or with a cog's `native class`
    // (`native_objects`: its objects' data is dropped by the cog's code,
    // docs/15), what an inlined callee's registers hold is released at
    // its return, as its activation would be (elsewhere that changes
    // nothing the program can see, and the clear would keep `sroa` from
    // replacing the callee's objects). A cog's native methods alone make
    // only the runtime's values, whose release no program sees.
    let release = native_objects
        || methods
            .iter()
            .any(|m| m.name == "deinitialize" && m.func.is_some());
    for _ in 0..passes {
        inline_pass(functions, methods, release);
    }
}

fn inline_pass(functions: &mut [Function], methods: &[RtMethod], release: bool) {
    let orig: Vec<Function> = functions.to_vec();
    let eligible: Vec<bool> = orig.iter().map(eligible_callee).collect();
    let yields: Vec<bool> = orig.iter().map(yield_callee).collect();
    for g in functions.iter_mut() {
        inline_into(g, &orig, &eligible, &yields, methods, release);
    }
}

/// Whether a function's body can be copied into a caller.
fn eligible_callee(f: &Function) -> bool {
    if !matches!(f.kind, FuncKind::Method(_)) || f.frame_size != 0 {
        return false;
    }
    let size: usize = f.blocks.iter().map(|b| b.insts.len()).sum();
    if size > MAX_INSTS {
        return false;
    }
    f.blocks.iter().all(|b| {
        b.handler.is_none()
            && !matches!(
                b.term,
                Term::BreakOut(_) | Term::ReturnOut(_) | Term::Resume(_)
            )
            && b.insts.iter().all(|i| {
                !matches!(
                    i,
                    Inst::MakeBlock { .. }
                        | Inst::BlockParam { .. }
                        | Inst::FrameGet { .. }
                        | Inst::FrameSet { .. }
                        | Inst::CatchException { .. }
                        | Inst::CatchAny { .. }
                        | Inst::FieldGetByName { .. }
                        | Inst::HashGetSym { .. }
                        | Inst::HashRest { .. }
                        | Inst::Call {
                            kind: CallKind::Yield | CallKind::Super(_),
                            ..
                        }
                )
            })
    })
}

fn size(f: &Function) -> usize {
    f.blocks.iter().map(|b| b.insts.len()).sum()
}

/// The `yield`s of `f`.
fn yield_calls(f: &Function) -> impl Iterator<Item = &Inst> {
    f.blocks.iter().flat_map(|b| b.insts.iter()).filter(|i| {
        matches!(
            i,
            Inst::Call {
                kind: CallKind::Yield,
                ..
            }
        )
    })
}

/// Whether a method that yields can be copied into a caller with the
/// literal block it is given (the module's doc): `eligible_callee`'s
/// rules, a `yield` allowed, with plain positional arguments.
fn yield_callee(f: &Function) -> bool {
    if !matches!(f.kind, FuncKind::Method(_)) || f.frame_size != 0 || size(f) > MAX_INSTS {
        return false;
    }
    let n = yield_calls(f).count();
    if n == 0 || n > MAX_YIELDS {
        return false;
    }
    // Its block parameter, and the registers it is copied into (the
    // `&blk` variable), are read by these copies and their scope's
    // `Release` only: the block is used by `yield` alone.
    let mut params: Vec<Reg> = f
        .blocks
        .iter()
        .flat_map(|b| b.insts.iter())
        .filter_map(|i| match i {
            Inst::BlockParam { dst } => Some(*dst),
            _ => None,
        })
        .collect();
    loop {
        let before = params.len();
        for i in f.blocks.iter().flat_map(|b| b.insts.iter()) {
            if let Inst::Move { dst, src } | Inst::Take { dst, src } = i {
                if params.contains(src) && !params.contains(dst) {
                    params.push(*dst);
                }
            }
        }
        if params.len() == before {
            break;
        }
    }
    let only_released = f.blocks.iter().all(|b| {
        b.insts.iter().all(|i| match i {
            Inst::Release { .. } => true,
            Inst::Move { dst, src } | Inst::Take { dst, src } if params.contains(src) => {
                params.contains(dst)
            }
            _ => i.uses().iter().all(|r| !params.contains(r)),
        }) && b.term.uses().is_none_or(|r| !params.contains(&r))
    });
    if !only_released {
        return false;
    }
    f.blocks.iter().all(|b| {
        b.handler.is_none()
            && !matches!(
                b.term,
                Term::BreakOut(_) | Term::ReturnOut(_) | Term::Resume(_)
            )
            && b.insts.iter().all(|i| match i {
                Inst::Call {
                    kind: CallKind::Yield,
                    splat,
                    kw,
                    kw_splat,
                    block,
                    ..
                } => !splat && kw.is_empty() && kw_splat.is_none() && block.is_none(),
                _ => !matches!(
                    i,
                    Inst::MakeBlock { .. }
                        | Inst::FrameGet { .. }
                        | Inst::FrameSet { .. }
                        | Inst::CatchException { .. }
                        | Inst::CatchAny { .. }
                        | Inst::FieldGetByName { .. }
                        | Inst::HashGetSym { .. }
                        | Inst::HashRest { .. }
                        | Inst::Call {
                            kind: CallKind::Super(_),
                            ..
                        }
                ),
            })
    })
}

/// Whether block `b` can be copied at each `yield` of callee `f`
/// (method `callee`): the module's doc.
fn block_inlinable(b: &Function, f: &Function, callee: MethodId) -> bool {
    let nparams = b.param_kinds.len();
    b.kind == FuncKind::Block
        && b.frame_size == 0
        && size(b) <= MAX_BLOCK_INSTS
        && size(f) + yield_calls(f).count() * size(b) <= MAX_WITH_BLOCKS
        && b.param_kinds.iter().all(|k| *k == RtParamKind::Positional)
        && yield_calls(f).all(|y| matches!(y, Inst::Call { args, .. } if args.len() == nparams))
        && b.blocks.iter().all(|blk| {
            blk.handler.is_none()
                && !matches!(blk.term, Term::Resume(_))
                && blk.insts.iter().all(|i| {
                    !matches!(
                        i,
                        Inst::MakeBlock { .. }
                            | Inst::BlockParam { .. }
                            | Inst::HasArg { .. }
                            | Inst::CatchException { .. }
                            | Inst::CatchAny { .. }
                            | Inst::FieldGetByName { .. }
                            | Inst::HashGetSym { .. }
                            | Inst::HashRest { .. }
                            | Inst::Call {
                                kind: CallKind::Yield | CallKind::Super(_),
                                ..
                            }
                    ) && !matches!(i, Inst::Call { kind: CallKind::Method(m), .. } if *m == callee)
                })
        })
}

/// The callee of a call that can be inlined: its function, receiver
/// register (`None` = the caller's `self`), argument registers and
/// destination.
struct Site {
    fid: FuncId,
    mid: MethodId,
    recv: Option<Reg>,
    args: Vec<Reg>,
    dst: Reg,
    /// The block the call gives, for a callee that yields.
    block: Option<Reg>,
}

fn site(inst: &Inst, eligible: &[bool], yields: &[bool], methods: &[RtMethod]) -> Option<Site> {
    let Inst::Call {
        dst,
        kind: CallKind::Method(mid),
        recv,
        args,
        splat: false,
        kw,
        kw_splat: None,
        block,
        ..
    } = inst
    else {
        return None;
    };
    if !kw.is_empty() {
        return None;
    }
    let m = methods.get(*mid as usize)?;
    let fid = m.func?;
    // (The block parameter is not a positional one: a method that yields
    // declares it, `&blk`.)
    let params: Vec<&RtParam> = m
        .params
        .iter()
        .filter(|p| p.kind != RtParamKind::Block)
        .collect();
    let bound = m.synth == RtSynth::None
        && !m.is_abstract
        && m.has_block == block.is_some()
        && m.native_key.is_none()
        && m.dispatch() == Dispatch::Static
        && params.len() >= args.len()
        && params.iter().all(|p| p.kind == RtParamKind::Positional)
        // (A parameter the call leaves out takes its default, which the
        // body runs where `HasArg` says it was not given, #938.)
        && params[args.len()..].iter().all(|p| p.has_default);
    let callee_ok = if block.is_some() { yields } else { eligible };
    if !bound || !callee_ok.get(fid as usize).copied().unwrap_or(false) {
        return None;
    }
    Some(Site {
        fid,
        mid: *mid,
        recv: *recv,
        args: args.clone(),
        dst: *dst,
        block: *block,
    })
}

fn inline_into(
    g: &mut Function,
    orig: &[Function],
    eligible: &[bool],
    yields: &[bool],
    methods: &[RtMethod],
    release: bool,
) {
    let blocks = std::mem::take(&mut g.blocks);
    // The blocks reading each register: a literal block's register read
    // after its call must be written first in the call's block, or be
    // read nowhere else (`dead_after`).
    let mut read_in: HashMap<Reg, Vec<usize>> = HashMap::default();
    for (bi, b) in blocks.iter().enumerate() {
        let mut regs: Vec<Reg> = b.insts.iter().flat_map(|i| i.uses()).collect();
        regs.extend(b.term.uses());
        for r in regs {
            let at = read_in.entry(r).or_default();
            if at.last() != Some(&bi) {
                at.push(bi);
            }
        }
    }
    let caller_is_method = matches!(g.kind, FuncKind::Method(_));
    let caller_is_block = g.kind == FuncKind::Block;
    let n = blocks.len();
    let mut out: Vec<Block> = vec![Block::default(); n];
    let mut extra: Vec<Option<Block>> = Vec::new();
    let mut origins: HashMap<(FuncId, u32, u32), u32> = HashMap::default();
    for (bi, blk) in blocks.into_iter().enumerate() {
        let handler = blk.handler;
        let mut cur = Block {
            handler,
            ..Default::default()
        };
        let mut cur_id = bi;
        // The literal blocks made in `cur` so far, by register: the
        // `MakeBlock`'s index in `cur.insts`, the block's function, and its
        // index in the original block.
        let mut made: HashMap<Reg, (usize, FuncId, usize)> = HashMap::default();
        let lines = blk.lines;
        let insts = blk.insts;
        for (i, inst) in insts.iter().cloned().enumerate() {
            let line = lines[i];
            let keep =
                |cur: &mut Block, made: &mut HashMap<Reg, (usize, FuncId, usize)>, inst: Inst| {
                    // (Read or written again: no longer this call's alone.)
                    for r in inst.uses().into_iter().chain(inst.defs()) {
                        made.remove(&r);
                    }
                    if let Inst::MakeBlock {
                        dst,
                        func,
                        destructure: None,
                        is_lambda: false,
                    } = &inst
                    {
                        made.insert(*dst, (cur.insts.len(), *func, i));
                    }
                    cur.insts.push(inst);
                    cur.lines.push(line);
                };
            let Some(s) = site(&inst, eligible, yields, methods) else {
                keep(&mut cur, &mut made, inst);
                continue;
            };
            let f = &orig[s.fid as usize];
            // A literal block, made here and read by this call alone, which
            // can be copied at the callee's `yield`s (the module's doc).
            let literal = match s.block {
                None => None,
                Some(br) => match made.get(&br).copied() {
                    Some((at, bf, made_at))
                        if read_only_by(
                            br,
                            &insts[..made_at],
                            &insts[i + 1..],
                            &blk.term,
                            &read_in,
                            bi,
                        ) && block_inlinable(&orig[bf as usize], f, s.mid)
                            && (!returns_out(&orig[bf as usize])
                                || caller_is_block
                                || (caller_is_method && handler.is_none())) =>
                    {
                        Some((br, at, bf))
                    }
                    _ => {
                        keep(&mut cur, &mut made, inst);
                        continue;
                    }
                },
            };
            // (A call leaving parameters out is inlined only when the
            // callee binds them as the lowering does, `defaults_shape`.)
            if !defaults_shape(f, s.args.len()) {
                debug_assert!(
                    false,
                    "`{}` binds a defaulted parameter in another shape than the lowering's: the inliner's mapping of `HasArg` would not hold (#938)",
                    f.name
                );
                keep(&mut cur, &mut made, inst);
                continue;
            }
            // The block is copied at the `yield`s: its closure is not made.
            if let Some((br, at, _)) = literal {
                let nil = const_index(g, &Constant::Nil);
                cur.insts[at] = Inst::LoadConst { dst: br, idx: nil };
            }
            let base_reg = g.nregs;
            g.nregs += f.nregs;
            let cont_id = n + extra.len();
            extra.push(None);
            let base_blk = n + extra.len();
            // A `yield`'s block copy and the rest of its callee block go
            // after the callee's blocks (`later`), which keep their places.
            let later_base = base_blk + f.blocks.len();
            let mut later: Vec<Option<Block>> = Vec::new();
            let const_map: Vec<u32> = f.consts.iter().map(|c| const_index(g, c)).collect();
            // (`HasArg`'s answers here, below.)
            let has = [
                const_index(g, &Constant::Bool(false)),
                const_index(g, &Constant::Bool(true)),
            ];
            // The callee's registers start as nil, as in a fresh
            // activation (and a previous pass through this code leaves
            // nothing behind).
            cur.insts.push(Inst::ClearRegs {
                from: base_reg,
                to: base_reg + f.nregs,
            });
            cur.lines.push(line);
            for cb in &f.blocks {
                // A line of the callee becomes an origin entry here; a line
                // the callee itself inlined (flagged) becomes a chain of them.
                let term_line = map_line(g, &mut origins, f, s.fid, cb.term_line, line);
                let mut nb = Block {
                    handler,
                    term_line,
                    ..Default::default()
                };
                // A block reading a parameter the call leaves out is the
                // one a `HasArg` of it guards, which is false here (below):
                // it never runs, and is `Unreachable` (an internal error
                // if it ever did, rather than a nil read as the argument).
                let given = s.args.len();
                if cb
                    .insts
                    .iter()
                    .any(|ci| matches!(ci, Inst::Arg { index, .. } if *index as usize >= given))
                {
                    nb.term = Term::Unreachable;
                    extra.push(Some(nb));
                    continue;
                }
                // Where `nb` goes: the callee block's own place (`None`),
                // or a continuation after a `yield` (`later[k]`).
                let mut slot: Option<usize> = None;
                for (k, ci) in cb.insts.iter().enumerate() {
                    let l = map_line(g, &mut origins, f, s.fid, cb.lines[k], line);
                    if let (
                        Some((_, _, bf)),
                        Inst::Call {
                            kind: CallKind::Yield,
                            dst: ydst,
                            args: yargs,
                            ..
                        },
                    ) = (literal, ci)
                    {
                        let b = &orig[bf as usize];
                        let bb = g.nregs;
                        g.nregs += b.nregs;
                        let bconsts: Vec<u32> =
                            b.consts.iter().map(|c| const_index(g, c)).collect();
                        // The `yield`'s continuation, then the block's body.
                        let ycont = later.len();
                        later.push(None);
                        let ycont_id = (later_base + ycont) as BlockId;
                        let bentry = (later_base + later.len()) as BlockId;
                        // The block's registers start as nil, as in its
                        // own activation.
                        nb.insts.push(Inst::ClearRegs {
                            from: bb,
                            to: bb + b.nregs,
                        });
                        nb.lines.push(l);
                        nb.term = Term::Jump(bentry);
                        nb.term_line = l;
                        place(&mut extra, &mut later, slot, nb);
                        for bblk in &b.blocks {
                            let bterm_line = map_line(g, &mut origins, b, bf, bblk.term_line, l);
                            let mut nb2 = Block {
                                handler,
                                term_line: bterm_line,
                                ..Default::default()
                            };
                            for (q, bi) in bblk.insts.iter().enumerate() {
                                let copied = match bi {
                                    // (One parameter per argument:
                                    // `block_inlinable`.)
                                    Inst::Arg { dst, index } => Inst::Move {
                                        dst: bb + dst,
                                        src: base_reg + yargs[*index as usize],
                                    },
                                    // The caller's `self`, method block and
                                    // frame are the block's (the module's
                                    // doc): kept as they are.
                                    other => {
                                        rewrite_with(other, &|x| bb + x, &|c| bconsts[c as usize])
                                    }
                                };
                                nb2.insts.push(copied);
                                let bl = map_line(g, &mut origins, b, bf, bblk.lines[q], l);
                                nb2.lines.push(bl);
                            }
                            nb2.term = match &bblk.term {
                                // The block's value (`next v` too): the
                                // `yield`'s.
                                Term::Return(r) => {
                                    nb2.insts.push(Inst::Move {
                                        dst: base_reg + ydst,
                                        src: bb + r,
                                    });
                                    nb2.lines.push(bterm_line);
                                    if release {
                                        nb2.insts.push(Inst::ClearRegs {
                                            from: bb,
                                            to: bb + b.nregs,
                                        });
                                        nb2.lines.push(bterm_line);
                                    }
                                    Term::Jump(ycont_id)
                                }
                                // `break v`: the call's value.
                                Term::BreakOut(r) => {
                                    nb2.insts.push(Inst::Move {
                                        dst: s.dst,
                                        src: bb + r,
                                    });
                                    nb2.lines.push(bterm_line);
                                    if release {
                                        nb2.insts.push(Inst::ClearRegs {
                                            from: bb,
                                            to: bb + b.nregs,
                                        });
                                        nb2.lines.push(bterm_line);
                                        nb2.insts.push(Inst::ClearRegs {
                                            from: base_reg,
                                            to: base_reg + f.nregs,
                                        });
                                        nb2.lines.push(bterm_line);
                                    }
                                    Term::Jump(cont_id as BlockId)
                                }
                                // `return v` from the block's own method:
                                // the caller's, when the caller is it.
                                // (A method caller here has no handler at
                                // the call: the condition above.)
                                Term::ReturnOut(r) if caller_is_method => Term::Return(bb + r),
                                Term::ReturnOut(r) => Term::ReturnOut(bb + r),
                                Term::Jump(t) => Term::Jump(bentry + t),
                                Term::Branch { cond, then, els } => Term::Branch {
                                    cond: bb + cond,
                                    then: bentry + then,
                                    els: bentry + els,
                                },
                                Term::Raise(r) => Term::Raise(bb + r),
                                Term::Unreachable => Term::Unreachable,
                                Term::Resume(_) => unreachable!("refused by `block_inlinable`"),
                            };
                            later.push(Some(nb2));
                        }
                        nb = Block {
                            handler,
                            term_line,
                            ..Default::default()
                        };
                        slot = Some(ycont);
                        continue;
                    }
                    let copied = match ci {
                        Inst::Arg { dst, index } => Inst::Move {
                            dst: base_reg + dst,
                            src: s.args[*index as usize],
                        },
                        // Whether the call gave parameter `index`: the
                        // call's own positional arguments fill the first
                        // `given` parameters (the binding's rule,
                        // `Activation::has_arg` on its mask, #938).
                        Inst::HasArg { dst, index } => Inst::LoadConst {
                            dst: base_reg + dst,
                            idx: has[usize::from((*index as usize) < given)],
                        },
                        // The callee's block, which is not made: its
                        // parameter (read by its `Release` alone) is nil.
                        Inst::BlockParam { dst } if literal.is_some() => Inst::LoadConst {
                            dst: base_reg + dst,
                            idx: const_index(g, &Constant::Nil),
                        },
                        Inst::SelfRef { dst } => match s.recv {
                            Some(r) => Inst::Move {
                                dst: base_reg + dst,
                                src: r,
                            },
                            None => Inst::SelfRef {
                                dst: base_reg + dst,
                            },
                        },
                        other => {
                            let mut copied = rewrite(other, base_reg, &const_map);
                            // An implicit-self call in the callee is a
                            // call on the receiver here (a function's too:
                            // it ignores it, but holds it to the call's end,
                            // as the callee's activation would).
                            if let (
                                Some(r),
                                Inst::Call {
                                    kind:
                                        CallKind::Method(_) | CallKind::Send(_) | CallKind::Function(_),
                                    recv: recv @ None,
                                    ..
                                },
                            ) = (s.recv, &mut copied)
                            {
                                *recv = Some(r);
                            }
                            copied
                        }
                    };
                    nb.insts.push(copied);
                    nb.lines.push(l);
                }
                nb.term = match &cb.term {
                    Term::Return(r) => {
                        nb.insts.push(Inst::Move {
                            dst: s.dst,
                            src: base_reg + r,
                        });
                        nb.lines.push(term_line);
                        // What the callee's registers hold goes at its
                        // return (a receiver it was the last to use, a
                        // temporary, finalized there).
                        if release {
                            nb.insts.push(Inst::ClearRegs {
                                from: base_reg,
                                to: base_reg + f.nregs,
                            });
                            nb.lines.push(term_line);
                        }
                        Term::Jump(cont_id as BlockId)
                    }
                    Term::Jump(t) => Term::Jump(base_blk as BlockId + t),
                    Term::Branch { cond, then, els } => Term::Branch {
                        cond: base_reg + cond,
                        then: base_blk as BlockId + then,
                        els: base_blk as BlockId + els,
                    },
                    Term::Raise(r) => Term::Raise(base_reg + r),
                    Term::Unreachable => Term::Unreachable,
                    Term::BreakOut(_) | Term::ReturnOut(_) | Term::Resume(_) => unreachable!(),
                };
                place(&mut extra, &mut later, slot, nb);
            }
            extra.extend(
                later
                    .into_iter()
                    .map(|b| Some(b.expect("continuation filled"))),
            );
            cur.term = Term::Jump(base_blk as BlockId);
            cur.term_line = line;
            store(&mut out, &mut extra, cur_id, cur);
            cur = Block {
                handler,
                ..Default::default()
            };
            cur_id = cont_id;
            made.clear();
        }
        cur.term = blk.term;
        cur.term_line = blk.term_line;
        store(&mut out, &mut extra, cur_id, cur);
    }
    out.extend(extra.into_iter().map(|b| b.expect("block filled")));
    g.blocks = out;
}

/// Whether a literal block's register `r`, written by the `MakeBlock`
/// that `before` (the block's instructions before it) leads up to, is
/// read by its call alone: by nothing between the two (`made` drops it
/// at any read), and by nothing after the call (`after`, then the
/// block's terminator): the block's next mention of `r` writes it
/// without reading it, or nothing in the block reads it (before the
/// `MakeBlock` either, where a loop's back edge would bring the previous
/// pass's closure) and no other block does.
fn read_only_by(
    r: Reg,
    before: &[Inst],
    after: &[Inst],
    term: &Term,
    read_in: &HashMap<Reg, Vec<usize>>,
    bi: usize,
) -> bool {
    for inst in after {
        if inst.uses().contains(&r) {
            return false;
        }
        if inst.defs().contains(&r) {
            return true;
        }
    }
    term.uses() != Some(r)
        && before.iter().all(|inst| !inst.uses().contains(&r))
        && read_in.get(&r).is_none_or(|at| at.iter().all(|b| *b == bi))
}

/// Whether block `b` returns from its method (`return` in it).
fn returns_out(b: &Function) -> bool {
    b.blocks
        .iter()
        .any(|blk| matches!(blk.term, Term::ReturnOut(_)))
}

/// A copied callee block `b` in its place: the callee block's own
/// (`slot` `None`, next in `extra`), or a continuation after a `yield`
/// (`later[k]`).
fn place(
    extra: &mut Vec<Option<Block>>,
    later: &mut [Option<Block>],
    slot: Option<usize>,
    b: Block,
) {
    match slot {
        None => extra.push(Some(b)),
        Some(k) => later[k] = Some(b),
    }
}

fn map_line(
    g: &mut Function,
    origins: &mut HashMap<(FuncId, u32, u32), u32>,
    f: &Function,
    fid: FuncId,
    l: u32,
    call_line: u32,
) -> u32 {
    let (callee, line, call_line) = if l & INLINE_LINE_FLAG != 0 {
        let o = f.inlined[(l & !INLINE_LINE_FLAG) as usize];
        let outer = map_line(g, origins, f, fid, o.call_line, call_line);
        (o.callee, o.line, outer)
    } else {
        (fid, l, call_line)
    };
    let key = (callee, line, call_line);
    if let Some(idx) = origins.get(&key) {
        return INLINE_LINE_FLAG | idx;
    }
    let idx = g.inlined.len() as u32;
    g.inlined.push(InlineOrigin {
        callee,
        line,
        call_line,
    });
    origins.insert(key, idx);
    INLINE_LINE_FLAG | idx
}

fn store(out: &mut [Block], extra: &mut [Option<Block>], id: usize, b: Block) {
    if id < out.len() {
        out[id] = b;
    } else {
        extra[id - out.len()] = Some(b);
    }
}

/// Whether `f`, called with `given` positional arguments, binds the
/// parameters the call leaves out as the lowering does (`FnBuilder`'s
/// parameter binding: `HasArg` → `Branch` → the given block reading the
/// `Arg` and storing it, the missing block running the default): every
/// block that reads an `Arg` of index `given` or more holds only that
/// binding (the `Arg`, the moves and the release of storing it, then a
/// `Jump`) and is entered only by the `then` edge of a `Branch` on the
/// `HasArg` of the same index in its one predecessor. Then a constant
/// `HasArg` (false) makes that block dead, and `inline_into` may leave it
/// `Unreachable`. The mapping's own precondition, checked where the site
/// is chosen, not a rule of the language (#938).
fn defaults_shape(f: &Function, given: usize) -> bool {
    for (b, blk) in f.blocks.iter().enumerate() {
        let Some(index) = blk.insts.iter().find_map(|i| match i {
            Inst::Arg { index, .. } if *index as usize >= given => Some(*index),
            _ => None,
        }) else {
            continue;
        };
        let only_binding = blk.insts.iter().all(|i| match i {
            Inst::Arg { index: k, .. } => *k == index,
            Inst::Move { .. } | Inst::Release { .. } => true,
            _ => false,
        }) && matches!(blk.term, Term::Jump(_));
        if !only_binding {
            return false;
        }
        let preds: Vec<&Block> = f
            .blocks
            .iter()
            // (The IR's own edges, a handler's included: `live::successors`.)
            .filter(|p| quarz_ir::live::successors(p).contains(&(b as BlockId)))
            .collect();
        let [p] = preds.as_slice() else {
            return false;
        };
        let Term::Branch { cond, then, els } = &p.term else {
            return false;
        };
        if *then != b as BlockId || *els == b as BlockId {
            return false;
        }
        // The last definition of the condition in the predecessor.
        let def = p.insts.iter().rev().find(|i| i.defs().contains(cond));
        if !matches!(def, Some(Inst::HasArg { index: k, .. }) if *k == index) {
            return false;
        }
    }
    true
}

fn const_index(g: &mut Function, c: &Constant) -> u32 {
    if let Some(i) = g.consts.iter().position(|x| x == c) {
        return i as u32;
    }
    g.consts.push(c.clone());
    (g.consts.len() - 1) as u32
}

/// `inst` with its registers moved up by `base` and its constant indices
/// mapped through `consts`.
fn rewrite(inst: &Inst, base: Reg, consts: &[u32]) -> Inst {
    let mut inst = rewrite_with(inst, &|x| base + x, &|c| consts[c as usize]);
    // (The callee's `self` is not the caller's.)
    if let Inst::Call { on_self, .. } = &mut inst {
        *on_self = false;
    }
    inst
}

/// `inst` with its registers mapped through `reg` and its constant
/// indices through `cst` (`ClearRegs` maps its bounds, so `reg` must
/// keep ranges: an offset does).
pub(crate) fn rewrite_with(
    inst: &Inst,
    reg: &dyn Fn(Reg) -> Reg,
    cst: &dyn Fn(u32) -> u32,
) -> Inst {
    let r = |x: &Reg| reg(*x);
    let rs = |xs: &[Reg]| xs.iter().map(|x| reg(*x)).collect::<Vec<_>>();
    let kw = |xs: &[(u32, Reg)]| {
        xs.iter()
            .map(|(k, v)| (cst(*k), reg(*v)))
            .collect::<Vec<_>>()
    };
    match inst {
        Inst::LoadConst { dst, idx } => Inst::LoadConst {
            dst: r(dst),
            idx: cst(*idx),
        },
        Inst::Move { dst, src } => Inst::Move {
            dst: r(dst),
            src: r(src),
        },
        Inst::Take { dst, src } => Inst::Take {
            dst: r(dst),
            src: r(src),
        },
        Inst::Release { src } => Inst::Release { src: r(src) },
        Inst::SelfRef { dst } => Inst::SelfRef { dst: r(dst) },
        Inst::Arg { dst, index } => Inst::Arg {
            dst: r(dst),
            index: *index,
        },
        Inst::HasArg { dst, index } => Inst::HasArg {
            dst: r(dst),
            index: *index,
        },
        Inst::BlockParam { dst } => Inst::BlockParam { dst: r(dst) },
        Inst::FrameGet { dst, depth, slot } => Inst::FrameGet {
            dst: r(dst),
            depth: *depth,
            slot: *slot,
        },
        Inst::FrameSet { depth, slot, src } => Inst::FrameSet {
            depth: *depth,
            slot: *slot,
            src: r(src),
        },
        Inst::FieldGet {
            dst,
            obj,
            index,
            class,
        } => Inst::FieldGet {
            dst: r(dst),
            obj: r(obj),
            index: *index,
            class: *class,
        },
        // (Made after inlining, `live::take_dying_fields`: a callee
        // inlined never holds one.)
        Inst::FieldTake { .. } => unreachable!("a FieldTake before inlining"),
        Inst::FieldSet {
            obj,
            index,
            src,
            class,
        } => Inst::FieldSet {
            obj: r(obj),
            index: *index,
            src: r(src),
            class: *class,
        },
        Inst::FieldGetByName {
            dst,
            found,
            obj,
            name,
        } => Inst::FieldGetByName {
            dst: r(dst),
            found: r(found),
            obj: r(obj),
            name: cst(*name),
        },
        Inst::ConstGet { dst, id } => Inst::ConstGet {
            dst: r(dst),
            id: *id,
        },
        Inst::ClassRef { dst, class } => Inst::ClassRef {
            dst: r(dst),
            class: *class,
        },
        Inst::VariantSingleton { dst, class } => Inst::VariantSingleton {
            dst: r(dst),
            class: *class,
        },
        Inst::Call {
            dst,
            kind,
            recv,
            args,
            splat,
            kw: kws,
            kw_splat,
            block,
            moved,
            kw_moved,
            recv_classes,
            recv_class_objects,
            on_self,
        } => Inst::Call {
            dst: r(dst),
            kind: kind.clone(),
            recv: recv.as_ref().map(r),
            args: rs(args),
            splat: *splat,
            kw: kw(kws),
            kw_splat: kw_splat.as_ref().map(r),
            block: block.as_ref().map(r),
            moved: *moved,
            kw_moved: *kw_moved,
            recv_classes: recv_classes.clone(),
            recv_class_objects: recv_class_objects.clone(),
            on_self: *on_self,
        },
        Inst::OwnedCall {
            dst,
            method,
            recv,
            args,
            kw: kws,
            unused,
            moved,
            kw_moved,
        } => Inst::OwnedCall {
            unused: *unused,
            moved: *moved,
            kw_moved: *kw_moved,
            dst: r(dst),
            method: *method,
            recv: match recv {
                VarLoc::Reg(x) => VarLoc::Reg(r(x)),
                VarLoc::Frame { depth, slot } => VarLoc::Frame {
                    depth: *depth,
                    slot: *slot,
                },
                VarLoc::Field { obj, index } => VarLoc::Field {
                    obj: r(obj),
                    index: *index,
                },
            },
            args: rs(args),
            kw: kw(kws),
        },
        Inst::IsNil { dst, src } => Inst::IsNil {
            dst: r(dst),
            src: r(src),
        },
        Inst::BinOp {
            dst,
            op,
            lhs,
            rhs,
            method,
        } => Inst::BinOp {
            dst: r(dst),
            op: *op,
            lhs: r(lhs),
            rhs: r(rhs),
            method: *method,
        },
        Inst::Not { dst, src } => Inst::Not {
            dst: r(dst),
            src: r(src),
        },
        Inst::CaseEq {
            dst,
            pattern,
            value,
        } => Inst::CaseEq {
            dst: r(dst),
            pattern: r(pattern),
            value: r(value),
        },
        Inst::Equal { dst, a, b } => Inst::Equal {
            dst: r(dst),
            a: r(a),
            b: r(b),
        },
        Inst::ClassIs { dst, src, class } => Inst::ClassIs {
            dst: r(dst),
            src: r(src),
            class: *class,
        },
        Inst::ClassIsA { dst, src, class } => Inst::ClassIsA {
            dst: r(dst),
            src: r(src),
            class: *class,
        },
        Inst::IsA { dst, src, ty } => Inst::IsA {
            dst: r(dst),
            src: r(src),
            ty: ty.clone(),
        },
        Inst::As {
            dst,
            src,
            ty,
            optional,
            name,
        } => Inst::As {
            dst: r(dst),
            src: r(src),
            ty: ty.clone(),
            optional: *optional,
            name: name.clone(),
        },
        Inst::MakeBlock {
            dst,
            func,
            destructure,
            is_lambda,
        } => Inst::MakeBlock {
            dst: r(dst),
            func: *func,
            destructure: *destructure,
            is_lambda: *is_lambda,
        },
        Inst::MethodRef {
            dst,
            recv,
            name,
            method,
        } => Inst::MethodRef {
            dst: r(dst),
            recv: r(recv),
            name: cst(*name),
            method: *method,
        },
        Inst::SymbolProc {
            dst,
            name,
            method,
            discard,
            among,
        } => Inst::SymbolProc {
            dst: r(dst),
            name: cst(*name),
            method: *method,
            discard: *discard,
            among: among.clone(),
        },
        Inst::MakeArray { dst, items } => Inst::MakeArray {
            dst: r(dst),
            items: items
                .iter()
                .map(|i| ArrayItem {
                    reg: r(&i.reg),
                    splat: i.splat,
                })
                .collect(),
        },
        Inst::MakeHash { dst, items } => Inst::MakeHash {
            dst: r(dst),
            items: items
                .iter()
                .map(|i| match i {
                    HashItem::Pair(k, v) => HashItem::Pair(r(k), r(v)),
                    HashItem::Splat(x) => HashItem::Splat(r(x)),
                })
                .collect(),
        },
        Inst::MakeRange {
            dst,
            lo,
            hi,
            exclusive,
        } => Inst::MakeRange {
            dst: r(dst),
            lo: lo.as_ref().map(r),
            hi: hi.as_ref().map(r),
            exclusive: *exclusive,
        },
        Inst::MakeRegexp { dst, source, flags } => Inst::MakeRegexp {
            dst: r(dst),
            source: r(source),
            flags: flags.clone(),
        },
        Inst::Interpolate { dst, parts, into } => Inst::Interpolate {
            dst: r(dst),
            into: into.map(|b| r(&b)),
            parts: parts
                .iter()
                .map(|p| match p {
                    StrPiece::Lit(i) => StrPiece::Lit(cst(*i)),
                    StrPiece::Val(x) => StrPiece::Val(r(x)),
                })
                .collect(),
        },
        Inst::ToSym { dst, src } => Inst::ToSym {
            dst: r(dst),
            src: r(src),
        },
        Inst::IsArray { dst, src } => Inst::IsArray {
            dst: r(dst),
            src: r(src),
        },
        Inst::IsHash { dst, src } => Inst::IsHash {
            dst: r(dst),
            src: r(src),
        },
        Inst::IsObject { dst, src } => Inst::IsObject {
            dst: r(dst),
            src: r(src),
        },
        Inst::ToArray { dst, src } => Inst::ToArray {
            dst: r(dst),
            src: r(src),
        },
        Inst::Len { dst, src } => Inst::Len {
            dst: r(dst),
            src: r(src),
        },
        Inst::ArrayGet { dst, arr, index } => Inst::ArrayGet {
            dst: r(dst),
            arr: r(arr),
            index: *index,
        },
        Inst::ArraySlice {
            dst,
            arr,
            from,
            drop_last,
        } => Inst::ArraySlice {
            dst: r(dst),
            arr: r(arr),
            from: *from,
            drop_last: *drop_last,
        },
        Inst::ArrayGetReg {
            dst,
            arr,
            index,
            borrow,
            objects,
        } => Inst::ArrayGetReg {
            dst: r(dst),
            arr: r(arr),
            index: r(index),
            borrow: *borrow,
            objects: *objects,
        },
        Inst::ArrayIndex {
            dst,
            arr,
            index,
            word,
        } => Inst::ArrayIndex {
            dst: r(dst),
            arr: r(arr),
            index: r(index),
            word: *word,
        },
        Inst::BytesIndex {
            dst,
            bytes,
            index,
            method,
        } => Inst::BytesIndex {
            dst: r(dst),
            bytes: r(bytes),
            index: r(index),
            method: *method,
        },
        Inst::ArrayNewWords {
            dst,
            capacity,
            float,
        } => Inst::ArrayNewWords {
            dst: r(dst),
            capacity: r(capacity),
            float: *float,
        },
        Inst::ArrayPushWord { arr, src, float } => Inst::ArrayPushWord {
            arr: r(arr),
            src: r(src),
            float: *float,
        },
        Inst::ArrayWords { dst, arr, float } => Inst::ArrayWords {
            dst: r(dst),
            arr: r(arr),
            float: *float,
        },
        Inst::ArrayGetWord {
            dst,
            arr,
            index,
            float,
        } => Inst::ArrayGetWord {
            dst: r(dst),
            arr: r(arr),
            index: r(index),
            float: *float,
        },
        Inst::ArraySliceReg { dst, arr, from, to } => Inst::ArraySliceReg {
            dst: r(dst),
            arr: r(arr),
            from: r(from),
            to: r(to),
        },
        Inst::ClearRegs { from, to } => Inst::ClearRegs {
            from: r(from),
            to: r(to),
        },
        Inst::ArrayPush { arr, src } => Inst::ArrayPush {
            arr: r(arr),
            src: r(src),
        },
        Inst::ObjectFields { dst, src } => Inst::ObjectFields {
            dst: r(dst),
            src: r(src),
        },
        Inst::HashGetSym {
            dst,
            found,
            hash,
            key,
        } => Inst::HashGetSym {
            dst: r(dst),
            found: r(found),
            hash: r(hash),
            key: cst(*key),
        },
        Inst::HashRest { dst, hash, keys } => Inst::HashRest {
            dst: r(dst),
            hash: r(hash),
            keys: keys.iter().map(|k| cst(*k)).collect(),
        },
        Inst::CatchException { dst } => Inst::CatchException { dst: r(dst) },
        Inst::CatchAny { dst } => Inst::CatchAny { dst: r(dst) },
        Inst::Rescuing { src, enter } => Inst::Rescuing {
            src: r(src),
            enter: *enter,
        },
        Inst::NoMatch { src, is_assert } => Inst::NoMatch {
            src: r(src),
            is_assert: *is_assert,
        },
        Inst::MarkUsable { obj } => Inst::MarkUsable { obj: r(obj) },
    }
}
