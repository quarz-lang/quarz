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

use std::collections::HashMap;

use quarz_ir::*;

/// The largest body (in instructions) worth inlining.
const MAX_INSTS: usize = 40;

/// Inline the eligible calls of every function in `functions` (indexed
/// by `FuncId`), `passes` levels deep.
pub fn inline_calls(functions: &mut [Function], methods: &[RtMethod], passes: usize) {
    for _ in 0..passes {
        inline_pass(functions, methods);
    }
}

fn inline_pass(functions: &mut [Function], methods: &[RtMethod]) {
    let orig: Vec<Function> = functions.to_vec();
    let eligible: Vec<bool> = orig.iter().map(eligible_callee).collect();
    for g in functions.iter_mut() {
        inline_into(g, &orig, &eligible, methods);
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
                )
            })
    })
}

/// The callee of a call that can be inlined: its function, receiver
/// register (`None` = the caller's `self`), argument registers and
/// destination.
struct Site {
    fid: FuncId,
    recv: Option<Reg>,
    args: Vec<Reg>,
    dst: Reg,
}

fn site(inst: &Inst, eligible: &[bool], methods: &[RtMethod]) -> Option<Site> {
    let Inst::Call {
        dst,
        kind: CallKind::Method(mid),
        recv,
        args,
        splat: false,
        kw,
        kw_splat: None,
        block: None,
    } = inst
    else {
        return None;
    };
    if !kw.is_empty() {
        return None;
    }
    let m = methods.get(*mid as usize)?;
    let fid = m.func?;
    let bound = m.synth == RtSynth::None
        && !m.is_abstract
        && !m.has_block
        && m.native_key.is_none()
        && (!m.overridden || m.singleton || m.is_extension)
        && m.params.len() == args.len()
        && m.params
            .iter()
            .all(|p| p.kind == RtParamKind::Positional && !p.has_default);
    if !bound || !eligible.get(fid as usize).copied().unwrap_or(false) {
        return None;
    }
    Some(Site {
        fid,
        recv: *recv,
        args: args.clone(),
        dst: *dst,
    })
}

fn inline_into(g: &mut Function, orig: &[Function], eligible: &[bool], methods: &[RtMethod]) {
    let blocks = std::mem::take(&mut g.blocks);
    let n = blocks.len();
    let mut out: Vec<Block> = vec![Block::default(); n];
    let mut extra: Vec<Option<Block>> = Vec::new();
    let mut origins: HashMap<(FuncId, u32, u32), u32> = HashMap::new();
    for (bi, blk) in blocks.into_iter().enumerate() {
        let handler = blk.handler;
        let mut cur = Block {
            handler,
            ..Default::default()
        };
        let mut cur_id = bi;
        let lines = blk.lines;
        for (i, inst) in blk.insts.into_iter().enumerate() {
            let line = lines[i];
            let Some(s) = site(&inst, eligible, methods) else {
                cur.insts.push(inst);
                cur.lines.push(line);
                continue;
            };
            let f = &orig[s.fid as usize];
            let base_reg = g.nregs;
            g.nregs += f.nregs;
            let cont_id = n + extra.len();
            extra.push(None);
            let base_blk = n + extra.len();
            let const_map: Vec<u32> = f.consts.iter().map(|c| const_index(g, c)).collect();
            // A line of the callee becomes an origin entry here; a line
            // the callee itself inlined (flagged) becomes a chain of them.
            let mut origin = |l: u32| -> u32 { map_line(g, &mut origins, f, s.fid, l, line) };
            // The callee's registers start as nil, as in a fresh
            // activation (and a previous pass through this code leaves
            // nothing behind).
            cur.insts.push(Inst::ClearRegs {
                from: base_reg,
                to: base_reg + f.nregs,
            });
            cur.lines.push(line);
            for cb in &f.blocks {
                let mut nb = Block {
                    handler,
                    term_line: origin(cb.term_line),
                    ..Default::default()
                };
                for (k, ci) in cb.insts.iter().enumerate() {
                    let copied = match ci {
                        Inst::Arg { dst, index } => Inst::Move {
                            dst: base_reg + dst,
                            src: s.args[*index as usize],
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
                            // call on the receiver here.
                            if let (
                                Some(r),
                                Inst::Call {
                                    kind: CallKind::Method(_) | CallKind::Send(_),
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
                    nb.lines.push(origin(cb.lines[k]));
                }
                nb.term = match &cb.term {
                    Term::Return(r) => {
                        nb.insts.push(Inst::Move {
                            dst: s.dst,
                            src: base_reg + r,
                        });
                        nb.lines.push(origin(cb.term_line));
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
                extra.push(Some(nb));
            }
            cur.term = Term::Jump(base_blk as BlockId);
            cur.term_line = line;
            store(&mut out, &mut extra, cur_id, cur);
            cur = Block {
                handler,
                ..Default::default()
            };
            cur_id = cont_id;
        }
        cur.term = blk.term;
        cur.term_line = blk.term_line;
        store(&mut out, &mut extra, cur_id, cur);
    }
    out.extend(extra.into_iter().map(|b| b.expect("block filled")));
    g.blocks = out;
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
    let r = |x: &Reg| base + *x;
    let rs = |xs: &[Reg]| xs.iter().map(|x| base + *x).collect::<Vec<_>>();
    let kw = |xs: &[(u32, Reg)]| {
        xs.iter()
            .map(|(k, v)| (consts[*k as usize], base + *v))
            .collect::<Vec<_>>()
    };
    match inst {
        Inst::LoadConst { dst, idx } => Inst::LoadConst {
            dst: r(dst),
            idx: consts[*idx as usize],
        },
        Inst::Move { dst, src } => Inst::Move {
            dst: r(dst),
            src: r(src),
        },
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
            name: consts[*name as usize],
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
        } => Inst::Call {
            dst: r(dst),
            kind: kind.clone(),
            recv: recv.as_ref().map(r),
            args: rs(args),
            splat: *splat,
            kw: kw(kws),
            kw_splat: kw_splat.as_ref().map(r),
            block: block.as_ref().map(r),
        },
        Inst::OwnedCall {
            dst,
            method,
            recv,
            args,
            kw: kws,
        } => Inst::OwnedCall {
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
        Inst::MethodRef { dst, recv, name } => Inst::MethodRef {
            dst: r(dst),
            recv: r(recv),
            name: consts[*name as usize],
        },
        Inst::SymbolProc { dst, name, method } => Inst::SymbolProc {
            dst: r(dst),
            name: consts[*name as usize],
            method: *method,
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
                    StrPiece::Lit(i) => StrPiece::Lit(consts[*i as usize]),
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
        Inst::ArrayGetReg { dst, arr, index } => Inst::ArrayGetReg {
            dst: r(dst),
            arr: r(arr),
            index: r(index),
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
            key: consts[*key as usize],
        },
        Inst::HashRest { dst, hash, keys } => Inst::HashRest {
            dst: r(dst),
            hash: r(hash),
            keys: keys.iter().map(|k| consts[*k as usize]).collect(),
        },
        Inst::CatchException { dst } => Inst::CatchException { dst: r(dst) },
        Inst::CatchAny { dst } => Inst::CatchAny { dst: r(dst) },
        Inst::NoMatch { src, is_assert } => Inst::NoMatch {
            src: r(src),
            is_assert: *is_assert,
        },
    }
}
