//! Which registers hold an unboxed number at each point of a function.
//!
//! Every register has a boxed home in memory that is always up to date
//! (stores write through). On top of that, a register whose value is
//! statically known to be an `Int` that fits a machine word, a `Float`
//! or a `Bool` is also kept in an SSA variable, so arithmetic on it needs
//! no tag test, no overflow-into-BigInt handling beyond a check, and no
//! release of the old value. The knowledge comes from constants, from the
//! overload the lowering recorded for an operator (`Int#+(Int)` says both
//! operands are Ints: an operand whose state is unknown is checked once
//! at run time, and a check that fails, which the static types rule out,
//! raises an internal error), and from copies. A forward dataflow analysis over the
//! basic blocks gives the state at each block's entry; the generator then
//! tracks it instruction by instruction with the same transfer function.

use quarz_ir::*;

/// What is known about a register's current value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum State {
    /// Anything: only the boxed home is valid.
    Unknown,
    /// Nil, a boolean, a number or a class: no release needed on
    /// overwrite.
    NonHeap,
    Bool,
    Int,
    Float,
    /// An object (any class): the boxed home is valid, and the address of
    /// its allocation is also in a variable, so its fields are read
    /// without a tag test or a load of the home.
    Obj,
    /// An array: the boxed home is valid, and the address of its
    /// allocation is also in a variable (as for `Obj`), so its elements
    /// and length are read without a tag test or a load of the home.
    Arr,
}

impl State {
    pub fn meet(self, other: State) -> State {
        if self == other {
            self
        } else if !self.boxed() && !other.boxed() {
            State::NonHeap
        } else {
            State::Unknown
        }
    }

    /// Whether the home holds the value, which may be on the heap.
    pub fn boxed(self) -> bool {
        matches!(self, State::Unknown | State::Obj | State::Arr)
    }

    pub fn needs_release(self) -> bool {
        self.boxed()
    }
}

/// The static types of a binary operation's operands and result.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Num {
    Int,
    Float,
}

#[derive(Clone, Copy, Debug)]
pub struct BinTypes {
    pub lhs: Num,
    pub rhs: Num,
    /// `None` for a comparison (the result is a Bool).
    pub result: Option<Num>,
}

/// The operand types of a `BinOp` whose overload is known to be one of
/// Int's or Float's arithmetic or comparison methods.
pub fn bin_types(inst: &Inst, methods: &[RtMethod], builtin: &RtBuiltin) -> Option<BinTypes> {
    let Inst::BinOp {
        op,
        method: Some(mid),
        ..
    } = inst
    else {
        return None;
    };
    let m = methods.get(*mid as usize)?;
    let lhs = if m.owner == builtin.int {
        Num::Int
    } else if m.owner == builtin.float {
        Num::Float
    } else {
        return None;
    };
    let rhs = match m.params.first().and_then(|p| p.ty.as_deref()) {
        Some("Int") => Num::Int,
        Some("Float") => Num::Float,
        _ => return None,
    };
    let result = match op {
        FastOp::Add | FastOp::Sub | FastOp::Mul | FastOp::Div | FastOp::Mod => {
            if lhs == Num::Int && rhs == Num::Int {
                Some(Num::Int)
            } else {
                Some(Num::Float)
            }
        }
        FastOp::Lt | FastOp::Le | FastOp::Gt | FastOp::Ge | FastOp::Eq | FastOp::Ne => None,
        _ => return None,
    };
    Some(BinTypes { lhs, rhs, result })
}

/// `x == y` / `x != y` through `==(other: Object)` with both operands
/// unboxed numbers of one kind here: a machine comparison.
pub fn num_eq(inst: &Inst, st: &[State], methods: &[RtMethod], builtin: &RtBuiltin) -> Option<Num> {
    let Inst::BinOp {
        op: FastOp::Eq | FastOp::Ne,
        lhs,
        rhs,
        ..
    } = inst
    else {
        return None;
    };
    if bin_types(inst, methods, builtin).is_some() {
        return None;
    }
    match (st[*lhs as usize], st[*rhs as usize]) {
        (State::Int, State::Int) => Some(Num::Int),
        (State::Float, State::Float) => Some(Num::Float),
        _ => None,
    }
}

/// The registers an instruction may write.
pub fn defs(inst: &Inst) -> Vec<Reg> {
    inst.defs()
}

/// Instructions whose generated code reads no register's home except
/// through the states (so unboxed registers need no write-back first).
pub fn reads_no_home(inst: &Inst) -> bool {
    matches!(
        inst,
        Inst::LoadConst { .. }
            | Inst::Move { .. }
            | Inst::Take { .. }
            | Inst::SelfRef { .. }
            | Inst::Arg { .. }
            | Inst::BlockParam { .. }
            | Inst::FrameGet { .. }
            | Inst::FieldGet { .. }
            | Inst::ClassRef { .. }
            | Inst::MakeBlock { .. }
            | Inst::Not { .. }
            | Inst::ClassIs { .. }
            | Inst::IsNil { .. }
            | Inst::CatchException { .. }
            | Inst::CatchAny { .. }
            | Inst::ClearRegs { .. }
            | Inst::Release { .. }
    )
}

/// Of those, the ones that may still unwind to the block's handler
/// (which reads the homes).
pub fn may_unwind(inst: &Inst) -> bool {
    matches!(
        inst,
        Inst::BlockParam { .. }
            | Inst::FrameGet { .. }
            | Inst::FieldGet { .. }
            | Inst::MakeBlock { .. }
    )
}

pub use quarz_ir::live::liveness;
use quarz_ir::live::successors;

/// A typed entry's parameter or result type, passed as a machine value:
/// an `Int` or a `Float` as a word, a `Bool` as a byte, `Nil` (a result
/// only) as nothing, and any other parameter (`Boxed`) as the address
/// of the caller's value, which the caller keeps.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mach {
    Int,
    Float,
    Bool,
    Nil,
    Boxed,
}

impl Mach {
    pub fn of(ty: Option<&str>) -> Option<Mach> {
        match ty {
            Some("Int") => Some(Mach::Int),
            Some("Float") => Some(Mach::Float),
            Some("Bool") => Some(Mach::Bool),
            Some("Nil") => Some(Mach::Nil),
            _ => None,
        }
    }

    /// The state of a register holding a value of the type.
    pub fn state(self) -> State {
        match self {
            Mach::Int => State::Int,
            Mach::Float => State::Float,
            Mach::Bool => State::Bool,
            Mach::Nil => State::NonHeap,
            Mach::Boxed => State::Unknown,
        }
    }

    /// Whether a register in state `st` holds a value of the type in its
    /// variable (a `Nil` result is nil whatever the register's state:
    /// the checker sees to it).
    pub fn held(self, st: State) -> bool {
        matches!(
            (self, st),
            (Mach::Int, State::Int) | (Mach::Float, State::Float) | (Mach::Bool, State::Bool)
        ) || self == Mach::Nil
    }
}

/// The shape of a function's typed entry: parameters and result passed
/// as machine values (see `Gen::typed`).
#[derive(Clone, Debug)]
pub struct TypedSig {
    pub params: Vec<Mach>,
    pub ret: Mach,
}

/// The functions that get a typed entry, by id: a method whose
/// positional, non-defaulted parameters (at most six) are all declared
/// `Int`, `Float` or `Bool`, and its result one of those or `Nil`, with
/// no block, no frame of its own and nothing in the body that reads the
/// argument list.
pub fn typed_sigs(functions: &[Function], methods: &[RtMethod]) -> Vec<Option<TypedSig>> {
    functions
        .iter()
        .enumerate()
        .map(|(fid, f)| {
            let FuncKind::Method(mid) = f.kind else {
                return None;
            };
            let m = methods.get(mid as usize)?;
            if m.func != Some(fid as FuncId)
                || m.has_block
                || m.is_abstract
                || m.native_key.is_some()
                || m.synth != RtSynth::None
                || m.params.len() > 6
                || f.frame_size != 0
            {
                return None;
            }
            let params: Vec<Mach> = m
                .params
                .iter()
                .map(|p| {
                    if p.kind == RtParamKind::Positional && !p.has_default {
                        Some(match Mach::of(p.ty.as_deref()) {
                            Some(Mach::Nil) | None => Mach::Boxed,
                            Some(t) => t,
                        })
                    } else {
                        None
                    }
                })
                .collect::<Option<_>>()?;
            let ret = Mach::of(m.ret.as_deref())?;
            // (Nothing to unbox at all: the boxed body as it is.)
            if ret == Mach::Nil && params.iter().all(|p| *p == Mach::Boxed) {
                return None;
            }
            let plain = f.blocks.iter().all(|b| {
                b.insts.iter().all(|i| {
                    !matches!(
                        i,
                        Inst::MakeBlock { .. }
                            | Inst::BlockParam { .. }
                            | Inst::HasArg { .. }
                            | Inst::Call {
                                kind: CallKind::Yield,
                                ..
                            }
                    )
                })
            });
            plain.then_some(TypedSig { params, ret })
        })
        .collect()
}

/// The result type of a call that goes through a typed entry: a direct
/// call (bound to one body) of a function that has one.
pub fn call_num(inst: &Inst, methods: &[RtMethod], typed: &[Option<TypedSig>]) -> Option<Mach> {
    let Inst::Call {
        kind: CallKind::Method(mid),
        args,
        splat: false,
        kw,
        kw_splat: None,
        block: None,
        ..
    } = inst
    else {
        return None;
    };
    if !kw.is_empty() {
        return None;
    }
    let m = methods.get(*mid as usize)?;
    if m.native_key.is_some() || (m.overridden && !m.is_extension) || m.synth != RtSynth::None {
        return None;
    }
    let fid = m.func?;
    let sig = typed.get(fid as usize)?.as_ref()?;
    (sig.params.len() == args.len()).then_some(sig.ret)
}

/// A call to `Int#to_f` with an unboxed receiver: the conversion is
/// done inline (the receiver and the result register).
pub fn int_to_f(inst: &Inst, methods: &[RtMethod], st: &[State]) -> Option<(Reg, Reg)> {
    let Inst::Call {
        dst,
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
        return None;
    };
    let m = methods.get(*mid as usize)?;
    (args.is_empty()
        && kw.is_empty()
        && m.native_key.as_deref() == Some("Int#to_f")
        && st[*recv as usize] == State::Int)
        .then_some((*recv, *dst))
}

/// The declared type of a method's positional, non-defaulted parameter,
/// when it is Int or Float.
pub fn param_num(f: &Function, methods: &[RtMethod], index: u32) -> Option<Num> {
    let FuncKind::Method(mid) = f.kind else {
        return None;
    };
    let p = methods.get(mid as usize)?.params.get(index as usize)?;
    if p.kind != RtParamKind::Positional || p.has_default {
        return None;
    }
    num_of(p.ty.as_deref())
}

/// Whether a method's parameter `index` is a positional, non-defaulted
/// one declared `Bool`: read into its variable once (as a typed entry
/// receives it).
pub fn param_bool(f: &Function, methods: &[RtMethod], index: u32) -> bool {
    let FuncKind::Method(mid) = f.kind else {
        return false;
    };
    methods
        .get(mid as usize)
        .and_then(|m| m.params.get(index as usize))
        .is_some_and(|p| {
            p.kind == RtParamKind::Positional && !p.has_default && p.ty.as_deref() == Some("Bool")
        })
}

/// The declared type of a field, when it is Int or Float.
/// How field `index` of a `class` object is stored (see
/// `quarz_ir::field_slots`) and where, from the fields' start.
pub fn field_slot(classes: &[RtClass], class: ClassId, index: u32) -> (FieldKind, u32) {
    let fields = classes
        .get(class as usize)
        .map_or(&[][..], |c| &c.fields[..]);
    let slots = field_slots(fields);
    match slots.kinds.get(index as usize) {
        Some(k) => (*k, slots.offsets[index as usize]),
        // (Not a field of the class: as a value, which the runtime path
        // reads.)
        None => (FieldKind::Value, index * VALUE_BYTES),
    }
}

pub fn field_num(classes: &[RtClass], class: ClassId, index: u32) -> Option<Num> {
    let field = classes.get(class as usize)?.fields.get(index as usize)?;
    num_of(field.ty.as_deref())
}

fn num_of(name: Option<&str>) -> Option<Num> {
    match name {
        Some("Int") => Some(Num::Int),
        Some("Float") => Some(Num::Float),
        _ => None,
    }
}

/// Apply an instruction's effect on the states (the generator emits code
/// that matches this exactly).
pub fn transfer(
    inst: &Inst,
    st: &mut [State],
    f: &Function,
    methods: &[RtMethod],
    classes: &[RtClass],
    builtin: &RtBuiltin,
    typed: &[Option<TypedSig>],
) {
    // An update may replace an array's allocation (by a copy, when it is
    // shared): a push, or any method called on it.
    if let Inst::ArrayPush { arr: r, .. } | Inst::Call { recv: Some(r), .. } = inst {
        if st[*r as usize] == State::Arr {
            st[*r as usize] = State::Unknown;
        }
    }
    match inst {
        // A call through a typed entry leaves its result unboxed (the
        // caller checks a result that comes back boxed).
        Inst::Call { dst, .. } if call_num(inst, methods, typed).is_some() => {
            st[*dst as usize] = call_num(inst, methods, typed).map_or(State::Unknown, Mach::state);
        }
        Inst::Call { dst, .. } if int_to_f(inst, methods, st).is_some() => {
            st[*dst as usize] = State::Float;
        }
        Inst::ClearRegs { from, to } => {
            for r in *from..*to {
                st[r as usize] = State::NonHeap;
            }
        }
        Inst::Release { src } => st[*src as usize] = State::NonHeap,
        Inst::ClassRef { dst, .. } => st[*dst as usize] = State::NonHeap,
        // A parameter or field of a numeric type is checked once and
        // then known (a check that fails raises an internal error).
        Inst::Arg { dst, index } => {
            st[*dst as usize] = match param_num(f, methods, *index) {
                Some(n) => num_state(n),
                None if param_bool(f, methods, *index) => State::Bool,
                None => State::Unknown,
            };
        }
        // The object is one after its field is read or written (or the
        // instruction failed).
        Inst::FieldGet {
            dst,
            obj,
            class,
            index,
        } => {
            if obj != dst {
                st[*obj as usize] = State::Obj;
            }
            st[*dst as usize] = match field_num(classes, *class, *index) {
                Some(n) => num_state(n),
                // A Bool field is a word read into the variable.
                None if field_slot(classes, *class, *index).0 == FieldKind::Bool => State::Bool,
                None => State::Unknown,
            };
        }
        Inst::FieldSet { obj, .. } => st[*obj as usize] = State::Obj,
        Inst::SelfRef { dst } => {
            st[*dst as usize] = if self_is_object(f, methods, classes, builtin) {
                State::Obj
            } else {
                State::Unknown
            };
        }
        Inst::LoadConst { dst, idx } => {
            st[*dst as usize] = match f.consts[*idx as usize] {
                Constant::Int(_) => State::Int,
                Constant::Float(_) => State::Float,
                Constant::Bool(_) => State::Bool,
                Constant::Nil => State::NonHeap,
                _ => State::Unknown,
            };
        }
        Inst::Move { dst, src } => st[*dst as usize] = st[*src as usize],
        // The value moves; a boxed source is left nil.
        Inst::Take { dst, src } => {
            st[*dst as usize] = st[*src as usize];
            if dst != src && st[*src as usize].boxed() {
                st[*src as usize] = State::NonHeap;
            }
        }
        Inst::BinOp { dst, .. } if num_eq(inst, st, methods, builtin).is_some() => {
            st[*dst as usize] = State::Bool;
        }
        Inst::BinOp { dst, lhs, rhs, .. } => match bin_types(inst, methods, builtin) {
            Some(t) if !(t.result == Some(Num::Float) && float_mod(inst)) => {
                // The operands are checked (or already known) on the
                // fast path; the slow path leaves the function.
                st[*lhs as usize] = num_state(t.lhs);
                st[*rhs as usize] = num_state(t.rhs);
                st[*dst as usize] = match t.result {
                    Some(n) => num_state(n),
                    None => State::Bool,
                };
            }
            _ => st[*dst as usize] = State::Unknown,
        },
        Inst::Not { dst, .. }
        | Inst::IsNil { dst, .. }
        | Inst::HasArg { dst, .. }
        | Inst::Equal { dst, .. }
        | Inst::CaseEq { dst, .. }
        | Inst::IsArray { dst, .. }
        | Inst::IsHash { dst, .. }
        | Inst::IsObject { dst, .. }
        | Inst::ClassIsA { dst, .. }
        | Inst::ClassIs { dst, .. }
        | Inst::IsA { dst, .. } => st[*dst as usize] = State::Bool,
        // A length is always a machine-word Int, and the receiver an
        // array after it (the runtime does the others).
        Inst::Len { dst, src } => {
            if src != dst {
                st[*src as usize] = State::Arr;
            }
            st[*dst as usize] = State::Int;
        }
        // `ArrayWords` makes an array; its elements are words.
        Inst::ArrayWords { dst, .. }
        | Inst::MakeArray { dst, .. }
        | Inst::ArrayNewWords { dst, .. } => st[*dst as usize] = State::Arr,
        // The array stays one (the runtime grows it in place: nothing else
        // refers to it).
        Inst::ArrayPushWord { arr, .. } => st[*arr as usize] = State::Arr,
        // A result nothing reads is not written (for the calls compiled
        // inline, without keywords): the register is as it was.
        Inst::OwnedCall {
            dst,
            method,
            recv,
            args,
            unused,
            kw,
        } if kw.is_empty() => {
            // `xs = xs.push(v)`, compiled inline, leaves an array in the
            // register (see `Gen`'s `OwnedCall`).
            let push = args.len() == 1
                && methods
                    .get(*method as usize)
                    .and_then(|m| m.native_key.as_deref())
                    == Some("Array#push")
                && !matches!(recv, VarLoc::Reg(r) if *r == args[0]);
            if let VarLoc::Reg(r) = recv {
                st[*r as usize] = if push { State::Arr } else { State::Unknown };
            }
            if !*unused {
                st[*dst as usize] = State::Unknown;
            }
        }
        Inst::ArrayIndex { dst, arr, word, .. } => {
            if arr != dst {
                st[*arr as usize] = State::Arr;
            }
            st[*dst as usize] = match word {
                Some(true) => State::Float,
                Some(false) => State::Int,
                None => State::Unknown,
            };
        }
        Inst::ArrayGetWord {
            dst, arr, float, ..
        } => {
            if arr != dst {
                st[*arr as usize] = State::Arr;
            }
            st[*dst as usize] = if *float { State::Float } else { State::Int };
        }
        // So is the array an element is read from.
        Inst::ArrayGetReg { dst, arr, .. } => {
            if arr != dst {
                st[*arr as usize] = State::Arr;
            }
            st[*dst as usize] = State::Unknown;
        }
        _ => {
            for r in defs(inst) {
                st[r as usize] = State::Unknown;
            }
        }
    }
}

/// Whether `self` in `f` is always an object: an instance method of a
/// class whose instances are objects (a class of the program's own, or
/// built on exceptions only, a `data` type, a variant), not of a module
/// (its `self` is whatever includes it) or of a built-in value class.
pub fn self_is_object(
    f: &Function,
    methods: &[RtMethod],
    classes: &[RtClass],
    builtin: &RtBuiltin,
) -> bool {
    let FuncKind::Method(mid) = f.kind else {
        return false;
    };
    let Some(m) = methods.get(mid as usize) else {
        return false;
    };
    if m.singleton || m.is_extension {
        return false;
    }
    let Some(c) = classes.get(m.owner as usize) else {
        return false;
    };
    match c.kind {
        RtClassKind::Data | RtClassKind::Variant => true,
        RtClassKind::Class => c.ancestors.iter().all(|&a| {
            let ac = &classes[a as usize];
            a == builtin.object
                || ac.kind == RtClassKind::Module
                || ac.is_exception
                || (ac.file != 0 && ac.kind == RtClassKind::Class)
        }),
        _ => false,
    }
}

/// A `Float` remainder has no inline form; it stays on the generic path.
pub fn float_mod(inst: &Inst) -> bool {
    matches!(
        inst,
        Inst::BinOp {
            op: FastOp::Mod,
            ..
        }
    )
}

pub fn num_state(n: Num) -> State {
    match n {
        Num::Int => State::Int,
        Num::Float => State::Float,
    }
}

/// The state of every register at the entry of every block.
pub fn analyze(
    f: &Function,
    methods: &[RtMethod],
    classes: &[RtClass],
    builtin: &RtBuiltin,
    typed: &[Option<TypedSig>],
) -> Vec<Vec<State>> {
    let nregs = f.nregs as usize;
    let nblocks = f.blocks.len();
    // Unreached until proven otherwise: the meet identity is "all
    // known", represented by `None`.
    let mut entry: Vec<Option<Vec<State>>> = vec![None; nblocks];
    entry[0] = Some(vec![State::NonHeap; nregs]);
    // Handler blocks are entered from an unwind with only the boxed homes
    // valid.
    for blk in &f.blocks {
        if let Some(h) = blk.handler {
            entry[h.block as usize] = Some(vec![State::Unknown; nregs]);
        }
    }
    let mut changed = true;
    while changed {
        changed = false;
        for (i, blk) in f.blocks.iter().enumerate() {
            let Some(start) = entry[i].clone() else {
                continue;
            };
            let mut st = start;
            for inst in &blk.insts {
                transfer(inst, &mut st, f, methods, classes, builtin, typed);
            }
            let targets: Vec<(BlockId, Option<Reg>)> = match &blk.term {
                Term::Jump(t) => vec![(*t, None)],
                Term::Branch { cond, then, els } => {
                    vec![(*then, class_tested(blk, *cond)), (*els, None)]
                }
                _ => vec![],
            };
            for (t, obj) in targets {
                // Past a class test that held, the register holds an
                // object (the test read its allocation).
                let mut out = st.clone();
                if let Some(r) = obj {
                    out[r as usize] = State::Obj;
                }
                let slot = &mut entry[t as usize];
                let merged = match slot {
                    None => out,
                    Some(old) => old.iter().zip(&out).map(|(a, b)| a.meet(*b)).collect(),
                };
                if slot.as_ref() != Some(&merged) {
                    *slot = Some(merged);
                    changed = true;
                }
            }
        }
    }
    entry
        .into_iter()
        .map(|e| e.unwrap_or_else(|| vec![State::Unknown; nregs]))
        .collect()
}

/// The register a block's branch on `cond` tests the class of: `cond` is
/// the result of the block's last `ClassIs`, and neither it nor the
/// tested register is written after it.
pub fn class_tested(blk: &Block, cond: Reg) -> Option<Reg> {
    let (at, src) = blk
        .insts
        .iter()
        .enumerate()
        .rev()
        .find_map(|(i, inst)| match inst {
            Inst::ClassIs { dst, src, .. } if *dst == cond && dst != src => Some((i, *src)),
            _ => None,
        })?;
    let rewritten = blk.insts[at + 1..]
        .iter()
        .any(|inst| inst.defs().iter().any(|d| *d == cond || *d == src));
    (!rewritten).then_some(src)
}

/// The blocks of a typed entry that run before its frame is set up
/// (the stack check, the nil of the homes and result slots): those
/// whose code only computes on unboxed registers (numbers, comparisons,
/// copies, branches, a `return` of the declared type), entered only
/// from such blocks, starting with the entry block. Leaving the region
/// sets the frame up (on the edge, or before a runtime call), so a call that returns at once never touches its frame.
#[allow(clippy::too_many_arguments)]
pub fn pure_region(
    f: &Function,
    entry_states: &[Vec<State>],
    methods: &[RtMethod],
    classes: &[RtClass],
    builtin: &RtBuiltin,
    typed_all: &[Option<TypedSig>],
    sig: &TypedSig,
    heap: &[bool],
) -> Vec<bool> {
    let n = f.blocks.len();
    let mut region: Vec<bool> = (0..n)
        .map(|b| {
            let blk = &f.blocks[b];
            if blk.handler.is_some() {
                return false;
            }
            let mut st = entry_states[b].clone();
            for inst in &blk.insts {
                if !pure_inst(inst, &st, f, methods, builtin) {
                    return false;
                }
                transfer(inst, &mut st, f, methods, classes, builtin, typed_all);
            }
            match &blk.term {
                Term::Jump(_) => true,
                Term::Branch { cond, .. } => {
                    matches!(st[*cond as usize], State::Bool | State::Int | State::Float)
                }
                Term::Return(r) => {
                    sig.ret.held(st[*r as usize])
                        && (0..st.len()).all(|k| !heap[k] || !st[k].needs_release())
                }
                _ => false,
            }
        })
        .collect();
    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (b, blk) in f.blocks.iter().enumerate() {
        for s in successors(blk) {
            preds[s as usize].push(b);
        }
    }
    // Nothing set up may flow into the region.
    loop {
        let mut changed = false;
        for b in 0..n {
            if region[b] && preds[b].iter().any(|&p| !region[p]) {
                region[b] = false;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    if n > 0 && !region[0] {
        return vec![false; n];
    }
    region
}

/// Whether an instruction's code, in state `st`, works on unboxed
/// variables only: no home is read or written, nothing is released,
/// and only a failed speculation (which sets the frame up first) calls
/// out.
fn pure_inst(
    inst: &Inst,
    st: &[State],
    f: &Function,
    methods: &[RtMethod],
    builtin: &RtBuiltin,
) -> bool {
    let free = |r: Reg| !st[r as usize].needs_release();
    match inst {
        Inst::LoadConst { dst, idx } => {
            matches!(
                f.consts[*idx as usize],
                Constant::Bool(_) | Constant::Int(_) | Constant::Float(_)
            ) && free(*dst)
        }
        Inst::Move { dst, src } | Inst::Take { dst, src } => {
            dst == src
                || (matches!(st[*src as usize], State::Int | State::Float | State::Bool)
                    && free(*dst))
        }
        // A parameter received as a machine value (a boxed one is
        // counted into its register, which the frame set up later would
        // overwrite).
        Inst::Arg { dst, index } => {
            free(*dst)
                && (param_num(f, methods, *index).is_some() || param_bool(f, methods, *index))
        }
        Inst::BinOp { dst, lhs, rhs, .. } => {
            bin_types(inst, methods, builtin).is_some()
                && !float_mod(inst)
                && matches!(
                    (st[*lhs as usize], st[*rhs as usize]),
                    (State::Int, State::Int) | (State::Float, State::Float)
                )
                && free(*dst)
        }
        Inst::ClearRegs { from, to } => (*from..*to).all(free),
        Inst::Call { .. } => int_to_f(inst, methods, st).is_some_and(|(_, d)| free(d)),
        _ => false,
    }
}
