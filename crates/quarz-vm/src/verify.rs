//! The facts compiled code trusts, checked as the interpreter runs
//! (`QUARZ_VERIFY`). Lowering leaves what the checker's types say on some
//! instructions (an array's elements stored as words, an object's class,
//! the `Int` method of an operator), which the interpreter does not need
//! and compiled code reads without a check, or with one that only says a
//! type went wrong somewhere. With the variable set (or, in a debug build,
//! unless it is `0`), the interpreter checks
//! each of them before trusting it; a violated one is a bug in the checker
//! or in lowering, so it stops the program, with what was violated and
//! where, rather than raise something a `rescue` could hide.

use std::sync::OnceLock;

use quarz_ir::{Block, FuncId};

use quarz_ir::{FieldKind, FuncInfo, FuncKind, Inst, RtParamKind};

/// `Interp::verify_heap`'s entry, by function id.
pub(crate) type Heap = Rc<Vec<bool>>;

use crate::interp::Interp;
use crate::rc::Rc;
use crate::value::{ArrayData, Value};

/// Whether the facts are checked, read once: `QUARZ_VERIFY` set to `1`,
/// or `moves` (which asks for more); unset, in a debug build (#536 step
/// 10), so that a debug `quarz` used outside cargo checks them too. Any
/// other value (`0`) turns them off.
pub fn enabled() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| match std::env::var("QUARZ_VERIFY") {
        Ok(v) => matches!(v.as_str(), "1" | "moves"),
        Err(_) => cfg!(debug_assertions),
    })
}

/// Whether it also asks for the moved shadow (`moves`): the interpreter
/// tracks which registers a value moved out of, or whose scope ended,
/// and stops at a read of one before it is written again.
pub fn moves() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| std::env::var("QUARZ_VERIFY").is_ok_and(|v| v == "moves"))
}

/// What `inst` moves out of its operands (when it runs, even if it
/// then raises): a `Take`'s source, a call's moved operands.
fn moved_out(inst: &Inst, shadow: &mut [bool]) {
    match inst {
        Inst::Take { src, .. } => shadow[*src as usize] = true,
        Inst::Call {
            recv,
            args,
            kw,
            moved,
            kw_moved,
            ..
        } if *moved != 0 || *kw_moved != 0 => {
            for (i, a) in args.iter().enumerate().take(15) {
                if moved & (1 << i) != 0 {
                    shadow[*a as usize] = true;
                }
            }
            if let Some(r) = recv.filter(|_| moved & (1 << 15) != 0) {
                shadow[r as usize] = true;
            }
            kw_moved_out(kw, *kw_moved, shadow);
        }
        Inst::OwnedCall {
            args,
            kw,
            moved,
            kw_moved,
            ..
        } if *moved != 0 || *kw_moved != 0 => {
            for (i, a) in args.iter().enumerate().take(15) {
                if moved & (1 << i) != 0 {
                    shadow[*a as usize] = true;
                }
            }
            kw_moved_out(kw, *kw_moved, shadow);
        }
        _ => {}
    }
}

/// The keyword arguments a call moved in (`Inst::Call::kw_moved`).
fn kw_moved_out(kw: &[(u32, quarz_ir::Reg)], kw_moved: u16, shadow: &mut [bool]) {
    for (i, (_, r)) in kw.iter().enumerate().take(16) {
        if kw_moved & (1 << i) != 0 {
            shadow[*r as usize] = true;
        }
    }
}

fn is_int(v: &Value) -> bool {
    // Only a machine Int: a big one is an `Integer` (`value::integer`),
    // and an `Int` that overflows raises.
    matches!(v, Value::Int(_))
}

/// `v` is a value of the machine-word type `kind`.
fn has_kind(v: &Value, kind: FieldKind) -> bool {
    match kind {
        FieldKind::Value => true,
        FieldKind::Int => is_int(v),
        FieldKind::Float => matches!(v, Value::Float(_)),
        FieldKind::Bool => matches!(v, Value::Bool(_)),
    }
}

/// `v` is a value of the class a declared type names, for the names a
/// fact uses (`Int`, `Float`); any other name is not checked.
fn has_type(v: &Value, ty: &str) -> bool {
    match ty {
        "Int" => is_int(v),
        "Float" => matches!(v, Value::Float(_)),
        _ => true,
    }
}

fn describe(v: &Value) -> &'static str {
    match v {
        Value::Nil => "nil",
        Value::Bool(_) => "a Bool",
        Value::Int(_) => "an Int",
        Value::BigInt(_) => "an Integer",
        Value::Float(_) => "a Float",
        Value::Array(_) => "an Array",
        Value::Object(_) => "an object",
        _ => "another value",
    }
}

fn storage(data: &ArrayData) -> &'static str {
    match data {
        ArrayData::Values(_) => "values",
        ArrayData::Ints(_) => "Ints",
        ArrayData::Floats(_) => "Floats",
        ArrayData::Objects(_) => "objects",
    }
}

fn words(float: bool) -> &'static str {
    if float {
        "Floats"
    } else {
        "Ints"
    }
}

impl Interp {
    /// Check what `inst` trusts about its operands, before it runs.
    pub(crate) fn verify_before(&self, regs: &[Value], inst: &Inst) {
        match inst {
            // A receiver of a class no check of the call saw (docs/05 §9):
            // the checks should have covered every class it can have.
            Inst::As {
                src,
                ty: quarz_ir::RtType::Nothing,
                name,
                ..
            } => self.violated(format!("{} is not {name}", describe(&regs[*src as usize]))),
            Inst::ArrayGetWord {
                arr, index, float, ..
            } => {
                let Value::Array(a) = &regs[*arr as usize] else {
                    return self.violated(format!(
                        "ArrayGetWord on {}, not an array",
                        describe(&regs[*arr as usize])
                    ));
                };
                let len = match (&**a, float) {
                    (ArrayData::Ints(xs), false) => xs.len(),
                    (ArrayData::Floats(xs), true) => xs.len(),
                    (data, _) => {
                        return self.violated(format!(
                            "ArrayGetWord of {} on an array of {}",
                            words(*float),
                            storage(data)
                        ))
                    }
                };
                match &regs[*index as usize] {
                    Value::Int(i) if (0..len as i64).contains(i) => {}
                    Value::Int(i) => {
                        self.violated(format!("ArrayGetWord index {i} out of range (len {len})"))
                    }
                    v => self.violated(format!("ArrayGetWord index is {}", describe(v))),
                }
            }
            Inst::ArrayPushWord { arr, src, float } => {
                let src = &regs[*src as usize];
                let ok = if *float {
                    matches!(src, Value::Float(_))
                } else {
                    matches!(src, Value::Int(_))
                };
                if !ok {
                    return self.violated(format!(
                        "ArrayPushWord of {} pushes {}",
                        words(*float),
                        describe(src)
                    ));
                }
                match &regs[*arr as usize] {
                    Value::Array(a) => {
                        let stored = matches!(
                            (&**a, float),
                            (ArrayData::Ints(_), false) | (ArrayData::Floats(_), true)
                        );
                        if !stored {
                            return self.violated(format!(
                                "ArrayPushWord of {} on an array of {}",
                                words(*float),
                                storage(a)
                            ));
                        }
                        if Rc::strong_count(a) != 1 {
                            self.violated(format!(
                                "ArrayPushWord on an array with {} references",
                                Rc::strong_count(a)
                            ));
                        }
                    }
                    v => self.violated(format!("ArrayPushWord on {}", describe(v))),
                }
            }
            // A field `FieldTake` took is never read again (#704).
            Inst::FieldGet { obj, index, .. } if matches!(&regs[*obj as usize], Value::Object(o) if crate::value::was_taken(o, *index as usize)) => {
                self.violated(format!(
                    "FieldGet of field {index}, which a FieldTake took (#704)"
                ))
            }
            Inst::FieldGet {
                obj, index, class, ..
            }
            | Inst::FieldSet {
                obj, index, class, ..
            } if *class != u32::MAX => {
                let name = if matches!(inst, Inst::FieldGet { .. }) {
                    "FieldGet"
                } else {
                    "FieldSet"
                };
                if let Some(what) = self.field_class_violation(name, &regs[*obj as usize], *class) {
                    return self.violated(what);
                }
                let world = &self.program.world;
                if let Inst::FieldSet { src, .. } = inst {
                    let kind = self.field_kind(*class, *index);
                    let v = &regs[*src as usize];
                    if !has_kind(v, kind) {
                        self.violated(format!(
                            "FieldSet of {}'s {:?} field {index} stores {}",
                            world.classes[*class as usize].name,
                            kind,
                            describe(v)
                        ));
                    }
                }
            }
            Inst::BinOp {
                lhs,
                rhs,
                method: Some(m),
                ..
            } => {
                let world = &self.program.world;
                let m = self.program.method(*m);
                let owner = if m.owner == world.builtin.int {
                    "Int"
                } else if m.owner == world.builtin.float {
                    "Float"
                } else {
                    return;
                };
                let (l, r) = (&regs[*lhs as usize], &regs[*rhs as usize]);
                if !has_type(l, owner) {
                    return self.violated(format!("BinOp {owner}#{} on {}", m.name, describe(l)));
                }
                if let Some(ty) = m.params.first().and_then(|p| p.ty.as_deref()) {
                    if !has_type(r, ty) {
                        self.violated(format!(
                            "BinOp {owner}#{}({ty}) with {}",
                            m.name,
                            describe(r)
                        ));
                    }
                }
            }
            _ => {}
        }
    }

    /// What is wrong with reading or writing (`name`) a field of `class`
    /// on `v`, if anything: it must be an object of `class` or below. The
    /// interpreter's check of `FieldGet`/`FieldSet`, and compiled code's
    /// of its `FieldGet` and `FieldSet` fast paths (`ffi::qz_verify_field_class`).
    pub(crate) fn field_class_violation(
        &self,
        name: &str,
        v: &Value,
        class: u32,
    ) -> Option<String> {
        let world = &self.program.world;
        let Value::Object(o) = v else {
            return Some(format!(
                "{name} of {} on {}",
                world.classes[class as usize].name,
                describe(v)
            ));
        };
        (!world.class_is_a(o.class, class)).then(|| {
            format!(
                "{name} of {} on a {}",
                world.classes[class as usize].name, world.classes[o.class as usize].name
            )
        })
    }

    /// Check what `inst` trusts about its result, after it ran.
    pub(crate) fn verify_after(&self, f: &FuncInfo, regs: &[Value], inst: &Inst) {
        match inst {
            // (Compiled code keeps the result as a machine word.)
            Inst::BytesIndex { dst, .. } => {
                let v = &regs[*dst as usize];
                if !is_int(v) {
                    self.violated(format!("BytesIndex gives {}", describe(v)));
                }
            }
            Inst::ArrayIndex {
                dst,
                word: Some(float),
                ..
            } => {
                let v = &regs[*dst as usize];
                let ok = if *float {
                    matches!(v, Value::Float(_))
                } else {
                    is_int(v)
                };
                if !ok {
                    self.violated(format!(
                        "ArrayIndex of an Array[{}] gives {}",
                        if *float { "Float" } else { "Int" },
                        describe(v)
                    ));
                }
            }
            Inst::ArrayGetReg {
                dst,
                arr,
                index,
                objects: true,
                ..
            } => {
                let in_range = match (&regs[*arr as usize], &regs[*index as usize]) {
                    (Value::Array(a), Value::Int(i)) => (0..a.len() as i64).contains(i),
                    _ => false,
                };
                let v = &regs[*dst as usize];
                if in_range && !matches!(v, Value::Object(_)) {
                    self.violated(format!("ArrayGetReg of objects gives {}", describe(v)));
                }
            }
            Inst::FieldGet {
                dst, index, class, ..
            } if *class != u32::MAX => {
                let kind = self.field_kind(*class, *index);
                let v = &regs[*dst as usize];
                if !has_kind(v, kind) {
                    self.violated(format!(
                        "FieldGet of {}'s {:?} field {index} gives {}",
                        self.program.world.classes[*class as usize].name,
                        kind,
                        describe(v)
                    ));
                }
            }
            Inst::Arg { dst, index } => {
                let FuncKind::Method(mid) = f.kind else {
                    return;
                };
                let m = self.program.method(mid);
                let Some(p) = m.params.get(*index as usize) else {
                    return;
                };
                if p.kind != RtParamKind::Positional || p.has_default {
                    return;
                }
                let Some(ty @ ("Int" | "Float")) = p.ty.as_deref() else {
                    return;
                };
                let v = &regs[*dst as usize];
                if !has_type(v, ty) {
                    self.violated(format!(
                        "parameter {} of {} declared {ty} is {}",
                        p.name,
                        m.name,
                        describe(v)
                    ));
                }
            }
            _ => {}
        }
    }

    /// The moved shadow, before `inst` runs: none of its operands is a
    /// register a value moved out of or whose scope ended.
    pub(crate) fn shadow_reads(&self, shadow: &[bool], inst: &Inst) {
        for r in inst.uses() {
            if shadow[r as usize] {
                self.violated(format!(
                    "{} reads r{r}, moved out or released before",
                    inst_name(inst)
                ));
            }
        }
    }

    /// The same for a terminator's operand.
    pub(crate) fn shadow_term(&self, shadow: &[bool], term: &quarz_ir::Term) {
        if let Some(r) = term.uses() {
            if shadow[r as usize] {
                self.violated(format!(
                    "the terminator reads r{r}, moved out or released before"
                ));
            }
        }
    }

    /// The shadow after `inst` ran (`ok`) or raised: its moved operands
    /// gone either way; on success its results written (valid again)
    /// and a released variable's scope ended.
    pub(crate) fn shadow_after(shadow: &mut [bool], inst: &Inst, ok: bool) {
        moved_out(inst, shadow);
        if !ok {
            return;
        }
        for r in inst.defs() {
            shadow[r as usize] = false;
        }
        if let Inst::Release { src } = inst {
            shadow[*src as usize] = true;
        }
    }

    /// `live::heap_possible` of function `fid`, found once: a function id
    /// names one body for the interpreter's life (its function tables are
    /// extend-only: an entry is never replaced, moved or removed, a failed
    /// REPL input's included, docs/05 §7).
    pub(crate) fn verify_heap(&self, fid: FuncId, f: &FuncInfo, blocks: &[Block]) -> Heap {
        let mut cache = self.verify_heap.borrow_mut();
        let i = fid as usize;
        if cache.len() <= i {
            cache.resize(i + 1, None);
        }
        match &cache[i] {
            Some(heap) => heap.clone(),
            None => {
                let heap = Rc::new(quarz_ir::live::heap_possible_in(
                    f.nregs,
                    blocks,
                    &f.consts,
                    f.kind,
                    &self.program.world.methods,
                ));
                cache[i] = Some(heap.clone());
                heap
            }
        }
    }

    /// #536 step 9: a register `live::heap_possible` leaves out holds no
    /// counted value after `inst` wrote it. Compiled code shares that
    /// analysis (`gen.rs`) and never releases such a register, so a
    /// counted value there would leak, or be read as a number.
    pub(crate) fn verify_heap_after(
        &self,
        f: &FuncInfo,
        heap: &[bool],
        regs: &[Value],
        inst: &Inst,
    ) {
        for r in inst.defs() {
            let v = &regs[r as usize];
            if !heap.get(r as usize).copied().unwrap_or(true)
                && (v.type_tag() as u64) >= crate::value::NEEDS_DROP_FROM
            {
                self.violated(format!(
                    "{} in {} wrote {} to r{r}, which `live::heap_possible` says holds no counted value",
                    inst_name(inst),
                    f.name,
                    describe(v)
                ));
            }
        }
    }

    /// The machine-word kind of field `index` of `class`, by this
    /// program's classes (the layouts objects carry may be another
    /// program's in a process that runs several).
    fn field_kind(&self, class: u32, index: u32) -> FieldKind {
        let fields = &self.program.world.classes[class as usize].fields;
        let mut cache = self.verify_kinds.borrow_mut();
        if cache.len() <= class as usize {
            cache.resize(class as usize + 1, None);
        }
        cache[class as usize]
            .get_or_insert_with(|| quarz_ir::field_slots(fields).kinds)
            .get(index as usize)
            .copied()
            .unwrap_or(FieldKind::Value)
    }

    /// Report a violated fact and stop: it is a bug in the checker or in
    /// lowering, which the program must not go on past (nor rescue).
    #[cold]
    pub(crate) fn violated(&self, what: String) {
        self.flush();
        let mut msg = format!("quarz: internal error: QIR fact violated: {what}\n");
        for frame in self.capture_backtrace() {
            msg.push_str("    from ");
            msg.push_str(&frame);
            msg.push('\n');
        }
        // Straight to the stream: a test harness capturing `eprint!` would
        // lose it with the process.
        use std::io::Write;
        let _ = std::io::stderr().write_all(msg.as_bytes());
        std::process::exit(101);
    }
}

/// The instruction's kind, for messages.
fn inst_name(inst: &Inst) -> String {
    let s = format!("{inst:?}");
    s.split([' ', '{', '(']).next().unwrap_or("").to_string()
}

/// The frame slots `Task.blocking` moved a capture out of (#478), by
/// frame address, while the moved shadow is on: reading one before it is
/// written again is a bug in `live::blocking_takes`. (Global: a task may
/// move to another worker thread.)
static TAKEN: std::sync::Mutex<Vec<(usize, u32)>> = std::sync::Mutex::new(Vec::new());

/// Slot `slot` of the frame at `frame` was moved out.
pub fn frame_taken(frame: *const u8, slot: u32) {
    if moves() {
        TAKEN.lock().unwrap().push((frame as usize, slot));
    }
}

/// The frame at `frame` is freed: its address may be another's next.
pub fn frame_dropped(frame: *const u8) {
    if moves() {
        let mut taken = TAKEN.lock().unwrap();
        if !taken.is_empty() {
            taken.retain(|(f, _)| *f != frame as usize);
        }
    }
}

impl Interp {
    /// The moved shadow of frame slots: `inst` reading a slot that
    /// `Task.blocking` moved out stops the program; writing it makes it
    /// valid again.
    pub(crate) fn shadow_frame(&self, act: &crate::vm::Activation, inst: &Inst) {
        let (depth, slot, write) = match inst {
            Inst::FrameGet { depth, slot, .. } => (*depth, *slot, false),
            Inst::OwnedCall {
                recv: quarz_ir::VarLoc::Frame { depth, slot },
                ..
            } => (*depth, *slot, false),
            Inst::FrameSet { depth, slot, .. } => (*depth, *slot, true),
            _ => return,
        };
        let mut taken = TAKEN.lock().unwrap();
        if taken.is_empty() {
            return;
        }
        let mut frame: &crate::value::Frame = self.frame(act);
        for _ in 0..depth {
            match frame.parent.as_deref() {
                Some(p) => frame = p,
                None => return,
            }
        }
        let key = (std::ptr::from_ref(frame).cast::<u8>() as usize, slot);
        if write {
            taken.retain(|k| *k != key);
        } else if taken.contains(&key) {
            drop(taken);
            self.violated(format!(
                "{} reads frame slot {slot} (depth {depth}), which Task.blocking moved out",
                inst_name(inst)
            ));
        }
    }
}
