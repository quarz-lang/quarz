//! The facts compiled code trusts, checked as the interpreter runs
//! (`QUARZ_VERIFY`). Lowering leaves what the checker's types say on some
//! instructions (an array's elements stored as words, an object's class,
//! the `Int` method of an operator), which the interpreter does not need
//! and compiled code reads without a check, or with one that only says a
//! type went wrong somewhere. With the variable set, the interpreter checks
//! each of them before trusting it; a violated one is a bug in the checker
//! or in lowering, so it stops the program, with what was violated and
//! where, rather than raise something a `rescue` could hide.

use std::sync::OnceLock;

use quarz_ir::{FieldKind, FuncInfo, FuncKind, Inst, RtParamKind};

use crate::interp::Interp;
use crate::rc::Rc;
use crate::value::{ArrayData, Value};

/// Whether `QUARZ_VERIFY` asks for the checks (`1`, or `moves`, which
/// asks for more), read once.
pub fn enabled() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| {
        std::env::var("QUARZ_VERIFY").is_ok_and(|v| matches!(v.as_str(), "1" | "moves"))
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
            recv, args, moved, ..
        } if *moved != 0 => {
            for (i, a) in args.iter().enumerate().take(15) {
                if moved & (1 << i) != 0 {
                    shadow[*a as usize] = true;
                }
            }
            if let Some(r) = recv.filter(|_| moved & (1 << 15) != 0) {
                shadow[r as usize] = true;
            }
        }
        _ => {}
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
                let world = &self.program.world;
                let Value::Object(o) = &regs[*obj as usize] else {
                    return self.violated(format!(
                        "{name} of {} on {}",
                        world.classes[*class as usize].name,
                        describe(&regs[*obj as usize])
                    ));
                };
                if !world.class_is_a(o.class, *class) {
                    return self.violated(format!(
                        "{name} of {} on a {}",
                        world.classes[*class as usize].name, world.classes[o.class as usize].name
                    ));
                }
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

    /// Check what `inst` trusts about its result, after it ran.
    pub(crate) fn verify_after(&self, f: &FuncInfo, regs: &[Value], inst: &Inst) {
        match inst {
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
