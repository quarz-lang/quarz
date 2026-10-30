//! Object, Nil, Bool, Class, Kernel, Comparable and Exception.

use crate::rc::Rc;
use std::hash::{Hash, Hasher};

use crate::interp::{Args, EvalResult, Flow, Interp, NativeFn};
use crate::value::*;
use quarz_ir::ClassId;
use smallvec::smallvec;

use super::{int, string};

pub fn register(m: &mut super::Registry<NativeFn>) {
    native!(m, "Object#==", obj_eq);
    native!(m, "Object#!=", obj_ne);
    native!(m, "Object#equal?", obj_equal);
    native!(m, "Object#hash", obj_hash);
    native!(m, "Object#to_s", obj_to_s);
    native!(m, "Object#inspect", obj_inspect);
    native!(m, "Object#nil?", obj_nil);
    native!(m, "Object#class", obj_class);
    native!(m, "Object#is_a?", |i, r, a| match a.arg(0) {
        Value::Class(cid) => Ok(Value::Bool(i.program.world.class_is_a(i.class_of(r), *cid))),
        _ => Err(i.err_type("is_a? takes a class")),
    });
    native!(m, "Object#frozen?", obj_frozen);
    native!(m, "Object#dup", obj_dup);
    native!(m, "Object#instance_exec", |i, r, a| {
        let b = super::block(i, &a)?;
        i.call_block_on(&b, Some(r.clone()), a.pos)
    });
    native!(m, "Type#name", class_name);
    // Reflection, at compile time only (docs/14 §4): the natives read the
    // declarations the compiler hands the interpreter (`Interp::reflect`).
    native!(m, "Type#fields", |i, r, _| {
        let class = reflected_class(i, r)?;
        let fields = reflect_of(i)?.fields(class);
        let out: Result<Vec<Value>, Flow> = fields.iter().map(|f| meta_field(i, f)).collect();
        Ok(Value::array(out?))
    });
    native!(m, "Type#field", |i, r, a| {
        let class = reflected_class(i, r)?;
        let Value::Symbol(name) = a.arg(0) else {
            return Err(i.err_type("field takes a symbol"));
        };
        let name = i.symbol_name(*name);
        let fields = reflect_of(i)?.fields(class);
        match fields.iter().find(|f| f.name.as_str() == &*name) {
            Some(f) => meta_field(i, f),
            None => Ok(Value::Nil),
        }
    });
    native!(m, "Type#methods", |i, r, _| {
        let class = reflected_class(i, r)?;
        let methods = reflect_of(i)?.methods(class);
        let out: Result<Vec<Value>, Flow> = methods.iter().map(|m| meta_method(i, m)).collect();
        Ok(Value::array(out?))
    });
    native!(m, "Type#method?", |i, r, a| {
        let class = reflected_class(i, r)?;
        let Value::Symbol(name) = a.arg(0) else {
            return Err(i.err_type("method? takes a symbol"));
        };
        let name = i.symbol_name(*name);
        Ok(Value::Bool(
            reflect_of(i)?
                .methods(class)
                .iter()
                .any(|m| m.name.as_str() == &*name),
        ))
    });
    native!(m, "Type#includes?", |i, r, a| {
        let class = reflected_class(i, r)?;
        let Value::Class(m) = a.arg(0) else {
            return Err(i.err_type("includes? takes a class"));
        };
        Ok(Value::Bool(i.program.world.class_is_a(class, *m)))
    });
    // Classes only: the values carry no type arguments.
    native!(m, "Type#<=", |i, r, a| match (r, a.arg(0)) {
        (Value::Class(c), Value::Class(d)) => Ok(Value::Bool(i.program.world.class_is_a(*c, *d))),
        _ => Err(i.err_type("Type#<= takes a class")),
    });
    // Generation (docs/14 §5), at compile time only: the block lifted to
    // a method of the class, recorded for the compiler.
    native!(m, "Meta::ClassDef#def_method", |i, r, a| def_method(
        i, r, &a, false
    ));
    native!(m, "Meta::ClassDef#def_class_method", |i, r, a| {
        def_method(i, r, &a, true)
    });
    native!(m, "Meta::ClassDef#def_field", |i, r, a| {
        let class = reflected_class(i, r)?;
        let Value::Symbol(name) = a.arg(0) else {
            return Err(i.err_type("def_field takes the field's name as a symbol"));
        };
        let Value::Class(ty) = a.arg(1) else {
            return Err(i.err_type("def_field takes the field's type as a class"));
        };
        let default = a.arg(2).clone();
        if !i.program.world.class_is_a(i.class_of(&default), *ty) {
            return Err(i.err_type(&format!(
                "the default of `@{}` is a {}, not a {}",
                i.symbol_name(*name),
                i.class_name(&default),
                i.program.world.class(*ty).name
            )));
        }
        let flag = |key: &str| -> Result<bool, Flow> {
            match a.kw(i, key) {
                None => Ok(false),
                Some(Value::Bool(b)) => Ok(*b),
                Some(_) => Err(i.err_type(&format!("{key}: takes a Bool"))),
            }
        };
        let (mutable, reader, writer) = (flag("var")?, flag("reader")?, flag("writer")?);
        if writer && !mutable {
            return Err(i.err_arg("writer: needs var: true, an assignable field"));
        }
        let request = crate::reflect::FieldRequest {
            class,
            name: i.symbol_name(*name).to_string(),
            ty: *ty,
            default,
            mutable,
            reader,
            writer,
        };
        reflect_of(i)?
            .def_field(i, request)
            .map_err(|m| i.err_runtime(&m))?;
        Ok(Value::Nil)
    });
    native!(m, "Meta::ClassDef#doc", |i, _, a| {
        let Some(text) = a.arg(0).as_str() else {
            return Err(i.err_type("doc takes a string"));
        };
        reflect_of(i)?.doc(text.to_string());
        Ok(Value::Nil)
    });
    native!(m, "Nil#to_a", |_, _, _| Ok(Value::array(vec![])));
    native!(m, "Nil#&", |_, _, _| Ok(Value::Bool(false)));
    native!(m, "Nil#|", |_, _, a| Ok(Value::Bool(a.arg(0).is_truthy())));
    native!(m, "Bool#&", bool_and);
    native!(m, "Bool#|", bool_or);
    native!(m, "Bool#^", bool_xor);
    native!(m, "Proc#arity", proc_arity);
    native!(m, "Exception#backtrace", exc_backtrace);
    native!(m, "Exception#full_message", exc_full_message);
    native!(m, "Exception#cause", exc_cause);
    native!(m, "Exception#==", exc_eq);
    native!(m, "Exception#hash", exc_hash);
    native!(m, "Exception#inspect", obj_inspect);
    native!(m, "Kernel#puts", kernel_puts);
    native!(m, "Kernel#print", kernel_print);
    native!(m, "Kernel#p", kernel_p);
    native!(m, "Kernel#pp", kernel_p);
    native!(m, "Kernel#warn", kernel_warn);
    native!(m, "Kernel#exit", kernel_exit);
    native!(m, "Kernel#abort", kernel_abort);
    native!(m, "Kernel#exit!", kernel_exit_now);
    native!(m, "Kernel#at_exit", kernel_at_exit);
    native!(m, "Kernel#gets", kernel_gets);
    native!(m, "Kernel#gets?", kernel_gets_opt);
    native!(m, "Kernel#readline", kernel_gets);
    native!(m, "Kernel#readlines", |i, _, _| {
        let mut lines = Vec::new();
        loop {
            match super::core_gets(i, false)? {
                Value::Nil => break,
                line => lines.push(line),
            }
        }
        Ok(Value::array(lines))
    });
    native!(m, "Kernel#printf", |i, _, a| {
        let fmt = string(i, a.arg(0), "format string")?;
        let text = format_values(i, fmt, &a.pos[1..])?;
        i.write_out(&text);
        Ok(Value::Nil)
    });
    native!(m, "Kernel#format", kernel_format);
    native!(m, "Kernel#sprintf", kernel_format);
    native!(m, "Kernel#Integer", kernel_integer);
    native!(m, "Kernel#Float", kernel_float);
    native!(m, "Kernel#String", kernel_string);
}

/// The default `==`: run where no class's own applies, or by `super`
/// from one, so it does not look the receiver's up again (which would
/// find that very method).
fn obj_eq(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    Ok(Value::Bool(interp.values_equal_default(recv, args.arg(0))?))
}

fn obj_ne(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    Ok(Value::Bool(!interp.values_equal(recv, args.arg(0))?))
}

fn obj_equal(_: &Interp, recv: &Value, args: Args) -> EvalResult {
    Ok(Value::Bool(recv.identical(args.arg(0))))
}

fn obj_hash(_: &Interp, recv: &Value, _: Args) -> EvalResult {
    let mut h = std::collections::hash_map::DefaultHasher::new();
    recv.hash(&mut h);
    Ok(Value::Int((h.finish() >> 1) as i64))
}

fn obj_to_s(interp: &Interp, recv: &Value, _: Args) -> EvalResult {
    match recv {
        Value::Object(_) => Ok(Value::string(interp.object_to_s(recv)?)),
        _ => Ok(Value::str(&interp.to_s(recv)?)),
    }
}

/// The default `inspect` (of `Object` and `Exception`): the receiver
/// formatted, not looked up again, which would find this very method.
fn obj_inspect(interp: &Interp, recv: &Value, _: Args) -> EvalResult {
    Ok(Value::string(interp.format_value(recv, true)?))
}

fn obj_nil(_: &Interp, recv: &Value, _: Args) -> EvalResult {
    Ok(Value::Bool(recv.is_nil()))
}

fn obj_class(interp: &Interp, recv: &Value, _: Args) -> EvalResult {
    Ok(Value::Class(interp.class_of(recv)))
}

fn obj_frozen(_: &Interp, recv: &Value, _: Args) -> EvalResult {
    Ok(Value::Bool(!matches!(
        recv,
        Value::ArrayBuilder(_)
            | Value::HashBuilder(_)
            | Value::SetBuilder(_)
            | Value::StringBuilder(_)
            | Value::BytesBuilder(_)
    )))
}

fn obj_dup(interp: &Interp, recv: &Value, _: Args) -> EvalResult {
    if let Value::Object(o) = recv {
        if crate::deinit::has(o.class) {
            // What it owns is released once: a copy would release it again.
            return Err(interp.err_type(&format!(
                "cannot dup {}: its class defines `deinitialize`",
                interp.class_name(recv)
            )));
        }
    }
    Ok(match recv {
        Value::ArrayBuilder(a) => Value::ArrayBuilder(Value::array_builder(a.borrow().clone())),
        Value::HashBuilder(h) => Value::HashBuilder(Value::hash_builder(
            super::collections::read(interp, h)?.clone(),
        )),
        Value::SetBuilder(s) => Value::SetBuilder(Value::set_builder(
            super::collections::read(interp, s)?.clone(),
        )),
        Value::StringBuilder(s) => {
            Value::StringBuilder(Rc::new(std::cell::RefCell::new(s.borrow().clone())))
        }
        Value::BytesBuilder(b) => {
            Value::BytesBuilder(Rc::new(std::cell::RefCell::new(b.borrow().clone())))
        }
        Value::Object(o) => Value::Object(Object::new(o.class, o.fields())),
        other => other.clone(),
    })
}

fn reflected_class(interp: &Interp, recv: &Value) -> Result<ClassId, Flow> {
    match recv {
        Value::Class(c) => Ok(*c),
        _ => Err(interp.err_type("reflection takes a class")),
    }
}

/// `def_method(name, params?, *, visibility:) { }` and
/// `def_class_method`: the block's function and what it captured, handed
/// to the compiler (`Reflect::generate`).
fn def_method(interp: &Interp, recv: &Value, a: &Args, singleton: bool) -> EvalResult {
    let what = if singleton {
        "def_class_method"
    } else {
        "def_method"
    };
    let class = reflected_class(interp, recv)?;
    let Value::Symbol(name) = a.arg(0) else {
        return Err(interp.err_type(&format!("{what} takes the method's name as a symbol")));
    };
    let name = interp.symbol_name(*name).to_string();
    let symbol = |v: &Value| -> Result<String, Flow> {
        match v {
            Value::Symbol(s) => Ok(interp.symbol_name(*s).to_string()),
            _ => Err(interp.err_type(&format!("{what} takes parameter names as symbols"))),
        }
    };
    let params: Vec<String> = match a.pos.len() {
        1 => Vec::new(),
        2 => match a.arg(1) {
            Value::Array(items) => items.iter().map(|v| symbol(&v)).collect::<Result<_, _>>()?,
            v => vec![symbol(v)?],
        },
        _ => return Err(interp.err_arg(&format!("{what} takes a name and the parameter names"))),
    };
    let visibility = match a.kw(interp, "visibility") {
        None => "public".to_string(),
        Some(v) => {
            let s = symbol(v)?;
            if !["public", "private", "protected"].contains(&s.as_str()) {
                return Err(interp.err_arg(&format!(
                    "visibility must be :public, :private or :protected, not :{s}"
                )));
            }
            s
        }
    };
    let Some(Value::Proc(closure)) = &a.block else {
        return Err(interp.err_arg(&format!("{what} takes a block, the method's body")));
    };
    let ClosureBody::Func(func) = &closure.body else {
        return Err(interp.err_arg(&format!(
            "the block given to {what} must be written at the call: it becomes the method's body"
        )));
    };
    let mut captures = Vec::new();
    for (depth, slots) in super::concurrency::captured_slots(interp, *func)
        .iter()
        .enumerate()
    {
        for &slot in slots {
            let Some(frame) = &closure.frame else {
                return Err(interp.err_runtime("the block's frames are gone"));
            };
            captures.push((depth as u32, slot, frame.get(depth as u32, slot)));
        }
    }
    let request = crate::reflect::GenRequest {
        class,
        name,
        params,
        singleton,
        visibility,
        func: *func,
        captures,
    };
    reflect_of(interp)?
        .generate(interp, request)
        .map_err(|m| interp.err_runtime(&m))?;
    Ok(Value::Nil)
}

fn reflect_of(interp: &Interp) -> Result<std::rc::Rc<dyn crate::reflect::Reflect>, Flow> {
    interp
        .reflect
        .borrow()
        .clone()
        .ok_or_else(|| interp.err_runtime("reflection is available at compile time only"))
}

fn meta_class(interp: &Interp, name: &str) -> Result<ClassId, Flow> {
    interp
        .program
        .world
        .class_by_name(name)
        .ok_or_else(|| interp.err_runtime(&format!("the prelude has no `{name}`")))
}

/// A `Meta::Field` value.
fn meta_field(interp: &Interp, f: &crate::reflect::ReflectField) -> EvalResult {
    let class = meta_class(interp, "Meta::Field")?;
    let name = Value::Symbol(interp.intern(&f.name));
    Ok(Value::Object(Object::new(
        class,
        smallvec![
            name,
            Value::Class(f.ty),
            Value::Bool(f.mutable),
            Value::Bool(f.default)
        ],
    )))
}

/// A `Meta::MethodSig` value, with its `Meta::Param`s.
fn meta_method(interp: &Interp, m: &crate::reflect::ReflectMethod) -> EvalResult {
    use crate::reflect::ReflectKind;
    let sig = meta_class(interp, "Meta::MethodSig")?;
    let param = meta_class(interp, "Meta::Param")?;
    let mut params = Vec::with_capacity(m.params.len());
    for p in &m.params {
        let kind = match p.kind {
            ReflectKind::Required => "Meta::ParamKind::Required",
            ReflectKind::Optional => "Meta::ParamKind::Optional",
            ReflectKind::Rest => "Meta::ParamKind::Rest",
            ReflectKind::Keyword => "Meta::ParamKind::Keyword",
            ReflectKind::Block => "Meta::ParamKind::Block",
        };
        let kind = interp.variant_singleton(meta_class(interp, kind)?);
        let name = Value::Symbol(interp.intern(&p.name));
        params.push(Value::Object(Object::new(
            param,
            smallvec![name, Value::Class(p.ty), kind],
        )));
    }
    let name = Value::Symbol(interp.intern(&m.name));
    Ok(Value::Object(Object::new(
        sig,
        smallvec![
            name,
            Value::array(params),
            Value::Class(m.ret),
            Value::Bool(m.is_static)
        ],
    )))
}

fn class_name(interp: &Interp, recv: &Value, _: Args) -> EvalResult {
    match recv {
        Value::Class(c) => Ok(Value::str(&interp.program.world.class(*c).name)),
        _ => Ok(Value::str(&interp.class_name(recv))),
    }
}

fn bool_and(_: &Interp, recv: &Value, args: Args) -> EvalResult {
    Ok(Value::Bool(recv.is_truthy() && args.arg(0).is_truthy()))
}

fn bool_or(_: &Interp, recv: &Value, args: Args) -> EvalResult {
    Ok(Value::Bool(recv.is_truthy() || args.arg(0).is_truthy()))
}

fn bool_xor(_: &Interp, recv: &Value, args: Args) -> EvalResult {
    Ok(Value::Bool(recv.is_truthy() != args.arg(0).is_truthy()))
}

fn proc_arity(interp: &Interp, recv: &Value, _: Args) -> EvalResult {
    let Value::Proc(c) = recv else {
        return Err(interp.err_type("expected a Proc"));
    };
    Ok(Value::Int(match &c.body {
        ClosureBody::Func(fid) => interp.func(*fid).arity as i64,
        ClosureBody::MethodName(..) => 1,
        ClosureBody::BoundMethod { .. } | ClosureBody::Native(_) => -1,
    }))
}

fn exc_backtrace(_: &Interp, recv: &Value, _: Args) -> EvalResult {
    match recv {
        Value::Object(o) => {
            let items: Vec<Value> = o
                .backtrace()
                .map(|b| b.iter().map(|s| Value::str(s)).collect())
                .unwrap_or_default();
            Ok(Value::array(items))
        }
        _ => Ok(Value::array(vec![])),
    }
}

fn exc_full_message(interp: &Interp, recv: &Value, _: Args) -> EvalResult {
    let mut s = format!(
        "{}: {}",
        interp.class_name(recv),
        interp.exception_message(recv)
    );
    if let Value::Object(o) = recv {
        if let Some(bt) = o.backtrace() {
            for frame in bt.iter() {
                s.push_str(&format!("\n    from {frame}"));
            }
        }
    }
    Ok(Value::string(s))
}

fn exc_cause(_: &Interp, recv: &Value, _: Args) -> EvalResult {
    match recv {
        Value::Object(o) => Ok(o.cause().unwrap_or(Value::Nil)),
        _ => Ok(Value::Nil),
    }
}

/// `Exception#==`: the same exception, or copies of one (`ExcInfo::id`).
/// One without an id was never copied, so it equals only itself.
fn exc_eq(_: &Interp, recv: &Value, args: Args) -> EvalResult {
    let (Value::Object(a), Value::Object(b)) = (recv, args.arg(0)) else {
        return Ok(Value::Bool(false));
    };
    if Rc::ptr_eq(a, b) {
        return Ok(Value::Bool(true));
    }
    let id = |o: &Rc<Object>| o.exc_info().map(|i| i.id);
    Ok(Value::Bool(id(a).is_some() && id(a) == id(b)))
}

/// `Exception#hash`: of its identity, recorded now if it has none yet
/// (as a copy records it, `raised`), so that it never changes.
fn exc_hash(_: &Interp, recv: &Value, _: Args) -> EvalResult {
    let Value::Object(o) = recv else {
        return Ok(Value::Int(0));
    };
    if o.exc_info().is_none() {
        o.init_exc(ExcInfo::new(None, None));
    }
    let id = o.exc_info().map_or(0, |i| i.id);
    // The id mixed, as an Int's hash is.
    Ok(Value::Int(
        (id.wrapping_mul(0x9E37_79B9_7F4A_7C15) >> 1) as i64,
    ))
}

/// Whether `c` may become the cause of `o`: not `o` itself, nor an
/// exception whose causes lead to it, a copy counting as its original.
fn may_cause(o: &Object, c: &Rc<Object>) -> bool {
    let id = o.exc_info().map(|i| i.id);
    let mut link = Some(c.clone());
    while let Some(l) = link {
        if std::ptr::eq(&*l, o) || (id.is_some() && l.exc_info().map(|i| i.id) == id) {
            return false;
        }
        link = match l.cause() {
            Some(Value::Object(n)) => Some(n),
            _ => None,
        };
    }
    true
}

/// The exception to raise for `o`, with what it lacks: the backtrace
/// `backtrace` makes, when it was never raised, and `cause`, when it has
/// none and may have it (`may_cause`). An exception is immutable, so
/// they go into `o` itself only when nothing else refers to it (`raise
/// Foo.new(..)`); otherwise into a copy, which is raised in its place:
/// the original keeps what it had, and only its identity (`ExcInfo::id`)
/// is recorded in it if it had none, for the copy to share (unseen, and
/// set once, safely also when shared). So an exception never refers back
/// to itself through its cause, nor through a copy of itself.
pub(crate) fn raised(
    o: Rc<Object>,
    backtrace: impl FnOnce() -> Vec<String>,
    cause: Option<Value>,
) -> Rc<Object> {
    let (has_backtrace, has_cause) = match o.exc_info() {
        Some(i) => (i.backtrace.get().is_some(), i.cause.get().is_some()),
        None => (false, false),
    };
    let cause = match cause {
        Some(Value::Object(c)) if !has_cause && may_cause(&o, &c) => Some(Value::Object(c)),
        _ => None,
    };
    if has_backtrace && cause.is_none() {
        return o;
    }
    let new_backtrace = (!has_backtrace).then(|| Rc::new(backtrace()));
    if !Rc::is_shared(&o) && Rc::strong_count(&o) == 1 {
        if o.exc_info().is_some() {
            o.complete_exc(new_backtrace, cause);
        } else {
            o.init_exc(ExcInfo::new(new_backtrace, cause));
        }
        return o;
    }
    if o.exc_info().is_none() {
        o.init_exc(ExcInfo::new(None, None));
    }
    let info = o.exc_info().expect("recorded above");
    let copy_info = ExcInfo::with_id(
        info.id,
        new_backtrace.or_else(|| info.backtrace.get().cloned()),
        cause.or_else(|| info.cause.get().cloned()),
    );
    let copy = Object::new(o.class, o.fields());
    copy.init_exc(copy_info);
    copy
}

// ----- Kernel ---------------------------------------------------------------------

pub fn puts_to(interp: &Interp, args: &[Value], out: &mut String) -> Result<(), Flow> {
    if args.is_empty() {
        out.push('\n');
        return Ok(());
    }
    for a in args {
        match a {
            Value::Array(items) => {
                if items.is_empty() {
                    out.push('\n');
                }
                for x in items.iter() {
                    puts_to(interp, std::slice::from_ref(&x), out)?;
                }
            }
            _ => {
                let s = interp.to_s(a)?;
                out.push_str(&s);
                if !s.ends_with('\n') {
                    out.push('\n');
                }
            }
        }
    }
    Ok(())
}

fn kernel_puts(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    let mut out = String::new();
    puts_to(interp, &args.pos, &mut out)?;
    interp.write_out(&out);
    Ok(Value::Nil)
}

fn kernel_print(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    let mut out = String::new();
    for a in &args.pos {
        out.push_str(&interp.to_s(a)?);
    }
    interp.write_out(&out);
    Ok(Value::Nil)
}

fn kernel_p(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    let mut out = String::new();
    for a in &args.pos {
        out.push_str(&interp.inspect(a)?);
        out.push('\n');
    }
    interp.write_out(&out);
    Ok(match args.pos.len() {
        0 => Value::Nil,
        1 => args.pos[0].clone(),
        _ => Value::array(args.pos.into_vec()),
    })
}

fn kernel_warn(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    let mut out = String::new();
    puts_to(interp, &args.pos, &mut out)?;
    interp.flush();
    eprint!("{out}");
    Ok(Value::Nil)
}

/// `exit`: raises `SystemExit`, as Ruby's, so that `ensure` clauses run
/// and `rescue SystemExit` sees it; one nothing rescues ends the program
/// with its status (`task_exit`).
fn kernel_exit(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    let code = match args.arg(0) {
        Value::Int(i) => *i,
        _ => 0,
    };
    Err(Flow::Raise(system_exit(interp, code, "exit")))
}

/// `abort`: the message on standard error, then `SystemExit` with status 1.
fn kernel_abort(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    interp.flush();
    let message = args.arg(0).as_str().unwrap_or("").to_string();
    eprintln!("{message}");
    Err(Flow::Raise(system_exit(interp, 1, &message)))
}

/// `exit!`: ends the program at once, running no `ensure` clause and no
/// `at_exit` block (the output written so far is flushed).
fn kernel_exit_now(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    let code = match args.arg(0) {
        Value::Int(i) => *i as i32,
        _ => 1,
    };
    interp.flush();
    crate::transfer::write_worker_output();
    std::process::exit(code)
}

/// A raised `SystemExit` with `status`.
pub(crate) fn system_exit(interp: &Interp, status: i64, message: &str) -> Value {
    let class = interp.program.exc.system_exit;
    let e = interp.make_exception(class, message);
    if let (Value::Object(o), Some(i)) = (&e, interp.field_index(class, "status")) {
        o.set_field(i, Value::Int(status));
    }
    e
}

fn kernel_at_exit(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    if let Some(b) = args.block {
        interp.add_at_exit(b);
    }
    Ok(Value::Nil)
}

fn read_line(interp: &Interp) -> Result<Option<String>, Flow> {
    super::io::stdin_line(interp)
}

fn kernel_gets(interp: &Interp, _: &Value, _: Args) -> EvalResult {
    match read_line(interp)? {
        Some(l) => Ok(Value::string(l)),
        None => Err(interp.raise(interp.program.exc.eof_error, "end of file reached")),
    }
}

fn kernel_gets_opt(interp: &Interp, _: &Value, _: Args) -> EvalResult {
    match read_line(interp)? {
        Some(l) => Ok(Value::string(l)),
        None => Ok(Value::Nil),
    }
}

fn kernel_format(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    let fmt = string(interp, args.arg(0), "format string")?;
    let s = format_values(interp, fmt, &args.pos[1..])?;
    Ok(Value::string(s))
}

/// A subset of `sprintf`: `%d %i %s %f %e %g %x %o %b %c %%` with flags
/// `-`, `0`, `+`, space, width and precision.
pub fn format_values(interp: &Interp, fmt: &str, args: &[Value]) -> Result<String, Flow> {
    let mut out = String::new();
    let mut chars = fmt.chars().peekable();
    let mut next_arg = 0;
    while let Some(c) = chars.next() {
        if c != '%' {
            out.push(c);
            continue;
        }
        let mut left = false;
        let mut zero = false;
        let mut plus = false;
        let mut space = false;
        let mut width: Option<usize> = None;
        let mut precision: Option<usize> = None;
        loop {
            match chars.peek() {
                Some('-') => {
                    left = true;
                    chars.next();
                }
                Some('0') if width.is_none() => {
                    zero = true;
                    chars.next();
                }
                Some('+') => {
                    plus = true;
                    chars.next();
                }
                Some(' ') => {
                    space = true;
                    chars.next();
                }
                _ => break,
            }
        }
        while let Some(d) = chars.peek().and_then(|c| c.to_digit(10)) {
            width = Some(width.unwrap_or(0) * 10 + d as usize);
            chars.next();
        }
        if chars.peek() == Some(&'.') {
            chars.next();
            let mut p = 0;
            while let Some(d) = chars.peek().and_then(|c| c.to_digit(10)) {
                p = p * 10 + d as usize;
                chars.next();
            }
            precision = Some(p);
        }
        let Some(conv) = chars.next() else {
            return Err(interp.err_arg("incomplete format specifier"));
        };
        if conv == '%' {
            out.push('%');
            continue;
        }
        let arg = args.get(next_arg).cloned().unwrap_or(Value::Nil);
        next_arg += 1;
        let body = match conv {
            'd' | 'i' => {
                let v = match &arg {
                    Value::Float(f) => Value::Int(f.floor() as i64),
                    other => other.clone(),
                };
                let s = interp.to_s(&v)?.to_string();
                sign(s, plus, space)
            }
            's' => {
                let s = interp.to_s(&arg)?.to_string();
                match precision {
                    Some(p) => s.chars().take(p).collect(),
                    None => s,
                }
            }
            'f' => {
                let f = super::float(interp, &arg, "format argument")?;
                sign(format!("{:.*}", precision.unwrap_or(6), f), plus, space)
            }
            'e' => {
                let f = super::float(interp, &arg, "format argument")?;
                sign(format!("{:.*e}", precision.unwrap_or(6), f), plus, space)
            }
            'g' => {
                let f = super::float(interp, &arg, "format argument")?;
                sign(crate::interp::format_float(f), plus, space)
            }
            'x' => format!("{:x}", int(interp, &arg, "format argument")?),
            'X' => format!("{:X}", int(interp, &arg, "format argument")?),
            'o' => format!("{:o}", int(interp, &arg, "format argument")?),
            'b' => format!("{:b}", int(interp, &arg, "format argument")?),
            'c' => match &arg {
                Value::Int(i) => char::from_u32(*i as u32)
                    .map(|c| c.to_string())
                    .unwrap_or_default(),
                other => interp.to_s(other)?.chars().take(1).collect(),
            },
            other => return Err(interp.err_arg(&format!("unknown format specifier %{other}"))),
        };
        let padded = match width {
            Some(w) if body.chars().count() < w => {
                let pad = w - body.chars().count();
                if left {
                    format!("{body}{}", " ".repeat(pad))
                } else if zero && matches!(conv, 'd' | 'i' | 'f' | 'e' | 'x' | 'X' | 'o' | 'b') {
                    let (sign_part, digits) = match body.strip_prefix(['-', '+', ' ']) {
                        Some(rest) => (body[..1].to_string(), rest.to_string()),
                        None => (String::new(), body.clone()),
                    };
                    format!("{sign_part}{}{digits}", "0".repeat(pad))
                } else {
                    format!("{}{body}", " ".repeat(pad))
                }
            }
            _ => body,
        };
        out.push_str(&padded);
    }
    Ok(out)
}

fn sign(s: String, plus: bool, space: bool) -> String {
    if s.starts_with('-') {
        s
    } else if plus {
        format!("+{s}")
    } else if space {
        format!(" {s}")
    } else {
        s
    }
}

/// `Integer(text)` and `Integer(text, base)`, as Ruby's: `String#to_i`'s
/// reading (a prefix naming the base, base 0 by default taking it from the
/// prefix, octal for a bare leading `0`), but the whole text must be the
/// number, with blanks around it only and single `_`s between digits.
fn kernel_integer(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    let s = string(interp, args.arg(0), "Integer()")?;
    let base = match args.pos.get(1) {
        Some(b) => int(interp, b, "base")?,
        None => 0,
    };
    if base != 0 && !(2..=36).contains(&base) {
        return Err(interp.err_arg(&format!("invalid radix {base}")));
    }
    let (negative, digits, base, end) = super::string::int_digits(s, base as u32, 10);
    let rest = &s.as_bytes()[end..];
    if digits.is_empty() || !rest.iter().all(|b| b.is_ascii_whitespace() || *b == 0x0b) {
        return Err(interp.err_arg(&format!("invalid value for Integer(): {s:?}")));
    }
    let digits = if negative {
        format!("-{digits}")
    } else {
        digits
    };
    match i64::from_str_radix(&digits, base) {
        Ok(v) => Ok(Value::Int(v)),
        Err(_) => {
            use num_traits::Num;
            match num_bigint::BigInt::from_str_radix(&digits, base) {
                Ok(n) => interp.int_of_big(&n),
                Err(_) => Err(interp.err_arg(&format!("invalid value for Integer(): {s:?}"))),
            }
        }
    }
}

fn kernel_float(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    let s = string(interp, args.arg(0), "Float()")?;
    match s.trim().replace('_', "").parse::<f64>() {
        Ok(f) => Ok(Value::Float(f)),
        Err(_) => Err(interp.err_arg(&format!("invalid value for Float(): {s:?}"))),
    }
}

fn kernel_string(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    let v = args.arg(0);
    if v.is_str() {
        return Ok(v.clone());
    }
    Ok(Value::str(&interp.to_s(v)?))
}
