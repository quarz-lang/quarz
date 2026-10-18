//! Expression evaluation over the checked AST.

use std::rc::Rc;

use indexmap::IndexMap;
use quarz_syntax::ast::*;
use quarz_syntax::token::OpAssign;
use quarz_types::{CallTarget, ConstTarget, Member};
use smallvec::smallvec;

use crate::interp::*;
use crate::interp::{fast_binop, ArgVec, FastOp};
use crate::value::*;

/// Positional arguments, keyword arguments and the `&block` argument of a
/// call.
pub type EvaluatedArgs = (ArgVec, Vec<(Symbol, Value)>, Option<Value>);

impl Interp {
    pub fn eval_body(&self, body: &[Expr], ctx: &Ctx) -> EvalResult {
        let mut last = Value::Nil;
        for e in body {
            last = self.eval(e, ctx)?;
        }
        Ok(last)
    }

    pub fn eval(&self, expr: &Expr, ctx: &Ctx) -> EvalResult {
        use ExprKind::*;
        match &expr.kind {
            Nil => Ok(Value::Nil),
            True => Ok(Value::Bool(true)),
            False => Ok(Value::Bool(false)),
            SelfRef => Ok(ctx.self_val.clone()),
            Int(lit) => {
                let v = match lit.value {
                    Some(i) => Value::Int(i),
                    None => parse_int(&lit.digits, lit.base),
                };
                // An integer literal in a Float context is a Float.
                if !self.out.float_literals.is_empty() && self.out.float_literals.contains(&expr.id)
                {
                    let f = match &v {
                        Value::Int(i) => *i as f64,
                        Value::BigInt(b) => {
                            use num_traits::ToPrimitive;
                            b.to_f64().unwrap_or(f64::INFINITY)
                        }
                        _ => 0.0,
                    };
                    return Ok(Value::Float(f));
                }
                Ok(v)
            }
            Float(f) => Ok(Value::Float(*f)),
            Bytes(bytes) => Ok(Value::Bytes(Rc::from(&bytes[..]))),
            Str(parts) => {
                let s = self.eval_str_parts(parts, ctx)?;
                Ok(Value::string(s))
            }
            Symbol(name) => Ok(Value::Symbol(self.intern(name))),
            DSymbol(parts) => {
                let s = self.eval_str_parts(parts, ctx)?;
                Ok(Value::Symbol(self.intern(&s)))
            }
            Regexp { parts, flags } => {
                let is_static = parts.iter().all(|p| matches!(p, StrPart::Lit(_)));
                if is_static {
                    if let Some(v) = self.regexp_cached(expr.id) {
                        return Ok(v);
                    }
                }
                let source = self.eval_str_parts(parts, ctx)?;
                let v = self.make_regexp(&source, flags)?;
                if is_static {
                    self.cache_regexp(expr.id, v.clone());
                }
                Ok(v)
            }
            Magic(m) => Ok(match m {
                quarz_syntax::ast::Magic::File => Value::str(&self.file_names[ctx.file as usize]),
                quarz_syntax::ast::Magic::Line => Value::Int(0),
                quarz_syntax::ast::Magic::Method => match ctx.method {
                    Some(mid) => Value::str(&self.world.method(mid).name),
                    None => Value::Nil,
                },
            }),
            Array(items) => {
                let mut out = Vec::with_capacity(items.len());
                for a in items {
                    match a {
                        Arg::Positional(e) => out.push(self.eval(e, ctx)?),
                        Arg::Splat(e) => match self.eval(e, ctx)? {
                            Value::Array(a) => out.extend(a.iter().cloned()),
                            other => out.push(other),
                        },
                        _ => {}
                    }
                }
                Ok(Value::array(out))
            }
            Hash(entries) => {
                let mut map = IndexMap::with_capacity(entries.len());
                for e in entries {
                    match e {
                        HashEntry::Pair { key, value } => {
                            let k = self.eval(key, ctx)?;
                            let v = self.eval(value, ctx)?;
                            map.insert(k, v);
                        }
                        HashEntry::DoubleSplat(x) => {
                            if let Value::Hash(h) = self.eval(x, ctx)? {
                                for (k, v) in h.iter() {
                                    map.insert(k.clone(), v.clone());
                                }
                            }
                        }
                    }
                }
                Ok(Value::Hash(Rc::new(map)))
            }
            Range { lo, hi, exclusive } => {
                let lo = match lo {
                    Some(e) => self.eval(e, ctx)?,
                    None => Value::Nil,
                };
                let hi = match hi {
                    Some(e) => self.eval(e, ctx)?,
                    None => Value::Nil,
                };
                Ok(Value::Range(Rc::new(RangeVal {
                    lo,
                    hi,
                    exclusive: *exclusive,
                })))
            }
            Lambda(block) => {
                let tag = self.new_tag();
                Ok(Value::Proc(Rc::new(Closure {
                    body: ClosureBody::Block(AstRef::new(block)),
                    frame: Some(ctx.frame.clone()),
                    self_val: ctx.self_val.clone(),
                    frame_size: self.out.frame_sizes.get(&expr.id).copied().unwrap_or(0),
                    destructure: None,
                    is_lambda: true,
                    tag,
                    method_block: ctx.block.clone(),
                    method_tag: tag,
                    file: ctx.file,
                })))
            }
            Local(name) => match self.out.var_refs.get(&expr.span) {
                Some(r) => Ok(ctx.frame.get(r.depth, r.slot)),
                None => Err(self.raise(
                    self.exc.runtime_error,
                    &format!("unresolved variable `{name}`"),
                )),
            },
            IVar(name) => {
                let Value::Object(o) = &ctx.self_val else {
                    return Err(self.raise(
                        self.exc.runtime_error,
                        &format!("@{name} outside of an object"),
                    ));
                };
                let idx = match self.out.ivar_fields.get(&expr.id) {
                    Some(i) => *i,
                    None => self.field_index(o.class, name).unwrap_or(0),
                };
                Ok(o.fields.borrow().get(idx).cloned().unwrap_or(Value::Nil))
            }
            Const(path) => match self.out.const_targets.get(&expr.id) {
                Some(ConstTarget::Class(cid)) => Ok(Value::Class(*cid)),
                Some(ConstTarget::VariantSingleton(cid)) => Ok(self.variant_singleton(*cid)),
                Some(ConstTarget::Const(cid)) => self.const_value(*cid),
                None => Err(self.raise(
                    self.exc.runtime_error,
                    &format!("unresolved constant `{path}`"),
                )),
            },
            TypeApp(_) => match self.out.const_targets.get(&expr.id) {
                Some(ConstTarget::Class(cid)) => Ok(Value::Class(*cid)),
                _ => Err(self.raise(self.exc.runtime_error, "unresolved type")),
            },
            Call(call) => self.eval_call(expr, call, ctx),
            MethodRef { recv, name } => {
                let r = self.eval(recv, ctx)?;
                let tag = self.new_tag();
                Ok(Value::Proc(Rc::new(Closure {
                    body: ClosureBody::BoundMethod {
                        recv: r,
                        name: Rc::from(name.as_str()),
                    },
                    frame: None,
                    self_val: Value::Nil,
                    frame_size: 0,
                    destructure: None,
                    is_lambda: true,
                    tag,
                    method_block: None,
                    method_tag: tag,
                    file: ctx.file,
                })))
            }
            Yield(args) => {
                let Some(block) = &ctx.block else {
                    return Err(self.raise(self.exc.runtime_error, "no block given (yield)"));
                };
                let (pos, _, _) = self.eval_args(args, ctx)?;
                self.call_block(block, pos)
            }
            Super { args, block } => {
                let Some(CallTarget::Super { method }) = self.out.calls.get(&expr.id) else {
                    return Err(self.raise(self.exc.runtime_error, "unresolved super"));
                };
                let (pos, kw) = match args {
                    Some(args) => {
                        let (p, k, _) = self.eval_args(args, ctx)?;
                        (p, k)
                    }
                    None => {
                        // zsuper: forward the current method's parameters.
                        let Some(mid) = ctx.method else {
                            return Err(
                                self.raise(self.exc.runtime_error, "super outside of a method")
                            );
                        };
                        let m = self.world.method(mid);
                        let mut pos = ArgVec::new();
                        let mut kw = Vec::new();
                        for (i, p) in m.params.iter().enumerate() {
                            let v = ctx.frame.get(0, i as u32);
                            match p.kind {
                                ParamKind::KeywordOnly => kw.push((self.intern(&p.name), v)),
                                ParamKind::Rest => {
                                    if let Value::Array(a) = v {
                                        pos.extend(a.iter().cloned());
                                    }
                                }
                                ParamKind::KeywordRest | ParamKind::Block => {}
                                ParamKind::Positional => pos.push(v),
                            }
                        }
                        (pos, kw)
                    }
                };
                let blk = match block {
                    Some(b) => Some(self.make_block(b, expr.id, ctx)),
                    None => ctx.block.clone(),
                };
                let r = self.invoke(*method, ctx.self_val.clone(), pos, kw, blk.clone());
                self.catch_break(&blk, r)
            }
            Assign { target, value } => self.eval_assign(expr, target, value, ctx),
            OpAssign { target, op, value } => self.eval_op_assign(expr, target, *op, value, ctx),
            MultiAssign { targets, value } => {
                let v = self.eval(value, ctx)?;
                self.assign_multi(targets, &v, ctx)?;
                Ok(v)
            }
            TypedDecl { value, .. } => {
                let v = self.eval(value, ctx)?;
                if let Some(r) = self.out.var_refs.get(&expr.span) {
                    ctx.frame.set(r.depth, r.slot, v.clone());
                }
                Ok(v)
            }
            And(a, b) => {
                let l = self.eval(a, ctx)?;
                if l.is_truthy() {
                    self.eval(b, ctx)
                } else {
                    Ok(l)
                }
            }
            Or(a, b) => {
                let l = self.eval(a, ctx)?;
                if l.is_truthy() {
                    Ok(l)
                } else {
                    self.eval(b, ctx)
                }
            }
            Not(a) => {
                let v = self.eval(a, ctx)?;
                Ok(Value::Bool(!v.is_truthy()))
            }
            If { cond, then, els } => {
                let c = self.eval(cond, ctx)?;
                if c.is_truthy() {
                    self.eval_body(then, ctx)
                } else {
                    match els {
                        Some(els) => self.eval_body(els, ctx),
                        None => Ok(Value::Nil),
                    }
                }
            }
            While {
                cond,
                body,
                negate,
                do_while,
            } => {
                let loop_ctx = Ctx {
                    breakable: Breakable::Loop,
                    ..ctx.clone()
                };
                let mut first = *do_while;
                loop {
                    if !first {
                        let c = self.eval(cond, ctx)?.is_truthy();
                        if c == *negate {
                            break;
                        }
                    }
                    first = false;
                    match self.eval_body(body, &loop_ctx) {
                        Ok(_) | Err(Flow::Next(_)) => {}
                        Err(Flow::Break(v, 0)) => return Ok(v),
                        Err(e) => return Err(e),
                    }
                }
                Ok(Value::Nil)
            }
            Case {
                subject,
                whens,
                els,
            } => {
                let subject = match subject {
                    Some(s) => Some(self.eval(s, ctx)?),
                    None => None,
                };
                for w in whens {
                    for c in &w.conds {
                        let Arg::Positional(ce) = c else { continue };
                        let cv = self.eval(ce, ctx)?;
                        let matched = match &subject {
                            Some(s) => self.case_eq(&cv, s)?,
                            None => cv.is_truthy(),
                        };
                        if matched {
                            return self.eval_body(&w.body, ctx);
                        }
                    }
                }
                match els {
                    Some(els) => self.eval_body(els, ctx),
                    None => Ok(Value::Nil),
                }
            }
            CaseIn { subject, arms, els } => {
                let v = self.eval(subject, ctx)?;
                for arm in arms {
                    if self.match_pattern(&arm.pattern, &v, ctx)? {
                        if let Some(g) = &arm.guard {
                            let c = self.eval(&g.cond, ctx)?.is_truthy();
                            if c == g.negate {
                                continue;
                            }
                        }
                        return self.eval_body(&arm.body, ctx);
                    }
                }
                match els {
                    Some(els) => self.eval_body(els, ctx),
                    None => Err(self.raise(
                        self.exc.no_matching_pattern,
                        &format!("no pattern matched {}", self.inspect(&v)?),
                    )),
                }
            }
            MatchPattern {
                value,
                pattern,
                raises,
            } => {
                let v = self.eval(value, ctx)?;
                let matched = self.match_pattern(pattern, &v, ctx)?;
                if *raises {
                    if !matched {
                        return Err(self.raise(
                            self.exc.no_matching_pattern,
                            &format!("{} does not match the pattern", self.inspect(&v)?),
                        ));
                    }
                    Ok(Value::Nil)
                } else {
                    Ok(Value::Bool(matched))
                }
            }
            Begin(block) => self.eval_begin(block, ctx),
            Return(value) => {
                let v = match value {
                    Some(e) => self.eval(e, ctx)?,
                    None => Value::Nil,
                };
                Err(Flow::Return(v, ctx.method_tag))
            }
            Break(value) => {
                let v = match value {
                    Some(e) => self.eval(e, ctx)?,
                    None => Value::Nil,
                };
                let tag = match ctx.breakable {
                    Breakable::Loop | Breakable::None => 0,
                    Breakable::Block(t) => t,
                };
                Err(Flow::Break(v, tag))
            }
            Next(value) => {
                let v = match value {
                    Some(e) => self.eval(e, ctx)?,
                    None => Value::Nil,
                };
                Err(Flow::Next(v))
            }
            Retry => Err(Flow::Retry),
            Seq(exprs) => self.eval_body(exprs, ctx),
            Using(_) | Require { .. } => Ok(Value::Nil),
            ClassDef(_)
            | ModuleDef(_)
            | DataDef(_)
            | EnumDef(_)
            | ExtensionDef(_)
            | MethodDef(_)
            | FieldDecl(_)
            | AttrDecl { .. }
            | Mixin { .. }
            | Visibility { .. }
            | Alias { .. }
            | TypeAlias { .. }
            | ConstAssign { .. }
            | Extern { .. } => Ok(Value::Nil),
        }
    }

    fn eval_str_parts(&self, parts: &[StrPart], ctx: &Ctx) -> Result<String, Flow> {
        let mut s = String::new();
        for p in parts {
            match p {
                StrPart::Lit(l) => s.push_str(l),
                StrPart::Interp(e) => {
                    let v = self.eval(e, ctx)?;
                    s.push_str(&self.to_s(&v)?);
                }
            }
        }
        Ok(s)
    }

    pub fn make_regexp(&self, source: &str, flags: &str) -> EvalResult {
        let mut pattern = String::new();
        let mut inline = String::new();
        if flags.contains('i') {
            inline.push('i');
        }
        if flags.contains('m') {
            inline.push('s');
        }
        if flags.contains('x') {
            inline.push('x');
        }
        if !inline.is_empty() {
            pattern.push_str(&format!("(?{inline})"));
        }
        // Ruby's `\A`/`\z` are the same; `\h` is a hex digit.
        pattern.push_str(&source.replace("\\h", "[0-9a-fA-F]"));
        match regex::Regex::new(&pattern) {
            Ok(regex) => Ok(Value::Regexp(Rc::new(RegexpVal {
                regex,
                source: source.to_string(),
                flags: flags.to_string(),
            }))),
            Err(e) => Err(self.raise(
                self.exc.argument_error,
                &format!("invalid regexp /{source}/: {e}"),
            )),
        }
    }

    /// `===` for `case/when`.
    pub fn case_eq(&self, pattern: &Value, v: &Value) -> Result<bool, Flow> {
        match pattern {
            Value::Class(cid) => Ok(self.world.class_is_a(self.class_of(v), *cid)),
            Value::Range(r) => self.range_covers(r, v),
            Value::Regexp(re) => Ok(match v {
                Value::Str(s) => re.regex.is_match(s),
                _ => false,
            }),
            Value::Proc(_) => Ok(self.call_block(pattern, smallvec![v.clone()])?.is_truthy()),
            _ => self.values_equal(pattern, v),
        }
    }

    pub fn range_covers(&self, r: &RangeVal, v: &Value) -> Result<bool, Flow> {
        use std::cmp::Ordering;
        if !r.lo.is_nil() {
            match self.compare(&r.lo, v) {
                Ok(Ordering::Greater) => return Ok(false),
                Ok(_) => {}
                Err(_) => return Ok(false),
            }
        }
        if !r.hi.is_nil() {
            match self.compare(v, &r.hi) {
                Ok(Ordering::Greater) => return Ok(false),
                Ok(Ordering::Equal) if r.exclusive => return Ok(false),
                Ok(_) => {}
                Err(_) => return Ok(false),
            }
        }
        Ok(true)
    }

    // ----- calls -------------------------------------------------------------------

    /// Evaluate call arguments into positional, keyword and block-pass
    /// values.
    pub fn eval_args(&self, args: &[Arg], ctx: &Ctx) -> Result<EvaluatedArgs, Flow> {
        let mut pos = ArgVec::new();
        let mut kw = Vec::new();
        let mut block = None;
        for a in args {
            match a {
                Arg::Positional(e) => pos.push(self.eval(e, ctx)?),
                Arg::Splat(e) => match self.eval(e, ctx)? {
                    Value::Array(a) => pos.extend(a.iter().cloned()),
                    other => pos.push(other),
                },
                Arg::Keyword { name, value, .. } => {
                    let v = self.eval(value, ctx)?;
                    kw.push((self.intern(name), v));
                }
                Arg::DoubleSplat(e) => {
                    if let Value::Hash(h) = self.eval(e, ctx)? {
                        for (k, v) in h.iter() {
                            if let Value::Symbol(s) = k {
                                kw.push((*s, v.clone()));
                            }
                        }
                    }
                }
                Arg::BlockPass(e) => {
                    block = Some(match &e.kind {
                        ExprKind::Symbol(name) => {
                            let tag = self.new_tag();
                            Value::Proc(Rc::new(Closure {
                                body: ClosureBody::MethodName(Rc::from(name.as_str())),
                                frame: None,
                                self_val: Value::Nil,
                                frame_size: 0,
                                destructure: None,
                                is_lambda: true,
                                tag,
                                method_block: None,
                                method_tag: tag,
                                file: ctx.file,
                            }))
                        }
                        _ => self.eval(e, ctx)?,
                    });
                }
            }
        }
        Ok((pos, kw, block))
    }

    fn eval_call(&self, expr: &Expr, call: &Call, ctx: &Ctx) -> EvalResult {
        let target = self.out.calls.get(&expr.id);
        // Receiver.
        let recv = match &call.recv {
            Some(r) => self.eval(r, ctx)?,
            None => ctx.self_val.clone(),
        };
        if call.safe_nav && recv.is_nil() {
            return Ok(Value::Nil);
        }
        match target {
            Some(CallTarget::IsA(ty)) => return Ok(Value::Bool(self.is_a(&recv, ty))),
            Some(CallTarget::As { ty, optional }) => {
                if self.is_a(&recv, ty) {
                    return Ok(recv);
                }
                if *optional {
                    return Ok(Value::Nil);
                }
                return Err(self.err_type(&format!(
                    "cannot cast {} to {}",
                    self.class_name(&recv),
                    self.world.type_name(ty)
                )));
            }
            Some(CallTarget::Constant(b)) => return Ok(Value::Bool(*b)),
            _ => {}
        }
        let (pos, kw, passed_block) = self.eval_args(&call.args, ctx)?;
        let block = match &call.block {
            Some(b) => Some(self.make_block(b, expr.id, ctx)),
            None => passed_block,
        };
        match target {
            Some(CallTarget::Method { method }) => {
                // Arithmetic and comparisons on numbers without a call.
                if let Some(op) = self.fast_ops[*method as usize] {
                    if pos.len() == 1 && kw.is_empty() && block.is_none() {
                        if let Some(v) = fast_binop(op, &recv, &pos[0]) {
                            return Ok(v);
                        }
                    }
                }
                let mid = self.resolve_dynamic(&recv, *method);
                let r = self.invoke(mid, recv, pos, kw, block.clone());
                self.catch_break(&block, r)
            }
            Some(CallTarget::Constructor { class, init }) => {
                let r = self.construct(*class, *init, pos, kw, block.clone());
                self.catch_break(&block, r)
            }
            Some(CallTarget::ProcCall) => {
                let r = self.call_block(&recv, pos);
                self.catch_break(&block, r)
            }
            Some(CallTarget::Raise) => self.eval_raise(pos),
            Some(CallTarget::Super { method }) => {
                let r = self.invoke(*method, recv, pos, kw, block.clone());
                self.catch_break(&block, r)
            }
            Some(CallTarget::IsA(_))
            | Some(CallTarget::As { .. })
            | Some(CallTarget::Constant(_)) => unreachable!(),
            None => {
                // Not statically resolved (should not happen after a clean
                // check); fall back to dynamic dispatch by name.
                let r = self.send(&recv, &call.name, pos, block.clone());
                self.catch_break(&block, r)
            }
        }
    }

    fn eval_raise(&self, args: ArgVec) -> EvalResult {
        let mut it = args.into_iter();
        let first = it.next().unwrap_or(Value::Nil);
        let exc = match first {
            Value::Class(cid) => {
                let msg = match it.next() {
                    Some(m) => self.to_s(&m)?.to_string(),
                    None => self.world.class(cid).name.clone(),
                };
                self.make_exception(cid, &msg)
            }
            Value::Str(s) => self.make_exception(self.exc.runtime_error, &s),
            Value::Object(o) => {
                if o.backtrace.borrow().is_none() {
                    let bt = self.capture_backtrace();
                    *o.backtrace.borrow_mut() = Some(Rc::new(bt));
                }
                Value::Object(o)
            }
            other => {
                return Err(self.err_type(&format!("cannot raise {}", self.class_name(&other))))
            }
        };
        Err(Flow::Raise(exc))
    }

    // ----- assignment -----------------------------------------------------------------

    fn eval_assign(&self, expr: &Expr, target: &LValue, value: &Expr, ctx: &Ctx) -> EvalResult {
        match target {
            LValue::Local { span, .. } => {
                let r = self.out.var_refs.get(span).copied();
                // `x = x.meth(args)`: move the value out of `x` so that a
                // uniquely referenced collection is updated in place.
                if let (Some(r), ExprKind::Call(call)) = (r, &value.kind) {
                    if let Some(Expr {
                        kind: ExprKind::Local(_),
                        span: rspan,
                        ..
                    }) = &call.recv
                    {
                        let same = self.out.var_refs.get(rspan) == Some(&r);
                        if same && call.block.is_none() && !call.safe_nav {
                            if let Some(CallTarget::Method { method }) =
                                self.out.calls.get(&value.id)
                            {
                                let (pos, kw, passed) = self.eval_args(&call.args, ctx)?;
                                if passed.is_none() {
                                    let old = ctx.frame.get(r.depth, r.slot);
                                    ctx.frame.set(r.depth, r.slot, Value::Nil);
                                    return match self.invoke_owned(*method, old, pos, kw) {
                                        Ok(v) => {
                                            ctx.frame.set(r.depth, r.slot, v.clone());
                                            Ok(v)
                                        }
                                        Err((e, old)) => {
                                            ctx.frame.set(r.depth, r.slot, old);
                                            Err(e)
                                        }
                                    };
                                }
                            }
                        }
                    }
                }
                let v = self.eval(value, ctx)?;
                if let Some(r) = r {
                    ctx.frame.set(r.depth, r.slot, v.clone());
                }
                Ok(v)
            }
            LValue::IVar(name) => {
                let v = self.eval(value, ctx)?;
                self.set_ivar(expr.id, name, v.clone(), ctx)?;
                Ok(v)
            }
            LValue::Const(_) => Ok(Value::Nil),
            LValue::Attr {
                recv,
                name,
                safe_nav,
            } => {
                let r = self.eval(recv, ctx)?;
                if *safe_nav && r.is_nil() {
                    return Ok(Value::Nil);
                }
                let v = self.eval(value, ctx)?;
                self.send(&r, &format!("{name}="), smallvec![v.clone()], None)?;
                Ok(v)
            }
            LValue::Index { recv, args } => {
                let r = self.eval(recv, ctx)?;
                let (mut pos, _, _) = self.eval_args(args, ctx)?;
                let v = self.eval(value, ctx)?;
                pos.push(v.clone());
                self.send(&r, "[]=", pos, None)?;
                Ok(v)
            }
        }
    }

    fn set_ivar(&self, node: u32, name: &str, v: Value, ctx: &Ctx) -> Result<(), Flow> {
        let Value::Object(o) = &ctx.self_val else {
            return Err(self.raise(
                self.exc.runtime_error,
                &format!("@{name} outside of an object"),
            ));
        };
        let idx = match self.out.ivar_fields.get(&node) {
            Some(i) => *i,
            None => self.field_index(o.class, name).unwrap_or(0),
        };
        let mut fields = o.fields.borrow_mut();
        if idx >= fields.len() {
            fields.resize(idx + 1, Value::Nil);
        }
        fields[idx] = v;
        Ok(())
    }

    fn eval_op_assign(
        &self,
        expr: &Expr,
        target: &LValue,
        op: OpAssign,
        value: &Expr,
        ctx: &Ctx,
    ) -> EvalResult {
        // Read.
        let (current, recv, index_args) = match target {
            LValue::Local { span, .. } => {
                let r = self.out.var_refs.get(span).copied();
                let cur = r
                    .map(|r| ctx.frame.get(r.depth, r.slot))
                    .unwrap_or(Value::Nil);
                (cur, None, ArgVec::new())
            }
            LValue::IVar(name) => {
                let Value::Object(o) = &ctx.self_val else {
                    return Err(self.raise(self.exc.runtime_error, "@ivar outside of an object"));
                };
                let idx = match self.out.ivar_fields.get(&expr.id) {
                    Some(i) => *i,
                    None => self.field_index(o.class, name).unwrap_or(0),
                };
                let cur = o.fields.borrow().get(idx).cloned().unwrap_or(Value::Nil);
                (cur, None, ArgVec::new())
            }
            LValue::Attr { recv, name, .. } => {
                let r = self.eval(recv, ctx)?;
                let cur = self.send(&r, name, smallvec![], None)?;
                (cur, Some(r), ArgVec::new())
            }
            LValue::Index { recv, args } => {
                let r = self.eval(recv, ctx)?;
                let (pos, _, _) = self.eval_args(args, ctx)?;
                let cur = self.send(&r, "[]", pos.clone(), None)?;
                (cur, Some(r), pos)
            }
            LValue::Const(_) => return Ok(Value::Nil),
        };
        // Combine.
        let result = match op {
            OpAssign::OrOr => {
                if current.is_truthy() {
                    return Ok(current);
                }
                self.eval(value, ctx)?
            }
            OpAssign::AndAnd => {
                if !current.is_truthy() {
                    return Ok(current);
                }
                self.eval(value, ctx)?
            }
            _ => {
                let rhs = self.eval(value, ctx)?;
                let name = op.as_str().trim_end_matches('=');
                self.binary_op(&current, name, rhs)?
            }
        };
        // Write.
        match target {
            LValue::Local { span, .. } => {
                if let Some(r) = self.out.var_refs.get(span) {
                    ctx.frame.set(r.depth, r.slot, result.clone());
                }
            }
            LValue::IVar(name) => self.set_ivar(expr.id, name, result.clone(), ctx)?,
            LValue::Attr { name, .. } => {
                self.send(
                    recv.as_ref().unwrap(),
                    &format!("{name}="),
                    smallvec![result.clone()],
                    None,
                )?;
            }
            LValue::Index { .. } => {
                let mut pos = index_args;
                pos.push(result.clone());
                self.send(recv.as_ref().unwrap(), "[]=", pos, None)?;
            }
            LValue::Const(_) => {}
        }
        Ok(result)
    }

    /// Apply a binary operator by name with fast paths for numbers.
    pub fn binary_op(&self, lhs: &Value, name: &str, rhs: Value) -> EvalResult {
        if let Some(op) = FastOp::from_name(name) {
            if let Some(v) = fast_binop(op, lhs, &rhs) {
                return Ok(v);
            }
        }
        self.send(lhs, name, smallvec![rhs], None)
    }

    fn assign_multi(&self, targets: &[MultiTarget], v: &Value, ctx: &Ctx) -> Result<(), Flow> {
        let items: Vec<Value> = match v {
            Value::Array(a) => a.iter().cloned().collect(),
            other => vec![other.clone()],
        };
        let splat = targets
            .iter()
            .position(|t| matches!(t, MultiTarget::Splat(_)));
        let n = targets.len();
        for (i, t) in targets.iter().enumerate() {
            let value = match splat {
                Some(si) if i == si => {
                    let after = n - si - 1;
                    let end = items.len().saturating_sub(after).max(si);
                    Value::array(items.get(si..end).map(|s| s.to_vec()).unwrap_or_default())
                }
                Some(si) if i > si => {
                    let from_end = n - i;
                    items
                        .len()
                        .checked_sub(from_end)
                        .and_then(|j| items.get(j))
                        .cloned()
                        .unwrap_or(Value::Nil)
                }
                _ => items.get(i).cloned().unwrap_or(Value::Nil),
            };
            match t {
                MultiTarget::Single(lv) | MultiTarget::Splat(Some(lv)) => {
                    self.assign_lvalue(lv, value, ctx)?
                }
                MultiTarget::Splat(None) => {}
                MultiTarget::Nested(ts) => self.assign_multi(ts, &value, ctx)?,
            }
        }
        Ok(())
    }

    fn assign_lvalue(&self, lv: &LValue, v: Value, ctx: &Ctx) -> Result<(), Flow> {
        match lv {
            LValue::Local { span, .. } => {
                if let Some(r) = self.out.var_refs.get(span) {
                    ctx.frame.set(r.depth, r.slot, v);
                }
                Ok(())
            }
            LValue::IVar(name) => {
                let Value::Object(o) = &ctx.self_val else {
                    return Err(self.raise(self.exc.runtime_error, "@ivar outside of an object"));
                };
                let idx = self.field_index(o.class, name).unwrap_or(0);
                let mut fields = o.fields.borrow_mut();
                if idx >= fields.len() {
                    fields.resize(idx + 1, Value::Nil);
                }
                fields[idx] = v;
                Ok(())
            }
            LValue::Attr { recv, name, .. } => {
                let r = self.eval(recv, ctx)?;
                self.send(&r, &format!("{name}="), smallvec![v], None)?;
                Ok(())
            }
            LValue::Index { recv, args } => {
                let r = self.eval(recv, ctx)?;
                let (mut pos, _, _) = self.eval_args(args, ctx)?;
                pos.push(v);
                self.send(&r, "[]=", pos, None)?;
                Ok(())
            }
            LValue::Const(_) => Ok(()),
        }
    }

    // ----- begin / rescue --------------------------------------------------------------

    fn eval_begin(&self, block: &BeginBlock, ctx: &Ctx) -> EvalResult {
        let result = loop {
            let r = self.eval_body(&block.body, ctx);
            match r {
                Ok(v) => {
                    break match &block.else_body {
                        Some(e) => self.eval_body(e, ctx),
                        None => Ok(v),
                    };
                }
                Err(Flow::Raise(exc)) => {
                    let mut handled = None;
                    for rescue in &block.rescues {
                        let classes = self.out.rescue_classes.get(&rescue.span);
                        let matches = match classes {
                            Some(ids) => ids.iter().any(|c| self.exception_is_a(&exc, *c)),
                            None => self.exception_is_a(&exc, self.world.builtin.standard_error),
                        };
                        if matches {
                            handled = Some(rescue);
                            break;
                        }
                    }
                    let Some(rescue) = handled else {
                        break Err(Flow::Raise(exc));
                    };
                    if rescue.var.is_some() {
                        if let Some(r) = self.out.var_refs.get(&rescue.span) {
                            ctx.frame.set(r.depth, r.slot, exc.clone());
                        }
                    }
                    match self.eval_body(&rescue.body, ctx) {
                        Err(Flow::Retry) => continue,
                        other => break other,
                    }
                }
                Err(other) => break Err(other),
            }
        };
        if let Some(ensure) = &block.ensure {
            self.eval_body(ensure, ctx)?;
        }
        result
    }

    // ----- patterns ---------------------------------------------------------------------

    pub fn match_pattern(&self, pat: &Pattern, v: &Value, ctx: &Ctx) -> Result<bool, Flow> {
        match &pat.kind {
            PatternKind::Bind(_) => {
                if let Some(r) = self.out.var_refs.get(&pat.span) {
                    ctx.frame.set(r.depth, r.slot, v.clone());
                }
                Ok(true)
            }
            PatternKind::Capture(inner, _) => {
                if !self.match_pattern(inner, v, ctx)? {
                    return Ok(false);
                }
                if let Some(r) = self.out.var_refs.get(&pat.span) {
                    ctx.frame.set(r.depth, r.slot, v.clone());
                }
                Ok(true)
            }
            PatternKind::Alt(alts) => {
                for a in alts {
                    if self.match_pattern(a, v, ctx)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            PatternKind::Pin(e) => {
                let p = self.eval(e, ctx)?;
                self.values_equal(&p, v)
            }
            PatternKind::Value(e) => {
                let p = self.eval(e, ctx)?;
                self.case_eq(&p, v)
            }
            PatternKind::Range { lo, hi, exclusive } => {
                let lo = match lo {
                    Some(e) => self.eval(e, ctx)?,
                    None => Value::Nil,
                };
                let hi = match hi {
                    Some(e) => self.eval(e, ctx)?,
                    None => Value::Nil,
                };
                self.range_covers(
                    &RangeVal {
                        lo,
                        hi,
                        exclusive: *exclusive,
                    },
                    v,
                )
            }
            PatternKind::Const(_) => {
                let Some(cid) = self.out.pattern_classes.get(&pat.span) else {
                    return Ok(false);
                };
                Ok(self.world.class_is_a(self.class_of(v), *cid))
            }
            PatternKind::ConstArray(_, ap) => {
                let Some(cid) = self.out.pattern_classes.get(&pat.span) else {
                    return Ok(false);
                };
                if !self.world.class_is_a(self.class_of(v), *cid) {
                    return Ok(false);
                }
                let Value::Object(o) = v else {
                    return Ok(false);
                };
                let fields: Vec<Value> = o.fields.borrow().clone();
                self.match_array_pattern(ap, &fields, pat.span, ctx)
            }
            PatternKind::ConstHash(_, hp) => {
                let Some(cid) = self.out.pattern_classes.get(&pat.span) else {
                    return Ok(false);
                };
                if !self.world.class_is_a(self.class_of(v), *cid) {
                    return Ok(false);
                }
                let Value::Object(o) = v else {
                    return Ok(false);
                };
                for pair in &hp.pairs {
                    let Some(idx) = self.field_index(o.class, &pair.key) else {
                        return Ok(false);
                    };
                    let fv = o.fields.borrow().get(idx).cloned().unwrap_or(Value::Nil);
                    match &pair.pattern {
                        Some(p) => {
                            if !self.match_pattern(p, &fv, ctx)? {
                                return Ok(false);
                            }
                        }
                        None => {
                            if let Some(r) = self.out.var_refs.get(&pair.span) {
                                ctx.frame.set(r.depth, r.slot, fv);
                            }
                        }
                    }
                }
                Ok(true)
            }
            PatternKind::Array(ap) => {
                let Value::Array(a) = v else { return Ok(false) };
                let items: Vec<Value> = a.iter().cloned().collect();
                self.match_array_pattern(ap, &items, pat.span, ctx)
            }
            PatternKind::Find {
                pre_rest,
                middle,
                post_rest,
            } => {
                let Value::Array(a) = v else { return Ok(false) };
                let items: Vec<Value> = a.iter().cloned().collect();
                if middle.len() > items.len() {
                    return Ok(false);
                }
                for start in 0..=(items.len() - middle.len()) {
                    let mut ok = true;
                    for (p, x) in middle.iter().zip(items[start..].iter()) {
                        if !self.match_pattern(p, x, ctx)? {
                            ok = false;
                            break;
                        }
                    }
                    if ok {
                        if pre_rest.is_some() {
                            if let Some(r) = self.out.var_refs.get(&pat.span) {
                                ctx.frame.set(
                                    r.depth,
                                    r.slot,
                                    Value::array(items[..start].to_vec()),
                                );
                            }
                        }
                        if post_rest.is_some() {
                            let key = quarz_syntax::Span::empty(pat.span.end as usize);
                            if let Some(r) = self.out.var_refs.get(&key) {
                                ctx.frame.set(
                                    r.depth,
                                    r.slot,
                                    Value::array(items[start + middle.len()..].to_vec()),
                                );
                            }
                        }
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            PatternKind::Hash(hp) => match v {
                Value::Hash(h) => {
                    for pair in &hp.pairs {
                        let key = Value::Symbol(self.intern(&pair.key));
                        let Some(fv) = h.get(&key) else {
                            return Ok(false);
                        };
                        match &pair.pattern {
                            Some(p) => {
                                if !self.match_pattern(p, fv, ctx)? {
                                    return Ok(false);
                                }
                            }
                            None => {
                                if let Some(r) = self.out.var_refs.get(&pair.span) {
                                    ctx.frame.set(r.depth, r.slot, fv.clone());
                                }
                            }
                        }
                    }
                    if let Some(HashPatternRest::Bind(_)) = &hp.rest {
                        let mut rest = IndexMap::new();
                        for (k, val) in h.iter() {
                            let is_matched = hp
                                .pairs
                                .iter()
                                .any(|p| matches!(k, Value::Symbol(s) if *self.symbol_name(*s) == *p.key));
                            if !is_matched {
                                rest.insert(k.clone(), val.clone());
                            }
                        }
                        if let Some(r) = self.out.var_refs.get(&pat.span) {
                            ctx.frame.set(r.depth, r.slot, Value::Hash(Rc::new(rest)));
                        }
                    }
                    if let Some(HashPatternRest::Nil) = &hp.rest {
                        if h.len() != hp.pairs.len() {
                            return Ok(false);
                        }
                    }
                    Ok(true)
                }
                Value::Object(o) => {
                    for pair in &hp.pairs {
                        let Some(idx) = self.field_index(o.class, &pair.key) else {
                            return Ok(false);
                        };
                        let fv = o.fields.borrow().get(idx).cloned().unwrap_or(Value::Nil);
                        match &pair.pattern {
                            Some(p) => {
                                if !self.match_pattern(p, &fv, ctx)? {
                                    return Ok(false);
                                }
                            }
                            None => {
                                if let Some(r) = self.out.var_refs.get(&pair.span) {
                                    ctx.frame.set(r.depth, r.slot, fv);
                                }
                            }
                        }
                    }
                    Ok(true)
                }
                _ => Ok(false),
            },
        }
    }

    fn match_array_pattern(
        &self,
        ap: &ArrayPattern,
        items: &[Value],
        span: quarz_syntax::Span,
        ctx: &Ctx,
    ) -> Result<bool, Flow> {
        let fixed = ap.pre.len() + ap.post.len();
        if ap.rest.is_none() && items.len() != fixed {
            return Ok(false);
        }
        if items.len() < fixed {
            return Ok(false);
        }
        for (p, x) in ap.pre.iter().zip(items.iter()) {
            if !self.match_pattern(p, x, ctx)? {
                return Ok(false);
            }
        }
        let post_start = items.len() - ap.post.len();
        for (p, x) in ap.post.iter().zip(items[post_start..].iter()) {
            if !self.match_pattern(p, x, ctx)? {
                return Ok(false);
            }
        }
        if let Some(Some(_)) = &ap.rest {
            // The rest variable is keyed by the owning pattern's span.
            if let Some(r) = self.out.var_refs.get(&span) {
                ctx.frame.set(
                    r.depth,
                    r.slot,
                    Value::array(items[ap.pre.len()..post_start].to_vec()),
                );
            }
        }
        Ok(true)
    }

    pub fn lookup_member(&self, name: &str) -> Option<Member> {
        self.world.top.get(name).copied()
    }
}

/// Parse an integer literal (digits without prefix/underscores) in a base.
pub fn parse_int(digits: &str, base: u8) -> Value {
    let (neg, digits) = match digits.strip_prefix('-') {
        Some(d) => (true, d),
        None => (false, digits),
    };
    match i64::from_str_radix(digits, base as u32) {
        Ok(v) => Value::Int(if neg { -v } else { v }),
        Err(_) => {
            use num_bigint::BigInt;
            use num_traits::Num;
            let b = BigInt::from_str_radix(digits, base as u32).unwrap_or_default();
            int_from_big(if neg { -b } else { b })
        }
    }
}
