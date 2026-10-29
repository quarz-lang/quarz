//! Quoted blocks (docs/14 §6): a block literal given for a `Quoted[P]`
//! block parameter is passed as a `Quoted`, holding its body as a
//! `Meta::Expr` tree, the values the tree's `Capture` nodes stand for,
//! the block as a closure too, and its file. The tree is built at the
//! call, of `data` values made without running code (as baked values
//! are), from the checked syntax tree and what the checker resolved.

use super::*;
use quarz_types::check::BlockPass;

/// What building one quoted block's tree collects.
struct Quote<'a> {
    /// The values read from outside the block, by what they read, and
    /// where each is read at the call.
    captures: Vec<(String, Source<'a>)>,
    /// The quoted levels entered (the block itself first): a variable
    /// reference less deep than this is a parameter of one of them.
    levels: u32,
    /// Whether the block's procedure type has a receiver (`SelfRef`).
    receiver: bool,
}

/// Where a capture's value is read at the call.
#[derive(Clone, Copy)]
enum Source<'a> {
    /// A variable, at its place from the call.
    Var(VarRef),
    /// The `self` of the code around the block.
    SelfValue,
    /// A field or a constant, as the expression reads it there.
    Expr(&'a Expr),
    /// Nothing known: `nil`.
    Nil,
}

impl<'a> FnBuilder<'a> {
    /// The `Quoted` for the block `b` of call `call_id`, whose closure is
    /// in `proc_reg`.
    pub(super) fn quoted(&mut self, call_id: u32, b: &'a AstBlock, proc_reg: Reg) -> Reg {
        let receiver = self
            .out
            .quoted_blocks
            .get(&call_id)
            .copied()
            .unwrap_or(false);
        let mut q = Quote {
            captures: Vec::new(),
            levels: 0,
            receiver,
        };
        let params: Vec<&'a str> = b.params.list.iter().map(|p| p.name.as_str()).collect();
        let tree = if self.lw.quoted_once {
            // Built once, by a constant of its own that the final lowering
            // adds after the checker's (docs/14 §6): its initializer only
            // makes nodes, of literals and constants' values.
            let id = self.lw.alloc_func();
            let mut t = FnBuilder::new(
                &mut *self.lw,
                self.world,
                self.out,
                format!("tree of the block in {}", self.func.name),
                FuncKind::Init,
                self.file,
                &[],
                Vec::new(),
                HashSet::default(),
                false,
                None,
                self.class_id,
            );
            let tree = t.quote_block(&mut q, b, &params);
            t.term(Term::Return(tree));
            let f = t.finish();
            self.lw.set_func(id, f);
            let line = self.line_of(b.span);
            let cid = self.lw.add_quoted_const(self.world, self.file, line, id);
            let dst = self.reg();
            self.emit(Inst::ConstGet { dst, id: cid });
            dst
        } else {
            self.quote_block(&mut q, b, &params)
        };
        // The captures, read here, at the call.
        let regs: Vec<Reg> = q
            .captures
            .iter()
            .map(|(_, source)| match *source {
                Source::Var(r) => self.load_var(r),
                Source::SelfValue => self.self_reg_value(),
                Source::Expr(e) => self.expr(e),
                Source::Nil => self.nil(),
            })
            .collect();
        let items: Vec<ArrayItem> = regs
            .into_iter()
            .map(|reg| ArrayItem { reg, splat: false })
            .collect();
        let captures = self.reg();
        self.emit(Inst::MakeArray {
            dst: captures,
            items,
        });
        let file = self
            .lw
            .files
            .get(self.file as usize)
            .map(|f| f.name.clone())
            .unwrap_or_default();
        let file = self.load_const(Constant::Str(file));
        // By its `initialize`, which takes the arguments over (field
        // stores would leave the captures referenced from here).
        let quoted = self.world.builtin.quoted;
        let init = self
            .world
            .class(quoted)
            .methods
            .get("initialize")
            .and_then(|ms| ms.first().copied());
        let dst = self.reg();
        self.emit(Inst::Call {
            dst,
            kind: CallKind::Construct {
                class: quoted,
                init,
            },
            recv: None,
            args: vec![tree, captures, proc_reg, file],
            splat: false,
            kw: Vec::new(),
            kw_splat: None,
            block: None,
            moved: 0,
        });
        dst
    }

    /// A `Meta::Expr::Block` of `b`'s statements, its parameters `params`.
    fn quote_block<'q: 'a>(&mut self, q: &mut Quote<'q>, b: &'q AstBlock, params: &[&str]) -> Reg {
        q.levels += 1;
        let body: Vec<Reg> = b.body.iter().map(|e| self.quote_expr(q, e)).collect();
        q.levels -= 1;
        let names: Vec<Reg> = params
            .iter()
            .map(|n| self.load_const(Constant::Symbol(n.to_string())))
            .collect();
        let names = self.array_of(names);
        let body = self.array_of(body);
        let line = self.int(self.line_of(b.span) as i64);
        self.node("Block", vec![names, body, line])
    }

    fn quote_expr<'q: 'a>(&mut self, q: &mut Quote<'q>, e: &'q Expr) -> Reg {
        let line = self.line_of(e.span) as i64;
        match &e.kind {
            ExprKind::Nil
            | ExprKind::True
            | ExprKind::False
            | ExprKind::Int(_)
            | ExprKind::Float(_)
            | ExprKind::Bytes(_)
            | ExprKind::Symbol(_)
            | ExprKind::Regexp { .. }
            | ExprKind::Static(_) => self.lit(e, line),
            ExprKind::Str(parts) => {
                if parts.iter().all(|p| matches!(p, StrPart::Lit(_))) {
                    return self.lit(e, line);
                }
                let regs: Vec<Reg> = parts
                    .iter()
                    .map(|p| match p {
                        StrPart::Lit(s) => {
                            let v = self.load_const(Constant::Str(s.clone()));
                            let l = self.int(line);
                            self.node("Lit", vec![v, l])
                        }
                        StrPart::Interp(x) => self.quote_expr(q, x),
                    })
                    .collect();
                let parts = self.array_of(regs);
                let l = self.int(line);
                self.node("Interp", vec![parts, l])
            }
            ExprKind::SelfRef => {
                if q.receiver {
                    let l = self.int(line);
                    self.node("SelfRef", vec![l])
                } else {
                    self.capture(q, "self".to_string(), "self", Source::SelfValue, line)
                }
            }
            ExprKind::Local(name) => match self.var_ref(e.span) {
                // A parameter of a quoted level.
                Some(r) if r.depth < q.levels => {
                    let n = self.load_const(Constant::Symbol(name.clone()));
                    let d = self.int(r.depth as i64);
                    let l = self.int(line);
                    self.node("Arg", vec![n, d, l])
                }
                // A variable of the code around the block, read from the
                // call (its depth from there).
                Some(r) => {
                    let key = format!("{}:{}", r.depth - q.levels, r.slot);
                    if let Some(i) = q.captures.iter().position(|(k, _)| *k == key) {
                        return self.capture_node(i, name, line);
                    }
                    let v = Source::Var(VarRef {
                        depth: r.depth - q.levels,
                        slot: r.slot,
                    });
                    self.capture(q, key, name, v, line)
                }
                None => self.capture(q, format!("?{name}"), name, Source::Nil, line),
            },
            ExprKind::IVar(name) => {
                let v = Source::Expr(e);
                let shown = if name.starts_with('@') {
                    name.clone()
                } else {
                    format!("@{name}")
                };
                self.capture(q, shown.clone(), &shown, v, line)
            }
            ExprKind::Const(path) => {
                if self.out.quoted_lits.contains(&e.id) {
                    let v = self.expr(e);
                    let l = self.int(line);
                    self.node("Lit", vec![v, l])
                } else {
                    let name = path.names.join("::");
                    let key = match self.out.const_targets.get(&e.id) {
                        Some(ConstTarget::Const(c)) => format!("const:{c}"),
                        _ => format!("const@{}", e.id),
                    };
                    self.capture(q, key, &name, Source::Expr(e), line)
                }
            }
            ExprKind::Array(items) => {
                let regs: Vec<Reg> = items
                    .iter()
                    .filter_map(|a| match a {
                        Arg::Positional(x) => Some(self.quote_expr(q, x)),
                        _ => None,
                    })
                    .collect();
                let items = self.array_of(regs);
                let l = self.int(line);
                self.node("ArrayLit", vec![items, l])
            }
            ExprKind::Hash(entries) => {
                let mut pairs = Vec::new();
                for h in entries {
                    if let ast::HashEntry::Pair { key, value } = h {
                        let k = self.quote_expr(q, key);
                        let v = self.quote_expr(q, value);
                        pairs.push(self.array_of(vec![k, v]));
                    }
                }
                let pairs = self.array_of(pairs);
                let l = self.int(line);
                self.node("HashLit", vec![pairs, l])
            }
            ExprKind::Call(call) => self.quote_call(q, e, call, line),
            ExprKind::And(a, b) | ExprKind::Or(a, b) => {
                // A type's own `&&`/`||`: the call the checker made of it,
                // `a.&&() { b }`.
                // Its method, from the made-up call; its receiver and block
                // from the operands written.
                if let Some(c) = self.out.logical_calls.get(&e.id) {
                    let call_id = c.id;
                    let method = self.method_ref(call_id);
                    let recv = self.quote_expr(q, a);
                    q.levels += 1;
                    let body = self.quote_expr(q, b);
                    q.levels -= 1;
                    let names = self.array_of(Vec::new());
                    let body = self.array_of(vec![body]);
                    // The block's line is its operand's.
                    let l = self.int(self.line_of(b.span) as i64);
                    let block = self.node("Block", vec![names, body, l]);
                    let args = self.array_of(Vec::new());
                    let l = self.int(line);
                    return self.node("Call", vec![recv, method, args, block, l]);
                }
                let left = self.quote_expr(q, a);
                let right = self.quote_expr(q, b);
                let l = self.int(line);
                let kind = if matches!(e.kind, ExprKind::And(..)) {
                    "And"
                } else {
                    "Or"
                };
                self.node(kind, vec![left, right, l])
            }
            ExprKind::Not(a) => {
                let operand = self.quote_expr(q, a);
                let l = self.int(line);
                self.node("Not", vec![operand, l])
            }
            ExprKind::If { cond, then, els } => {
                let c = self.quote_expr(q, cond);
                let t = match then.first() {
                    Some(x) => self.quote_expr(q, x),
                    None => {
                        let v = self.nil();
                        let l = self.int(line);
                        self.node("Lit", vec![v, l])
                    }
                };
                let f = match els.as_ref().and_then(|x| x.first()) {
                    Some(x) => self.quote_expr(q, x),
                    None => self.nil(),
                };
                let l = self.int(line);
                self.node("If", vec![c, t, f, l])
            }
            ExprKind::For(f) => {
                let x = if self.out.for_loops.contains(&e.id) {
                    &f.each
                } else {
                    &f.comprehension
                };
                self.quote_expr(q, x)
            }
            // Refused by the checker (`check_quotable`).
            _ => {
                let v = self.nil();
                let l = self.int(line);
                self.node("Lit", vec![v, l])
            }
        }
    }

    /// A `Call` node: what the checker resolved the call to, its
    /// receiver, arguments and block.
    fn quote_call<'q: 'a>(
        &mut self,
        q: &mut Quote<'q>,
        e: &'q Expr,
        call: &'q ast::Call,
        line: i64,
    ) -> Reg {
        self.quote_call_with(q, e, call, None, line)
    }

    /// `quote_call` with the receiver `recv` given (a logical operator's
    /// left operand, which the made-up call does not hold).
    fn quote_call_with<'q: 'a>(
        &mut self,
        q: &mut Quote<'q>,
        e: &'q Expr,
        call: &'q ast::Call,
        recv: Option<&'q Expr>,
        line: i64,
    ) -> Reg {
        let method = self.method_ref(e.id);
        let recv = match recv.or(call.recv.as_ref()) {
            Some(r) => self.quote_expr(q, r),
            // The block's `self`: a `SelfRef` (written as `nil`) when its
            // procedure type has a receiver, else the `self` of the code
            // around it, captured as `self` written would be.
            None if q.receiver => self.nil(),
            None => self.capture(q, "self".to_string(), "self", Source::SelfValue, line),
        };
        let mut args = Vec::new();
        let mut block = None;
        for a in &call.args {
            match a {
                Arg::Positional(x) => args.push(self.quote_expr(q, x)),
                // `&:name`: a block calling `name` on its argument.
                Arg::BlockPass(x) => {
                    if let (ExprKind::Symbol(_), Some(BlockPass::Symbol(_, mid, _))) =
                        (&x.kind, self.out.block_pass.get(&e.id))
                    {
                        let mid = *mid;
                        block = Some(self.symbol_block(mid, line));
                    }
                }
                _ => {}
            }
        }
        if let Some(b) = &call.block {
            let names: Vec<&str> = b.params.list.iter().map(|p| p.name.as_str()).collect();
            block = Some(self.quote_block(q, b, &names));
        }
        let args = self.array_of(args);
        let block = block.unwrap_or_else(|| self.nil());
        let l = self.int(line);
        self.node("Call", vec![recv, method, args, block, l])
    }

    /// `&:name` as a block: `Block([:x], [Call(Arg(:x, 0), name)])`.
    fn symbol_block(&mut self, mid: MethodId, line: i64) -> Reg {
        let x = self.load_const(Constant::Symbol("x".to_string()));
        let d = self.int(0);
        let l = self.int(line);
        let arg = self.node("Arg", vec![x, d, l]);
        let method = self.method_ref_of(mid, None);
        let args = self.array_of(Vec::new());
        let nil = self.nil();
        let l = self.int(line);
        let call = self.node("Call", vec![arg, method, args, nil, l]);
        let x = self.load_const(Constant::Symbol("x".to_string()));
        let names = self.array_of(vec![x]);
        let body = self.array_of(vec![call]);
        let l = self.int(line);
        self.node("Block", vec![names, body, l])
    }

    /// The `Meta::MethodRef` of the method call `id` was resolved to (a
    /// construction: `new`, its `initialize` overload).
    fn method_ref(&mut self, id: u32) -> Reg {
        match self.out.calls.get(&id).cloned() {
            Some(CallTarget::Method { method }) => self.method_ref_of(method, None),
            Some(CallTarget::Constructor { class, init }) => {
                // The `initialize` overload's index, in the class that
                // declares it (an inherited one is its superclass's).
                let index = init
                    .and_then(|i| {
                        let owner = self.world.method(i).owner;
                        self.world
                            .class(owner)
                            .methods
                            .get("initialize")
                            .and_then(|ms| ms.iter().position(|m| *m == i))
                    })
                    .unwrap_or(0);
                let owner = self.class_ref(class);
                let name = self.load_const(Constant::Symbol("new".to_string()));
                let singleton = self.load_const(Constant::Bool(true));
                let index = self.int(index as i64);
                let ext = self.nil();
                self.method_ref_node(vec![owner, name, singleton, index, ext])
            }
            _ => self.nil(),
        }
    }

    fn method_ref_of(&mut self, mid: MethodId, _: Option<()>) -> Reg {
        let m = self.world.method(mid);
        let (owner, name, singleton) = (m.owner, m.name.clone(), m.singleton);
        // Which of the methods of that name it is, in declaration order:
        // the owner's, or the extension's.
        let (index, ext) = match m.extension {
            Some(x) => {
                let e = &self.world.extensions[x as usize];
                let index = e
                    .methods
                    .get(&name)
                    .and_then(|ms| ms.iter().position(|i| *i == mid))
                    .unwrap_or(0);
                (index, e.module)
            }
            None => {
                let c = self.world.class(owner);
                let table = if singleton {
                    &c.singleton_methods
                } else {
                    &c.methods
                };
                let index = table
                    .get(&name)
                    .and_then(|ms| ms.iter().position(|i| *i == mid))
                    .unwrap_or(0);
                (index, None)
            }
        };
        let owner = self.class_ref(owner);
        let name = self.load_const(Constant::Symbol(name));
        let singleton = self.load_const(Constant::Bool(singleton));
        let index = self.int(index as i64);
        let ext = match ext {
            Some(c) => self.class_ref(c),
            None => self.nil(),
        };
        self.method_ref_node(vec![owner, name, singleton, index, ext])
    }

    fn method_ref_node(&mut self, args: Vec<Reg>) -> Reg {
        let class = self.world.builtin.meta_method_ref;
        self.construct_data(class, args)
    }

    /// A `Capture` of the value `v` (read at the call) under `key`.
    fn capture<'q: 'a>(
        &mut self,
        q: &mut Quote<'q>,
        key: String,
        name: &str,
        v: Source<'q>,
        line: i64,
    ) -> Reg {
        let index = match q.captures.iter().position(|(k, _)| *k == key) {
            Some(i) => i,
            None => {
                q.captures.push((key, v));
                q.captures.len() - 1
            }
        };
        self.capture_node(index, name, line)
    }

    fn capture_node(&mut self, index: usize, name: &str, line: i64) -> Reg {
        let i = self.int(index as i64);
        let n = self.load_const(Constant::Symbol(name.to_string()));
        let l = self.int(line);
        self.node("Capture", vec![i, n, l])
    }

    /// A `Lit` of a literal expression's value.
    fn lit(&mut self, e: &'a Expr, line: i64) -> Reg {
        let v = self.expr(e);
        let l = self.int(line);
        self.node("Lit", vec![v, l])
    }

    /// A `Meta::Expr` variant `name` of fields `args`, in order.
    fn node(&mut self, name: &str, args: Vec<Reg>) -> Reg {
        let full = format!("Meta::Expr::{name}");
        let enum_id = self.world.builtin.meta_expr;
        let class = self
            .world
            .class(enum_id)
            .variants
            .iter()
            .copied()
            .find(|v| self.world.class(*v).name == full)
            .expect("Meta::Expr variant");
        self.construct_data(class, args)
    }

    /// A `data` value or variant of `class` from its fields (none held in
    /// place: they are objects, arrays and words), by its constructor.
    fn construct_data(&mut self, class: ClassId, args: Vec<Reg>) -> Reg {
        let init = self.lw.layouts[class as usize].init;
        let dst = self.reg();
        self.emit(Inst::Call {
            dst,
            kind: CallKind::Construct { class, init },
            recv: None,
            args,
            splat: false,
            kw: Vec::new(),
            kw_splat: None,
            block: None,
            moved: 0,
        });
        dst
    }

    fn array_of(&mut self, regs: Vec<Reg>) -> Reg {
        let items = regs
            .into_iter()
            .map(|reg| ArrayItem { reg, splat: false })
            .collect();
        let dst = self.reg();
        self.emit(Inst::MakeArray { dst, items });
        dst
    }

    fn int(&mut self, v: i64) -> Reg {
        self.load_const(Constant::Int(v))
    }

    fn class_ref(&mut self, class: ClassId) -> Reg {
        let dst = self.reg();
        self.emit(Inst::ClassRef { dst, class });
        dst
    }

    /// `self` of the code around the block, as a value.
    fn self_reg_value(&mut self) -> Reg {
        let src = self.self_reg();
        let dst = self.reg();
        self.emit(Inst::Move { dst, src });
        dst
    }
}
