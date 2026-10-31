//! Dropping what a program cannot run, before it is embedded in an
//! executable (a compiled program decodes its module at start-up, and
//! the prelude alone has a thousand methods).
//!
//! Reachability is by name for methods: a call resolved to a method may
//! dispatch to any method of that name in a subclass or an extension,
//! and methods are also found by name at run time (`Send`, `&:name`,
//! `recv.:name`, a symbol, an operator, and the few names the runtime
//! itself calls, such as `to_s` and `each`). Quarz has no way to call a
//! method whose name is computed at run time, so a name that appears
//! nowhere reachable can never be looked up.
//!
//! A method found by name runs only on a value of its owner or of a
//! descendant, so it is kept only once such a class is live: one the
//! reachable code names (a class reference, a construction, a literal),
//! one a reachable native may make (the classes of its result and block
//! types, `RtMethod::makes`, with their descendants and variants), or
//! one the runtime makes by itself (the values of the literals,
//! exceptions). A method called as resolved is kept whatever its owner.
//! Ids stay as they are: a dropped function becomes an empty body (that
//! fails if it ever runs), a dropped method an empty record no table
//! refers to.

use std::collections::HashSet;

use crate::*;

/// Names the runtime calls by itself (interpolation, `p`, hashing,
/// sorting, iteration, ranges, JSON, exceptions, construction, the
/// enumerators natives build). A new by-name call in the runtime
/// (`Interp::send`, `call_named`, `has_user_method`, an enumerator)
/// must add its name here.
pub const RUNTIME_NAMES: &[&str] = &[
    "to_s",
    "inspect",
    "==",
    "!=",
    "===",
    "<=>",
    "hash",
    "eql?",
    "each",
    // An `Enumerator` subclass's, which `each` and the enumerators over
    // it call.
    "next",
    "rewind",
    "succ",
    "status",
    "to_json",
    // An interpolation into what turns out not to be a builder.
    "<<",
    "initialize",
    // Run when an object's last reference goes.
    "deinitialize",
    "message",
    "call",
    // Enumerators made by natives call these on their receiver.
    "each_with_index_pairs",
    "each_slice",
    "each_cons",
    "each_char",
    "times",
    "upto",
    "downto",
    "step",
    "+",
    "-",
    "*",
    "/",
    "%",
    "<",
    "<=",
    ">",
    ">=",
];

struct Shake<'a> {
    module: &'a Module,
    by_name: HashMap<&'a str, Vec<MethodId>>,
    /// The methods each class owns (an extension's, its target's).
    by_owner: Vec<Vec<MethodId>>,
    /// The classes that list each one as their superclass or variant of.
    children: Vec<Vec<ClassId>>,
    funcs: Vec<bool>,
    methods: Vec<bool>,
    consts: Vec<bool>,
    names: HashSet<String>,
    /// Classes with possible instances (or class objects).
    live: Vec<bool>,
    /// Classes whose methods may run: the ancestors of the live ones, and
    /// the modules they extend.
    active: Vec<bool>,
    work: Vec<FuncId>,
}

impl Shake<'_> {
    fn func(&mut self, f: FuncId) {
        if let Some(seen) = self.funcs.get_mut(f as usize) {
            if !*seen {
                *seen = true;
                self.work.push(f);
            }
        }
    }

    fn name(&mut self, name: &str) {
        if self.names.contains(name) {
            return;
        }
        self.names.insert(name.to_string());
        let mids = self.by_name.get(name).cloned().unwrap_or_default();
        for m in mids {
            let owner = self.module.world.methods[m as usize].owner;
            if self.active.get(owner as usize).copied().unwrap_or(true) {
                self.method(m);
            }
        }
    }

    /// Class `c` may have instances.
    fn class(&mut self, c: ClassId) {
        let Some(seen) = self.live.get_mut(c as usize) else {
            return;
        };
        if *seen {
            return;
        }
        *seen = true;
        let classes = &self.module.world.classes;
        let class = &classes[c as usize];
        let mut act: Vec<ClassId> = class.ancestors.clone();
        act.push(c);
        for a in class.ancestors.iter().chain([&c]) {
            for e in &classes[*a as usize].extends {
                act.extend(classes[*e as usize].ancestors.iter().copied());
                act.push(*e);
            }
        }
        for a in act {
            self.activate(a);
        }
        let variants = class.variants.clone();
        for v in variants {
            self.class(v);
        }
    }

    /// Class `c` and its descendants may have instances.
    fn class_and_descendants(&mut self, c: ClassId) {
        let mut stack = vec![c];
        let mut seen = HashSet::new();
        while let Some(c) = stack.pop() {
            if !seen.insert(c) {
                continue;
            }
            self.class(c);
            if let Some(ch) = self.children.get(c as usize) {
                stack.extend(ch.iter().copied());
            }
        }
    }

    /// The methods of class `c` may run: those whose names are reached
    /// are kept.
    fn activate(&mut self, c: ClassId) {
        let Some(seen) = self.active.get_mut(c as usize) else {
            return;
        };
        if *seen {
            return;
        }
        *seen = true;
        let mids = self.by_owner[c as usize].clone();
        for m in mids {
            if self
                .names
                .contains(&self.module.world.methods[m as usize].name)
            {
                self.method(m);
            }
        }
    }

    fn method(&mut self, m: MethodId) {
        let Some(seen) = self.methods.get_mut(m as usize) else {
            return;
        };
        if *seen {
            return;
        }
        *seen = true;
        let method = &self.module.world.methods[m as usize];
        let (name, func) = (method.name.as_str(), method.func);
        // What a native hands out is of these classes, or of
        // descendants of theirs (but `Object`'s: every class is one).
        let object = self.module.world.builtin.object;
        for c in method.makes.clone() {
            if c == object {
                self.class(c);
            } else {
                self.class_and_descendants(c);
            }
        }
        self.name(name);
        if let Some(f) = func {
            self.func(f);
        }
    }

    fn constant(&mut self, c: ConstId) {
        if let Some(seen) = self.consts.get_mut(c as usize) {
            if !*seen {
                *seen = true;
                if let Some(f) = self.module.world.consts[c as usize].init {
                    self.func(f);
                }
            }
        }
    }

    fn scan(&mut self, fid: FuncId) {
        let f = &self.module.functions[fid as usize];
        refs(f, &mut |r| match r {
            Ref::Method(m) => self.method(m),
            Ref::Name(n) => self.name(n),
            Ref::Func(f) => self.func(f),
            Ref::Const(c) => self.constant(c),
            Ref::Class(c) => self.class(c),
            Ref::Regexp => self.class(self.module.world.builtin.regexp),
            Ref::Bytes => self.class(self.module.world.builtin.bytes),
        });
    }
}

/// What a function refers to, for reachability (here and when the
/// lowering decides which prelude methods to lower).
pub enum Ref<'a> {
    /// A method called as resolved (one of that name in a subclass or an
    /// extension may run instead: its name counts too).
    Method(MethodId),
    /// A method name looked up at run time.
    Name(&'a str),
    Func(FuncId),
    Const(ConstId),
    /// A class named: its instances or its class object may exist.
    Class(ClassId),
    /// A regular expression made (`Regexp` instances exist).
    Regexp,
    /// A `Bytes` constant.
    Bytes,
}

/// Visit what `f` refers to.
pub fn refs<'a>(f: &'a Function, visit: &mut dyn FnMut(Ref<'a>)) {
    for c in &f.consts {
        match c {
            Constant::Symbol(s) => visit(Ref::Name(s)),
            Constant::Regexp { .. } => visit(Ref::Regexp),
            Constant::Bytes(_) => visit(Ref::Bytes),
            _ => {}
        }
    }
    for o in &f.inlined {
        visit(Ref::Func(o.callee));
    }
    for blk in &f.blocks {
        for inst in &blk.insts {
            match inst {
                Inst::Call { kind, .. } => match kind {
                    CallKind::Method(m) | CallKind::Super(m) | CallKind::Function(m) => {
                        visit(Ref::Method(*m))
                    }
                    CallKind::Send(name) => visit(Ref::Name(name)),
                    // By name: the receiver's class may be a subclass,
                    // with an `initialize` of its own.
                    CallKind::Construct { init, class }
                    | CallKind::ConstructRecv { init, class } => {
                        visit(Ref::Class(*class));
                        visit(Ref::Name("initialize"));
                        if let Some(m) = init {
                            visit(Ref::Method(*m));
                        }
                    }
                    CallKind::ProcCall | CallKind::Yield | CallKind::Raise => {}
                },
                Inst::OwnedCall { method, .. } => visit(Ref::Method(*method)),
                Inst::BinOp { method, op, .. } => {
                    visit(Ref::Name(op.name()));
                    if let Some(m) = method {
                        visit(Ref::Method(*m));
                    }
                }
                Inst::SymbolProc {
                    method: Some(m),
                    among,
                    ..
                } => {
                    visit(Ref::Method(*m));
                    for (_, m) in among {
                        visit(Ref::Method(*m));
                    }
                }
                // Called by name (the checks found different methods).
                Inst::SymbolProc {
                    method: None, name, ..
                } => {
                    if let Some(Constant::Str(n)) = f.consts.get(*name as usize) {
                        visit(Ref::Name(n));
                    }
                }
                Inst::MethodRef {
                    method: Some(m), ..
                } => visit(Ref::Method(*m)),
                Inst::MakeBlock { func, .. } => visit(Ref::Func(*func)),
                Inst::ConstGet { id, .. } => visit(Ref::Const(*id)),
                Inst::ClassRef { class, .. } | Inst::VariantSingleton { class, .. } => {
                    visit(Ref::Class(*class))
                }
                Inst::MakeRegexp { .. } => visit(Ref::Regexp),
                _ => {}
            }
        }
    }
}

/// A function whose body only fails (`Term::Unreachable`).
pub fn empty_function(name: String, kind: FuncKind, file: u32, arity: i32) -> Function {
    Function {
        name,
        kind,
        file,
        nregs: 1,
        frame_size: 0,
        param_kinds: Vec::new(),
        arity,
        consts: Vec::new(),
        blocks: vec![Block {
            insts: Vec::new(),
            lines: Vec::new(),
            term: Term::Unreachable,
            term_line: 0,
            handler: None,
        }],
        inlined: Vec::new(),
    }
}

/// Replace what `module` cannot run by empty records (see the module
/// documentation). Returns the number of functions dropped.
pub fn shake(module: &mut Module) -> usize {
    let mut by_name: HashMap<&str, Vec<MethodId>> = HashMap::default();
    for (i, m) in module.world.methods.iter().enumerate() {
        by_name
            .entry(m.name.as_str())
            .or_default()
            .push(i as MethodId);
    }
    let nclasses = module.world.classes.len();
    let mut by_owner: Vec<Vec<MethodId>> = vec![Vec::new(); nclasses];
    for (i, m) in module.world.methods.iter().enumerate() {
        if let Some(v) = by_owner.get_mut(m.owner as usize) {
            v.push(i as MethodId);
        }
    }
    let mut children: Vec<Vec<ClassId>> = vec![Vec::new(); nclasses];
    for (i, c) in module.world.classes.iter().enumerate() {
        for p in c.superclass.iter().chain(c.variant_of.iter()) {
            if let Some(v) = children.get_mut(*p as usize) {
                v.push(i as ClassId);
            }
        }
        // A module's descendants are the classes that include it.
        for a in &c.ancestors {
            if *a != i as ClassId && module.world.classes[*a as usize].kind == RtClassKind::Module {
                children[*a as usize].push(i as ClassId);
            }
        }
    }
    let mut s = Shake {
        module,
        by_name,
        by_owner,
        children,
        funcs: vec![false; module.functions.len()],
        methods: vec![false; module.world.methods.len()],
        consts: vec![false; module.world.consts.len()],
        names: HashSet::new(),
        live: vec![false; nclasses],
        active: vec![false; nclasses],
        work: Vec::new(),
    };
    // What the runtime makes by itself: the values of the literals and of
    // the operations on them, procs, classes, and every exception.
    let b = &module.world.builtin;
    for c in [
        b.object, b.nil, b.bool_, b.int, b.integer, b.float, b.string, b.symbol, b.array, b.hash,
        b.range, b.proc_, b.class_,
    ] {
        s.class(c);
    }
    for (i, c) in module.world.classes.iter().enumerate() {
        if c.is_exception || c.kind == RtClassKind::Main {
            s.class(i as ClassId);
        }
        // A cog's root module is a `Cog` value (docs/10 §6).
        if c.cog.is_some() {
            s.class(b.cog);
        }
    }
    for u in &module.units {
        s.func(u.body);
    }
    for c in &module.world.classes {
        for f in &c.fields {
            if let Some(d) = f.default {
                s.func(d);
            }
        }
        for v in &c.ivars {
            if let Some(d) = v.default {
                s.func(d);
            }
        }
    }
    for n in RUNTIME_NAMES {
        s.name(n);
    }
    while let Some(f) = s.work.pop() {
        s.scan(f);
    }
    let (funcs, methods, names) = (s.funcs, s.methods, s.names);

    let mut dropped = 0;
    for (i, f) in module.functions.iter_mut().enumerate() {
        if funcs[i] {
            continue;
        }
        dropped += 1;
        // The name goes too: nothing reachable shows this function (an
        // inlined copy keeps its origin reachable).
        *f = empty_function(String::new(), f.kind, f.file, f.arity);
    }
    for (i, m) in module.world.methods.iter_mut().enumerate() {
        if methods[i] {
            continue;
        }
        m.name.clear();
        m.params.clear();
        m.native_key = None;
        m.func = None;
        m.ret = None;
        m.overridden = false;
        m.overloaded = false;
    }
    let keep =
        |map: &mut HashMap<String, Vec<MethodId>>| map.retain(|name, _| names.contains(name));
    for c in &mut module.world.classes {
        keep(&mut c.methods);
        keep(&mut c.singleton_methods);
    }
    for e in &mut module.world.extensions {
        keep(&mut e.methods);
    }
    dropped
}
