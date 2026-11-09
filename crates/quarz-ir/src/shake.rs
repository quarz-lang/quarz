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
/// must add its name here (and, for a native's, to `NATIVE_NAMES`).
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

/// The names natives call methods of the values they are given by: what
/// `Interp::to_s`, `inspect`, `values_equal`, `compare` and the keys'
/// `==` and `hash` look up, and what `Interp::send` and
/// `has_user_method` are given in the natives (an `Enumerable`'s `each`,
/// `next` and `rewind`, `to_json`, and the methods enumerators made by
/// natives call on their receiver). A native that calls another name
/// must add it here (and to `RUNTIME_NAMES`).
pub const NATIVE_NAMES: &[&str] = &[
    "to_s",
    "inspect",
    "==",
    "hash",
    "<=>",
    "each",
    "next",
    "rewind",
    "to_json",
    "status",
    "each_with_index_pairs",
    "each_slice",
    "each_cons",
    "each_char",
    "times",
    "upto",
    "downto",
    "step",
];

/// What a native the runtime calls by `name` calls by name in turn (what
/// a run reaches, for the compile-time walks: the runner's `bad_reach`
/// and a static round's lowering): the printing ones each other's
/// (`Object#to_s` of an array is its elements' `inspect`), `==` and
/// `hash` each other's (a key's), `<=>` itself; the other names, all.
pub fn calls_for(name: &str) -> &'static [&'static str] {
    match name {
        "to_s" | "inspect" | "<<" => &["to_s", "inspect"],
        "==" | "hash" => &["==", "hash"],
        "<=>" => &["<=>"],
        _ => NATIVE_NAMES,
    }
}

/// The names the native registered as `key` (`Class#name` or
/// `Class.name`) may call by name on the values it is given
/// (`Interp::to_s`, `inspect`, `values_equal`, `compare`, the keys' `==`
/// and `hash`, enumerators): none for a native of a class whose methods
/// take only built-in values (an `Int`'s, `Math`'s), the printing ones
/// for `Kernel`'s printing functions, and every name a native calls by
/// (`NATIVE_NAMES`) for the others, which are not told apart.
pub fn native_calls(key: &str) -> &'static [&'static str] {
    let (class, name) = key
        .split_once('#')
        .or_else(|| key.split_once('.'))
        .unwrap_or(("", key));
    match (class, name) {
        // (A string's `sub` and `gsub` with a block, and a builder's
        // `<<`, make strings of what they are given.)
        ("String", "sub" | "gsub" | "sub!" | "gsub!" | "%") | ("String::Builder", _) => {
            &["to_s", "inspect"]
        }
        (
            "Int" | "Float" | "Integer" | "Math" | "Duration" | "Time" | "Bytes" | "Regexp"
            | "MatchData" | "Symbol" | "Bool" | "Nil" | "String" | "Type",
            _,
        ) => &[],
        // (Compile-time natives: names and types, no values of a program's.)
        (c, _) if c.starts_with("Meta::") => &[],
        // An object's own: what it is for.
        ("Object", "to_s" | "inspect") => &["to_s", "inspect"],
        ("Object", "==" | "!=" | "hash") => &["==", "hash"],
        ("Object", _) => &[],
        // A collection's elements are printed, compared, hashed and
        // ordered, not iterated by name (those taking a collection,
        // `Set#merge`, iterate a built-in one).
        (
            "Array" | "Hash" | "Set" | "Range" | "Array::Builder" | "Hash::Builder"
            | "Set::Builder",
            _,
        ) => &["to_s", "inspect", "==", "hash", "<=>"],
        ("Kernel", "p" | "pp" | "puts" | "print" | "warn" | "format" | "sprintf") => {
            &["to_s", "inspect"]
        }
        _ => NATIVE_NAMES,
    }
}

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
            // (Only `reach_refs` gives these.)
            Ref::Runtime(n) => self.name(n),
            Ref::Exact { method: m, .. } | Ref::Bounded { method: m, .. } => self.method(m),
            Ref::Construct { class, init, .. } => {
                self.class(class);
                self.name("initialize");
                if let Some(m) = init {
                    self.method(m);
                }
            }
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
    /// A method of an object's the runtime calls by this name for an
    /// instruction (an interpolation's `to_s`, a hash literal's `hash`):
    /// from `reach_refs` only.
    Runtime(&'static str),
    /// A method called as it is, never an override (`super`, a
    /// function): from `reach_refs` only. `on_self`: a `super` run on the
    /// `self` of the method it is written in (`Inst::Call::on_self`).
    Exact {
        method: MethodId,
        on_self: bool,
    },
    /// A method called as resolved on a receiver whose static type says
    /// it is an instance of one of `classes` or of a subclass
    /// (`Inst::Call::recv_classes`), or on the method's own `self`
    /// (`on_self`, `Inst::Call::on_self`), which a run may know a bound
    /// for: an override runs in its place only if such a receiver's
    /// lookup may find it, and its body runs with that receiver as
    /// `self` (docs/14 §7). From `reach_refs` only; `refs` gives
    /// `Method`, what is kept in a compiled program not being narrowed
    /// by it.
    Bounded {
        method: MethodId,
        classes: Option<&'a [ClassId]>,
        on_self: bool,
    },
    /// `Class.new(...)` (`recv` false: an instance of `class` itself) or
    /// `new` on the receiver of a class method (`recv`: of `class` or a
    /// subclass), built with `init` when it is `class`'s (its own or an
    /// inherited `initialize`): from
    /// `reach_refs` only.
    Construct {
        class: ClassId,
        init: Option<MethodId>,
        recv: bool,
    },
}

/// Visit what `f` refers to.
pub fn refs<'a>(f: &'a Function, visit: &mut dyn FnMut(Ref<'a>)) {
    refs_in(f, false, visit)
}

/// What `f` refers to, for what a run of it may reach (the compile-time
/// checks of `static` code): as `refs`, but a `super` call and a
/// function's are `Ref::Exact`, a construction is `Ref::Construct`
/// (not every `initialize` by name), a symbol constant is no method's
/// name, and the runtime's calls by name for an instruction are
/// `Ref::Runtime`.
pub fn reach_refs<'a>(f: &'a Function, visit: &mut dyn FnMut(Ref<'a>)) {
    refs_in(f, true, visit)
}

fn refs_in<'a>(f: &'a Function, exact: bool, visit: &mut dyn FnMut(Ref<'a>)) {
    for c in &f.consts {
        match c {
            // A symbol is a method's name only where a call says so: the
            // instructions that call by name (`CallKind::Send`, `&:name`
            // and `.:name` without a method, `BinOp`) carry their names
            // themselves, and no native calls a method a `Symbol` value
            // names (`Meta::Method#bind` in a generated body is replaced
            // by the call of its method; the runtime's own calls by name,
            // `RUNTIME_NAMES`, use names of its own). So what a run
            // reaches does not count a symbol value (`:count` as a hash
            // key or a tag); shake keeps the methods of every symbol's
            // name all the same.
            Constant::Symbol(_) if exact => {}
            Constant::Symbol(s) => visit(Ref::Name(s)),
            Constant::Regexp { .. } => visit(Ref::Regexp),
            // A `JSON.decode[T]` descriptor: the native builds values of
            // the `data` classes it names (`dC:...`).
            Constant::Str(s) if s.starts_with(crate::JSON_TYPE_PREFIX) => {
                for n in s[crate::JSON_TYPE_PREFIX.len()..].split(';') {
                    if let Some(c) = n
                        .strip_prefix('d')
                        .and_then(|n| n.split_once(':'))
                        .and_then(|(c, _)| c.parse::<ClassId>().ok())
                    {
                        visit(Ref::Class(c));
                    }
                }
            }
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
                Inst::Call {
                    kind,
                    recv_classes,
                    on_self,
                    ..
                } => match kind {
                    CallKind::Super(m) if exact => visit(Ref::Exact {
                        method: *m,
                        on_self: *on_self,
                    }),
                    CallKind::Function(m) if exact => visit(Ref::Exact {
                        method: *m,
                        on_self: false,
                    }),
                    CallKind::Construct { init, class } if exact => visit(Ref::Construct {
                        class: *class,
                        init: *init,
                        recv: false,
                    }),
                    CallKind::ConstructRecv { init, class } if exact => visit(Ref::Construct {
                        class: *class,
                        init: *init,
                        recv: true,
                    }),
                    CallKind::Method(m) if exact && (recv_classes.is_some() || *on_self) => {
                        visit(Ref::Bounded {
                            method: *m,
                            classes: recv_classes.as_deref(),
                            on_self: *on_self,
                        })
                    }
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
                    CallKind::ProcCall
                    | CallKind::Yield
                    | CallKind::InstanceExec
                    | CallKind::Raise => {}
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
                // `.:name` the checks could not choose a method for: by
                // name at run time.
                Inst::MethodRef {
                    method: None, name, ..
                } => {
                    if let Some(Constant::Str(n)) = f.consts.get(*name as usize) {
                        visit(Ref::Name(n));
                    }
                }
                Inst::MakeBlock { func, .. } => visit(Ref::Func(*func)),
                Inst::ConstGet { id, .. } => visit(Ref::Const(*id)),
                Inst::ClassRef { class, .. } | Inst::VariantSingleton { class, .. } => {
                    visit(Ref::Class(*class))
                }
                Inst::MakeRegexp { .. } => visit(Ref::Regexp),
                // The runtime's calls by name an instruction makes (what a
                // run reaches; shake keeps `RUNTIME_NAMES` anyway).
                // (`Interp::to_s` of an array or a `data` value is its
                // elements' and fields' `inspect`.)
                Inst::Interpolate { .. } if exact => {
                    visit(Ref::Runtime("to_s"));
                    visit(Ref::Runtime("inspect"));
                    visit(Ref::Runtime("<<"));
                }
                // (`values_equal` of two hashes or sets looks their keys
                // up: `hash` as well.)
                Inst::Equal { .. } if exact => {
                    visit(Ref::Runtime("=="));
                    visit(Ref::Runtime("hash"));
                }
                // (`case_eq`: a range's bounds by `<=>`, else `==`.)
                Inst::CaseEq { .. } if exact => {
                    visit(Ref::Runtime("=="));
                    visit(Ref::Runtime("hash"));
                    visit(Ref::Runtime("<=>"));
                }
                Inst::MakeHash { .. } if exact => {
                    visit(Ref::Runtime("hash"));
                    visit(Ref::Runtime("=="));
                }
                // (Its message shows the value: `inspect`.)
                Inst::NoMatch { .. } if exact => visit(Ref::Runtime("inspect")),
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
        kw_names: Vec::new(),
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
        takes: Vec::new(),
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
