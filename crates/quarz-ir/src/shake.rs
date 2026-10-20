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
//! nowhere reachable can never be looked up. Ids stay as they are: a
//! dropped function becomes an empty body (that fails if it ever runs),
//! a dropped method an empty record no table refers to.

use std::collections::HashSet;

use crate::*;

/// Names the runtime calls by itself (interpolation, `p`, hashing,
/// sorting, iteration, ranges, JSON, exceptions, construction, the
/// enumerators natives build). A new by-name call in the runtime
/// (`Interp::send`, `call_named`, `has_user_method`, an enumerator)
/// must add its name here.
const RUNTIME_NAMES: &[&str] = &[
    "to_s",
    "inspect",
    "==",
    "!=",
    "===",
    "<=>",
    "hash",
    "eql?",
    "each",
    "succ",
    "status",
    "to_json",
    "initialize",
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
    funcs: Vec<bool>,
    methods: Vec<bool>,
    consts: Vec<bool>,
    names: HashSet<String>,
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
            self.method(m);
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
        for c in &f.consts {
            if let Constant::Symbol(s) = c {
                self.name(s);
            }
        }
        for o in &f.inlined {
            self.func(o.callee);
        }
        for blk in &f.blocks {
            for inst in &blk.insts {
                match inst {
                    Inst::Call { kind, .. } => match kind {
                        CallKind::Method(m) | CallKind::Super(m) => self.method(*m),
                        CallKind::Send(name) => self.name(name),
                        CallKind::Construct { init, .. } => {
                            self.name("initialize");
                            if let Some(m) = init {
                                self.method(*m);
                            }
                        }
                        CallKind::ProcCall | CallKind::Yield | CallKind::Raise => {}
                    },
                    Inst::OwnedCall { method, .. } => self.method(*method),
                    Inst::BinOp { method, op, .. } => {
                        self.name(op.name());
                        if let Some(m) = method {
                            self.method(*m);
                        }
                    }
                    Inst::SymbolProc {
                        method: Some(m), ..
                    } => self.method(*m),
                    Inst::MakeBlock { func, .. } => self.func(*func),
                    Inst::ConstGet { id, .. } => self.constant(*id),
                    _ => {}
                }
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
    let mut s = Shake {
        module,
        by_name,
        funcs: vec![false; module.functions.len()],
        methods: vec![false; module.world.methods.len()],
        consts: vec![false; module.world.consts.len()],
        names: HashSet::new(),
        work: Vec::new(),
    };
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
