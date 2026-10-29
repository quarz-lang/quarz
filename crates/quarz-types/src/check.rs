//! Type checking of method bodies, constant initializers and the main
//! program (phase 3).

use std::rc::Rc;

use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};

use rustc_hash::FxHashMap;

use quarz_syntax::ast::*;
use quarz_syntax::token::OpAssign;
use quarz_syntax::{Diagnostic, Span};

use crate::declare::{TypeScope, SELF_PARAM};
use crate::types::*;
use crate::world::*;

/// Where a local variable lives at run time: `depth` frames up from the
/// current one (0 = the current frame), at `slot`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct VarRef {
    pub depth: u32,
    pub slot: u32,
}

/// What a call expression was resolved to.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub enum CallTarget {
    /// An ordinary method call. The runtime dispatches on the receiver's
    /// class by name when it differs from the method's owner.
    Method { method: MethodId },
    /// `Class.new(...)`: allocate and run `initialize` if any.
    Constructor {
        class: ClassId,
        init: Option<MethodId>,
    },
    /// Calling a procedure value.
    ProcCall,
    /// `x.is_a?(T)`
    IsA(Type),
    /// `x.as(T)` / `x.as?(T)`
    As { ty: Type, optional: bool },
    /// `respond_to?` folded to a constant.
    Constant(bool),
    /// `raise ...`; with a class written by name (`raise K` or `raise K,
    /// m`), the class and its `initialize`, which builds the exception
    /// from the message (`K.new(m)`); without one, `K.new("K")` when the
    /// flag is set, else `K.new()`.
    Raise {
        new: Option<(ClassId, MethodId, bool)>,
    },
    /// `super(...)` resolved to the superclass method.
    Super { method: MethodId },
}

/// What a constant expression refers to.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub enum ConstTarget {
    Class(ClassId),
    /// A field-less enum variant used as a value.
    VariantSingleton(ClassId),
    Const(ConstId),
}

/// The checker's output for the evaluator.
/// The type parameters of a method's call, bound (`Output::type_args`).
pub type TypeArgs = Vec<(TypeParamId, Type)>;

#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct Output {
    pub node_types: FxHashMap<NodeId, Type>,
    pub calls: FxHashMap<NodeId, CallTarget>,
    pub const_targets: FxHashMap<NodeId, ConstTarget>,
    /// Variable occurrences (uses and definitions) keyed by their span.
    pub var_refs: FxHashMap<Span, VarRef>,
    /// Implicit-self calls inside a block with a receiver that go to an
    /// enclosing `self` instead: the receiver of the call is read from
    /// the hidden slot `var_refs[span]`.
    pub outer_self_calls: rustc_hash::FxHashSet<NodeId>,
    /// Calls on a union-typed receiver whose members resolve to different
    /// methods with no common ancestor declaring the name: looked up by
    /// name on the receiver's class at run time.
    pub dynamic_calls: rustc_hash::FxHashSet<NodeId>,
    /// Calls on a union receiver whose members answer with different
    /// methods: each member with its method, for a test of the
    /// receiver's type that calls the right one (an extension's method,
    /// active where the call is, is not found by name at run time).
    pub union_calls: HashMap<NodeId, Vec<(Type, MethodId)>>,
    /// Calls whose checks (a block checked once per member of its
    /// receiver's union) gave tables that disagree, or members that a
    /// test of the class cannot tell apart: called by name.
    pub union_conflicts: rustc_hash::FxHashSet<NodeId>,
    /// Nodes whose checks (a block's, once per type of what it is given)
    /// typed them differently: `node_types` holds the last one's, so
    /// nothing is specialized for it.
    pub varied_types: rustc_hash::FxHashSet<NodeId>,
    /// `&:name` symbols whose checks found different methods: called by
    /// name.
    pub varied_symbols: rustc_hash::FxHashSet<NodeId>,
    /// Interpolations checked more than once whose `to_s` differed.
    pub interp_conflicts: rustc_hash::FxHashSet<NodeId>,
    /// Interpolated expressions (`"#{x}"`) whose type's `to_s` is an
    /// extension's active there: called for the piece, which otherwise
    /// takes the class's own.
    pub interp_to_s: HashMap<NodeId, Vec<(ClassId, Option<MethodId>)>>,
    /// A compound assignment's reader and operator (`f.w += 1`: `w` and
    /// `+`); its writer is the node's `calls` entry.
    pub op_getters: HashMap<NodeId, MethodId>,
    pub op_operators: HashMap<NodeId, MethodId>,
    /// `as`/`as?`/`is_a?` calls whose run-time test must check elements:
    /// the value may be of the class without being of the type.
    pub element_tests: rustc_hash::FxHashSet<NodeId>,
    /// `x.foo!(args)` calls that are sugar for `x = x.foo(args)` (the
    /// receiver's type has no `foo!`): the call targets `foo` and its
    /// result is stored into the receiver, a local or a field.
    pub bang_assign: rustc_hash::FxHashSet<NodeId>,
    /// Functions that must store their `self` in a hidden frame slot.
    pub self_slots: FxHashMap<SelfOwner, u32>,
    /// Calls of a `static def` from code that is not static (a method
    /// body, the top level): each is an error after lowering when the
    /// callee turns out to be compile-time only (docs/14 §3).
    pub static_calls: Vec<(u32, Span, MethodId)>,
    /// The `static(...)` expressions (docs/14 §8), by their node: the file,
    /// the class whose class methods an implicit receiver names, and the
    /// call, evaluated at compile time once every file is checked.
    #[serde(default)]
    pub static_exprs: FxHashMap<NodeId, (u32, ClassId, Expr)>,
    /// Their values, baked (filled by the runner, `StaticRunner::eval`).
    #[serde(default)]
    pub static_values: FxHashMap<NodeId, crate::world::Baked>,
    /// The blocks given to `Meta::ClassDef`'s generating natives
    /// (`def_method`), by their call: the procedure type each was checked
    /// as, from which the generated method takes its signature (docs/14
    /// §5).
    pub lifted_blocks: FxHashMap<NodeId, Type>,
    /// Calls whose block literal is given as a `Quoted` (docs/14 §6), and
    /// whether its procedure type has a receiver (the tree's `SelfRef`):
    /// the lowering builds its tree.
    #[serde(default)]
    pub quoted_blocks: FxHashMap<NodeId, bool>,
    /// The constants read in quoted blocks whose values are literals in
    /// the tree (`Meta::Expr::Lit`), the others being captures.
    #[serde(default)]
    pub quoted_lits: rustc_hash::FxHashSet<NodeId>,
    /// The type arguments a call of a `static def` was resolved with (the
    /// callee's type parameters, bound), for the signatures of what it
    /// generates.
    pub type_args: FxHashMap<NodeId, TypeArgs>,
    /// In `initialize`: the assignments and `super` calls after which the
    /// object is usable (its required fields assigned, docs/03 §4), and
    /// the methods where it is from the start. Failing before that point,
    /// `initialize` leaves an object whose `deinitialize` does not run.
    pub usable_after: rustc_hash::FxHashSet<NodeId>,
    pub usable_on_entry: rustc_hash::FxHashSet<SelfOwner>,
    /// Frame sizes of blocks (keyed by the call node) and lambdas (keyed by
    /// the lambda node).
    pub frame_sizes: FxHashMap<NodeId, u32>,
    /// Frame size of each file's top-level statements, by file index.
    pub unit_frame_sizes: Vec<u32>,
    /// Field index for `@x` reads and writes, keyed by the node.
    pub ivar_fields: FxHashMap<NodeId, usize>,
    /// Classes referred to by constant patterns, keyed by pattern span.
    pub pattern_classes: FxHashMap<Span, ClassId>,
    /// Methods whose `&block` is passed as `&:sym` or `&proc`, by call node.
    pub block_pass: FxHashMap<NodeId, BlockPass>,
    /// For block parameters that destructure a tuple: the arity.
    pub block_destructure: FxHashMap<NodeId, usize>,
    /// Exception classes of each `rescue` clause, keyed by its span.
    pub rescue_classes: FxHashMap<Span, Vec<ClassId>>,
    /// Integer literals typed as `Float` because of their context.
    pub float_literals: rustc_hash::FxHashSet<NodeId>,
    /// Integer literals that are `Integer`s: where one is expected, or
    /// too large for an `Int`.
    pub integer_literals: rustc_hash::FxHashSet<NodeId>,
    /// Expressions whose value is discarded because it is the result of
    /// something declared to return `Nil` (the last expression of such a
    /// method, block or lambda, the value of its `return` or `next`): they
    /// are evaluated and the result is `nil`.
    pub discarded: rustc_hash::FxHashSet<NodeId>,
    /// `for` comprehensions whose value is not used, checked (and to be
    /// lowered) as their `each` expansion (see `ast::ForExpr`).
    pub for_loops: rustc_hash::FxHashSet<NodeId>,
    /// `a && b`, `a || b` (`and`, `or`) and `x &&= v`, `x ||= v` on a value
    /// whose type defines the operator: the call the checker made of it,
    /// `a.&&() { b }`, with the expression's id (see `logical_method`).
    /// Lowering calls it on the left operand's value.
    pub logical_calls: FxHashMap<NodeId, Expr>,
    /// Blocks (by their call's id) and lambdas checked as shareable
    /// procedures: lowering copies what they capture when it makes them,
    /// as `spawn` does, so that they no longer read the creator's frame.
    pub shareable_procs: rustc_hash::FxHashSet<NodeId>,
    /// `new` called on the receiver in a class method: it builds an
    /// instance of the class the method is called on.
    pub self_new: rustc_hash::FxHashSet<NodeId>,
    /// `!x` on a union where only some members define `!`: those members
    /// with their `!` (a value of another member gets the built-in
    /// negation).
    pub not_dispatch: FxHashMap<NodeId, Vec<(Type, MethodId)>>,
    /// The variables (frame, slot) whose release may be observed
    /// (`World::release_observable`): they live to the end of their
    /// scope, not their last use.
    pub lexical_slots: rustc_hash::FxHashSet<(SelfOwner, u32)>,
    /// Statements whose value is not used and may be released observably
    /// (`Res.new(..)` on its own): released at the end of the statement.
    pub released_stmts: rustc_hash::FxHashSet<NodeId>,
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub enum BlockPass {
    /// `&:name`: call `name` (resolved to `method` for the parameter's
    /// static type) on the block's argument; with `true`, for a block
    /// whose result is `Void`, the call's value is discarded (the
    /// procedure gives nil), as in `{ |x| x.name }`.
    Symbol(String, MethodId, bool),
    /// `&expr`: the expression evaluates to a procedure.
    Proc,
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
struct VarInfo {
    name: String,
    declared: Type,
    narrowed: Option<Type>,
    /// In its frame's `Vars::narrowed`.
    listed: bool,
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
struct Frame {
    vars: Vars,
    is_block: bool,
    /// Whose `self` this frame's function runs with (for the hidden
    /// slot that blocks with receivers read the enclosing `self` from).
    owner: SelfOwner,
}

/// The name of the hidden frame variable holding a function's `self`.
const SELF_SLOT: &str = "%self";

/// A function whose frame may hold its `self` in a hidden slot.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum SelfOwner {
    Method(MethodId),
    /// A block or lambda, by the node of the call (or lambda) it belongs to.
    Block(NodeId),
    /// A unit's top level, by file.
    Unit(u32),
    /// A constant or field initializer.
    Init,
}

/// A block with a receiver being checked: what `self` was outside it,
/// and the frame of the function that `self` belongs to.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
struct ReceiverCtx {
    outer_self: Type,
    outer_frame: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub(crate) enum VarKey {
    Local(String),
    IVar(String),
}

pub(crate) type Facts = Vec<(VarKey, Type)>;

/// Narrowed types of all variables and immutable fields at a point.
/// The narrowings at a point: per frame, its number of variables and
/// the narrowed ones (by slot), and the fields'.
type Snapshot = (Vec<FrameSnap>, HashMap<String, Type>);

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
struct FrameSnap {
    len: usize,
    narrowed: Vec<(usize, Type)>,
}

impl FrameSnap {
    /// The narrowing of `slot` then; `None` for a variable declared since.
    fn get(&self, slot: usize) -> Option<Option<&Type>> {
        if slot >= self.len {
            return None;
        }
        Some(
            self.narrowed
                .binary_search_by_key(&slot, |(s, _)| *s)
                .ok()
                .map(|i| &self.narrowed[i].1),
        )
    }
}

/// A frame's variables, found by name, with the slots that may be
/// narrowed listed, so that a snapshot of a branch costs what is narrowed
/// rather than every variable.
#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
struct Vars {
    list: Vec<VarInfo>,
    /// The last slot of each name (a later declaration wins), once the
    /// frame has `INDEXED` variables; a short one is searched.
    index: HashMap<String, usize>,
    /// The slots whose narrowing has been set (a superset of the narrowed
    /// ones; `listed` marks them).
    narrowed: Vec<usize>,
}

impl std::ops::Deref for Vars {
    type Target = [VarInfo];
    fn deref(&self) -> &[VarInfo] {
        &self.list
    }
}

impl Vars {
    const INDEXED: usize = 32;

    fn push(&mut self, v: VarInfo) {
        self.list.push(v);
        let n = self.list.len();
        if n == Self::INDEXED {
            for (i, v) in self.list.iter().enumerate() {
                self.index.insert(v.name.clone(), i);
            }
        } else if n > Self::INDEXED {
            self.index.insert(self.list[n - 1].name.clone(), n - 1);
        }
    }

    /// Rename `slot` (hiding a scoped variable), keeping the index.
    fn rename(&mut self, slot: usize, to: String) {
        let from = std::mem::replace(&mut self.list[slot].name, to.clone());
        if self.list.len() >= Self::INDEXED {
            match self.list.iter().rposition(|v| v.name == from) {
                Some(i) => {
                    self.index.insert(from, i);
                }
                None => {
                    self.index.remove(&from);
                }
            }
            self.index.insert(to, slot);
        }
    }

    fn find(&self, name: &str) -> Option<usize> {
        if self.list.len() >= Self::INDEXED {
            self.index.get(name).copied()
        } else {
            self.list.iter().rposition(|v| v.name == name)
        }
    }

    fn set_narrowed(&mut self, slot: usize, t: Option<Type>) {
        let v = &mut self.list[slot];
        if t.is_some() && !v.listed {
            v.listed = true;
            self.narrowed.push(slot);
        }
        v.narrowed = t;
    }

    /// The narrowed slots, in order; drops the others from the list.
    fn snapshot(&mut self) -> FrameSnap {
        let list = &mut self.list;
        self.narrowed.retain(|&s| {
            let keep = list[s].narrowed.is_some();
            list[s].listed = keep;
            keep
        });
        self.narrowed.sort_unstable();
        FrameSnap {
            len: self.list.len(),
            narrowed: self
                .narrowed
                .iter()
                .map(|&s| (s, self.list[s].narrowed.clone().unwrap()))
                .collect(),
        }
    }
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
struct Env {
    frames: Vec<Frame>,
    self_type: Type,
    /// In a method whose signature mentions `Self`: `self` (and what
    /// `Self`-returning calls on it give) has the opaque type `Self`,
    /// bounded by the class, so that only those can be returned as `Self`
    /// (`Shape.new` cannot: a subclass's caller expects its own class).
    self_opaque: bool,
    class_id: Option<ClassId>,
    /// The class whose body this code is lexically in (fields are
    /// reachable only there); `class_id` changes inside receiver blocks.
    lexical_class: Option<ClassId>,
    /// The blocks with receivers enclosing the current code, outermost
    /// first.
    receivers: Vec<ReceiverCtx>,
    method: Option<MethodId>,
    scope: TypeScope,
    /// The method's return type; `None` outside a method (the top level).
    ret_expected: Option<Type>,
    block_type: Option<Type>,
    /// The block may be left out (`&block: ((A) -> R)?`), so `yield`
    /// cannot run it.
    block_optional: bool,
    in_initialize: bool,
    /// In a `static def`'s body or a `static` statement: code that runs
    /// at compile time, which may call compile-time-only methods.
    is_static: bool,
    assigned_fields: HashSet<String>,
    loop_depth: u32,
    /// Whether a `break`, and a `next`, of the innermost loop has been
    /// checked.
    loop_exits: LoopExits,
    /// While an `ensure` is checked: the types it assigns to each variable
    /// (by frame and slot).
    ensure_assigns: Option<HashMap<(usize, usize), Type>>,
    /// A narrowing being applied is a fact, not an assignment.
    applying_facts: bool,
    /// For each enclosing block (innermost last): the proc's return type
    /// (for `next`) and the collected `break` value types.
    blocks: Vec<BlockCtx>,
    ivar_narrow: HashMap<String, Type>,
    in_rescue: u32,
    file: u32,
    /// While checking a `case/in` arm: the number of variables the current
    /// frame had before the `case`. Pattern variables declared by earlier
    /// arms (at or past this index) are re-declared rather than re-bound.
    pattern_base: Option<usize>,
    /// Index of the innermost frame that runs on another task (`spawn`
    /// block). Variables from frames below it are captured by value and must
    /// be shareable; they cannot be assigned.
    task_frame: Option<usize>,
    /// What that frame is, for diagnostics: a task block, or the body of
    /// a shareable procedure (which copies what it captures the same way).
    task_shareable_proc: bool,
    /// The frame of the innermost block given to `def_method` (docs/14
    /// §5), which becomes a method's body: it captures by value too, and
    /// cannot leave the enclosing method or use its `self`.
    lifted_frame: Option<usize>,
    /// The frame of a block given to the call in `static(...)` (docs/14
    /// §8): it runs at compile time and captures nothing.
    static_frame: Option<usize>,
    /// The next block checked is one (set by the call's check).
    next_block_lifted: bool,
    /// The locals of this body that may change after a closure captures
    /// them (assigned in two places or more, or parameters assigned):
    /// inside a closure that may run later, their narrowings from outside
    /// do not hold. `None` (a body not scanned) counts every local.
    reassigned: Option<Rc<HashSet<String>>>,
    /// The outer locals some closure that may run later in the body
    /// assigns, wherever it is made: not narrowed inside such closures,
    /// which may run after it.
    late_assigned: Rc<HashSet<String>>,
    /// The locals a closure that may run later (a lambda, a block given
    /// to a method that may keep it) assigns: any call (implicit ones
    /// included) may run it, so they are never narrowed in the body.
    never_narrow: Rc<HashSet<String>>,
    /// The next block checked is given to a method that may keep it.
    next_block_escapes: bool,
}

/// What the checks of a block found for `a && b` (`Checker::logical_seen`).
#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
struct LogicalSeen {
    /// A type's own method (the last found).
    method: Option<MethodId>,
    /// The built-in operator.
    builtin: bool,
    /// Reported, or called by name.
    settled: bool,
}

/// What an error reported when checking is done (`Checker::ambiguous`) is
/// about, for reporting it once.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
enum AmbiguousKey {
    Node(NodeId),
}

/// A class method calling `new` on its own class (`Checker::self_news`):
/// the class, the `initialize` called, the method, where, and its file.
pub type SelfNew = (ClassId, Option<MethodId>, MethodId, Span, u32);

/// The first overload's result and the marks to undo its checks, kept
/// while the others are tried (`resolve_pretyped`).
type KeptFirst = (Type, Vec<Option<Type>>, usize, (usize, usize));

/// An entry of `Checker::table_journal`: a node's table and conflict
/// flag before a change.
#[derive(Debug, serde::Serialize, serde::Deserialize)]
enum TableUndo {
    Union(NodeId, Option<Vec<(Type, MethodId)>>, bool),
    Interp(NodeId, Option<Vec<(ClassId, Option<MethodId>)>>),
    /// A compound assignment's reader or operator (`note_op_method`):
    /// what the checks saw, whether it was given up, what was recorded.
    Op(
        (NodeId, bool),
        Option<Option<MethodId>>,
        bool,
        Option<MethodId>,
    ),
    /// A node marked in `Output::varied_types`.
    Varied(NodeId),
    /// A call's `Output::quoted_blocks` entry and `Checker::quoted_seen`
    /// before a check changed them (docs/14 §6).
    Quoted(NodeId, Option<bool>, Option<bool>, Option<(u32, Span)>),
    /// `Checker::logical_seen` of a node before a check changed it.
    Logical(NodeId, Option<LogicalSeen>),
    /// `Output::logical_calls` of a node before a check changed it.
    LogicalCall(NodeId, Option<Box<Expr>>),
    /// A symbol marked in `Output::varied_symbols`.
    VariedSymbol(NodeId),
    /// A `&:name` symbol's record before a check recorded another.
    BlockPass(NodeId, Option<BlockPass>),
    /// A node's type before a check in a block recorded another.
    NodeType(NodeId, Option<Type>),
    /// An integer literal marked in `Output::float_literals` (`true`) or
    /// `integer_literals`, and whether that is not its default type (the
    /// overload rule's literal level, docs/01 §9).
    Literal(NodeId, bool, bool),
}

/// What a piece of code may assign (`Checker::assigned_names`): local
/// variables, and receivers of `x.foo!` calls (with the method), which
/// assign when the receiver's type has no `foo!`.
#[derive(Debug, Default, serde::Serialize, serde::Deserialize)]
struct Assigned {
    names: HashSet<String>,
    bangs: Vec<(String, String)>,
    /// How many places assign each name.
    counts: HashMap<String, u32>,
    /// Scanning for closures that may run later: whether a method keeps
    /// its block is not known before the call is checked, so any block
    /// counts as one.
    late: bool,
    /// Inside a closure that may run later (a lambda, with `late` any
    /// block), and what such closures assign.
    escaping: u32,
    escaped: HashSet<String>,
    /// What such closures assign that is not in scope where they are made
    /// (assigned nowhere before them in the walk): their own locals, or
    /// locals from before the walk (`Checker::lookup_var` tells).
    fresh: HashSet<String>,
    /// The names in scope at this point of the walk (assigned before it,
    /// a closure's parameters inside it).
    known: HashSet<String>,
    /// Inside a loop's body (`while`), whose locals are the method's,
    /// and what is assigned there.
    repeat: u32,
    repeated: HashSet<String>,
    /// The parameters of blocks and lambdas.
    closure_params: HashSet<String>,
    /// Inside a block or lambda, and what is assigned outside any.
    closure_depth: u32,
    outside: HashSet<String>,
    /// A `retry` was seen.
    retries: bool,
    /// The fields assigned (`@x = v`), and whether a `super` was seen
    /// (in `initialize`, it assigns the inherited fields).
    ivars: HashSet<String>,
    supers: bool,
}

impl Assigned {
    fn add(&mut self, name: &str) {
        self.names.insert(name.to_string());
        *self.counts.entry(name.to_string()).or_default() += 1;
        self.note_escaping(name);
        self.known.insert(name.to_string());
        if self.repeat > 0 {
            self.repeated.insert(name.to_string());
        }
        if self.closure_depth == 0 {
            self.outside.insert(name.to_string());
        }
    }

    /// Inside a closure that may run later, `name` is assigned.
    fn note_escaping(&mut self, name: &str) {
        if self.escaping > 0 {
            if self.known.contains(name) {
                self.escaped.insert(name.to_string());
            } else {
                self.fresh.insert(name.to_string());
            }
        }
    }

    /// Walk a closure's body: `escapes` when it may run later.
    /// Scan with `f` code where `name` is a local of its own (a rescue
    /// clause's variable): what it assigns to `name` is not the outer
    /// local's.
    fn scoped(&mut self, name: &str, f: impl FnOnce(&mut Self)) {
        let sets = |a: &Self| {
            [
                a.names.contains(name),
                a.escaped.contains(name),
                a.fresh.contains(name),
                a.known.contains(name),
                a.repeated.contains(name),
                a.outside.contains(name),
            ]
        };
        let had = sets(self);
        let count = self.counts.get(name).copied();
        let bangs = self.bangs.len();
        f(self);
        for (was, set) in had.into_iter().zip([
            &mut self.names,
            &mut self.escaped,
            &mut self.fresh,
            &mut self.known,
            &mut self.repeated,
            &mut self.outside,
        ]) {
            if !was {
                set.remove(name);
            }
        }
        match count {
            Some(c) => {
                self.counts.insert(name.to_string(), c);
            }
            None => {
                self.counts.remove(name);
            }
        }
        let mut i = 0;
        self.bangs.retain(|(n, _)| {
            i += 1;
            i <= bangs || n != name
        });
    }

    fn closure(&mut self, block: &Block, escapes: bool) {
        // (What it assigns first is its own: out of scope after it.)
        let known = self.known.clone();
        for p in &block.params.list {
            self.closure_params.insert(p.name.clone());
            self.known.insert(p.name.clone());
        }
        // (A block's own locals are new each time it runs: its body does
        // not count as code that runs again, as a loop's does.)
        self.closure_depth += 1;
        self.escaping += escapes as u32;
        Checker::assigned_names(&block.body, self);
        self.closure_depth -= 1;
        self.escaping -= escapes as u32;
        self.known = known;
    }
}

#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
struct LoopExits {
    /// The narrowings at each `break`.
    breaks: Vec<Snapshot>,
    /// A `break` runs an `ensure` on its way out, which the narrowings
    /// at it do not show.
    through_ensure: bool,
    skipped: bool,
    /// The `begin` blocks with an `ensure` around the point being checked.
    ensures: u32,
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
struct BlockCtx {
    ret: Type,
    breaks: Vec<Type>,
    is_lambda: bool,
    /// A block given to a method that may keep it (a named `&blk`).
    escapes: bool,
    /// A block given to `def_method`: `break` would leave the generated
    /// method's body.
    lifted: bool,
}

#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
struct InferTable {
    bindings: Vec<Option<Type>>,
}

impl InferTable {
    fn fresh(&mut self) -> Type {
        self.bindings.push(None);
        Type::Var(self.bindings.len() as InferVar - 1)
    }

    fn resolve(&self, t: &Type) -> Type {
        match t {
            // A variable of another method's table (a failed overload's
            // result leaking out) is unbound here.
            Type::Var(v) => match self.bindings.get(*v as usize) {
                Some(Some(b)) => self.resolve(b),
                _ => t.clone(),
            },
            Type::Nothing | Type::Void | Type::Param(_) => t.clone(),
            Type::Class(id, args) => {
                Type::Class(*id, args.iter().map(|a| self.resolve(a)).collect())
            }
            Type::ClassObject(id, args) => {
                Type::ClassObject(*id, args.iter().map(|a| self.resolve(a)).collect())
            }
            Type::TypeOf(t) => Type::type_of(self.resolve(t)),
            Type::Union(ms) => Type::union_of(ms.iter().map(|m| self.resolve(m)).collect()),
            Type::Tuple(ts) => Type::Tuple(ts.iter().map(|t| self.resolve(t)).collect()),
            Type::Proc(rc, ps, r, sh) => Type::Proc(
                rc.as_ref().map(|t| Box::new(self.resolve(t))),
                ps.iter().map(|p| self.resolve(p)).collect(),
                Box::new(self.resolve(r)),
                *sh,
            ),
        }
    }

    /// Bind `v` to `t`, never to a type that contains `v` (resolving
    /// would not end): `v = v | Int` binds `v` to `Int`, and a binding
    /// that nests `v` (`v = Array[v]`) fails.
    fn bind(&mut self, v: InferVar, t: Type) -> bool {
        let t = match self.resolve(&t) {
            Type::Union(ms) => {
                Type::union_of(ms.into_iter().filter(|m| *m != Type::Var(v)).collect())
            }
            t => t,
        };
        if t == Type::Var(v) {
            return true;
        }
        if t.mentions_var(v) {
            return false;
        }
        self.bindings[v as usize] = Some(t);
        true
    }

    fn save(&self) -> Vec<Option<Type>> {
        self.bindings.clone()
    }

    fn restore(&mut self, saved: Vec<Option<Type>>) {
        self.bindings = saved;
    }
}

/// The state of a `Checker` before a REPL input (`repl_snapshot`).
pub struct ReplSnapshot {
    world: World,
    out: Output,
    infer: InferTable,
    repl_env: Option<Env>,
    static_done: Vec<bool>,
    defaults_checked: HashSet<ClassId>,
    init_checked: HashSet<ClassId>,
    file_mains: Vec<Option<ClassId>>,
    self_news: Vec<SelfNew>,
}

/// The deepest `coerce` recursion: a defensive limit (see
/// `World::is_subtype`).
const COERCE_DEPTH: u32 = 256;

pub struct Checker {
    /// A compound assignment's reader (`false`) and operator (`true`)
    /// found by each check, and those given up (`note_op_method`).
    op_seen: HashMap<(NodeId, bool), Option<MethodId>>,
    /// What the checks of a block found for `a && b` / `a || b`: a type's
    /// own method, the built-in operator, and whether that was reported.
    logical_seen: HashMap<NodeId, LogicalSeen>,
    /// Files whose checks were read back (`mark_reused`).
    reused_files: rustc_hash::FxHashSet<u32>,
    /// Whether each check of a call (a union receiver's members, a block
    /// checked once per type) found its block parameter a `Quoted`: they
    /// must agree, the call passing one value (docs/14 §6).
    quoted_seen: HashMap<NodeId, bool>,
    /// The call of the `static(...)` being checked: it runs at compile
    /// time, so it may be compile-time only (docs/14 §8).
    static_expr_call: Option<NodeId>,
    /// The calls whose checks disagreed on that, with where they are:
    /// reported once the check ends (`flush_ambiguous`), so that the
    /// order the checks ran in (a union's members) does not matter.
    quoted_conflicts: HashMap<NodeId, (u32, Span)>,
    /// How many of `world.static_stmts` have been checked (and run):
    /// the extra units of a test run add theirs later.
    static_done: Vec<bool>,
    /// In the REPL, the unit being declared (its file and the offset its
    /// spans start at): a `static` statement may call a `static def` of
    /// an earlier input or of a required file, not of its own unit.
    pub repl_unit: Option<(u32, u32)>,
    op_given_up: rustc_hash::FxHashSet<(NodeId, bool)>,
    pub world: World,
    pub diagnostics: Vec<(u32, Diagnostic)>,
    /// Calls a run-time class test cannot choose a method for
    /// (`ambiguous_call`), reported once checking is done: inside a
    /// block, an error would make the method given it fail to match.
    ambiguous: Vec<(u32, AmbiguousKey, Diagnostic)>,
    /// What `note_union_table` and `note_interp_to_s` replaced, so that a
    /// check thrown away (an overload that does not match, a second pass)
    /// leaves nothing behind (`discard_tables`).
    table_journal: Vec<TableUndo>,
    /// Ambiguous calls found in method bodies, checked once whatever the
    /// check that needed them (`ensure_method_checked`): kept when that
    /// check is thrown away.
    kept_ambiguous: Vec<(u32, AmbiguousKey, Diagnostic)>,
    /// The ranges of `diagnostics` method bodies produced, and those
    /// rescued from a check thrown away (`truncate_diagnostics`).
    body_diagnostics: Vec<(usize, usize)>,
    rescued: Vec<(u32, Diagnostic)>,
    pub out: Output,
    infer: InferTable,
    env: Env,
    touched: Vec<NodeId>,
    /// The type arguments of each candidate tried for a call of a
    /// `static def` (`try_candidate`); `finish_call` keeps the chosen one.
    type_args_trials: Vec<(NodeId, MethodId, TypeArgs)>,
    /// The variables of the frames checked since the last
    /// `finish_frame_types`, with their declared types: those whose
    /// release may be observed go to `Output::lexical_slots`.
    frame_vars: Vec<(SelfOwner, u32, Type)>,
    /// Calls whose block has a `break` of its own, and the type of the
    /// values it gives the call (`loop { }` without one never returns).
    breaking_blocks: HashMap<NodeId, Type>,
    /// Statements whose value is not used (calls, literals) since the last
    /// `finish_frame_types`: those whose release may be observed go to
    /// `Output::released_stmts`.
    temp_stmts: Vec<NodeId>,
    /// The pseudo-class of each file's top-level methods, by file index.
    file_mains: Vec<Option<ClassId>>,
    /// The REPL's top-level environment, kept across inputs.
    repl_env: Option<Env>,
    /// Methods currently being checked (to detect inference cycles).
    in_progress: Vec<MethodId>,
    /// While re-checking an implicit-self call on an enclosing `self`.
    in_outer_self: bool,
    /// Classes whose field defaults have been checked.
    defaults_checked: HashSet<ClassId>,
    /// Classes checked for required fields without an `initialize`.
    init_checked: HashSet<ClassId>,
    /// Integer literals kept `Int` even where a `Float` is expected: the
    /// members of a union receiver disagreed on them (see `check_call_on`).
    int_literals: rustc_hash::FxHashSet<NodeId>,
    /// `new` on the receiver in class methods: (the class, its
    /// `initialize`, the class method, where).
    /// How deep `coerce` is in its own recursion (`COERCE_DEPTH`).
    coerce_depth: u32,
    /// The questions `coerce` is answering (`World::subtype_open`).
    coerce_open: Vec<(Type, Type)>,
    self_news: Vec<SelfNew>,
    /// Set by `check_body` for the statement it checks next: its value is
    /// not used (a statement before the last, or the last of a body that
    /// discards it). `check_expr` takes it, so only that statement itself
    /// sees it, not the expressions in it.
    stmt_unused: bool,
    /// Set before `check_body` by a caller whose body's value is discarded
    /// (it is declared to return `Nil`).
    next_body_void: bool,
}

/// Arguments after matching to parameters.
struct MatchedArg<'a> {
    param_ty: Type,
    arg: &'a Expr,
    /// Already computed type (for arguments typed before overload
    /// resolution).
    pre_type: Option<Type>,
}

impl Checker {
    pub fn new(world: World, file_mains: Vec<Option<ClassId>>) -> Checker {
        let mut world = world;
        world.freeze_ancestors(true);
        let env = Env {
            frames: vec![Frame {
                vars: Vars::default(),
                is_block: false,
                owner: SelfOwner::Init,
            }],
            self_type: Type::class(file_mains.iter().flatten().next().copied().unwrap_or(0)),
            self_opaque: false,
            class_id: None,
            lexical_class: None,
            receivers: Vec::new(),
            method: None,
            scope: TypeScope::default(),
            ret_expected: None,
            block_type: None,
            block_optional: false,
            in_initialize: false,
            is_static: false,
            assigned_fields: HashSet::default(),
            loop_depth: 0,
            loop_exits: LoopExits::default(),
            ensure_assigns: None,
            applying_facts: false,
            blocks: Vec::new(),
            ivar_narrow: HashMap::default(),
            in_rescue: 0,
            file: 1,
            pattern_base: None,
            task_frame: None,
            task_shareable_proc: false,
            reassigned: None,
            late_assigned: Rc::default(),
            never_narrow: Rc::default(),
            next_block_escapes: false,
            lifted_frame: None,
            static_frame: None,
            next_block_lifted: false,
        };
        Checker {
            op_seen: HashMap::default(),
            logical_seen: HashMap::default(),
            reused_files: Default::default(),
            static_done: Vec::new(),
            quoted_seen: HashMap::default(),
            static_expr_call: None,
            quoted_conflicts: HashMap::default(),
            repl_unit: None,
            op_given_up: Default::default(),
            world,
            diagnostics: Vec::new(),
            ambiguous: Vec::new(),
            table_journal: Vec::new(),
            kept_ambiguous: Vec::new(),
            body_diagnostics: Vec::new(),
            rescued: Vec::new(),
            out: Output::default(),
            infer: InferTable::default(),
            env,
            touched: Vec::new(),
            type_args_trials: Vec::new(),
            frame_vars: Vec::new(),
            breaking_blocks: HashMap::default(),
            temp_stmts: Vec::new(),
            file_mains,
            repl_env: None,
            in_progress: Vec::new(),
            in_outer_self: false,
            defaults_checked: HashSet::default(),
            init_checked: HashSet::default(),
            int_literals: Default::default(),
            coerce_depth: 0,
            coerce_open: Vec::new(),
            self_news: Vec::new(),
            stmt_unused: false,
            next_body_void: false,
        }
    }

    // ----- diagnostics -----------------------------------------------------

    fn error(&mut self, message: impl Into<String>, span: Span) {
        self.diagnostics
            .push((self.env.file, Diagnostic::error(message, span)));
    }

    /// An error in `file`, which is not the environment's (a `static`
    /// statement reported after its check).
    pub(crate) fn error_in(&mut self, file: u32, message: impl Into<String>, span: Span) {
        self.diagnostics
            .push((file, Diagnostic::error(message, span)));
    }

    fn warning(&mut self, message: impl Into<String>, span: Span) {
        self.diagnostics
            .push((self.env.file, Diagnostic::warning(message, span)));
    }

    fn name(&self, t: &Type) -> String {
        self.world.type_name(&self.infer.resolve(t))
    }

    // ----- entry points ------------------------------------------------------

    /// The pseudo-class holding the top-level methods of file `file`.
    fn file_main(&self, file: u32) -> Option<ClassId> {
        self.file_mains.get(file as usize).copied().flatten()
    }

    /// Register the pseudo-class of a file loaded after construction (a
    /// `require` in the REPL).
    pub fn add_file_main(&mut self, file: u32, main: ClassId) {
        let index = file as usize;
        if self.file_mains.len() <= index {
            self.file_mains.resize(index + 1, None);
        }
        self.file_mains[index] = Some(main);
    }

    /// Check every method body, constant initializer and each file's
    /// top-level statements.
    /// The constants' types, inferred from their initializers (the first
    /// step of `check_all`, also done before the `static` statements run:
    /// the cache's constant check must come before them).
    pub fn check_consts(&mut self) {
        let count = self.world.consts.len();
        for cid in 0..count as ConstId {
            self.const_type(cid, Span::empty(0));
        }
    }

    /// The constants of the files `in_files` accepts.
    pub fn check_consts_of(&mut self, in_files: &dyn Fn(u32) -> bool) {
        let count = self.world.consts.len();
        for cid in 0..count as ConstId {
            if in_files(self.world.consts[cid as usize].file) {
                self.const_type(cid, Span::empty(0));
            }
        }
    }

    /// Read a file's cached checks into this checker (`cache::apply`).
    pub fn apply_cached(
        &mut self,
        checks: crate::cache::Checks,
        file: u32,
        files: &dyn Fn(&str) -> Option<u32>,
    ) -> Option<Vec<Diagnostic>> {
        crate::cache::apply(
            &mut self.world,
            &mut self.out,
            &mut self.self_news,
            checks,
            file,
            files,
        )
    }

    pub fn check_all(&mut self, units: &[(u32, Vec<&Expr>)]) {
        self.check_consts();
        let count = self.world.methods.len();
        for mid in 0..count as MethodId {
            self.ensure_method_checked(mid);
        }
        self.check_field_defaults();
        self.check_uninitialized_fields();
        self.check_signature_bounds();
        for (file, body) in units {
            self.check_main(*file, body);
        }
        self.check_inherited_constructors();
    }

    /// The type arguments written in method signatures and field
    /// declarations meet their parameters' bounds (`x: Acc[Other]?`).
    fn check_signature_bounds(&mut self) {
        let saved_file = self.env.file;
        for mid in 0..self.world.methods.len() as MethodId {
            let m = self.world.method(mid);
            if m.file == 0 || m.synth != Synth::None || self.reused_files.contains(&m.file) {
                continue;
            }
            let (file, span) = (m.file, m.span);
            let mut types: Vec<(Type, Span)> =
                m.params.iter().map(|p| (p.ty.clone(), p.span)).collect();
            // The bounds of its own type parameters (`[V <: H[Int]]`).
            for p in &m.type_params {
                types.extend(p.bounds.iter().map(|b| (b.clone(), span)));
            }
            types.push((m.ret.clone(), span));
            if let Some((_, t)) = &m.block {
                types.push((t.clone(), span));
            }
            self.env.file = file;
            for (t, span) in types {
                self.check_bounds_deep(&t, span);
            }
        }
        for cid in 0..self.world.classes.len() as ClassId {
            let c = self.world.class(cid);
            if c.file == 0 || self.reused_files.contains(&c.file) {
                continue;
            }
            self.env.file = c.file;
            let fields: Vec<(Type, Span)> =
                c.fields.iter().map(|f| (f.ty.clone(), f.span)).collect();
            // The superclass and the modules included and extended, whose
            // arguments may be the class's own parameters (`G[U] < H[U]`):
            // a parameter meets a bound its own bounds imply.
            let span = c.span;
            let heads: Vec<Type> = c
                .superclass
                .iter()
                .chain(&c.includes)
                .chain(&c.extends)
                .cloned()
                .collect();
            let param_bounds: Vec<Type> = c
                .type_params
                .iter()
                .flat_map(|p| p.bounds.iter().cloned())
                .collect();
            for b in param_bounds {
                self.check_bounds_deep(&b, span);
            }
            for (t, span) in fields {
                self.check_bounds_deep(&t, span);
            }
            self.check_head_bounds(heads, span);
        }
        // An extension's included modules and its parameters' bounds.
        for i in 0..self.world.extensions.len() {
            let e = &self.world.extensions[i];
            if e.file == 0 || self.reused_files.contains(&e.file) {
                continue;
            }
            self.env.file = e.file;
            let span = e.span;
            let heads = e.includes.clone();
            let bounds: Vec<Type> = e
                .type_params
                .iter()
                .flat_map(|p| p.bounds.iter().cloned())
                .collect();
            for b in bounds {
                self.check_bounds_deep(&b, span);
            }
            self.check_head_bounds(heads, span);
        }
        self.env.file = saved_file;
    }

    /// The bounds of the classes and modules a class or extension builds
    /// on (a superclass, the modules included or extended), whose
    /// arguments may be its own parameters: a parameter meets a bound its
    /// own bounds imply.
    fn check_head_bounds(&mut self, heads: Vec<Type>, span: Span) {
        for t in heads {
            if let Type::Class(_, args) = &t {
                if !args.iter().any(|a| a.has_vars()) {
                    self.check_class_bounds(&t, span);
                }
                args.iter().for_each(|a| self.check_bounds_deep(a, span));
            }
        }
    }

    /// `check_class_bounds` for every class type in `t` whose arguments
    /// are known (not type parameters, whose bounds the signature states).
    fn check_bounds_deep(&mut self, t: &Type, span: Span) {
        match t {
            Type::Class(_, args) | Type::ClassObject(_, args) => {
                if matches!(t, Type::Class(..))
                    && !args.iter().any(|a| a.has_vars() || a.mentions_any_param())
                {
                    self.check_class_bounds(t, span);
                }
                args.iter().for_each(|a| self.check_bounds_deep(a, span));
            }
            Type::TypeOf(t) => self.check_bounds_deep(t, span),
            Type::Union(ms) | Type::Tuple(ms) => {
                ms.iter().for_each(|m| self.check_bounds_deep(m, span))
            }
            Type::Proc(rc, ps, r, _) => {
                if let Some(rc) = rc {
                    self.check_bounds_deep(rc, span);
                }
                ps.iter().for_each(|p| self.check_bounds_deep(p, span));
                self.check_bounds_deep(r, span);
            }
            Type::Nothing | Type::Void | Type::Param(_) | Type::Var(_) => {}
        }
    }

    /// A class method that calls `new` on its receiver builds an instance
    /// of each subclass it is called on: a subclass that inherits the
    /// method must accept the same arguments in its `initialize` (keep
    /// it, or add only optional parameters), or override the method.
    fn check_inherited_constructors(&mut self) {
        // (Kept: a later unit's subclasses inherit them too, as the
        // prelude's do a program's, `PreludeState::self_news`.)
        let mut sites = self.self_news.clone();
        sites.sort_by_key(|s| (s.0, s.2, s.3.start));
        sites.dedup_by_key(|s| (s.0, s.2, s.3.start));
        let mut reported = HashSet::default();
        for (cid, init, method, _, _) in sites {
            let mname = self.world.method(method).name.clone();
            let nclasses = self.world.classes.len() as ClassId;
            for sid in 0..nclasses {
                if sid == cid
                    || self.world.class(sid).kind != ClassKind::Class
                    || !self.world.class_is_a(sid, cid)
                {
                    continue;
                }
                // The class methods and initialize between the subclass
                // and the class that calls `new`.
                let mut overrides = false;
                let mut own_init = None;
                let mut cur = Some(sid);
                while let Some(c) = cur {
                    if c == cid {
                        break;
                    }
                    let class = self.world.class(c);
                    if class.singleton_methods.contains_key(&mname) {
                        overrides = true;
                        break;
                    }
                    if own_init.is_none() {
                        own_init = class
                            .methods
                            .get("initialize")
                            .and_then(|ids| ids.first().copied());
                    }
                    cur = class.superclass.as_ref().and_then(|t| match t {
                        Type::Class(id, _) => Some(*id),
                        _ => None,
                    });
                }
                let Some(sinit) = own_init else {
                    continue;
                };
                if overrides || !reported.insert((sid, method)) {
                    continue;
                }
                let s = self.world.method(sinit).clone();
                let fits = match init {
                    Some(i) => {
                        let p = self.world.method(i).clone();
                        p.params.len() <= s.params.len()
                            && p.params.iter().zip(&s.params).all(|(a, b)| {
                                a.kind == b.kind
                                    && (a.ty == b.ty || self.world.is_subtype(&a.ty, &b.ty))
                            })
                            && s.params[p.params.len()..]
                                .iter()
                                .all(|b| b.default.is_some())
                    }
                    None => s.params.iter().all(|b| b.default.is_some()),
                };
                if !fits {
                    let (sname, cname) = (
                        self.world.class(sid).name.clone(),
                        self.world.class(cid).name.clone(),
                    );
                    self.diagnostics.push((
                        s.file,
                        Diagnostic::error(
                            format!("`{sname}#initialize` does not take the arguments of `new` in `{cname}.{mname}`, which `{sname}` inherits: keep the parameters of `{cname}#initialize` (adding only optional ones) or override `self.{mname}` in `{sname}`"),
                            s.span,
                        ),
                    ));
                }
            }
        }
    }

    /// The fields `initialize` must assign (see `init`): every field and
    /// the class's own ones whose declared type does not admit `nil`
    /// and that have no default.
    /// Whether `m`, an `initialize` found for `cid`, may make a `cid`:
    /// it can assign every field that needs it.
    fn constructs(&self, cid: ClassId, m: &MethodInfo) -> bool {
        let owner = self.world.class(m.owner);
        if m.extension.is_some() || owner.kind == ClassKind::Module {
            return !self.world.has_fields_to_assign(cid, true);
        }
        // The classes from `cid` up to the owner, the owner aside.
        !self
            .world
            .superclass_chain(cid)
            .into_iter()
            .take_while(|k| *k != m.owner)
            .any(|k| self.world.has_fields_to_assign(k, false))
    }

    pub(crate) fn required_fields(
        &self,
        cid: ClassId,
    ) -> (
        std::collections::BTreeSet<String>,
        std::collections::BTreeSet<String>,
    ) {
        let all = self
            .world
            .all_fields(cid)
            .into_iter()
            .filter(|(f, _)| !f.has_default() && !self.world.field_may_stay_nil(&f.ty))
            .map(|(f, _)| f.name)
            .collect();
        let own = self
            .world
            .class(cid)
            .fields
            .iter()
            .filter(|f| !f.has_default() && !self.world.field_may_stay_nil(&f.ty))
            .map(|f| f.name.clone())
            .collect();
        (all, own)
    }

    /// A class with required fields of its own (see `required_fields`)
    /// must have an `initialize` that assigns them: an inherited one does
    /// not know them, and without one they would stay nil.
    fn check_uninitialized_fields(&mut self) {
        let count = self.world.classes.len();
        for cid in 0..count as ClassId {
            if !self.init_checked.insert(cid) {
                continue;
            }
            self.check_default_uses(cid);
            let class = self.world.class(cid);
            if class.kind != ClassKind::Class
                || class.auto_initialize
                || class
                    .methods
                    .get("initialize")
                    .is_some_and(|ms| !ms.is_empty())
            {
                continue;
            }
            let (_, own) = self.required_fields(cid);
            let Some(name) = own.into_iter().next() else {
                continue;
            };
            let span = class
                .fields
                .iter()
                .find(|f| f.name == name)
                .map_or(class.span, |f| f.span);
            self.error(
                format!(
                    "field `@{name}` has no default and `{}` has no `initialize` to assign it",
                    class.name
                ),
                span,
            );
        }
    }

    /// Field defaults run before `initialize`, in declaration order (the
    /// inherited ones first): one may not use the object, or read a
    /// field that is not set yet.
    fn check_default_uses(&mut self, cid: ClassId) {
        let fields: Vec<FieldInfo> = self
            .world
            .all_fields(cid)
            .into_iter()
            .map(|(f, _)| f)
            .collect();
        if self
            .world
            .class(cid)
            .fields
            .iter()
            .all(|f| f.default.is_none())
        {
            return;
        }
        let all: std::collections::BTreeSet<String> =
            fields.iter().map(|f| f.name.clone()).collect();
        let own: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
        let mut errors = Vec::new();
        {
            let calls = |id: NodeId| self.out.calls.get(&id).cloned();
            let world = &self.world;
            let uses_self = |mid: MethodId| {
                let m = world.method(mid);
                !(m.is_native && m.owner == world.builtin.kernel)
            };
            let diverges = |mid: MethodId| world.method(mid).ret.is_nothing();
            let mut set: Vec<String> = Vec::new();
            for f in &fields {
                if let Some(d) = &f.default {
                    if self
                        .world
                        .class(cid)
                        .fields
                        .iter()
                        .any(|g| g.name == f.name)
                    {
                        let mut c =
                            crate::init::InitCheck::new(&all, &own, &calls, &uses_self, &diverges);
                        c.default(d, &set);
                        errors.extend(c.errors);
                    }
                    set.push(f.name.clone());
                }
            }
        }
        for (msg, span) in errors {
            self.error(msg, span);
        }
    }

    /// Field defaults run with `self` = the new object, as `initialize`
    /// would: check each against its field's type (and record what the
    /// lowering needs, such as constant targets).
    fn check_field_defaults(&mut self) {
        let count = self.world.classes.len();
        for cid in 0..count as ClassId {
            if self.defaults_checked.contains(&cid) {
                continue;
            }
            let class = self.world.class(cid).clone();
            if class.fields.iter().all(|f| f.default.is_none()) {
                continue;
            }
            self.defaults_checked.insert(cid);
            let self_type = Type::Class(
                cid,
                class
                    .type_params
                    .iter()
                    .map(|p| Type::Param(p.id))
                    .collect(),
            );
            let scope = TypeScope {
                namespace: Some(cid),
                params: class
                    .type_params
                    .iter()
                    .map(|p| (p.name.clone(), p.id))
                    .collect(),
                self_type: Some(self_type.clone()),
            };
            let env = self.fresh_env(self_type, Some(cid), None, scope, class.file);
            let saved_env = std::mem::replace(&mut self.env, env);
            let saved_infer = std::mem::take(&mut self.infer);
            let saved_touched = std::mem::take(&mut self.touched);
            let saved_frame_vars = std::mem::take(&mut self.frame_vars);
            let saved_temp_stmts = std::mem::take(&mut self.temp_stmts);
            let mut active = class.usings.clone();
            for e in self.file_extensions(class.file) {
                if !active.contains(&e) {
                    active.push(e);
                }
            }
            let saved_active = std::mem::replace(&mut self.world.active_extensions, active);
            for f in &class.fields {
                let Some(d) = &f.default else {
                    continue;
                };
                self.scan_closures([&**d], std::iter::empty());
                let t = self.check_expr(d, Some(&f.ty));
                if !self.coerce(&t, &f.ty) {
                    self.error(
                        format!(
                            "default value of type {} for field `@{}` of type {}",
                            self.name(&t),
                            f.name,
                            self.name(&f.ty)
                        ),
                        d.span,
                    );
                }
            }
            self.finish_frame_types();
            self.env = saved_env;
            self.infer = saved_infer;
            self.touched = saved_touched;
            self.frame_vars = saved_frame_vars;
            self.temp_stmts = saved_temp_stmts;
            self.world.active_extensions = saved_active;
        }
    }

    fn check_main(&mut self, file: u32, body: &[&Expr]) {
        let main = self.file_main(file).unwrap_or(self.world.builtin.object);
        let mut env = self.fresh_env(
            Type::class(main),
            Some(main),
            None,
            TypeScope::default(),
            file,
        );
        env.ret_expected = Some(Type::Void);
        let saved_infer = std::mem::take(&mut self.infer);
        self.check_top_level(env, file, body, false);
        self.infer = saved_infer;
    }

    /// Check top-level statements in `env`, returning the environment. A
    /// file's statements' values are not used; the REPL shows its last's
    /// (`last_used`).
    fn check_top_level(&mut self, env: Env, file: u32, body: &[&Expr], last_used: bool) -> Env {
        let saved_env = std::mem::replace(&mut self.env, env);
        self.scan_closures(body.iter().copied(), std::iter::empty());
        // The REPL's top level goes on over inputs: what one input assigns
        // the next may assign again.
        if last_used {
            self.env.reassigned = None;
        }
        self.world.active_extensions = self.file_extensions(file);
        for (i, expr) in body.iter().enumerate() {
            self.stmt_unused = !(last_used && i + 1 == body.len());
            let t = self.check_expr(expr, None);
            if i + 1 < body.len() {
                self.note_temp_stmt(expr);
            }
            if t.is_nothing() {
                // Statements after `exit` etc. are unreachable; keep going
                // for diagnostics.
            }
        }
        self.finish_frame_types();
        let size = self.env.frames[0].vars.len() as u32;
        if self.out.unit_frame_sizes.len() <= file as usize {
            self.out.unit_frame_sizes.resize(file as usize + 1, 0);
        }
        self.out.unit_frame_sizes[file as usize] = size;
        std::mem::replace(&mut self.env, saved_env)
    }

    /// Check REPL input: unchecked methods and constants, then the
    /// statements in the persistent top-level environment.
    pub fn check_repl(&mut self, file: u32, body: &[&Expr]) {
        let count = self.world.consts.len();
        for cid in 0..count as ConstId {
            self.const_type(cid, Span::empty(0));
        }
        let count = self.world.methods.len();
        for mid in 0..count as MethodId {
            self.ensure_method_checked(mid);
        }
        self.check_field_defaults();
        self.check_uninitialized_fields();
        let main = self.file_main(file).unwrap_or(self.world.builtin.object);
        let env = match self.repl_env.take() {
            Some(env) => env,
            None => {
                let mut env = self.fresh_env(
                    Type::class(main),
                    Some(main),
                    None,
                    TypeScope::default(),
                    file,
                );
                env.ret_expected = Some(Type::Void);
                env
            }
        };
        // The REPL keeps its inference variables across inputs.
        let env = self.check_top_level(env, file, body, true);
        self.repl_env = Some(env);
    }

    /// What a REPL input may change, to roll it back if it fails
    /// (docs/05 §7: a failed input is discarded).
    pub fn repl_snapshot(&self) -> ReplSnapshot {
        ReplSnapshot {
            world: self.world.clone(),
            out: self.out.clone(),
            infer: self.infer.clone(),
            repl_env: self.repl_env.clone(),
            static_done: self.static_done.clone(),
            defaults_checked: self.defaults_checked.clone(),
            init_checked: self.init_checked.clone(),
            file_mains: self.file_mains.clone(),
            self_news: self.self_news.clone(),
        }
    }

    /// Back to `s`: a failed input leaves no declaration, variable or
    /// checked body behind.
    pub fn repl_restore(&mut self, s: ReplSnapshot) {
        self.world = s.world;
        self.out = s.out;
        self.infer = s.infer;
        self.repl_env = s.repl_env;
        self.static_done = s.static_done;
        self.defaults_checked = s.defaults_checked;
        self.init_checked = s.init_checked;
        self.file_mains = s.file_mains;
        self.self_news = s.self_news;
        self.quoted_seen.clear();
        self.quoted_conflicts.clear();
        self.table_journal.clear();
    }

    /// Discard the diagnostics of a failed REPL input and forget the
    /// variables it declared.
    pub fn take_diagnostics(&mut self) -> Vec<(u32, Diagnostic)> {
        self.flush_ambiguous();
        std::mem::take(&mut self.diagnostics)
    }

    /// Report the ambiguous calls found (`Checker::ambiguous`).
    /// Record a node's union table and conflict flag before a change.
    fn journal_union(&mut self, id: NodeId) {
        let before = self.out.union_calls.get(&id).cloned();
        let conflict = self.out.union_conflicts.contains(&id);
        self.table_journal
            .push(TableUndo::Union(id, before, conflict));
    }

    /// Where the call tables and the ambiguous calls stand, for
    /// `discard_tables`.
    fn table_mark(&self) -> (usize, usize) {
        (self.table_journal.len(), self.ambiguous.len())
    }

    /// Undo what the checks since `mark` recorded in the call tables.
    fn discard_tables(&mut self, mark: (usize, usize)) {
        while self.table_journal.len() > mark.0 {
            match self.table_journal.pop().unwrap() {
                TableUndo::Union(id, t, conflict) => {
                    if conflict {
                        self.out.union_conflicts.insert(id);
                    } else {
                        self.out.union_conflicts.remove(&id);
                    }
                    match t {
                        Some(t) => self.out.union_calls.insert(id, t),
                        None => self.out.union_calls.remove(&id),
                    };
                }
                TableUndo::Op(key, seen, given_up, recorded) => {
                    match seen {
                        Some(f) => self.op_seen.insert(key, f),
                        None => self.op_seen.remove(&key),
                    };
                    if given_up {
                        self.op_given_up.insert(key);
                    } else {
                        self.op_given_up.remove(&key);
                    }
                    let map = if key.1 {
                        &mut self.out.op_operators
                    } else {
                        &mut self.out.op_getters
                    };
                    match recorded {
                        Some(m) => map.insert(key.0, m),
                        None => map.remove(&key.0),
                    };
                }
                TableUndo::Quoted(id, blocks, seen, conflict) => {
                    match conflict {
                        Some(c) => self.quoted_conflicts.insert(id, c),
                        None => self.quoted_conflicts.remove(&id),
                    };
                    match blocks {
                        Some(r) => self.out.quoted_blocks.insert(id, r),
                        None => self.out.quoted_blocks.remove(&id),
                    };
                    match seen {
                        Some(q) => self.quoted_seen.insert(id, q),
                        None => self.quoted_seen.remove(&id),
                    };
                }
                TableUndo::Varied(id) => {
                    self.out.varied_types.remove(&id);
                }
                TableUndo::Literal(id, float, _) => {
                    if float {
                        self.out.float_literals.remove(&id);
                    } else {
                        self.out.integer_literals.remove(&id);
                    }
                }
                TableUndo::LogicalCall(id, call) => {
                    match call {
                        Some(c) => self.out.logical_calls.insert(id, *c),
                        None => self.out.logical_calls.remove(&id),
                    };
                }
                TableUndo::Logical(id, seen) => {
                    match seen {
                        Some(seen) => self.logical_seen.insert(id, seen),
                        None => self.logical_seen.remove(&id),
                    };
                }
                TableUndo::VariedSymbol(id) => {
                    self.out.varied_symbols.remove(&id);
                }
                TableUndo::BlockPass(id, b) => {
                    match b {
                        Some(b) => self.out.block_pass.insert(id, b),
                        None => self.out.block_pass.remove(&id),
                    };
                }
                TableUndo::NodeType(id, t) => {
                    match t {
                        Some(t) => self.out.node_types.insert(id, t),
                        None => self.out.node_types.remove(&id),
                    };
                }
                TableUndo::Interp(id, t) => {
                    self.out.interp_conflicts.remove(&id);
                    match t {
                        Some(t) => self.out.interp_to_s.insert(id, t),
                        None => self.out.interp_to_s.remove(&id),
                    };
                }
            }
        }
        self.ambiguous.truncate(mark.1);
    }

    /// Throw away the diagnostics from `n` on, except those of method
    /// bodies checked meanwhile (checked once, whatever needed them).
    fn truncate_diagnostics(&mut self, n: usize) {
        while let Some(&(start, end)) = self.body_diagnostics.last() {
            if end <= n {
                break;
            }
            self.body_diagnostics.pop();
            let start = start.max(n);
            let end = end.min(self.diagnostics.len());
            if start < end {
                self.rescued
                    .extend(self.diagnostics[start..end].iter().cloned());
            }
        }
        self.diagnostics.truncate(n);
    }

    fn flush_ambiguous(&mut self) {
        self.table_journal.clear();
        // The calls whose kept checks disagreed on taking a `Quoted`.
        let mut conflicts: Vec<(u32, Span)> = std::mem::take(&mut self.quoted_conflicts)
            .into_values()
            .collect();
        conflicts.sort_by_key(|(f, s)| (*f, s.start));
        for (file, span) in conflicts {
            self.error_in(
                file,
                "the methods this call may run take its block differently, one as a `Quoted`, another as a procedure: call them apart",
                span,
            );
        }
        self.body_diagnostics.clear();
        self.diagnostics.append(&mut self.rescued);
        let kept = std::mem::take(&mut self.kept_ambiguous);
        self.ambiguous.splice(0..0, kept);
        let mut seen: rustc_hash::FxHashSet<AmbiguousKey> = Default::default();
        for (file, id, d) in std::mem::take(&mut self.ambiguous) {
            if seen.insert(id) {
                self.diagnostics.push((file, d));
            }
        }
    }

    /// Start from what checking the prelude recorded (`PreludeState`).
    pub fn set_output(&mut self, out: Output) {
        self.out = out;
    }

    pub fn output(&self) -> &Output {
        &self.out
    }

    /// The checks of `file` were read back (`cache`): its classes' field
    /// defaults and initializers, and its signatures, are not checked
    /// again (their warnings come with them).
    pub fn mark_reused(&mut self, file: u32) {
        for c in &self.world.classes {
            if c.file == file {
                self.defaults_checked.insert(c.id);
                self.init_checked.insert(c.id);
            }
        }
        self.reused_files.insert(file);
    }

    /// The class methods that call `new` on their own class, whose
    /// subclasses' constructors must accept the call.
    pub fn self_news(&self) -> &[SelfNew] {
        &self.self_news
    }

    pub fn set_self_news(&mut self, sites: Vec<SelfNew>) {
        self.self_news = sites;
    }

    /// Names of the variables of the REPL's top level.
    /// The REPL's local variables with their declared types (not as an
    /// assignment narrowed them: `x: String? = nil` is a `String?`).
    pub fn repl_local_types(&self) -> Vec<(String, Type)> {
        match &self.repl_env {
            Some(env) => env.frames[0]
                .vars
                .iter()
                .map(|v| (v.name.clone(), self.resolve(&v.declared)))
                .collect(),
            None => Vec::new(),
        }
    }

    pub fn repl_locals(&self) -> Vec<String> {
        match &self.repl_env {
            Some(env) => env.frames[0].vars.iter().map(|v| v.name.clone()).collect(),
            None => Vec::new(),
        }
    }

    /// A call of `mid` at `expr`: when `mid` is a `static def` and the
    /// code is not static, it is an error if `mid` is compile-time only
    /// by declaration (a `static native def`), and otherwise recorded,
    /// to be judged once the method's reach is known (docs/14 §3).
    fn note_static_call(&mut self, expr: &Expr, mid: MethodId) {
        let m = self.world.method(mid);
        // (Inside `static(...)`, the call and a block given to it run at
        // compile time.)
        if !m.is_static
            || self.env.is_static
            || self.static_expr_call == Some(expr.id)
            || self.env.static_frame.is_some()
        {
            return;
        }
        if m.is_native {
            self.error(
                format!(
                    "`{}` runs at compile time only: call it in a `static def` or a `static` statement",
                    m.name
                ),
                expr.span,
            );
            return;
        }
        let entry = (self.env.file, expr.span, mid);
        // A block checked once per overload notes its call once.
        if !self.out.static_calls.contains(&entry) {
            self.out.static_calls.push(entry);
        }
    }

    /// Check the class bodies' `static` statements (docs/14) and, with a
    /// `runner`, run them: each is a call, on the class's `Meta::ClassDef`,
    /// of a `static` class method of a dependency.
    pub fn check_static_stmts(&mut self, runner: Option<&mut (dyn crate::StaticRunner + '_)>) {
        self.check_static_stmts_of(runner, &|_| true);
    }

    /// The same for the statements of the files `in_files` accepts (a
    /// cog's, docs/14 §2), those not checked yet.
    pub fn check_static_stmts_of(
        &mut self,
        mut runner: Option<&mut (dyn crate::StaticRunner + '_)>,
        in_files: &dyn Fn(u32) -> bool,
    ) {
        let total = self.world.static_stmts.len();
        if self.static_done.len() < total {
            self.static_done.resize(total, false);
        }
        let mut stmts = Vec::new();
        for (i, stmt) in self.world.static_stmts.iter().enumerate() {
            if !self.static_done[i] && in_files(stmt.file) {
                stmts.push((i, stmt.clone()));
            }
        }
        for (i, stmt) in stmts {
            // Done once it ran: until then its class, and the classes
            // under it, may still get members from it
            // (`pending_statement_classes`).
            if let Some(callee) = self.check_static_stmt(&stmt) {
                if let Some(r) = runner.as_deref_mut() {
                    if let Err(failure) = r.run(self, &stmt, callee) {
                        let mut message = failure.message;
                        for note in failure.notes {
                            message.push('\n');
                            message.push_str(&note);
                        }
                        self.error_in(stmt.file, message, stmt.span);
                    }
                }
            }
            self.static_done[i] = true;
        }
        // The conformance of these files' classes deferred past their
        // statements (docs/14 §5), which may have generated what they
        // lacked.
        let (due, later): (Vec<ClassId>, Vec<ClassId>) =
            std::mem::take(&mut self.world.conformance_deferred)
                .into_iter()
                .partition(|c| in_files(self.world.class(*c).file));
        self.world.conformance_deferred = later;
        if !due.is_empty() {
            let world = std::mem::take(&mut self.world);
            let mut declarer = crate::declare::Declarer::with_world(world);
            declarer.recheck_conformance(&due);
            self.diagnostics.append(&mut declarer.diagnostics);
            self.world = std::mem::take(&mut declarer.world);
            self.world.freeze_ancestors(true);
        }
    }

    /// The `static` statements of a unit that failed to declare (the
    /// REPL's: `file`, spans from `base`), marked done without running.
    pub fn drop_static_stmts(&mut self, file: u32, base: u32) {
        let total = self.world.static_stmts.len();
        if self.static_done.len() < total {
            self.static_done.resize(total, false);
        }
        for (i, stmt) in self.world.static_stmts.iter().enumerate() {
            if stmt.file == file && stmt.span.start >= base {
                self.static_done[i] = true;
            }
        }
        // The unit's classes whose conformance waited for its statements
        // are checked now: they stay declared, and a later unit's check
        // would report them at its own place.
        let (due, later): (Vec<ClassId>, Vec<ClassId>) =
            std::mem::take(&mut self.world.conformance_deferred)
                .into_iter()
                .partition(|c| {
                    let class = self.world.class(*c);
                    class.file == file && class.span.start >= base
                });
        self.world.conformance_deferred = later;
        if !due.is_empty() {
            let world = std::mem::take(&mut self.world);
            let mut declarer = crate::declare::Declarer::with_world(world);
            declarer.recheck_conformance(&due);
            self.diagnostics.append(&mut declarer.diagnostics);
            self.world = std::mem::take(&mut declarer.world);
            self.world.freeze_ancestors(true);
        }
    }

    /// Evaluate the `static(...)` expressions of the files `in_files`
    /// (docs/14 §8) with `runner`, recording their values
    /// (`Output::static_values`): after the check, every time, also for
    /// files read back from the cache, so that a dependency's `static
    /// def` that changed is seen.
    pub fn eval_static_exprs(
        &mut self,
        mut runner: Option<&mut (dyn crate::StaticRunner + '_)>,
        in_files: &dyn Fn(u32) -> bool,
    ) {
        let mut todo: Vec<(NodeId, u32, ClassId, Expr)> = self
            .out
            .static_exprs
            .iter()
            .filter(|(id, (file, _, _))| {
                in_files(*file) && !self.out.static_values.contains_key(id)
            })
            .map(|(id, (file, class, e))| (*id, *file, *class, e.clone()))
            .collect();
        todo.sort_by_key(|(id, ..)| *id);
        for (id, file, class, e) in todo {
            let Some(CallTarget::Method { method }) = self.out.calls.get(&e.id).cloned() else {
                continue;
            };
            let span = e.span;
            let stmt = StaticStmt {
                class,
                file,
                expr: std::rc::Rc::new(e),
                span,
            };
            let result = match runner.as_deref_mut() {
                Some(r) => r.eval(self, &stmt, method),
                None => continue,
            };
            match result {
                Ok(v) => {
                    self.out.static_values.insert(id, v);
                }
                Err(failure) => {
                    let mut message = failure.message;
                    for note in failure.notes {
                        message.push('\n');
                        message.push_str(&note);
                    }
                    self.error_in(file, message, span);
                }
            }
        }
    }

    /// The classes whose `static` statements have not all run yet: their
    /// members, and their descendants', may still be generated, so a
    /// compile-time run does not check their bodies ahead of a call
    /// that resolves to one (docs/14 §6).
    pub fn pending_statement_classes(&self) -> Vec<ClassId> {
        let mut out: Vec<ClassId> = Vec::new();
        for (i, stmt) in self.world.static_stmts.iter().enumerate() {
            if !self.static_done.get(i).copied().unwrap_or(false) && !out.contains(&stmt.class) {
                out.push(stmt.class);
            }
        }
        out
    }

    /// How a class reaches a module's `static def` (docs/14 §2): through
    /// `extend M[A]` in the class or an ancestor `A` itself, so that the
    /// `Meta::ClassDef[A]` the body was checked with holds for the class
    /// the statement runs on. A module without type parameters, or an
    /// `extend` naming another class, is refused, with why.
    fn extend_route(&self, class: ClassId, module: ClassId, name: &str) -> Result<(), String> {
        let mname = self.world.class(module).name.clone();
        if self.world.class(module).type_params.is_empty() {
            return Err(format!(
                "`{name}` is a `static def` of the module `{mname}`, which has no type parameter for the class it runs on: declare the module generic (`module {mname}[T]`, `self` is then `Meta::ClassDef[T]`) and extend it with the class (`extend {mname}[Post]`), or make `{name}` a class method (`static def self.{name}`) of a superclass"
            ));
        }
        for a in self.world.ancestor_ids(class) {
            let c = self.world.class(a);
            if c.kind == ClassKind::Module {
                continue;
            }
            for t in &c.extends {
                if let Type::Class(id, args) = t {
                    if *id == module {
                        return match args.first() {
                            // The class's own instance type, as `extend`
                            // requires (declare.rs, `check_static_mixins`).
                            Some(Type::Class(x, xargs))
                                if *x == a
                                    && xargs.len() == c.type_params.len()
                                    && xargs
                                        .iter()
                                        .zip(&c.type_params)
                                        .all(|(t, p)| *t == Type::Param(p.id)) =>
                            {
                                Ok(())
                            }
                            _ => Err(format!(
                                "`{name}` is a `static def` of the module `{mname}`, which `{}` extends as `{}`: a statement runs it only through `extend {mname}[{}]`, the class itself as its first type argument",
                                c.name,
                                self.world.type_name(t),
                                c.name
                            )),
                        };
                    }
                }
            }
        }
        Err(format!(
            "`{name}` is a `static def` of the module `{mname}`, which the class reaches only through another module: extend `{mname}` itself"
        ))
    }

    /// Type-check one `static` statement and validate what it calls:
    /// the `static def` class method, which must belong to a dependency.
    fn check_static_stmt(&mut self, stmt: &StaticStmt) -> Option<MethodId> {
        let class = self.world.class(stmt.class).clone();
        let instance = Type::Class(
            stmt.class,
            class
                .type_params
                .iter()
                .map(|p| Type::Param(p.id))
                .collect(),
        );
        let self_type = Type::Class(self.world.builtin.meta_classdef, vec![instance]);
        let scope = TypeScope {
            namespace: Some(stmt.class),
            params: class
                .type_params
                .iter()
                .map(|p| (p.name.clone(), p.id))
                .collect(),
            self_type: None,
        };
        let mut env = self.fresh_env(self_type, Some(stmt.class), None, scope, stmt.file);
        env.is_static = true;
        let errors_before = self.error_count();
        let saved_env = std::mem::replace(&mut self.env, env);
        let saved_infer = std::mem::take(&mut self.infer);
        let saved_touched = std::mem::take(&mut self.touched);
        let saved_frame_vars = std::mem::take(&mut self.frame_vars);
        let saved_temp_stmts = std::mem::take(&mut self.temp_stmts);
        self.scan_closures([&*stmt.expr], std::iter::empty());
        let active = self.file_extensions(stmt.file);
        let saved_active = std::mem::replace(&mut self.world.active_extensions, active);
        let t = self.check_expr(&stmt.expr, None);
        let _ = self.settle_vars(&t);
        self.world.active_extensions = saved_active;
        self.finish_frame_types();
        self.env = saved_env;
        self.infer = saved_infer;
        self.touched = saved_touched;
        self.frame_vars = saved_frame_vars;
        self.temp_stmts = saved_temp_stmts;
        let callee = match self.out.calls.get(&stmt.expr.id) {
            Some(CallTarget::Method { method }) => *method,
            _ => {
                if self.error_count() == errors_before {
                    self.error_in(
                        stmt.file,
                        "a statement in a class body must call a `static def` class method",
                        stmt.span,
                    );
                }
                return None;
            }
        };
        let m = self.world.method(callee).clone();
        let module_def = m.is_static
            && !m.singleton
            && !m.is_native
            && self.world.class(m.owner).kind == ClassKind::Module;
        if module_def {
            // Through `extend M[C]` (docs/14 §2): its `self` is the
            // module's first type parameter's `Meta::ClassDef`, which the
            // class must be (or descend from) where it runs.
            if let Err(message) = self.extend_route(stmt.class, m.owner, &m.name) {
                self.error_in(stmt.file, message, stmt.span);
                return None;
            }
        } else if !m.is_static || !m.singleton || m.is_native {
            let message = {
                format!(
                    "a statement in a class body must call a `static def` class method; `{}` is not one",
                    m.name
                )
            };
            self.error_in(stmt.file, message, stmt.span);
            return None;
        }
        let allowed = match self.repl_unit {
            Some((file, base)) => {
                if m.file == file && m.span.start >= base {
                    Err(if file == 1 {
                        "this input".to_string()
                    } else {
                        "this file".to_string()
                    })
                } else {
                    Ok(())
                }
            }
            None => self.world.static_callee_allowed(stmt.file, m.file),
        };
        if let Err(why) = allowed {
            let only = if self.repl_unit.is_some() {
                "those of the files required or the inputs entered before"
            } else {
                "those of the cogs (or required files) its file depends on"
            };
            self.error_in(
                stmt.file,
                format!(
                    "`{}` is a `static def` of {why}: a `static` statement runs only {only}",
                    m.name
                ),
                stmt.span,
            );
            return None;
        }
        Some(callee)
    }

    fn error_count(&self) -> usize {
        self.diagnostics
            .iter()
            .filter(|(_, d)| d.is_error())
            .count()
    }

    fn fresh_env(
        &self,
        self_type: Type,
        class_id: Option<ClassId>,
        method: Option<MethodId>,
        scope: TypeScope,
        file: u32,
    ) -> Env {
        let owner = match method {
            Some(mid) => SelfOwner::Method(mid),
            None => match self_type {
                Type::Class(c, _) if self.world.class(c).kind == ClassKind::Main => {
                    SelfOwner::Unit(file)
                }
                _ => SelfOwner::Init,
            },
        };
        Env {
            frames: vec![Frame {
                vars: Vars::default(),
                is_block: false,
                owner,
            }],
            self_type,
            self_opaque: false,
            lexical_class: class_id,
            class_id,
            receivers: Vec::new(),
            method,
            scope,
            ret_expected: None,
            block_type: None,
            block_optional: false,
            in_initialize: false,
            is_static: false,
            assigned_fields: HashSet::default(),
            loop_depth: 0,
            loop_exits: LoopExits::default(),
            ensure_assigns: None,
            applying_facts: false,
            blocks: Vec::new(),
            ivar_narrow: HashMap::default(),
            in_rescue: 0,
            file,
            pattern_base: None,
            task_frame: None,
            task_shareable_proc: false,
            reassigned: None,
            late_assigned: Rc::default(),
            never_narrow: Rc::default(),
            next_block_escapes: false,
            lifted_frame: None,
            static_frame: None,
            next_block_lifted: false,
        }
    }

    /// Note a statement whose value is not used, if it makes a new value
    /// (a call or literal, not a variable or an assignment's), for
    /// `finish_frame_types`.
    fn note_temp_stmt(&mut self, e: &Expr) {
        let fresh = match &e.kind {
            ExprKind::Call(_) => !self.out.bang_assign.contains(&e.id),
            ExprKind::Yield(_)
            | ExprKind::Super { .. }
            | ExprKind::Array(_)
            | ExprKind::Hash(_)
            | ExprKind::Lambda(_) => true,
            _ => false,
        };
        if fresh {
            self.temp_stmts.push(e.id);
        }
    }

    /// Note a frame's variables for `finish_frame_types`.
    fn note_frame_vars(&mut self, frame: &Frame) {
        if frame.owner == SelfOwner::Init {
            return;
        }
        for (i, v) in frame.vars.iter().enumerate() {
            self.frame_vars
                .push((frame.owner, i as u32, v.declared.clone()));
        }
    }

    fn note_lexical(&mut self, owner: SelfOwner, slot: u32, t: &Type) {
        let t = self.infer.resolve(t);
        if self.world.release_observable(&t) {
            self.out.lexical_slots.insert((owner, slot));
        }
    }

    /// Resolve the types recorded for the nodes of the frame just checked.
    fn finish_frame_types(&mut self) {
        let root = std::mem::take(&mut self.env.frames[0].vars);
        let owner = self.env.frames[0].owner;
        if owner != SelfOwner::Init {
            for (i, v) in root.iter().enumerate() {
                self.note_lexical(owner, i as u32, &v.declared);
            }
        }
        self.env.frames[0].vars = root;
        for (owner, slot, t) in std::mem::take(&mut self.frame_vars) {
            self.note_lexical(owner, slot, &t);
        }
        for id in std::mem::take(&mut self.temp_stmts) {
            if let Some(t) = self.out.node_types.get(&id) {
                let t = self.infer.resolve(t);
                if self.world.release_observable(&t) {
                    self.out.released_stmts.insert(id);
                }
            }
        }
        let touched = std::mem::take(&mut self.touched);
        for id in touched {
            if let Some(t) = self.out.node_types.get(&id) {
                let r = self.infer.resolve(t);
                self.out.node_types.insert(id, r);
            }
        }
        for t in self.out.lifted_blocks.values_mut() {
            if t.has_vars() {
                *t = self.infer.resolve(t);
            }
        }
        for args in self.out.type_args.values_mut() {
            for (_, t) in args.iter_mut() {
                if t.has_vars() {
                    *t = self.infer.resolve(t);
                }
            }
        }
        // Call targets with types (is_a?, as) are resolved too.
        let keys: Vec<NodeId> = self.out.calls.keys().copied().collect();
        for k in keys {
            let target = self.out.calls.get(&k).cloned();
            match target {
                Some(CallTarget::IsA(t)) => {
                    let r = self.infer.resolve(&t);
                    self.out.calls.insert(k, CallTarget::IsA(r));
                }
                Some(CallTarget::As { ty, optional }) => {
                    let r = self.infer.resolve(&ty);
                    self.out.calls.insert(k, CallTarget::As { ty: r, optional });
                }
                _ => {}
            }
        }
    }

    fn record(&mut self, id: NodeId, t: &Type) {
        // In a block (checked once per type of what it is given, and in
        // overload trials thrown away): what it replaces is journaled.
        if !self.env.blocks.is_empty() {
            let before = self.out.node_types.get(&id).cloned();
            if let (Some(b), false) = (&before, self.out.varied_types.contains(&id)) {
                if self.infer.resolve(b) != self.infer.resolve(t) {
                    self.out.varied_types.insert(id);
                    self.table_journal.push(TableUndo::Varied(id));
                }
            }
            self.table_journal.push(TableUndo::NodeType(id, before));
        }
        self.out.node_types.insert(id, t.clone());
        self.touched.push(id);
    }

    // ----- methods ---------------------------------------------------------

    /// The return type of a method (declared: one without is `Void`).
    fn method_ret(&self, mid: MethodId) -> Type {
        self.world.method(mid).ret.clone()
    }

    pub fn ensure_method_checked(&mut self, mid: MethodId) {
        if self.world.method(mid).checked {
            return;
        }
        if self.in_progress.contains(&mid) {
            return;
        }
        let Some(def) = self.world.method(mid).body.clone() else {
            self.world.method_mut(mid).checked = true;
            return;
        };
        self.in_progress.push(mid);
        let body_mark = (
            self.table_journal.len(),
            self.ambiguous.len(),
            self.diagnostics.len(),
        );

        let info = self.world.method(mid).clone();
        let owner = info.owner;
        // What the body needs of its class (not the whole class: its
        // tables are large and this runs for every method).
        let class = {
            let c = self.world.class(owner);
            OwnerInfo {
                type_params: c.type_params.clone(),
                kind: c.kind,
                usings: c.usings.clone(),
                parent: c.parent,
            }
        };
        let instance = Type::Class(
            owner,
            class
                .type_params
                .iter()
                .map(|p| Type::Param(p.id))
                .collect(),
        );
        let self_type = if info.singleton && info.is_static && !info.is_native {
            // A `static` class method runs on the class being declared:
            // `self` is its `Meta::ClassDef` (docs/14).
            Type::Class(self.world.builtin.meta_classdef, vec![instance])
        } else if info.is_static
            && !info.is_native
            && class.kind == ClassKind::Module
            && !class.type_params.is_empty()
        {
            // A generic module's `static def`, which a class reaches
            // through `extend M[C]`: it runs on that class, the module's
            // first type parameter (docs/14 §2).
            Type::Class(
                self.world.builtin.meta_classdef,
                vec![Type::Param(class.type_params[0].id)],
            )
        } else if info.singleton {
            Type::ClassObject(
                owner,
                class
                    .type_params
                    .iter()
                    .map(|p| Type::Param(p.id))
                    .collect(),
            )
        } else if let Some(ext) = info.extension {
            let e = &self.world.extensions[ext as usize];
            Type::Class(e.target, e.target_args.clone())
        } else {
            Type::Class(
                owner,
                class
                    .type_params
                    .iter()
                    .map(|p| Type::Param(p.id))
                    .collect(),
            )
        };
        let mut params: Vec<(String, TypeParamId)> = Vec::new();
        let namespace;
        if let Some(ext) = info.extension {
            let e = &self.world.extensions[ext as usize];
            params.extend(e.type_params.iter().map(|p| (p.name.clone(), p.id)));
            namespace = e.module;
        } else {
            params.extend(class.type_params.iter().map(|p| (p.name.clone(), p.id)));
            // A file's top-level methods resolve constants from the file's
            // namespace: the cog's root module, or the top level.
            namespace = if class.kind == ClassKind::Main {
                class.parent
            } else {
                Some(owner)
            };
        }
        params.extend(info.type_params.iter().map(|p| (p.name.clone(), p.id)));
        let scope = TypeScope {
            namespace,
            params,
            self_type: Some(self_type.clone()),
        };
        let mut env = self.fresh_env(self_type.clone(), Some(owner), Some(mid), scope, info.file);
        // A signature with `Self`: the body sees `Self` as opaque.
        let opaque = Self::mentions_self(&info);
        let self_subst: HashMap<TypeParamId, Type> = if opaque {
            HashMap::default()
        } else {
            [(
                SELF_PARAM,
                Self::self_binding(&self.world, &info, &self_type),
            )]
            .into_iter()
            .collect()
        };
        env.self_opaque = opaque;
        let bound = opaque.then(|| Self::self_binding(&self.world, &info, &self_type));
        let saved_bound = std::mem::replace(&mut self.world.self_bound, bound);
        env.ret_expected = Some(info.ret.subst(&self_subst));
        env.block_type = info.block.as_ref().map(|(_, t)| t.subst(&self_subst));
        env.block_optional = info.block_optional;
        env.in_initialize = info.name == "initialize" && !info.singleton;
        env.is_static = info.is_static;
        env.frames[0].vars = Vars::default();
        for p in &info.params {
            env.frames[0].vars.push(VarInfo {
                name: p.name.clone(),
                declared: p.ty.subst(&self_subst),
                narrowed: None,
                listed: false,
            });
        }
        if let Some((name, t)) = &info.block {
            let t = t.subst(&self_subst);
            env.frames[0].vars.push(VarInfo {
                name: name.clone(),
                declared: if info.block_optional {
                    self.world.nilable(t)
                } else {
                    t
                },
                narrowed: None,
                listed: false,
            });
        }
        // Active extensions: the class's `using`s plus those of the file's
        // top level, and its group's top-level extensions.
        let mut active = class.usings.clone();
        for e in self.file_extensions(info.file) {
            if !active.contains(&e) {
                active.push(e);
            }
        }
        // Usings of enclosing namespaces.
        let mut ns = class.parent;
        while let Some(n) = ns {
            for e in &self.world.class(n).usings {
                if !active.contains(e) {
                    active.push(*e);
                }
            }
            ns = self.world.class(n).parent;
        }

        let saved_env = std::mem::replace(&mut self.env, env);
        let saved_infer = std::mem::take(&mut self.infer);
        let saved_touched = std::mem::take(&mut self.touched);
        let saved_frame_vars = std::mem::take(&mut self.frame_vars);
        let saved_temp_stmts = std::mem::take(&mut self.temp_stmts);
        let saved_active = std::mem::replace(&mut self.world.active_extensions, active);

        // Closures in the body and in default values (which run in the
        // method's frame, with its parameters).
        if let Some(body) = &def.body {
            self.scan_closures(
                body.iter()
                    .chain(info.params.iter().filter_map(|p| p.default.as_deref())),
                info.params.iter().map(|p| p.name.as_str()),
            );
        }
        // Parameter slots are the first slots of the frame.
        for (i, p) in info.params.iter().enumerate() {
            self.out.var_refs.insert(
                p.span,
                VarRef {
                    depth: 0,
                    slot: i as u32,
                },
            );
            if let Some(d) = &p.default {
                let expected = p.ty.subst(&self_subst);
                let t = self.check_expr(d, Some(&expected));
                if !self.coerce(&t, &expected) {
                    self.error(
                        format!(
                            "default value of type {} for parameter `{}` of type {}",
                            self.name(&t),
                            p.name,
                            self.name(&expected)
                        ),
                        d.span,
                    );
                }
            }
            // (A field parameter of a class method has no object to go to.)
            if p.assigns_ivar && self.check_ivar_access(p.span) {
                self.env.assigned_fields.insert(p.name.clone());
            }
        }

        let body = def.body.as_ref().cloned().unwrap_or_default();
        let expected = self.env.ret_expected.clone();
        let void = expected == Some(Type::Void);
        self.next_body_void = void;
        let body_ty = self.check_body(&body, if void { None } else { expected.as_ref() });
        self.mark_discarded(body.last(), void);
        if let Some(ret) = expected.filter(|_| !void) {
            if !body_ty.is_nothing() && !self.coerce(&body_ty, &ret) {
                let span = body.last().map(|e| e.span).unwrap_or(info.span);
                let hint = if self.world.is_nil_type(&ret) {
                    "; to discard the body's value, write `-> Void`"
                } else {
                    ""
                };
                self.error(
                    format!(
                        "method `{}` returns {} but its body has type {}{hint}",
                        info.name,
                        self.name(&ret),
                        self.name(&body_ty)
                    ),
                    span,
                );
            }
        }

        if self.env.in_initialize {
            let (required, own) = self.required_fields(owner);
            let params: Vec<(Option<&Expr>, Option<String>)> = info
                .params
                .iter()
                .map(|p| (p.default.as_deref(), p.assigns_ivar.then(|| p.name.clone())))
                .collect();
            let errors = {
                let calls = |id: NodeId| self.out.calls.get(&id).cloned();
                let world = &self.world;
                // Every method on `self` but a built-in `Kernel` function
                // (which takes no `self`; one an `extension Kernel` adds
                // does) may read the object's fields.
                let uses_self = |mid: MethodId| {
                    let m = world.method(mid);
                    !(m.is_native && m.owner == world.builtin.kernel)
                };
                let diverges = |mid: MethodId| world.method(mid).ret.is_nothing();
                let mut c =
                    crate::init::InitCheck::new(&required, &own, &calls, &uses_self, &diverges);
                c.method(&params, &body, info.span);
                (c.errors, c.usable_after, c.usable_on_entry)
            };
            let (errors, usable_after, usable_on_entry) = errors;
            for (msg, span) in errors {
                self.error(msg, span);
            }
            self.out.usable_after.extend(usable_after);
            if usable_on_entry {
                self.out.usable_on_entry.insert(SelfOwner::Method(mid));
            }
            let fields = self.world.all_fields(owner);
            for (f, _) in fields {
                if !f.has_default()
                    && !f.mutable
                    && !required.contains(&f.name)
                    && !self.env.assigned_fields.contains(&f.name)
                {
                    self.error(
                        format!("field `@{}` must be assigned in `initialize`", f.name),
                        info.span,
                    );
                }
            }
        }

        let frame_size = self.env.frames[0].vars.len() as u32;
        self.finish_frame_types();
        self.world.method_mut(mid).frame_size = frame_size;
        self.world.method_mut(mid).checked = true;
        self.env = saved_env;
        self.infer = saved_infer;
        self.touched = saved_touched;
        self.frame_vars = saved_frame_vars;
        self.temp_stmts = saved_temp_stmts;
        self.world.active_extensions = saved_active;
        self.world.self_bound = saved_bound;
        self.in_progress.pop();
        // What the body recorded is its own, checked once: a check that
        // needed it and is thrown away must not undo it.
        self.table_journal.truncate(body_mark.0);
        let found = self.ambiguous.split_off(body_mark.1);
        self.kept_ambiguous.extend(found);
        let end = self.diagnostics.len();
        // (Nested bodies' ranges are inside this one.)
        self.body_diagnostics.retain(|(s, _)| *s < body_mark.2);
        if end > body_mark.2 {
            self.body_diagnostics.push((body_mark.2, end));
        }
    }

    /// The type of a constant, checking its initializer on first use.
    fn const_type(&mut self, cid: ConstId, span: Span) -> Type {
        let info = self.world.consts[cid as usize].clone();
        if let Some(t) = info.ty {
            return t;
        }
        if info.checking {
            self.error(format!("constant `{}` refers to itself", info.name), span);
            return Type::Nothing;
        }
        let Some(value) = info.value else {
            return Type::Nothing;
        };
        self.world.consts[cid as usize].checking = true;
        let scope = TypeScope {
            namespace: info.owner,
            params: Vec::new(),
            self_type: None,
        };
        let self_type = match info.owner {
            Some(o) => Type::ClassObject(o, vec![]),
            None => Type::class(
                self.file_main(info.file)
                    .unwrap_or(self.world.builtin.object),
            ),
        };
        let env = self.fresh_env(self_type, info.owner, None, scope, info.file);
        let saved_env = std::mem::replace(&mut self.env, env);
        let saved_infer = std::mem::take(&mut self.infer);
        let saved_touched = std::mem::take(&mut self.touched);
        let saved_frame_vars = std::mem::take(&mut self.frame_vars);
        let saved_temp_stmts = std::mem::take(&mut self.temp_stmts);
        self.scan_closures([&*value], std::iter::empty());
        let active = self.file_extensions(info.file);
        let saved_active = std::mem::replace(&mut self.world.active_extensions, active);
        let t = self.check_expr(&value, None);
        self.world.active_extensions = saved_active;
        let t = self.settle_vars(&t);
        let t = self.world.erase_narrowed(&t);
        if t.has_vars() {
            self.error(
                format!("cannot infer the type of constant `{}`", info.name),
                value.span,
            );
        }
        if !self.world.is_shareable(&t) {
            self.error(
                format!(
                    "constant `{}` has the non-shareable type {}",
                    info.name,
                    self.world.type_name(&t)
                ),
                value.span,
            );
        }
        self.finish_frame_types();
        self.env = saved_env;
        self.infer = saved_infer;
        self.touched = saved_touched;
        self.frame_vars = saved_frame_vars;
        self.temp_stmts = saved_temp_stmts;
        self.world.consts[cid as usize].ty = Some(t.clone());
        self.world.consts[cid as usize].checking = false;
        t
    }

    // ----- inference helpers -------------------------------------------------

    fn resolve(&self, t: &Type) -> Type {
        self.infer.resolve(t)
    }

    /// Whether a value of type `actual` can be used where `expected` is
    /// required, binding inference variables on either side.
    fn coerce(&mut self, actual: &Type, expected: &Type) -> bool {
        // A defensive limit, as `World::is_subtype`'s.
        if self.coerce_depth >= COERCE_DEPTH {
            return false;
        }
        // A question met again while being answered: no (see
        // `World::subtype_open`).
        let key = (self.infer.resolve(actual), self.infer.resolve(expected));
        if key.0 != key.1 && self.coerce_open.contains(&key) {
            return false;
        }
        self.coerce_open.push(key);
        self.coerce_depth += 1;
        let r = self.coerce_at(actual, expected);
        self.coerce_depth -= 1;
        self.coerce_open.pop();
        r
    }

    fn coerce_at(&mut self, actual: &Type, expected: &Type) -> bool {
        // A `Void` result is `Nil` here: no variable is bound to `Void`.
        let a = self.world.unvoid(&self.infer.resolve(actual));
        let e = self.world.unvoid(&self.infer.resolve(expected));
        if a == e || a.is_nothing() {
            return true;
        }
        match (&a, &e) {
            (_, Type::Var(v)) => self.infer.bind(*v, self.world.erase_narrowed(&a)),
            (Type::Var(v), _) => self.infer.bind(*v, self.world.erase_narrowed(&e)),
            (_, Type::Class(id, _)) if *id == self.world.builtin.object => true,
            (Type::Union(ms), _) => {
                let ms = ms.clone();
                // `?v | Nil` into `T?`: nil goes to nil, `?v` is `T`.
                let nil = self.world.nil();
                let e_some = if ms.contains(&nil) && e.members().contains(&nil) {
                    e.without_nil(self.world.builtin.nil)
                } else {
                    e.clone()
                };
                ms.iter().all(|m| {
                    let target = if matches!(m, Type::Var(_)) {
                        &e_some
                    } else {
                        &e
                    };
                    self.coerce(m, target)
                })
            }
            (_, Type::Union(ms)) => {
                let ms = ms.clone();
                // Prefer a member with the same class.
                if let Type::Class(aid, _) = &a {
                    for m in &ms {
                        if matches!(m, Type::Class(mid, _) if mid == aid) {
                            let saved = self.infer.save();
                            if self.coerce(&a, m) {
                                return true;
                            }
                            self.infer.restore(saved);
                        }
                    }
                }
                for m in &ms {
                    let saved = self.infer.save();
                    if self.coerce(&a, m) {
                        return true;
                    }
                    self.infer.restore(saved);
                }
                false
            }
            (Type::Class(aid, aargs), Type::Class(eid, eargs)) => {
                let ancestors = self.world.ancestors(*aid, aargs);
                let Some((_, anc_args)) = ancestors.into_iter().find(|(id, _)| id == eid) else {
                    // (A `data` type or enum Shareable by its fields.)
                    return *eid == self.world.builtin.shareable
                        && self.world.derived_shareable(*aid, aargs);
                };
                if !self.world.keeps_shareable(*aid, aargs, *eid) {
                    return false;
                }
                if anc_args.len() != eargs.len() {
                    return anc_args.is_empty() || eargs.is_empty();
                }
                let params = self.world.class(*eid).type_params.clone();
                for (i, (x, y)) in anc_args.iter().zip(eargs.iter()).enumerate() {
                    let ok = match params.get(i).map(|p| p.variance) {
                        Some(Variance::Covariant) => self.coerce(x, y),
                        Some(Variance::Contravariant) => self.coerce(y, x),
                        _ => self.unify(x, y),
                    };
                    if !ok {
                        return false;
                    }
                }
                true
            }
            // `Type[A]` to `Type[B]`: `A` to `B` (binding `T` in `Type[T]`).
            (Type::ClassObject(..) | Type::TypeOf(_), Type::ClassObject(..) | Type::TypeOf(_)) => {
                match (actual.instance_of(), expected.instance_of()) {
                    (Some(a), Some(e)) => self.coerce(&a, &e),
                    _ => false,
                }
            }
            (Type::ClassObject(..) | Type::TypeOf(_), Type::Class(eid, eargs))
                if *eid == self.world.builtin.class_ =>
            {
                match (actual.instance_of(), eargs.first()) {
                    (Some(a), Some(e)) => self.coerce(&a, e),
                    _ => true,
                }
            }
            // `Meta::ClassDef[X]` to `Type[Y]`: `X` to `Y`.
            (Type::Class(..), Type::ClassObject(..) | Type::TypeOf(_))
                if self.world.class_object_instance(actual).is_some() =>
            {
                match (
                    self.world.class_object_instance(actual),
                    expected.instance_of(),
                ) {
                    (Some(a), Some(e)) => self.coerce(&a, &e),
                    _ => false,
                }
            }
            (Type::Tuple(xs), Type::Tuple(ys)) => {
                if xs.len() != ys.len() {
                    return false;
                }
                let (xs, ys) = (xs.clone(), ys.clone());
                xs.iter().zip(ys.iter()).all(|(x, y)| self.coerce(x, y))
            }
            // Tuples compare element by element (`[2, "a"] < [2, "b"]`):
            // `[A, B]` is a `Comparable[[C, D]]` when `A` is a
            // `Comparable[C]` and `B` a `Comparable[D]`.
            (Type::Tuple(xs), Type::Class(eid, eargs))
                if *eid == self.world.builtin.comparable
                    && matches!(eargs.as_slice(), [Type::Tuple(ys)] if ys.len() == xs.len()) =>
            {
                let (xs, eid) = (xs.clone(), *eid);
                let [Type::Tuple(ys)] = eargs.as_slice() else {
                    unreachable!()
                };
                let ys = ys.clone();
                xs.iter()
                    .zip(ys.iter())
                    .all(|(x, y)| self.coerce(x, &Type::Class(eid, vec![y.clone()])))
            }
            (Type::Tuple(xs), Type::Class(eid, eargs)) => {
                if *eid == self.world.builtin.array && eargs.len() == 1 {
                    let elem = Type::union_of(xs.clone());
                    let target = eargs[0].clone();
                    return self.coerce(&elem, &target);
                }
                let array = self.world.builtin.array;
                self.world.class_is_a(array, *eid)
                    && self
                        .world
                        .keeps_shareable(array, &[Type::union_of(xs.clone())], *eid)
            }
            (Type::Proc(ra, ps, r, sa), Type::Proc(rb, qs, s, sb)) => {
                // A shareable procedure is a procedure; not the reverse.
                if ps.len() != qs.len() || (*sb && !*sa) {
                    return false;
                }
                // Receivers are contravariant, and a block with one is
                // not a block without one.
                match (ra.clone(), rb.clone()) {
                    (None, None) => {}
                    (Some(ra), Some(rb)) => {
                        if !self.coerce(&rb, &ra) {
                            return false;
                        }
                    }
                    _ => return false,
                }
                let (ps, qs, r, s) = (ps.clone(), qs.clone(), (**r).clone(), (**s).clone());
                for (p, q) in ps.iter().zip(qs.iter()) {
                    if !self.coerce(q, p) {
                        return false;
                    }
                }
                self.coerce(&r, &s)
            }
            (Type::Proc(..), Type::Class(eid, _)) => *eid == self.world.builtin.proc_,
            (Type::Param(_), _) | (_, Type::Param(_)) => self.world.is_subtype(&a, &e),
            _ => false,
        }
    }

    /// Both directions (for invariant type arguments).
    fn unify(&mut self, x: &Type, y: &Type) -> bool {
        let rx = self.world.unvoid(&self.infer.resolve(x));
        let ry = self.world.unvoid(&self.infer.resolve(y));
        if rx == ry {
            return true;
        }
        match (&rx, &ry) {
            (Type::Var(v), _) => self.infer.bind(*v, self.world.erase_narrowed(&ry)),
            (_, Type::Var(v)) => self.infer.bind(*v, self.world.erase_narrowed(&rx)),
            (Type::Class(a, aa), Type::Class(b, ba)) if a == b && aa.len() == ba.len() => {
                let (aa, ba) = (aa.clone(), ba.clone());
                aa.iter().zip(ba.iter()).all(|(p, q)| self.unify(p, q))
            }
            (Type::Tuple(xs), Type::Tuple(ys)) if xs.len() == ys.len() => {
                let (xs, ys) = (xs.clone(), ys.clone());
                xs.iter().zip(ys.iter()).all(|(p, q)| self.unify(p, q))
            }
            (Type::ClassObject(..) | Type::TypeOf(_), Type::ClassObject(..) | Type::TypeOf(_)) => {
                match (rx.instance_of(), ry.instance_of()) {
                    (Some(a), Some(b)) => self.unify(&a, &b),
                    _ => false,
                }
            }
            (Type::Union(_), _) | (_, Type::Union(_)) => {
                self.coerce(&rx, &ry) && self.coerce(&ry, &rx)
            }
            _ => self.world.is_subtype(&rx, &ry) && self.world.is_subtype(&ry, &rx),
        }
    }

    fn join(&mut self, a: &Type, b: &Type) -> Type {
        let ra = self.infer.resolve(a);
        let rb = self.infer.resolve(b);
        if ra.is_nothing() {
            return rb;
        }
        if rb.is_nothing() {
            return ra;
        }
        // A variable joined with another type stays undecided (`xs[0] ||
        // "s"` is `?v | String`): its type comes from where its values are
        // used.
        if matches!(ra, Type::Var(_)) || matches!(rb, Type::Var(_)) {
            return Type::union_of(vec![ra, rb]);
        }
        self.world.join(&ra, &rb)
    }

    fn is_truthy_type(&self, t: &Type) -> Option<bool> {
        let t = self.resolve(t);
        let has_nil = t.members().iter().any(|m| self.world.is_nil_type(m));
        let has_bool = t
            .members()
            .iter()
            .any(|m| matches!(m, Type::Class(id, _) if *id == self.world.builtin.bool_));
        let all_nil = t.members().iter().all(|m| self.world.is_nil_type(m));
        if matches!(t, Type::Var(_) | Type::Nothing | Type::Param(_)) {
            return None;
        }
        if t.members()
            .iter()
            .any(|m| self.world.is_object(m) || matches!(m, Type::Param(_) | Type::Var(_)))
        {
            return None;
        }
        if all_nil {
            return Some(false);
        }
        if !has_nil && !has_bool {
            return Some(true);
        }
        None
    }

    fn truthy_part(&self, t: &Type) -> Type {
        let t = self.resolve(t);
        t.without_nil(self.world.builtin.nil)
    }

    fn falsy_part(&self, t: &Type) -> Type {
        let t = self.resolve(t);
        let mut out = Vec::new();
        for m in t.members() {
            if self.world.is_nil_type(&m)
                || matches!(&m, Type::Class(id, _) if *id == self.world.builtin.bool_)
            {
                out.push(m);
            } else if self.world.is_object(&m) {
                out.push(self.world.nil());
                out.push(self.world.bool_());
            }
        }
        Type::union_of(out)
    }

    // ----- variables -------------------------------------------------------------

    /// Record a union call's table (`Output::union_calls`), merged with
    /// those of earlier checks of the same call: kept only while each
    /// member is a class a test tells apart from the others (not two
    /// instances of one generic class, not a class and its subclass) and
    /// every check agrees on each member's method.
    fn note_union_table(&mut self, id: NodeId, table: Vec<(Type, MethodId)>, span: Span) {
        if self.out.union_conflicts.contains(&id) {
            return;
        }
        self.journal_union(id);
        let mut merged = self.out.union_calls.remove(&id).unwrap_or_default();
        for (t, m) in table {
            match merged.iter().find(|(u, _)| *u == t) {
                Some((_, n)) if *n != m => {
                    // (Overloads chosen by the arguments' types.)
                    let n = *n;
                    self.ambiguous_call(id, &t, &t, n, m, span);
                    return;
                }
                Some(_) => {}
                None => merged.push((t, m)),
            }
        }
        // By the class a test sees: members of one class (two tuples, two
        // instances of a generic class) with the same method are one
        // entry, with different methods the test cannot choose; a
        // subclass is tested before its superclass. A module's member and
        // another member that are not related, answered differently with an
        // extension's method: a value may be both, and its class decides
        // which comes first (with the classes' own methods, the test finds
        // one the value has).
        let mut by_class: Vec<(ClassId, Type, MethodId)> = Vec::new();
        for (t, m) in &merged {
            let Some(c) = self.test_class(t) else {
                self.out.union_conflicts.insert(id);
                return;
            };
            let ext = |k: MethodId| self.world.method(k).extension.is_some();
            let clash = by_class.iter().find(|(d, _, n)| {
                n != m
                    && (*d == c
                        || ((self.world.class(*d).kind == ClassKind::Module
                            || self.world.class(c).kind == ClassKind::Module)
                            && (ext(*n) || ext(*m))
                            && !self.world.class_is_a(*d, c)
                            && !self.world.class_is_a(c, *d)))
            });
            if let Some((_, u, n)) = clash {
                let (u, n) = (u.clone(), *n);
                self.ambiguous_call(id, &u, t, n, *m, span);
                return;
            }
            if !by_class.iter().any(|(d, _, _)| *d == c) {
                by_class.push((c, t.clone(), *m));
            }
        }
        self.subclasses_first(&mut by_class, |e| e.0);
        let merged = by_class.into_iter().map(|(_, t, m)| (t, m)).collect();
        self.out.union_calls.insert(id, merged);
    }

    /// A call whose method a run-time test of the receiver's class cannot
    /// choose: `a` and `b` (the receiver's types in two members, or in two
    /// checks of a block) resolve to `m` and `n`.
    fn ambiguous_call(
        &mut self,
        id: NodeId,
        a: &Type,
        b: &Type,
        m: MethodId,
        n: MethodId,
        span: Span,
    ) {
        self.out.union_conflicts.insert(id);
        // Called by name, a native finds its overload: wrong only for an
        // extension's method (not found by name) or user overloads (the
        // first a lookup finds).
        let (mi, ni) = (self.world.method(m), self.world.method(n));
        let wrong =
            mi.extension.is_some() || ni.extension.is_some() || (!mi.is_native && !ni.is_native);
        if !wrong {
            return;
        }
        let name = self.world.method(m).name.clone();
        let (wm, wn) = (self.method_label(m), self.method_label(n));
        let what = if a == b {
            format!("on {}", self.name(a))
        } else {
            format!("for {} and {}", self.name(a), self.name(b))
        };
        let d = Diagnostic::error(
            format!(
                "cannot tell at run time which `{name}` to call {what}: {wm} or {wn} (give the value one type first)"
            ),
            span,
        );
        self.ambiguous
            .push((self.env.file, AmbiguousKey::Node(id), d));
    }

    /// `Owner#name`, or the extension's target for an extension's method.
    fn method_label(&self, m: MethodId) -> String {
        let info = self.world.method(m);
        let owner = match info.extension {
            Some(e) => {
                // `extension Array[T <: Int]`: its parameters with their bounds.
                let ext = &self.world.extensions[e as usize];
                let args: Vec<String> = ext
                    .target_args
                    .iter()
                    .map(|a| match a {
                        Type::Param(p) => match ext.type_params.iter().find(|tp| tp.id == *p) {
                            Some(tp) if !tp.bounds.is_empty() => {
                                let bs: Vec<String> =
                                    tp.bounds.iter().map(|b| self.world.type_name(b)).collect();
                                format!("{} <: {}", tp.name, bs.join(" & "))
                            }
                            Some(tp) => tp.name.clone(),
                            None => self.world.type_name(a),
                        },
                        _ => self.world.type_name(a),
                    })
                    .collect();
                let target = &self.world.class(ext.target).name;
                if args.is_empty() {
                    format!("extension {target}")
                } else {
                    format!("extension {target}[{}]", args.join(", "))
                }
            }
            None => self.world.class(info.owner).name.clone(),
        };
        let params: Vec<String> = info
            .params
            .iter()
            .map(|p| self.world.type_name(&p.ty))
            .collect();
        let sep = if info.singleton { "." } else { "#" };
        if params.is_empty() {
            format!("{owner}{sep}{}", info.name)
        } else {
            format!("{owner}{sep}{}({})", info.name, params.join(", "))
        }
    }

    /// Whether the bounds of an extension method's type parameters
    /// (`extension Array[T <: Int]`) hold for the receiver's arguments.
    fn extension_bounds_hold(&self, id: MethodId, subst: &HashMap<TypeParamId, Type>) -> bool {
        let Some(ext) = self.world.method(id).extension else {
            return true;
        };
        let ext = &self.world.extensions[ext as usize];
        ext.type_params.iter().all(|tp| match subst.get(&tp.id) {
            Some(t) => {
                let t = self.resolve(t);
                tp.bounds
                    .iter()
                    .all(|b| self.world.is_subtype(&t, &b.subst(subst)))
            }
            None => true,
        })
    }

    /// The class a run-time class test sees for a value of type `t`.
    fn test_class(&self, t: &Type) -> Option<ClassId> {
        let b = &self.world.builtin;
        match t {
            Type::Class(c, _) => Some(*c),
            Type::Tuple(_) => Some(b.array),
            Type::Proc(..) => Some(b.proc_),
            Type::ClassObject(..) => Some(b.class_),
            _ => None,
        }
    }

    /// Order entries so that a subclass comes before its superclasses
    /// (tested in order, the first that matches is the most specific).
    fn subclasses_first<T>(&self, entries: &mut [T], class: impl Fn(&T) -> ClassId) {
        entries.sort_by_key(|e| std::cmp::Reverse(self.world.ancestors(class(e), &[]).len()));
    }

    /// Record what an interpolation calls (`Output::interp_to_s`): for a
    /// value of class `cid`, an extension's `to_s` or (`None`) the value's
    /// own; a check that found another for the same class (each check of
    /// a block) gives it up.
    fn note_interp_to_s(&mut self, id: NodeId, cid: ClassId, m: Option<MethodId>, span: Span) {
        if self.out.interp_conflicts.contains(&id) {
            return;
        }
        let before = self.out.interp_to_s.get(&id).cloned();
        self.table_journal.push(TableUndo::Interp(id, before));
        let mut table = self.out.interp_to_s.remove(&id).unwrap_or_default();
        // As for a call (`note_union_table`): one class, or a module and an
        // unrelated member, answered differently.
        let clash = table.iter().find(|(d, n)| {
            *n != m
                && (*d == cid
                    || ((self.world.class(*d).kind == ClassKind::Module
                        || self.world.class(cid).kind == ClassKind::Module)
                        && !self.world.class_is_a(*d, cid)
                        && !self.world.class_is_a(cid, *d)))
        });
        if let Some((d, _)) = clash {
            let (a, b) = (
                self.world.class(*d).name.clone(),
                self.world.class(cid).name.clone(),
            );
            self.out.interp_conflicts.insert(id);
            let what = if a == b { a } else { format!("{a} and {b}") };
            let d = Diagnostic::error(
                format!(
                    "cannot tell at run time which `to_s` the interpolation calls for {what} (give the value one type first)"
                ),
                span,
            );
            self.ambiguous
                .push((self.env.file, AmbiguousKey::Node(id), d));
            return;
        }
        if !table.iter().any(|(d, _)| *d == cid) {
            table.push((cid, m));
        }
        self.subclasses_first(&mut table, |e| e.0);
        self.out.interp_to_s.insert(id, table);
    }

    /// A compound assignment's reader, resolved just now (a union's
    /// members answering differently are called by name).
    fn note_op_getter(&mut self, id: NodeId, span: Span) {
        let found = match (
            self.out.calls.get(&id),
            self.out.dynamic_calls.contains(&id),
        ) {
            (Some(CallTarget::Method { method }), false) => Some(*method),
            _ => None,
        };
        self.note_op_method(id, false, found, span);
        self.out.calls.remove(&id);
        self.out.dynamic_calls.remove(&id);
        self.journal_union(id);
        self.out.union_calls.remove(&id);
    }

    /// The writer's union record of a compound assignment's node, set
    /// aside while its reader (on the same node) is checked.
    fn take_union_record(&mut self, id: NodeId) -> (Option<Vec<(Type, MethodId)>>, bool) {
        self.journal_union(id);
        (
            self.out.union_calls.remove(&id),
            self.out.union_conflicts.remove(&id),
        )
    }

    fn restore_union_record(&mut self, id: NodeId, saved: (Option<Vec<(Type, MethodId)>>, bool)) {
        self.journal_union(id);
        self.out.union_calls.remove(&id);
        self.out.union_conflicts.remove(&id);
        if let Some(t) = saved.0 {
            self.out.union_calls.insert(id, t);
        }
        if saved.1 {
            self.out.union_conflicts.insert(id);
        }
    }

    /// Record a compound assignment's reader (`operator` false) or
    /// operator: given up (called by name) when a check finds none or
    /// another check (of a block, once per type) found another.
    fn note_op_method(&mut self, id: NodeId, operator: bool, found: Option<MethodId>, span: Span) {
        let key = (id, operator);
        let recorded = if operator {
            self.out.op_operators.get(&id).copied()
        } else {
            self.out.op_getters.get(&id).copied()
        };
        self.table_journal.push(TableUndo::Op(
            key,
            self.op_seen.get(&key).copied(),
            self.op_given_up.contains(&key),
            recorded,
        ));
        // Two checks found an extension's method and another: by name the
        // extension's is not found (as `ambiguous_call`).
        if let (Some(Some(before)), Some(now)) = (self.op_seen.get(&key).copied(), found) {
            let (b, n) = (self.world.method(before), self.world.method(now));
            // (User overloads, of one class or a class and its ancestor:
            // the first a lookup finds.)
            let related = b.owner == n.owner
                || self.world.class_is_a(b.owner, n.owner)
                || self.world.class_is_a(n.owner, b.owner);
            let wrong = b.extension.is_some()
                || n.extension.is_some()
                || (related && !b.is_native && !n.is_native);
            if before != now && wrong {
                let name = self.world.method(now).name.clone();
                let (wb, wn) = (self.method_label(before), self.method_label(now));
                let d = Diagnostic::error(
                    format!(
                        "cannot tell at run time which `{name}` to call: {wb} or {wn} (give the value one type first)"
                    ),
                    span,
                );
                self.ambiguous
                    .push((self.env.file, AmbiguousKey::Node(id), d));
            }
        }
        let map = if operator {
            &mut self.out.op_operators
        } else {
            &mut self.out.op_getters
        };
        let disagree = self.op_seen.insert(key, found).is_some_and(|f| f != found);
        if disagree || found.is_none() || self.op_given_up.contains(&key) {
            map.remove(&id);
            self.op_given_up.insert(key);
        } else if let Some(m) = found {
            map.insert(id, m);
        }
    }

    /// The extensions active throughout a file: its top level's `using`s
    /// and the top-level extensions of its group (`World::group_extensions`).
    fn file_extensions(&self, file: u32) -> Vec<ExtensionId> {
        let mut active = self
            .file_main(file)
            .map(|fm| self.world.class(fm).usings.clone())
            .unwrap_or_default();
        for e in self.world.group_extensions(file) {
            if !active.contains(&e) {
                active.push(e);
            }
        }
        active
    }

    fn lookup_var(&self, name: &str) -> Option<(usize, usize)> {
        let n = self.env.frames.len();
        for (i, frame) in self.env.frames.iter().enumerate().rev() {
            // The last declaration wins (pattern variables of later arms).
            if let Some(slot) = frame.vars.find(name) {
                return Some((n - 1 - i, slot));
            }
            if !frame.is_block {
                break;
            }
        }
        None
    }

    /// The innermost frame that captures by value, in diagnostics about
    /// assigning to what it captured.
    fn task_block_name(&self) -> &'static str {
        if self.env.lifted_frame == self.env.task_frame && self.env.lifted_frame.is_some() {
            "a block given to `def_method` (it becomes a method's body)"
        } else if self.env.task_shareable_proc {
            "a shareable procedure"
        } else {
            "a task block (`Task.spawn`, `Task.blocking`)"
        }
    }

    /// The same, in diagnostics about what it may capture.
    fn task_capture_name(&self) -> &'static str {
        if self.env.lifted_frame == self.env.task_frame && self.env.lifted_frame.is_some() {
            "a block given to `def_method`"
        } else if self.env.task_shareable_proc {
            "a shareable procedure"
        } else {
            "a `Task.spawn` block"
        }
    }

    /// Whether a value of type `t` may be baked into a generated method
    /// (docs/14 §5): what has a literal or is immutable data. `Object`, a
    /// type parameter and a module type may hold such a value; the
    /// statement's run decides for them.
    fn bakeable_type(&mut self, t: &Type) -> bool {
        let t = self.resolve(t);
        match &t {
            Type::Nothing | Type::Void | Type::Var(_) | Type::Param(_) => true,
            Type::ClassObject(_, _) | Type::TypeOf(_) => true,
            Type::Union(ms) | Type::Tuple(ms) => ms.clone().iter().all(|m| self.bakeable_type(m)),
            Type::Proc(..) => false,
            Type::Class(id, args) => {
                let id = *id;
                let b = &self.world.builtin;
                let literal = [
                    b.nil, b.bool_, b.int, b.integer, b.float, b.string, b.symbol, b.regexp,
                    b.bytes, b.array, b.hash, b.range, b.class_,
                ]
                .contains(&id);
                let class = self.world.class(id);
                let ok = literal
                    || id == b.object
                    || matches!(
                        class.kind,
                        ClassKind::Data | ClassKind::Enum | ClassKind::Variant | ClassKind::Module
                    );
                ok && args.clone().iter().all(|a| self.bakeable_type(a))
            }
        }
    }

    /// Whether a variable `depth` frames up lives outside the innermost
    /// task block.
    fn captured_across_task(&self, depth: usize) -> bool {
        match self.env.task_frame {
            Some(tf) => self.env.frames.len() - 1 - depth < tf,
            None => false,
        }
    }

    fn check_task_capture(&mut self, name: &str, depth: usize, t: &Type, span: Span) {
        if !self.captured_across_task(depth) {
            return;
        }
        if self.env.static_frame.is_some() && self.env.static_frame == self.env.task_frame {
            self.error(
                format!("a block in `static(...)` captures nothing: `{name}` is not a constant (docs/14 §8)"),
                span,
            );
            return;
        }
        let rt = self.resolve(t);
        if rt.has_vars() {
            return;
        }
        if self.env.lifted_frame.is_some() && self.env.lifted_frame == self.env.task_frame {
            if !self.bakeable_type(&rt) {
                self.error(
                    format!(
                        "`{name}` has type {}, whose values cannot be baked into a generated method; a block given to `def_method` captures only immutable values (literals, classes, `data`)",
                        self.world.type_name(&rt)
                    ),
                    span,
                );
            }
            return;
        }
        if !self.world.is_shareable(&rt) {
            self.error(
                format!(
                    "`{name}` has the non-shareable type {} and cannot be captured by {}",
                    self.world.type_name(&rt),
                    self.task_capture_name()
                ),
                span,
            );
        }
    }

    fn var_type(&self, depth: usize, slot: usize) -> Type {
        let n = self.env.frames.len();
        let v = &self.env.frames[n - 1 - depth].vars[slot];
        v.narrowed.clone().unwrap_or_else(|| v.declared.clone())
    }

    fn declare_var(&mut self, name: &str, ty: Type, span: Span) -> VarRef {
        let frame = self.env.frames.last_mut().unwrap();
        frame.vars.push(VarInfo {
            name: name.to_string(),
            declared: ty,
            narrowed: None,
            listed: false,
        });
        let r = VarRef {
            depth: 0,
            slot: frame.vars.len() as u32 - 1,
        };
        self.out.var_refs.insert(span, r);
        r
    }

    fn set_narrowed(&mut self, key: &VarKey, t: Option<Type>) {
        match key {
            VarKey::Local(name) => {
                // A closure that may run later assigns it.
                let t = t.filter(|_| !self.env.never_narrow.contains(name));
                if let Some((depth, slot)) = self.lookup_var(name) {
                    let n = self.env.frames.len();
                    if let (Some(rec), Some(t), false) =
                        (&mut self.env.ensure_assigns, &t, self.env.applying_facts)
                    {
                        let key = (n - 1 - depth, slot);
                        let j = match rec.get(&key) {
                            Some(old) => self.world.join(old, t),
                            None => t.clone(),
                        };
                        rec.insert(key, j);
                    }
                    let vars = &mut self.env.frames[n - 1 - depth].vars;
                    let t = t.filter(|t| *t != vars[slot].declared);
                    vars.set_narrowed(slot, t);
                }
            }
            VarKey::IVar(name) => match t {
                Some(t) => {
                    self.env.ivar_narrow.insert(name.clone(), t);
                }
                None => {
                    self.env.ivar_narrow.remove(name);
                }
            },
        }
    }

    /// Narrow the subject of a `case` in a branch (a fact).
    fn narrow_subject(&mut self, key: &VarKey, t: Option<Type>) {
        let saved = std::mem::replace(&mut self.env.applying_facts, true);
        self.set_narrowed(key, t);
        self.env.applying_facts = saved;
    }

    fn apply_facts(&mut self, facts: &Facts) {
        // A fact narrows the value a variable has; it assigns nothing.
        let saved = std::mem::replace(&mut self.env.applying_facts, true);
        for (key, t) in facts {
            self.set_narrowed(key, Some(t.clone()));
        }
        self.env.applying_facts = saved;
    }

    /// Snapshot of all narrowings (for branches).
    fn snapshot(&mut self) -> Snapshot {
        (
            self.env
                .frames
                .iter_mut()
                .map(|f| f.vars.snapshot())
                .collect(),
            self.env.ivar_narrow.clone(),
        )
    }

    /// Go back to the narrowings of `snap`. Variables declared since
    /// were unassigned then: they may be nil.
    fn restore(&mut self, snap: &Snapshot) {
        for (f, saved) in self.env.frames.iter_mut().zip(snap.0.iter()) {
            let now = std::mem::take(&mut f.vars.narrowed);
            for &slot in &now {
                f.vars.list[slot].listed = false;
                if slot < saved.len {
                    f.vars.list[slot].narrowed = None;
                }
            }
            f.vars.narrowed = now;
            f.vars.narrowed.retain(|&slot| slot >= saved.len);
            for &slot in &f.vars.narrowed {
                f.vars.list[slot].listed = true;
            }
            for (slot, t) in &saved.narrowed {
                f.vars.set_narrowed(*slot, Some(t.clone()));
            }
        }
        self.unset_since(snap);
        self.env.ivar_narrow = snap.1.clone();
    }

    /// Make the variables declared since `snap` nilable: on some path
    /// from there they are not assigned.
    fn unset_since(&mut self, snap: &Snapshot) {
        let nil = self.world.nil();
        for (fi, f) in self.env.frames.iter_mut().enumerate() {
            let known = snap.0.get(fi).map_or(0, |s| s.len);
            for slot in known..f.vars.len() {
                let t = Self::maybe_unset(&self.world, &self.infer, &f.vars[slot], &nil);
                f.vars.set_narrowed(slot, t);
            }
        }
    }

    /// The variables a pattern test (`v in Int => n`) declared since
    /// `snap` are bound only when it matches: their types become facts of
    /// a match, and they may be nil otherwise.
    fn bound_if_matched(&mut self, snap: &Snapshot, facts: &mut Facts) {
        let frame = self.env.frames.last().unwrap();
        let known = snap.0.last().map_or(0, |s| s.len);
        for v in frame.vars.iter().skip(known) {
            let t = v.narrowed.clone().unwrap_or_else(|| v.declared.clone());
            facts.push((VarKey::Local(v.name.clone()), t));
        }
        // An existing local the pattern binds holds its new value where it
        // matched (a fact), and its old one or the new where it did not:
        // the pattern may fail before binding it, or after.
        for (fi, slot, name, before, now) in self.rebound_since(snap) {
            facts.push((VarKey::Local(name), now.clone()));
            let either = self.join(&before, &now);
            self.env.frames[fi].vars.set_narrowed(slot, Some(either));
        }
        self.unset_since(snap);
    }

    /// The variables that existed at `snap` whose narrowing changed since
    /// (a pattern bound them): frame, slot, name, type then, type now.
    fn rebound_since(&self, snap: &Snapshot) -> Vec<(usize, usize, String, Type, Type)> {
        let mut changed = Vec::new();
        for (fi, f) in self.env.frames.iter().enumerate() {
            let Some(saved) = snap.0.get(fi) else {
                continue;
            };
            for slot in 0..saved.len.min(f.vars.len()) {
                let v = &f.vars[slot];
                let old = saved.get(slot).flatten();
                if v.narrowed.as_ref() == old {
                    continue;
                }
                let before = old.cloned().unwrap_or_else(|| v.declared.clone());
                let now = v.narrowed.clone().unwrap_or_else(|| v.declared.clone());
                changed.push((fi, slot, v.name.clone(), before, now));
            }
        }
        changed
    }

    /// The fields whose narrowing changed since `snap` (a guard assigned
    /// them).
    fn ivars_changed_since(&self, snap: &Snapshot) -> Vec<String> {
        let now = &self.env.ivar_narrow;
        let then = &snap.1;
        let mut names: Vec<String> = now
            .keys()
            .chain(then.keys())
            .filter(|n| now.get(*n) != then.get(*n))
            .cloned()
            .collect();
        names.sort();
        names.dedup();
        names
    }

    /// Widen each field's narrowing by what a failed guard may have left
    /// it (`None`: unnarrowed, its declared type).
    fn widen_ivars(&mut self, changed: &[(String, Option<Type>)]) {
        for (n, t) in changed {
            let cur = self.env.ivar_narrow.get(n).cloned();
            match (cur, t) {
                (Some(cur), Some(t)) => {
                    let either = self.join(&cur, t);
                    self.env.ivar_narrow.insert(n.clone(), either);
                }
                _ => {
                    self.env.ivar_narrow.remove(n);
                }
            }
        }
    }

    /// Widen each of `rebound` (frame, slot, a type a failed arm's
    /// pattern may have bound it to) by that type.
    fn widen_rebound(&mut self, rebound: &[(usize, usize, Type)]) {
        for (fi, slot, t) in rebound {
            let v = &self.env.frames[*fi].vars[*slot];
            let cur = v.narrowed.clone().unwrap_or_else(|| v.declared.clone());
            let either = self.join(&cur, t);
            self.env.frames[*fi].vars.set_narrowed(*slot, Some(either));
        }
    }

    /// Take back from `now` the narrowings of the variables declared
    /// since `snap`.
    fn keep_since(&mut self, snap: &Snapshot, now: &Snapshot) {
        for (fi, f) in self.env.frames.iter_mut().enumerate() {
            let known = snap.0.get(fi).map_or(0, |s| s.len);
            let Some(cur) = now.0.get(fi) else {
                continue;
            };
            for slot in known..cur.len.min(f.vars.len()) {
                let t = cur.get(slot).flatten().cloned();
                f.vars.set_narrowed(slot, t);
            }
        }
    }

    /// `t` with each undecided variable that is a member of a union with
    /// other types decided as those (`?v | Nil` used as a receiver, or as
    /// a method's result: nothing else tells what `?v` is).
    fn settle_vars(&mut self, t: &Type) -> Type {
        let t = self.infer.resolve(t);
        self.settle_in(&t);
        self.infer.resolve(&t)
    }

    fn settle_in(&mut self, t: &Type) {
        match t {
            Type::Union(ms) => {
                let (vars, rest): (Vec<Type>, Vec<Type>) =
                    ms.iter().cloned().partition(|m| matches!(m, Type::Var(_)));
                // `?v | Nil` tells nothing of `?v`.
                let nil = self.world.nil();
                if !vars.is_empty() && rest.iter().any(|r| *r != nil) {
                    let rest = self.world.erase_narrowed(&Type::union_of(rest));
                    for v in vars {
                        if let Type::Var(v) = v {
                            self.infer.bind(v, rest.clone());
                        }
                    }
                }
                ms.iter().for_each(|m| self.settle_in(m));
            }
            Type::Class(_, args) | Type::ClassObject(_, args) | Type::Tuple(args) => {
                args.iter().for_each(|a| self.settle_in(a));
            }
            Type::TypeOf(t) => self.settle_in(t),
            Type::Proc(rc, ps, r, _) => {
                if let Some(rc) = rc {
                    self.settle_in(rc);
                }
                ps.iter().for_each(|p| self.settle_in(p));
                self.settle_in(r);
            }
            Type::Var(_) | Type::Nothing | Type::Void | Type::Param(_) => {}
        }
    }

    /// The narrowing `j` (a join of narrowings) of a variable declared
    /// `declared`. A variable of a type not decided yet stays undecided:
    /// a test narrowed it inside a branch (to `String` in `in String`),
    /// which after the branches is no more than its own type, or nil.
    /// A narrowing made while the type was undecided, joined after `?v`
    /// was decided in a later branch, is cut back to the declared type.
    fn fit_narrowing(world: &World, infer: &InferTable, declared: &Type, j: Type) -> Option<Type> {
        let d = infer.resolve(declared);
        let nil = world.nil();
        let with_nil = || {
            j.members()
                .contains(&nil)
                .then(|| Type::union_of(vec![d.clone(), nil.clone()]))
        };
        if let Type::Var(_) = d {
            return with_nil();
        }
        if j == *declared || j == d {
            return None;
        }
        if !world.is_subtype(&j, &Type::union_of(vec![d.clone(), nil.clone()])) {
            return with_nil();
        }
        Some(j)
    }

    /// The narrowing of a variable that may be unassigned: its type or
    /// nil (any value it was given, on an earlier pass of a loop).
    fn maybe_unset(world: &World, infer: &InferTable, v: &VarInfo, nil: &Type) -> Option<Type> {
        let j = world.join(&infer.resolve(&v.declared), nil);
        if j == v.declared {
            None
        } else {
            Some(j)
        }
    }

    /// Merge the narrowings of two branches into the current environment
    /// (which holds the second branch's state).
    fn merge_with(&mut self, other: &Snapshot, other_dead: bool, self_dead: bool) {
        if self_dead && !other_dead {
            self.restore(other);
            return;
        }
        if other_dead {
            return;
        }
        let nil = self.world.nil();
        for (fi, f) in self.env.frames.iter_mut().enumerate() {
            let Some(saved) = other.0.get(fi) else {
                continue;
            };
            // Only variables narrowed in either branch can differ.
            let mut slots: Vec<usize> = f
                .vars
                .narrowed
                .iter()
                .copied()
                .chain(saved.narrowed.iter().map(|(s, _)| *s))
                .filter(|&s| s < saved.len && s < f.vars.len())
                .collect();
            slots.sort_unstable();
            slots.dedup();
            for slot in slots {
                let v = &f.vars[slot];
                let s = saved.get(slot).flatten();
                if v.narrowed.as_ref() != s {
                    let a = v.narrowed.clone().unwrap_or_else(|| v.declared.clone());
                    let b = s.cloned().unwrap_or_else(|| v.declared.clone());
                    let j = self
                        .world
                        .join(&self.infer.resolve(&a), &self.infer.resolve(&b));
                    let t = Self::fit_narrowing(&self.world, &self.infer, &v.declared, j);
                    f.vars.set_narrowed(slot, t);
                }
            }
            for slot in saved.len..f.vars.len() {
                // Declared after the other branch: unassigned there.
                let t = Self::maybe_unset(&self.world, &self.infer, &f.vars[slot], &nil);
                f.vars.set_narrowed(slot, t);
            }
        }
        let keys: Vec<String> = self.env.ivar_narrow.keys().cloned().collect();
        for k in keys {
            match other.1.get(&k) {
                Some(t) if *t == self.env.ivar_narrow[&k] => {}
                Some(t) => {
                    let a = self.env.ivar_narrow[&k].clone();
                    let j = self.world.join(&a, t);
                    self.env.ivar_narrow.insert(k, j);
                }
                None => {
                    self.env.ivar_narrow.remove(&k);
                }
            }
        }
    }

    /// Names assigned anywhere inside the expressions (for widening before
    /// loops and blocks).
    fn assigned_names(exprs: &[Expr], out: &mut Assigned) {
        for e in exprs {
            Self::assigned_names_expr(e, out);
        }
    }

    fn assigned_names_expr(e: &Expr, out: &mut Assigned) {
        use ExprKind::*;
        match &e.kind {
            // Both expansions assign the same names.
            For(f) => Self::assigned_names_expr(&f.comprehension, out),
            Assign { target, value } | OpAssign { target, value, .. } => {
                match &**target {
                    LValue::Local { name, .. } => out.add(name),
                    LValue::IVar(name) => {
                        out.ivars.insert(name.clone());
                    }
                    LValue::Attr { recv, .. } => Self::assigned_names_expr(recv, out),
                    LValue::Index { recv, args } => {
                        Self::assigned_names_expr(recv, out);
                        Self::assigned_names_args(args, out);
                    }
                    _ => {}
                }
                Self::assigned_names_expr(value, out);
            }
            MultiAssign { targets, value } => {
                fn collect(t: &MultiTarget, out: &mut Assigned) {
                    match t {
                        MultiTarget::Single(LValue::Local { name, .. })
                        | MultiTarget::Splat(Some(LValue::Local { name, .. })) => out.add(name),
                        MultiTarget::Single(LValue::IVar(name))
                        | MultiTarget::Splat(Some(LValue::IVar(name))) => {
                            out.ivars.insert(name.clone());
                        }
                        MultiTarget::Nested(ts) => ts.iter().for_each(|t| collect(t, out)),
                        _ => {}
                    }
                }
                targets.iter().for_each(|t| collect(t, out));
                Self::assigned_names_expr(value, out);
            }
            TypedDecl { name, value, .. } => {
                out.add(name);
                Self::assigned_names_expr(value, out);
            }
            Call(call) => {
                if let Some(r) = &call.recv {
                    Self::assigned_names_expr(r, out);
                    // `x.foo!` rebinds `x` when its type has no `foo!`.
                    if call.name.ends_with('!') && call.name != "!=" {
                        if let ExprKind::Local(name) = &r.kind {
                            out.bangs.push((name.clone(), call.name.clone()));
                            out.note_escaping(name);
                            if out.repeat > 0 {
                                out.repeated.insert(name.clone());
                            }
                        }
                    }
                }
                for a in &call.args {
                    match a {
                        Arg::Positional(x)
                        | Arg::Splat(x)
                        | Arg::DoubleSplat(x)
                        | Arg::BlockPass(x) => Self::assigned_names_expr(x, out),
                        Arg::Keyword { value, .. } => Self::assigned_names_expr(value, out),
                    }
                }
                if let Some(b) = &call.block {
                    out.closure(b, out.late);
                }
            }
            If { cond, then, els } => {
                Self::assigned_names_expr(cond, out);
                Self::assigned_names(then, out);
                if let Some(els) = els {
                    Self::assigned_names(els, out);
                }
            }
            While { cond, body, .. } => {
                out.repeat += 1;
                Self::assigned_names_expr(cond, out);
                Self::assigned_names(body, out);
                out.repeat -= 1;
            }
            And(a, b) | Or(a, b) => {
                Self::assigned_names_expr(a, out);
                Self::assigned_names_expr(b, out);
            }
            Not(a) | Static(a) => Self::assigned_names_expr(a, out),
            Case {
                subject,
                whens,
                els,
            } => {
                if let Some(s) = subject {
                    Self::assigned_names_expr(s, out);
                }
                for w in whens {
                    Self::assigned_names_args(&w.conds, out);
                    Self::assigned_names(&w.body, out);
                }
                if let Some(els) = els {
                    Self::assigned_names(els, out);
                }
            }
            CaseIn { subject, arms, els } => {
                Self::assigned_names_expr(subject, out);
                for a in arms {
                    let mut bound = HashSet::default();
                    Self::pattern_names(&a.pattern, &mut bound);
                    bound.iter().for_each(|n| out.add(n));
                    if let Some(g) = &a.guard {
                        Self::assigned_names_expr(&g.cond, out);
                    }
                    Self::assigned_names(&a.body, out);
                }
                if let Some(els) = els {
                    Self::assigned_names(els, out);
                }
            }
            Begin(b) => {
                // A body a rescue retries runs again, as a loop's does.
                let retried = b.rescues.iter().any(|r| Self::mentions_retry(&r.body));
                out.repeat += retried as u32;
                Self::assigned_names(&b.body, out);
                out.repeat -= retried as u32;
                for r in &b.rescues {
                    // (The clause's variable is its own: docs/01 §12.)
                    match &r.var {
                        Some(v) => out.scoped(v, |out| Self::assigned_names(&r.body, out)),
                        None => Self::assigned_names(&r.body, out),
                    }
                }
                if let Some(x) = &b.else_body {
                    Self::assigned_names(x, out);
                }
                if let Some(x) = &b.ensure {
                    Self::assigned_names(x, out);
                }
            }
            Seq(es) => Self::assigned_names(es, out),
            Return(Some(v)) | Break(Some(v)) | Next(Some(v)) => Self::assigned_names_expr(v, out),
            Lambda(b) => out.closure(b, true),
            Array(items) | Yield(items) => Self::assigned_names_args(items, out),
            Super { args, block } => {
                out.supers = true;
                if let Some(args) = args {
                    Self::assigned_names_args(args, out);
                }
                // The overridden method's block may be kept, as far as
                // this method knows.
                if let Some(b) = block {
                    out.closure(b, true);
                }
            }
            Hash(entries) => {
                for e in entries {
                    match e {
                        HashEntry::Pair { key, value } => {
                            Self::assigned_names_expr(key, out);
                            Self::assigned_names_expr(value, out);
                        }
                        HashEntry::DoubleSplat(x) => Self::assigned_names_expr(x, out),
                    }
                }
            }
            Range { lo, hi, .. } => {
                for x in [lo, hi].into_iter().flatten() {
                    Self::assigned_names_expr(x, out);
                }
            }
            MatchPattern { value, pattern, .. } => {
                Self::assigned_names_expr(value, out);
                let mut bound = HashSet::default();
                Self::pattern_names(pattern, &mut bound);
                bound.iter().for_each(|n| out.add(n));
            }
            Str(parts) | DSymbol(parts) | Regexp { parts, .. } => {
                for p in parts {
                    if let StrPart::Interp(x) = p {
                        Self::assigned_names_expr(x, out);
                    }
                }
            }
            Retry => out.retries = true,
            _ => {}
        }
    }

    /// The variables a pattern binds.
    /// Whether `body` may `retry` (a nested one counts: over, not under).
    fn mentions_retry(body: &[Expr]) -> bool {
        let mut a = Assigned::default();
        Self::assigned_names(body, &mut a);
        a.retries
    }

    fn pattern_names(p: &Pattern, out: &mut HashSet<String>) {
        fn array(a: &ArrayPattern, out: &mut HashSet<String>) {
            for p in a.pre.iter().chain(&a.post) {
                Checker::pattern_names(p, out);
            }
            if let Some(Some(r)) = &a.rest {
                out.insert(r.clone());
            }
        }
        fn hash(h: &HashPattern, out: &mut HashSet<String>) {
            for pair in &h.pairs {
                match &pair.pattern {
                    Some(p) => Checker::pattern_names(p, out),
                    None => {
                        out.insert(pair.key.clone());
                    }
                }
            }
            if let Some(HashPatternRest::Bind(r)) = &h.rest {
                out.insert(r.clone());
            }
        }
        match &p.kind {
            PatternKind::Bind(n) => {
                out.insert(n.clone());
            }
            PatternKind::Capture(p, n) => {
                Self::pattern_names(p, out);
                out.insert(n.clone());
            }
            PatternKind::Alt(ps) => ps.iter().for_each(|p| Self::pattern_names(p, out)),
            PatternKind::ConstArray(_, a) => array(a, out),
            PatternKind::Array(a) => array(a, out),
            PatternKind::ConstHash(_, h) => hash(h, out),
            PatternKind::Hash(h) => hash(h, out),
            PatternKind::Find {
                pre_rest,
                middle,
                post_rest,
            } => {
                out.extend(pre_rest.iter().chain(post_rest.iter()).cloned());
                middle.iter().for_each(|p| Self::pattern_names(p, out));
            }
            PatternKind::Value(_)
            | PatternKind::Pin(_)
            | PatternKind::Const(_)
            | PatternKind::Range { .. } => {}
        }
    }

    fn assigned_names_args(args: &[Arg], out: &mut Assigned) {
        for a in args {
            match a {
                Arg::Positional(x) | Arg::Splat(x) | Arg::DoubleSplat(x) | Arg::BlockPass(x) => {
                    Self::assigned_names_expr(x, out)
                }
                Arg::Keyword { value, .. } => Self::assigned_names_expr(value, out),
            }
        }
    }

    /// Reset the narrowing of outer variables assigned inside `body`.
    fn widen_assigned(&mut self, body: &[Expr]) {
        self.widen_assigned_except(body, None);
    }

    /// `widen_assigned`, with `own` a local of the body's own (a rescue
    /// clause's variable), which the outer local of the name is not.
    fn widen_assigned_except(&mut self, body: &[Expr], own: Option<&str>) {
        let mut assigned = Assigned::default();
        match own {
            Some(v) => assigned.scoped(v, |a| Self::assigned_names(body, a)),
            None => Self::assigned_names(body, &mut assigned),
        }
        self.widen_fields(&assigned);
        for (name, method) in assigned.bangs {
            if !assigned.names.contains(&name) && self.bang_may_assign(&name, &method) {
                assigned.names.insert(name);
            }
        }
        for name in assigned.names {
            self.set_narrowed(&VarKey::Local(name), None);
        }
    }

    /// The fields the code scanned into `assigned` may assign (in
    /// `initialize`; elsewhere only `var` fields, never narrowed) are
    /// not narrowed from here on; a `super` there assigns the inherited
    /// ones.
    fn widen_fields(&mut self, assigned: &Assigned) {
        for name in &assigned.ivars {
            self.env.ivar_narrow.remove(name);
        }
        if assigned.supers && self.env.in_initialize {
            for name in self.inherited_fields() {
                self.env.ivar_narrow.remove(&name);
            }
        }
    }

    /// The names of the fields the current method's owner inherits (which
    /// its `initialize`'s `super` assigns).
    fn inherited_fields(&self) -> Vec<String> {
        let Some(owner) = self.env.method.map(|m| self.world.method(m).owner) else {
            return Vec::new();
        };
        let own = &self.world.class(owner).fields;
        self.world
            .all_fields(owner)
            .into_iter()
            .filter(|(f, _)| own.iter().all(|o| o.name != f.name))
            .map(|(f, _)| f.name)
            .collect()
    }

    /// The facts of the left operand of `&&`/`||` that still hold after
    /// the right one ran: not those about a variable it assigns (or
    /// rebinds by a `!` method), nor, when it calls `super` in
    /// `initialize`, about an inherited field.
    fn facts_surviving(&self, facts: Facts, right: &Expr) -> Facts {
        let mut assigned = Assigned::default();
        Self::assigned_names_expr(right, &mut assigned);
        for (name, method) in &assigned.bangs {
            if self.bang_may_assign(name, method) {
                assigned.names.insert(name.clone());
            }
        }
        let inherited = if assigned.supers && self.env.in_initialize {
            self.inherited_fields()
        } else {
            Vec::new()
        };
        if assigned.names.is_empty() && assigned.ivars.is_empty() && inherited.is_empty() {
            return facts;
        }
        facts
            .into_iter()
            .filter(|(key, _)| match key {
                VarKey::Local(n) => !assigned.names.contains(n),
                VarKey::IVar(n) => !assigned.ivars.contains(n) && !inherited.contains(n),
            })
            .collect()
    }

    /// Stop narrowing `names` from here on in the body.
    fn never_narrow(&mut self, names: impl IntoIterator<Item = String>) {
        let names: Vec<String> = names
            .into_iter()
            .filter(|n| !self.env.never_narrow.contains(n))
            .collect();
        for name in names {
            self.set_narrowed(&VarKey::Local(name.clone()), None);
            Rc::make_mut(&mut self.env.never_narrow).insert(name);
        }
    }

    /// Entering code that may run again (a loop's body, a block, a
    /// lambda): a closure made later in it, which may run later (a
    /// lambda, or any block: whether its method keeps it is not known
    /// yet), may have assigned an outer local by the time the code runs
    /// again, so such locals are not narrowed from here on. A local of
    /// the closure itself (assigned nowhere outside it, not in scope
    /// here) is not one.
    fn prescan_repeated<'e>(
        &mut self,
        body: impl IntoIterator<Item = &'e Expr>,
        fresh_locals: bool,
    ) {
        let mut assigned = Assigned {
            late: true,
            ..Assigned::default()
        };
        for e in body {
            Self::assigned_names_expr(e, &mut assigned);
        }
        // The body's own locals count too when they outlive a run of it (a
        // loop's, a body a `rescue` retries); a block's or a lambda's are
        // new each time it runs (`fresh_locals`).
        let captured: Vec<String> = assigned
            .escaped
            .into_iter()
            .filter(|n| {
                (!fresh_locals && assigned.outside.contains(n)) || self.lookup_var(n).is_some()
            })
            .chain(
                assigned
                    .fresh
                    .into_iter()
                    .filter(|n| self.lookup_var(n).is_some()),
            )
            .collect();
        self.never_narrow(captured);
    }

    /// Set up the closure facts of a body (`Env::reassigned`,
    /// `Env::never_narrow`) before checking it.
    fn scan_closures<'e, 'p>(
        &mut self,
        body: impl IntoIterator<Item = &'e Expr> + Clone,
        params: impl Iterator<Item = &'p str>,
    ) {
        let body_again = body.clone();
        let params_list: Vec<String> = params.map(str::to_string).collect();
        let params = params_list.iter().map(|s| s.as_str());
        let mut assigned = Assigned::default();
        for e in body {
            Self::assigned_names_expr(e, &mut assigned);
        }
        // Locals that may change after a closure captures them: assigned
        // in two places or more, where code may run again, as parameters
        // (of the method, a block or a lambda), or rebound by a bang.
        let mut reassigned: HashSet<String> = assigned
            .counts
            .iter()
            .filter(|(_, n)| **n > 1)
            .map(|(name, _)| name.clone())
            .collect();
        reassigned.extend(assigned.repeated.iter().cloned());
        for p in params
            .map(str::to_string)
            .chain(assigned.closure_params.iter().cloned())
        {
            if assigned.names.contains(&p) {
                reassigned.insert(p);
            }
        }
        reassigned.extend(assigned.bangs.iter().map(|(n, _)| n.clone()));
        self.env.reassigned = Some(Rc::new(reassigned));
        // The same walk, counting any block as a closure that may run
        // later, for what they assign of the body's locals (the REPL keeps
        // adding).
        let mut late = Assigned {
            late: true,
            ..Assigned::default()
        };
        for e in body_again {
            Self::assigned_names_expr(e, &mut late);
        }
        // (`escaped` holds what is in scope where the closure is made: a
        // local of the body or of an enclosing closure, a parameter; which
        // of them a closure entered later sees, `enter_late_closure` asks.)
        let found: Vec<String> = late
            .escaped
            .into_iter()
            .chain(
                late.fresh
                    .into_iter()
                    .filter(|n| params_list.contains(n) || self.lookup_var(n).is_some()),
            )
            .collect();
        Rc::make_mut(&mut self.env.late_assigned).extend(found);
    }

    /// Entering a closure that may run later: the narrowings of outer
    /// locals that may change before it runs do not hold in it. Returns
    /// what `leave_late_closure` restores.
    /// Whether `m` runs its block in a task (`Task.spawn`, `Scope#spawn`,
    /// `Task.blocking`): the block is checked as a task's.
    fn runs_block_in_task(world: &World, m: &MethodInfo) -> bool {
        (m.name == "spawn" && (m.owner == world.builtin.task || m.owner == world.builtin.scope))
            || ((m.name == "blocking" || m.name == "__spawn_service")
                && m.owner == world.builtin.task)
    }

    /// Whether the code being checked is in a closure that may run later
    /// (a lambda, a block a method may keep), where the method's own
    /// anonymous block may no longer be live.
    fn in_late_closure(&self) -> bool {
        self.env.blocks.iter().any(|b| b.is_lambda || b.escapes)
    }

    fn enter_late_closure(&mut self, body: &[Expr]) -> (Snapshot, Rc<HashSet<String>>) {
        // The outer locals it assigns: any call (implicit ones included)
        // may run it from now on.
        let mut assigned = Assigned::default();
        Self::assigned_names(body, &mut assigned);
        let mut captured: Vec<String> = assigned
            .names
            .into_iter()
            .filter(|n| self.lookup_var(n).is_some())
            .collect();
        captured.extend(
            assigned
                .bangs
                .into_iter()
                .map(|(n, _)| n)
                .filter(|n| self.lookup_var(n).is_some()),
        );
        self.never_narrow(captured);
        let snap = self.snapshot();
        let saved_never = self.env.never_narrow.clone();
        // What other closures that may run later assign (made after this
        // one, maybe) may have changed by the time it runs; so may a field
        // `initialize` assigns later.
        // (Where the body is not known whole, the REPL's top level, which
        // later inputs add to: any outer local.)
        // (Only those in scope here: a name assigned first in the closure
        // is its own local, whatever the body assigns to it later.)
        let late: Vec<String> = match &self.env.reassigned {
            Some(_) => self
                .env
                .late_assigned
                .iter()
                .filter(|n| self.lookup_var(n).is_some())
                .cloned()
                .collect(),
            None => self
                .env
                .frames
                .iter()
                .flat_map(|f| f.vars.iter().map(|v| v.name.clone()))
                .collect(),
        };
        self.never_narrow(late);
        // A field read in it is its declared type: `initialize` may assign
        // the field after the closure is made, there or in a method it
        // calls (one a subclass in another file may override, so which
        // methods those are is not known here; docs/02 §6). Not where
        // only a generated constructor assigns them.
        if !self.fields_fixed_at_construction() {
            self.env.ivar_narrow.clear();
        }
        let names: Vec<String> = self
            .env
            .frames
            .iter()
            .flat_map(|f| f.vars.iter().map(|v| v.name.clone()))
            .filter(|n| self.env.reassigned.as_ref().is_none_or(|r| r.contains(n)))
            .collect();
        for name in names {
            self.set_narrowed(&VarKey::Local(name), None);
        }
        (snap, saved_never)
    }

    /// Whether `self`'s fields are all assigned before any of its code
    /// runs: a `data` type or enum variant whose only `initialize` is the
    /// generated one, which calls no method (and which nothing subclasses).
    fn fields_fixed_at_construction(&self) -> bool {
        let Some(c) = self.env.class_id else {
            return false;
        };
        let class = self.world.class(c);
        matches!(class.kind, ClassKind::Data | ClassKind::Variant)
            && class.methods.get("initialize").is_none_or(|ids| {
                ids.iter()
                    .all(|m| matches!(self.world.method(*m).synth, Synth::DataInit))
            })
    }

    fn leave_late_closure(&mut self, saved: &(Snapshot, Rc<HashSet<String>>), body: &[Expr]) {
        self.env.never_narrow = saved.1.clone();
        self.restore(&saved.0);
        self.widen_assigned(body);
    }

    /// Whether `name.method` (`method` ends with `!`) may be the sugar
    /// for `name = name.foo`: unless every member of the variable's type
    /// has a `foo!` (which its subclasses inherit; a narrowing to one
    /// that has only `foo` would take the sugar). `nil` calls nothing.
    fn bang_may_assign(&self, name: &str, method: &str) -> bool {
        let Some((depth, slot)) = self.lookup_var(name) else {
            return false;
        };
        let n = self.env.frames.len();
        let t = self
            .infer
            .resolve(&self.env.frames[n - 1 - depth].vars[slot].declared);
        let members = match &t {
            Type::Union(ms) => ms.clone(),
            t => vec![t.clone()],
        };
        let nil = self.world.nil();
        members
            .iter()
            .any(|m| *m != nil && self.world.lookup_methods(m, method).is_empty())
    }

    // ----- bodies --------------------------------------------------------------

    /// Whether `Self` appears in the method's signature.
    fn mentions_self(m: &MethodInfo) -> bool {
        let is = |t: &Type| t.mentions_param(SELF_PARAM);
        m.params.iter().any(|p| is(&p.ty))
            || m.block.as_ref().is_some_and(|(_, t)| is(t))
            || is(&m.ret)
    }

    /// Whether `self` is the method's own `self` with the opaque type
    /// `Self` (an instance method whose signature mentions `Self`, outside
    /// blocks run with another receiver).
    fn self_is_opaque(&self) -> bool {
        self.env.self_opaque
            && self.env.receivers.is_empty()
            && !matches!(self.env.self_type, Type::ClassObject(..))
    }

    /// Whether a call with an implicit or explicit `self` receiver of type
    /// `recv` binds `Self` opaquely: an instance method's `self`, or a
    /// class method's receiver (whose instances `Self` stands for).
    fn self_is_opaque_for(&self, recv: &Type) -> bool {
        self.env.self_opaque
            && self.env.receivers.is_empty()
            && (*recv == Type::Param(SELF_PARAM) || *recv == self.env.self_type)
    }

    /// What `Self` stands for in method `m` called on (or run with) `recv`:
    /// the receiver's type, or for a class method (`def self.build ->
    /// Self`), whose receiver is a class, that class's instances.
    fn self_binding(world: &World, m: &MethodInfo, recv: &Type) -> Type {
        match recv {
            Type::ClassObject(id, args) if m.singleton => Type::Class(*id, args.clone()),
            Type::TypeOf(t) if m.singleton => (**t).clone(),
            t => match (m.singleton, world.class_object_instance(t)) {
                (true, Some(instance)) => instance,
                _ => t.clone(),
            },
        }
    }

    /// Record (or, when a block is checked again in another context,
    /// forget) that the value of `e` is discarded; see `Output::discarded`.
    fn mark_discarded(&mut self, e: Option<&Expr>, void: bool) {
        if let Some(e) = e {
            if void {
                self.out.discarded.insert(e.id);
            } else {
                self.out.discarded.remove(&e.id);
            }
        }
    }

    fn check_body(&mut self, body: &[Expr], expected: Option<&Type>) -> Type {
        let void = std::mem::take(&mut self.next_body_void);
        if body.is_empty() {
            return self.world.nil();
        }
        let mut result = self.world.nil();
        let mut dead = false;
        // `using M` inside a body: its extensions are active from there to
        // the end of this statement list.
        let active_len = self.world.active_extensions.len();
        for (i, e) in body.iter().enumerate() {
            let last = i == body.len() - 1;
            if dead {
                self.warning("unreachable code", e.span);
                dead = false; // report once
            }
            if let ExprKind::Using(path) = &e.kind {
                self.activate_using(path, e.span);
            }
            self.stmt_unused = !last || void;
            let t = self.check_expr(e, if last { expected } else { None });
            if !last {
                self.note_temp_stmt(e);
            }
            if t.is_nothing() {
                dead = true;
                result = Type::Nothing;
            } else if last {
                result = t;
            }
        }
        self.world.active_extensions.truncate(active_len);
        result
    }

    /// `using M` in a body: make the module's extensions active (the
    /// caller scopes them).
    fn activate_using(&mut self, path: &ConstPath, span: Span) {
        let namespace = self.env.scope.namespace;
        match self.resolve_path(namespace, path, span) {
            Some(Member::Class(id)) if self.world.class(id).kind == ClassKind::Module => {
                let ids = self.world.class(id).extensions.clone();
                for e in ids {
                    if !self.world.active_extensions.contains(&e) {
                        self.world.active_extensions.push(e);
                    }
                }
            }
            Some(_) => self.error(format!("`using {path}`: not a module"), span),
            None => {}
        }
    }

    // ----- expressions --------------------------------------------------------

    pub fn check_expr(&mut self, expr: &Expr, expected: Option<&Type>) -> Type {
        let unused = std::mem::take(&mut self.stmt_unused);
        let t = match &expr.kind {
            ExprKind::For(f) => self.check_for(expr, f, expected, unused),
            // An `if` whose value is not used: its branches' types are not
            // joined, which would decide an inference variable (`b = xs[0]
            // if c` fixing an empty array's element type to Nil).
            ExprKind::If { cond, then, els } if unused => {
                self.check_if_as(cond, then, els.as_deref(), None, false)
            }
            _ => self.check_expr_inner(expr, expected),
        };
        self.record(expr.id, &t);
        if unused {
            self.warn_discarded_pure(expr);
        }
        t
    }

    /// `xs.push(1)` as a statement: a method of a built-in immutable type
    /// that takes no block only computes its result, so discarding it is
    /// almost certainly a mistake (Ruby's `push` changed `xs`).
    fn warn_discarded_pure(&mut self, expr: &Expr) {
        let ExprKind::Call(call) = &expr.kind else {
            return;
        };
        let Some(recv) = &call.recv else {
            return;
        };
        if call.block.is_some() || self.out.bang_assign.contains(&expr.id) {
            return;
        }
        let Some(CallTarget::Method { method }) = self.out.calls.get(&expr.id) else {
            return;
        };
        let m = self.world.method(*method);
        let b = &self.world.builtin;
        if m.file != 0
            || m.singleton
            || m.block.is_some()
            || !(m.owner == b.enumerable
                || m.owner == b.comparable
                || self.immutable_builtin(m.owner))
        {
            return;
        }
        let Some(rt) = self.out.node_types.get(&recv.id) else {
            return;
        };
        let rt = self.infer.resolve(rt).without_nil(b.nil);
        let Type::Class(cid, _) = rt else {
            return;
        };
        if !self.immutable_builtin(cid) {
            return;
        }
        let class = self.world.class(cid).name.clone();
        let name = m.name.clone();
        let hint = match &recv.kind {
            ExprKind::Local(v) | ExprKind::IVar(v) => {
                let v = if matches!(recv.kind, ExprKind::IVar(_)) {
                    format!("@{v}")
                } else {
                    v.clone()
                };
                let args = if call.args.is_empty() { "" } else { "(...)" };
                format!(": assign it (`{v} = {v}.{name}{args}`, or `{v}.{name}!{args}`)")
            }
            _ => String::new(),
        };
        self.warning(
            format!("the result of `{name}` is discarded; {class} is immutable, so the call changes nothing{hint}"),
            expr.span,
        );
    }

    fn immutable_builtin(&self, cid: ClassId) -> bool {
        let b = &self.world.builtin;
        [b.array, b.hash, b.set, b.string, b.bytes].contains(&cid)
    }

    /// A `for`: when its value is not used, as nested `each` calls (it then
    /// builds nothing), if that checks; else, or when a source has no
    /// `each` (a `Result`), as the comprehension. Checking the `each`
    /// expansion first is a trial: if it fails, what it inferred, declared
    /// and reported is undone.
    fn check_for(
        &mut self,
        expr: &Expr,
        f: &ForExpr,
        expected: Option<&Type>,
        unused: bool,
    ) -> Type {
        if unused {
            let infer = self.infer.save();
            let env = self.env.clone();
            let reported = self.diagnostics.len();
            let reported_tables = self.table_mark();
            self.check_expr(&f.each, None);
            let failed = self.diagnostics[reported..]
                .iter()
                .any(|(_, d)| d.is_error());
            if !failed {
                self.out.for_loops.insert(expr.id);
                return self.world.nil();
            }
            self.truncate_diagnostics(reported);
            self.discard_tables(reported_tables);
            self.infer.restore(infer);
            self.env = env;
        }
        self.out.for_loops.remove(&expr.id);
        self.check_expr(&f.comprehension, expected)
    }

    fn check_expr_inner(&mut self, expr: &Expr, expected: Option<&Type>) -> Type {
        use ExprKind::*;
        match &expr.kind {
            For(f) => self.check_for(expr, f, expected, false),
            Nil => self.world.nil(),
            True | False => self.world.bool_(),
            SelfRef => {
                self.check_task_self("`self`", expr.span);
                if self.self_is_opaque() {
                    Type::Param(SELF_PARAM)
                } else {
                    self.env.self_type.clone()
                }
            }
            Int(lit) => {
                if let Some(e) = expected {
                    let e = self.resolve(e);
                    if e == self.world.float() && !self.int_literals.contains(&expr.id) {
                        if self.out.float_literals.insert(expr.id) {
                            self.table_journal
                                .push(TableUndo::Literal(expr.id, true, true));
                        }
                        return self.world.float();
                    }
                    if e == self.world.integer() {
                        if self.out.integer_literals.insert(expr.id) {
                            let converted = lit.value.is_some();
                            self.table_journal
                                .push(TableUndo::Literal(expr.id, false, converted));
                        }
                        return self.world.integer();
                    }
                }
                if lit.value.is_none() {
                    if self.out.integer_literals.insert(expr.id) {
                        self.table_journal
                            .push(TableUndo::Literal(expr.id, false, false));
                    }
                    return self.world.integer();
                }
                self.world.int()
            }
            Float(_) => self.world.float(),
            Str(parts) => {
                self.check_str_parts(parts);
                self.world.string()
            }
            Symbol(_) => self.world.symbol(),
            DSymbol(parts) => {
                self.check_str_parts(parts);
                self.world.symbol()
            }
            Regexp { parts, .. } => {
                self.check_str_parts(parts);
                Type::class(self.world.builtin.regexp)
            }
            Bytes(_) => Type::class(self.world.builtin.bytes),
            Magic(m) => match m {
                quarz_syntax::ast::Magic::Line => self.world.int(),
                // A block in `static(...)` runs at compile time, outside
                // the method it is written in (docs/14 §8).
                quarz_syntax::ast::Magic::Method if self.env.static_frame.is_some() => {
                    self.error(
                        "a block in `static(...)` captures nothing: `__method__` is the method's name, not a constant (docs/14 §8)",
                        expr.span,
                    );
                    self.world.string()
                }
                // `__method__` is nil outside a method.
                quarz_syntax::ast::Magic::Method if self.env.method.is_none() => {
                    self.world.nilable(self.world.string())
                }
                _ => self.world.string(),
            },
            Array(items) => self.check_array(items, expected, expr.span),
            Hash(entries) => self.check_hash(entries, expected),
            Range {
                lo,
                hi,
                exclusive: _,
            } => {
                let mut t = Type::Nothing;
                let elem_expected = match expected.map(|e| self.resolve(e)) {
                    Some(Type::Class(id, args))
                        if id == self.world.builtin.range && args.len() == 1 =>
                    {
                        Some(args[0].clone())
                    }
                    _ => None,
                };
                for side in [lo, hi].into_iter().flatten() {
                    let st = self.check_expr(side, elem_expected.as_ref());
                    t = self.join(&t, &st);
                }
                if t.is_nothing() {
                    t = self.infer.fresh();
                }
                Type::Class(self.world.builtin.range, vec![t])
            }
            Lambda(block) => self.check_lambda(expr.id, block, expected),
            Local(name) => match self.lookup_var(name) {
                Some((depth, slot)) => {
                    self.out.var_refs.insert(
                        expr.span,
                        VarRef {
                            depth: depth as u32,
                            slot: slot as u32,
                        },
                    );
                    let t = self.var_type(depth, slot);
                    self.check_task_capture(name, depth, &t, expr.span);
                    t
                }
                None => {
                    self.error(format!("undefined local variable `{name}`"), expr.span);
                    Type::Nothing
                }
            },
            IVar(name) => self.check_ivar_read(expr, name),
            Const(path) => self.check_const(expr, path),
            TypeApp(te) => {
                let scope = self.env.scope.clone();
                match self.resolve_type_expr(te, &scope) {
                    Some(Type::Class(id, args)) => {
                        self.out
                            .const_targets
                            .insert(expr.id, ConstTarget::Class(id));
                        Type::ClassObject(id, args)
                    }
                    Some(_) => {
                        self.error("expected a class type", te.span);
                        Type::Nothing
                    }
                    None => Type::Nothing,
                }
            }
            Call(call) => {
                let t = self.check_call(expr, call, expected);
                self.check_dup(expr, call);
                // `bump` in a `Task.spawn` block in a method of a mutable
                // class: a call on the captured `self` (a call to a
                // built-in `Kernel` function such as `puts` does not use
                // it; one an `extension Kernel` adds does).
                if call.recv.is_none() {
                    if let Some(CallTarget::Method { method }) = self.out.calls.get(&expr.id) {
                        let m = self.world.method(*method);
                        if !(m.is_native && m.owner == self.world.builtin.kernel) {
                            let what = format!("calling `{}` uses `self`, which", call.name);
                            self.check_task_self(&what, expr.span);
                        }
                    }
                }
                t
            }
            MethodRef { recv, name } => {
                let rt = self.check_expr(recv, None);
                let rt = self.resolve(&rt);
                let cands = self.world.lookup_methods(&rt, name);
                let Some((mid, subst)) = cands.first().cloned() else {
                    self.error(
                        format!("undefined method `{name}` for {}", self.name(&rt)),
                        expr.span,
                    );
                    return Type::Nothing;
                };
                let m = self.world.method(mid).clone();
                // `initialize` runs only from `new` and `super` (docs/01
                // §3): a reference to it would run it on a made object.
                if name == "initialize" && !m.singleton {
                    self.error(
                        "`initialize` is called only by `new` and by `super` in `initialize` (in `.:initialize`)",
                        expr.span,
                    );
                    return Type::Nothing;
                }
                let mut subst = subst;
                subst.insert(SELF_PARAM, Self::self_binding(&self.world, &m, &rt));
                let params: Vec<Type> = m
                    .params
                    .iter()
                    .filter(|p| p.kind == ParamKind::Positional)
                    .map(|p| p.ty.subst(&subst))
                    .collect();
                let ret = self.method_ret(mid).subst(&subst);
                self.out
                    .calls
                    .insert(expr.id, CallTarget::Method { method: mid });
                self.note_static_call(expr, mid);
                Type::Proc(None, params, Box::new(ret), false)
            }
            Yield(args) => self.check_yield(expr, args),
            Super { args, block } => self.check_super(expr, args.as_deref(), block.as_deref()),
            Assign { target, value } => self.check_assign(expr, target, value, expected),
            OpAssign { target, op, value } => self.check_op_assign(expr, target, *op, value),
            MultiAssign { targets, value } => self.check_multi_assign(expr, targets, value),
            TypedDecl { name, ty, value } => {
                let scope = self.env.scope.clone();
                let Some(declared) = self.resolve_type_expr(ty, &scope) else {
                    return Type::Nothing;
                };
                let vt = self.check_expr(value, Some(&declared));
                if !self.coerce(&vt, &declared) {
                    self.error(
                        format!(
                            "cannot assign {} to `{name}` of type {}",
                            self.name(&vt),
                            self.name(&declared)
                        ),
                        value.span,
                    );
                }
                if self.lookup_var(name).is_some_and(|(d, _)| d == 0) {
                    self.error(format!("`{name}` is already declared"), expr.span);
                }
                self.declare_var(name, declared.clone(), expr.span);
                let narrowed = self.resolve(&vt);
                self.set_narrowed(&VarKey::Local(name.clone()), Some(narrowed));
                declared
            }
            And(a, b) => {
                let (ta, facts_true, _) = self.check_cond(a);
                if let Some(t) = self.logical_method(expr, "&&", &ta, b, expected) {
                    return t;
                }
                let snap = self.snapshot();
                self.apply_facts(&facts_true);
                let tb = self.check_expr(b, None);
                let b_dead = tb.is_nothing();
                self.merge_with(&snap, false, b_dead);
                if self.resolve(&ta) == self.world.bool_()
                    && self.resolve(&tb) == self.world.bool_()
                {
                    return self.world.bool_();
                }
                let fa = self.falsy_part(&ta);
                self.join(&fa, &tb)
            }
            Or(a, b) => {
                let (ta, _, facts_false) = self.check_cond(a);
                if let Some(t) = self.logical_method(expr, "||", &ta, b, expected) {
                    return t;
                }
                let snap = self.snapshot();
                self.apply_facts(&facts_false);
                let tb = self.check_expr(b, expected);
                let b_dead = tb.is_nothing();
                self.merge_with(&snap, false, b_dead);
                if self.resolve(&ta) == self.world.bool_()
                    && self.resolve(&tb) == self.world.bool_()
                {
                    return self.world.bool_();
                }
                let truthy = self.truthy_part(&ta);
                self.join(&truthy, &tb)
            }
            Static(inner) => self.check_static_expr(expr, inner, expected),
            Not(a) => {
                let t = self.check_expr(a, None);
                match self.not_method(expr, a, &t) {
                    Some(rt) => rt,
                    None => self.world.bool_(),
                }
            }
            If { cond, then, els } => self.check_if(cond, then, els.as_deref(), expected),
            While {
                cond,
                body,
                negate,
                do_while,
            } => {
                self.widen_assigned(body);
                self.widen_assigned(std::slice::from_ref(cond));
                self.prescan_repeated(body.iter().chain(std::iter::once(&**cond)), false);
                let (ct, facts_true, facts_false) = self.check_cond(cond);
                let (body_facts, exit_facts) = if *negate {
                    (facts_false, facts_true)
                } else {
                    (facts_true, facts_false)
                };
                let snap = self.snapshot();
                if !*do_while {
                    self.apply_facts(&body_facts);
                }
                self.env.loop_depth += 1;
                let saved_exits = std::mem::take(&mut self.env.loop_exits);
                self.check_body(body, None);
                let end_of_body = self.snapshot();
                let exits = std::mem::replace(&mut self.env.loop_exits, saved_exits);
                let broke = !exits.breaks.is_empty();
                self.env.loop_depth -= 1;
                let infinite = matches!(cond.kind, ExprKind::True) && !*negate
                    || matches!(cond.kind, ExprKind::False) && *negate;
                if infinite && !exits.through_ensure {
                    // Only a `break` leaves: as at the breaks.
                    if let Some((first, rest)) = exits.breaks.split_first() {
                        self.restore(first);
                        for b in rest {
                            self.merge_with(b, false, false);
                        }
                    }
                } else {
                    self.restore(&snap);
                    self.widen_assigned(body);
                    // Variables the body declares are unassigned when it
                    // does not run, or leaves before assigning them; a
                    // `begin ... end while` body runs once.
                    if !*do_while || broke || exits.skipped {
                        self.unset_since(&snap);
                    } else {
                        self.keep_since(&snap, &end_of_body);
                    }
                }
                // The loop ends with its condition false, unless a `break`
                // leaves it (`while w.nil?` with a `break`: `w` may still
                // be nil after it).
                if !broke {
                    self.apply_facts(&exit_facts);
                }
                let _ = ct;
                if infinite && !broke {
                    Type::Nothing
                } else {
                    self.world.nil()
                }
            }
            Case {
                subject,
                whens,
                els,
            } => self.check_case_when(subject.as_deref(), whens, els.as_deref(), expected),
            CaseIn { subject, arms, els } => {
                self.check_case_in(subject, arms, els.as_deref(), expected, expr.span)
            }
            MatchPattern {
                value,
                pattern,
                raises,
            } => {
                let vt = self.check_expr(value, None);
                let vt = self.resolve(&vt);
                let before = self.snapshot();
                let mut facts = self.check_pattern_facts(pattern, &vt, value);
                if *raises {
                    self.apply_facts(&facts);
                    self.world.nil()
                } else {
                    self.bound_if_matched(&before, &mut facts);
                    self.world.bool_()
                }
            }
            Begin(block) => self.check_begin(block, expected),
            Return(value) => {
                let in_lambda = self.env.blocks.last().is_some_and(|b| b.is_lambda);
                if !in_lambda && self.env.lifted_frame.is_some() {
                    self.error(
                        "`return` in a block given to `def_method`: the block becomes the generated method's body, whose value is its last expression",
                        expr.span,
                    );
                    if let Some(v) = value {
                        self.check_expr(v, None);
                    }
                    return Type::Nothing;
                }
                if in_lambda {
                    let ret = self.env.blocks.last().unwrap().ret.clone();
                    let void = self.resolve(&ret) == Type::Void;
                    let t = match value {
                        Some(v) => self.check_expr(v, if void { None } else { Some(&ret) }),
                        None => self.world.nil(),
                    };
                    if !self.coerce(&t, &ret) {
                        let message = if void {
                            format!(
                                "`return` gives a {} but the lambda is `-> Void`, which returns nil",
                                self.name(&t)
                            )
                        } else {
                            format!(
                                "lambda returns {} but `return` has type {}",
                                self.name(&ret),
                                self.name(&t)
                            )
                        };
                        self.error(message, expr.span);
                    }
                    return Type::Nothing;
                }
                if self.env.method.is_none()
                    && self
                        .env
                        .class_id
                        .is_some_and(|c| self.world.class(c).kind == ClassKind::Main)
                    && self.env.frames.len() == 1
                {
                    // `return` at the top level ends the program.
                    if let Some(v) = value {
                        self.check_expr(v, None);
                    }
                    return Type::Nothing;
                }
                match self.env.ret_expected.clone() {
                    Some(ret) => {
                        let void = ret == Type::Void;
                        let t = match value {
                            Some(v) => self.check_expr(v, if void { None } else { Some(&ret) }),
                            None => self.world.nil(),
                        };
                        self.mark_discarded(value.as_deref(), void);
                        // A `-> Void` method (or one without a return
                        // type) gives no value: `return x` would drop it.
                        let rt = self.resolve(&t);
                        if void && !rt.is_nothing() && !self.world.is_nil_type(&rt) {
                            self.error(
                                format!(
                                    "`return` gives a {} but the method is `-> Void`, which returns nil (write its return type: `-> T`)",
                                    self.name(&t)
                                ),
                                expr.span,
                            );
                        }
                        if !void && !self.coerce(&t, &ret) {
                            self.error(
                                format!(
                                    "`return` has type {} but the method returns {}",
                                    self.name(&t),
                                    self.name(&ret)
                                ),
                                expr.span,
                            );
                        }
                    }
                    None => {
                        if let Some(v) = value {
                            self.check_expr(v, None);
                        }
                    }
                }
                Type::Nothing
            }
            Break(value) => {
                let in_block = self.env.blocks.last().is_some_and(|b| !b.is_lambda);
                if self.env.loop_depth == 0 && !in_block {
                    self.error("`break` outside of a loop or block", expr.span);
                }
                if self.env.loop_depth == 0 && self.env.blocks.last().is_some_and(|b| b.lifted) {
                    self.error(
                        "`break` in a block given to `def_method`: the block becomes the generated method's body, which `break` cannot leave",
                        expr.span,
                    );
                }
                let t = match value {
                    Some(v) => self.check_expr(v, None),
                    None => self.world.nil(),
                };
                if self.env.loop_depth > 0 {
                    let snap = self.snapshot();
                    self.env.loop_exits.breaks.push(snap);
                    self.env.loop_exits.through_ensure |= self.env.loop_exits.ensures > 0;
                } else if let Some(b) = self.env.blocks.last_mut() {
                    b.breaks.push(t);
                }
                Type::Nothing
            }
            Next(value) => {
                let in_block = !self.env.blocks.is_empty();
                if self.env.loop_depth == 0 && !in_block {
                    self.error("`next` outside of a loop or block", expr.span);
                    return Type::Nothing;
                }
                if self.env.loop_depth > 0 {
                    self.env.loop_exits.skipped = true;
                }
                if in_block && self.env.loop_depth == 0 {
                    let ret = self.env.blocks.last().unwrap().ret.clone();
                    let void = self.resolve(&ret) == Type::Void;
                    let t = match value {
                        Some(v) => self.check_expr(v, if void { None } else { Some(&ret) }),
                        None => self.world.nil(),
                    };
                    self.mark_discarded(value.as_deref(), void);
                    // A block whose result is `Void` gives no value, as a
                    // `-> Void` method's `return` does not.
                    let rt = self.resolve(&t);
                    if void && !rt.is_nothing() && !self.world.is_nil_type(&rt) {
                        self.error(
                            format!(
                                "`next` gives a {} but the block's result is `Void`, which gives nil (use a bare `next`)",
                                self.name(&t)
                            ),
                            expr.span,
                        );
                    }
                    if !void && !self.coerce(&t, &ret) {
                        self.error(
                            format!(
                                "`next` has type {} but the block returns {}",
                                self.name(&t),
                                self.name(&ret)
                            ),
                            expr.span,
                        );
                    }
                } else if let Some(v) = value {
                    self.check_expr(v, None);
                }
                Type::Nothing
            }
            Retry => {
                if self.env.in_rescue == 0 {
                    self.error(
                        "`retry` outside of a rescue clause (it must be directly in one, not in a block)",
                        expr.span,
                    );
                }
                Type::Nothing
            }
            Seq(exprs) => self.check_body(exprs, expected),
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
            | Extern { .. } => {
                self.error("declarations are not allowed here", expr.span);
                Type::Nothing
            }
            Using(_) | Require { .. } => self.world.nil(),
        }
    }

    fn check_str_parts(&mut self, parts: &[StrPart]) {
        for p in parts {
            if let StrPart::Interp(e) = p {
                let t = self.check_expr(e, None);
                let t = self.resolve(&t);
                // Each class the value may be of (`Foo?`, a union).
                for m in t.members() {
                    let Type::Class(cid, _) = m else { continue };
                    let to_s = self
                        .world
                        .lookup_methods(&m, "to_s")
                        .into_iter()
                        .find(|(id, subst)| {
                            let m = self.world.method(*id);
                            m.params.is_empty()
                                && m.block.is_none()
                                && self.extension_bounds_hold(*id, subst)
                        })
                        .map(|(m, _)| m);
                    let found = to_s.filter(|m| self.world.method(*m).extension.is_some());
                    self.note_interp_to_s(e.id, cid, found, e.span);
                }
            }
        }
    }

    fn check_array(&mut self, items: &[Arg], expected: Option<&Type>, span: Span) -> Type {
        let expected = expected.map(|e| self.resolve(e));
        // A tuple expected, alone or among other types (`[Int, String]?`).
        let expected_tuple = match &expected {
            Some(t @ Type::Tuple(_)) => Some(t.clone()),
            Some(Type::Union(ms)) => {
                let tuples: Vec<&Type> = ms
                    .iter()
                    .filter(|m| matches!(m, Type::Tuple(ts) if ts.len() == items.len()))
                    .collect();
                // Another member an array may be (`Array[Int]`, a module
                // `Array` includes, `Object`, a type parameter) may take
                // the literal instead.
                let array = self.world.builtin.array;
                let arrays = ms.iter().any(|m| match m {
                    Type::Class(id, _) => self.world.class_is_a(array, *id),
                    Type::Param(_) | Type::Var(_) => true,
                    _ => false,
                });
                (tuples.len() == 1 && !arrays).then(|| tuples[0].clone())
            }
            _ => None,
        };
        // Tuple expectation.
        if let Some(Type::Tuple(ts)) = &expected_tuple {
            if ts.len() == items.len() && items.iter().all(|a| matches!(a, Arg::Positional(_))) {
                let mut out = Vec::new();
                for (a, et) in items.iter().zip(ts.iter()) {
                    let Arg::Positional(e) = a else {
                        unreachable!()
                    };
                    let t = self.check_expr(e, Some(et));
                    if !self.coerce(&t, et) {
                        self.error(
                            format!("expected {} but found {}", self.name(et), self.name(&t)),
                            e.span,
                        );
                    }
                    out.push(et.clone());
                }
                return Type::Tuple(out);
            }
        }
        let elem_expected = match &expected {
            Some(Type::Class(id, args)) if *id == self.world.builtin.array && args.len() == 1 => {
                Some(args[0].clone())
            }
            _ => None,
        };
        let mut elem = Type::Nothing;
        // The type of each element, while all are positional.
        let mut each: Option<Vec<Type>> = Some(Vec::new());
        for a in items {
            match a {
                Arg::Positional(e) => {
                    let t = self.check_expr(e, elem_expected.as_ref());
                    elem = self.join(&elem, &t);
                    if let Some(each) = &mut each {
                        each.push(t);
                    }
                }
                Arg::Splat(e) => {
                    each = None;
                    let t = self.check_expr(e, None);
                    let t = self.resolve(&t);
                    match &t {
                        Type::Class(id, args)
                            if *id == self.world.builtin.array && args.len() == 1 =>
                        {
                            elem = self.join(&elem, &args[0].clone());
                        }
                        Type::Tuple(ts) => {
                            for x in ts.clone() {
                                elem = self.join(&elem, &x);
                            }
                        }
                        _ => self.error(format!("cannot splat {}", self.name(&t)), e.span),
                    }
                }
                _ => self.error("unexpected argument form in an array literal", a.span()),
            }
        }
        // Several members the literal may be (two tuples of its length, a
        // tuple and an array): the first tuple its elements fit, else an
        // array (`[1, "a"]` for `[Int, String] | Array[Int]`, `[1, 2]` for
        // `[Int, String] | [Int, Int]`).
        if let (Some(Type::Union(ms)), Some(each)) = (&expected, &each) {
            for m in ms {
                let Type::Tuple(ts) = m else { continue };
                if ts.len() != each.len() {
                    continue;
                }
                let saved = self.infer.save();
                if each.iter().zip(ts).all(|(t, et)| self.coerce(t, et)) {
                    return Type::Tuple(ts.clone());
                }
                self.infer.restore(saved);
            }
        }
        if let Some(et) = &elem_expected {
            if elem.is_nothing() || self.coerce(&elem, et) {
                return self.world.array_of(et.clone());
            }
            self.error(
                format!(
                    "array elements have type {} but {} was expected",
                    self.name(&elem),
                    self.name(et)
                ),
                span,
            );
            return self.world.array_of(et.clone());
        }
        // With nothing expected, elements of different types make a
        // tuple (`[w, w.size]` is `[String, Int]`), and elements of one type
        // an array (`[1, 2]` is `Array[Int]`). A tuple is also an array of
        // the union of its element types, so it can be used as one.
        if expected.is_none() || matches!(expected, Some(Type::Var(_))) {
            if let Some(each) = each {
                // Elements with a common type (`[circle, rect]`: a
                // `Shape`; subclasses of one class) still make an array:
                // only a join that is a union makes a tuple.
                let each: Vec<Type> = each.iter().map(|t| self.resolve(t)).collect();
                if each.len() >= 2
                    && !each.iter().any(|t| t.has_vars() || t.is_nothing())
                    && matches!(self.resolve(&elem), Type::Union(_))
                {
                    return Type::Tuple(each);
                }
            }
        }
        if elem.is_nothing() {
            elem = self.infer.fresh();
        }
        self.world.array_of(elem)
    }

    fn check_hash(&mut self, entries: &[HashEntry], expected: Option<&Type>) -> Type {
        let expected = expected.map(|e| self.resolve(e));
        let (ek, ev) = match &expected {
            Some(Type::Class(id, args)) if *id == self.world.builtin.hash && args.len() == 2 => {
                (Some(args[0].clone()), Some(args[1].clone()))
            }
            _ => (None, None),
        };
        let mut kt = Type::Nothing;
        let mut vt = Type::Nothing;
        for e in entries {
            match e {
                HashEntry::Pair { key, value } => {
                    let k = self.check_expr(key, ek.as_ref());
                    let v = self.check_expr(value, ev.as_ref());
                    kt = self.join(&kt, &k);
                    vt = self.join(&vt, &v);
                }
                HashEntry::DoubleSplat(x) => {
                    let t = self.check_expr(x, None);
                    match self.resolve(&t) {
                        Type::Class(id, args)
                            if id == self.world.builtin.hash && args.len() == 2 =>
                        {
                            kt = self.join(&kt, &args[0].clone());
                            vt = self.join(&vt, &args[1].clone());
                        }
                        other => self.error(
                            format!("cannot splat {} into a hash", self.name(&other)),
                            x.span,
                        ),
                    }
                }
            }
        }
        if let (Some(ek), Some(ev)) = (&ek, &ev) {
            let ok = (kt.is_nothing() || self.coerce(&kt, ek))
                && (vt.is_nothing() || self.coerce(&vt, ev));
            if !ok {
                let span = entries.first().map(|e| match e {
                    HashEntry::Pair { key, .. } => key.span,
                    HashEntry::DoubleSplat(x) => x.span,
                });
                self.error(
                    format!(
                        "hash has type Hash[{}, {}] but Hash[{}, {}] was expected",
                        self.name(&kt),
                        self.name(&vt),
                        self.name(ek),
                        self.name(ev)
                    ),
                    span.unwrap_or(Span::empty(0)),
                );
            }
            return self.world.hash_of(ek.clone(), ev.clone());
        }
        if kt.is_nothing() {
            kt = self.infer.fresh();
        }
        if vt.is_nothing() {
            vt = self.infer.fresh();
        }
        self.world.hash_of(kt, vt)
    }

    fn check_ivar_read(&mut self, expr: &Expr, name: &str) -> Type {
        if !self.check_ivar_access(expr.span) {
            return Type::Nothing;
        }
        let Some(cid) = self.env.class_id else {
            self.error("instance variables are not available here", expr.span);
            return Type::Nothing;
        };
        if self.world.class(cid).kind == ClassKind::Main {
            self.error(
                "instance variables are not available at the top level",
                expr.span,
            );
            return Type::Nothing;
        }
        let Some((field, subst)) = self.world.find_field(cid, name) else {
            self.error(
                format!(
                    "undeclared field `@{name}` in `{}`",
                    self.world.class(cid).name
                ),
                expr.span,
            );
            return Type::Nothing;
        };
        let index = self.world.field_index(cid, name).unwrap();
        self.out.ivar_fields.insert(expr.id, index);
        if !field.mutable {
            if let Some(t) = self.env.ivar_narrow.get(name) {
                return t.clone();
            }
        }
        field.ty.subst(&subst)
    }

    fn check_const(&mut self, expr: &Expr, path: &ConstPath) -> Type {
        let namespace = self.env.scope.namespace;
        let Some(member) = self.resolve_path(namespace, path, expr.span) else {
            return Type::Nothing;
        };
        match member {
            Member::Class(id) => {
                let class = self.world.class(id);
                if class.kind == ClassKind::Variant && class.fields.is_empty() {
                    self.out
                        .const_targets
                        .insert(expr.id, ConstTarget::VariantSingleton(id));
                    return Type::class(id);
                }
                self.out
                    .const_targets
                    .insert(expr.id, ConstTarget::Class(id));
                Type::ClassObject(id, vec![])
            }
            Member::Const(cid) => {
                self.out
                    .const_targets
                    .insert(expr.id, ConstTarget::Const(cid));
                self.const_type(cid, expr.span)
            }
            Member::Alias(aid) => {
                let hint = if aid == self.world.builtin.class_alias {
                    "; the class of class values is `Type` (`when Type`, `in Type`)"
                } else {
                    ""
                };
                self.error(
                    format!("`{path}` is a type alias, not a value{hint}"),
                    expr.span,
                );
                Type::Nothing
            }
        }
    }

    pub fn resolve_path(
        &mut self,
        namespace: Option<ClassId>,
        path: &ConstPath,
        span: Span,
    ) -> Option<Member> {
        let mut member = if path.cog {
            match self.world.resolve_cog_path_start(namespace, path) {
                Ok(m) => Some(m),
                Err(message) => {
                    self.error(message, span);
                    return None;
                }
            }
        } else if path.absolute {
            self.world.top.get(&path.names[0]).copied()
        } else {
            self.world.resolve_member(namespace, &path.names[0])
        };
        if member.is_none() {
            self.error(format!("unknown constant `{}`", path.names[0]), span);
            return None;
        }
        for name in path.names.get(1..).unwrap_or_default() {
            let Some(Member::Class(cid)) = member.map(|m| self.world.through_alias(m)) else {
                self.error(format!("`{path}` is not a namespace"), span);
                return None;
            };
            member = self.world.member_in(Some(cid), name);
            if member.is_none() {
                for (anc, _) in self.world.ancestors(cid, &[]) {
                    if let Some(m) = self.world.class(anc).members.get(name) {
                        member = Some(*m);
                        break;
                    }
                }
            }
            if member.is_none() {
                self.error(
                    format!(
                        "unknown constant `{name}` in `{}`",
                        self.world.class(cid).name
                    ),
                    span,
                );
                return None;
            }
        }
        member
    }

    pub fn resolve_type_expr(&mut self, te: &TypeExpr, scope: &TypeScope) -> Option<Type> {
        self.resolve_type_expr_as(te, scope, false)
    }

    /// A lambda's declared result, which may be `Void`.
    fn resolve_result_type_expr(&mut self, te: &TypeExpr, scope: &TypeScope) -> Option<Type> {
        self.resolve_type_expr_as(te, scope, true)
    }

    fn resolve_type_expr_as(
        &mut self,
        te: &TypeExpr,
        scope: &TypeScope,
        result: bool,
    ) -> Option<Type> {
        // Reuse the declarer's resolution logic through a temporary.
        let mut d = crate::declare::Declarer::new();
        std::mem::swap(&mut d.world, &mut self.world);
        let t = if result {
            d.resolve_result_type(te, scope)
        } else {
            d.resolve_type(te, scope)
        };
        std::mem::swap(&mut d.world, &mut self.world);
        for (_, diag) in d.diagnostics {
            self.diagnostics.push((self.env.file, diag));
        }
        if let Some(t) = &t {
            self.check_bounds_deep(t, te.span);
        }
        t
    }

    // ----- conditions and narrowing ----------------------------------------------

    /// Check a condition and compute the narrowings that hold when it is
    /// true and when it is false.
    fn check_cond(&mut self, cond: &Expr) -> (Type, Facts, Facts) {
        use ExprKind::*;
        match &cond.kind {
            Not(inner) => {
                let (t, ft, ff) = self.check_cond(inner);
                self.record(inner.id, &t);
                // A type with its own `!` is called, and says nothing
                // about the operand.
                if let Some(rt) = self.not_method(cond, inner, &t) {
                    self.record(cond.id, &rt);
                    return (rt, Facts::default(), Facts::default());
                }
                let bt = self.world.bool_();
                self.record(cond.id, &bt);
                (bt, ff, ft)
            }
            And(a, b) => {
                let (ta, fat, _) = self.check_cond(a);
                if let Some(t) = self.logical_method(cond, "&&", &ta, b, None) {
                    self.record(cond.id, &t);
                    return (t, Vec::new(), Vec::new());
                }
                let snap = self.snapshot();
                self.apply_facts(&fat);
                let (tb, fbt, _) = self.check_cond(b);
                self.merge_with(&snap, false, tb.is_nothing());
                let mut facts_true = self.facts_surviving(fat, b);
                facts_true.extend(fbt);
                let t = if self.resolve(&ta) == self.world.bool_()
                    && self.resolve(&tb) == self.world.bool_()
                {
                    self.world.bool_()
                } else {
                    let fa = self.falsy_part(&ta);
                    self.join(&fa, &tb)
                };
                self.record(cond.id, &t);
                (t, facts_true, Vec::new())
            }
            Or(a, b) => {
                let (ta, _, faf) = self.check_cond(a);
                if let Some(t) = self.logical_method(cond, "||", &ta, b, None) {
                    self.record(cond.id, &t);
                    return (t, Vec::new(), Vec::new());
                }
                let snap = self.snapshot();
                self.apply_facts(&faf);
                let (tb, _, fbf) = self.check_cond(b);
                self.merge_with(&snap, false, tb.is_nothing());
                let mut facts_false = self.facts_surviving(faf, b);
                facts_false.extend(fbf);
                let t = if self.resolve(&ta) == self.world.bool_()
                    && self.resolve(&tb) == self.world.bool_()
                {
                    self.world.bool_()
                } else {
                    let truthy = self.truthy_part(&ta);
                    self.join(&truthy, &tb)
                };
                self.record(cond.id, &t);
                (t, Vec::new(), facts_false)
            }
            Local(name) => {
                let t = self.check_expr(cond, None);
                let key = VarKey::Local(name.clone());
                (
                    t.clone(),
                    vec![(key.clone(), self.truthy_part(&t))],
                    vec![(key, self.falsy_part(&t))],
                )
            }
            IVar(name) => {
                let t = self.check_expr(cond, None);
                let mutable = self
                    .env
                    .class_id
                    .and_then(|c| self.world.find_field(c, name))
                    .is_some_and(|(f, _)| f.mutable);
                if mutable {
                    return (t, Vec::new(), Vec::new());
                }
                let key = VarKey::IVar(name.clone());
                (
                    t.clone(),
                    vec![(key.clone(), self.truthy_part(&t))],
                    vec![(key, self.falsy_part(&t))],
                )
            }
            Assign { target, value } => {
                let t = self.check_expr(cond, None);
                if let LValue::Local { name, .. } = &**target {
                    let key = VarKey::Local(name.clone());
                    let vt = self.resolve(&t);
                    let _ = value;
                    return (
                        t.clone(),
                        vec![(key.clone(), self.truthy_part(&vt))],
                        vec![(key, self.falsy_part(&vt))],
                    );
                }
                (t, Vec::new(), Vec::new())
            }
            MatchPattern {
                value,
                pattern,
                raises: false,
            } => {
                let vt = self.check_expr(value, None);
                let vt = self.resolve(&vt);
                let before = self.snapshot();
                let mut facts = self.check_pattern_facts(pattern, &vt, value);
                self.bound_if_matched(&before, &mut facts);
                let bt = self.world.bool_();
                self.record(cond.id, &bt);
                (bt, facts, Vec::new())
            }
            Call(call) => {
                let t = self.check_expr(cond, None);
                let key = call.recv.as_ref().and_then(|r| self.var_key(r));
                let Some(key) = key else {
                    return (t, Vec::new(), Vec::new());
                };
                let recv_ty = self.resolve(&self.out.node_types[&call.recv.as_ref().unwrap().id]);
                match (call.name.as_str(), call.args.as_slice()) {
                    // Only the prelude's `Object#nil?` tells (`&.` may not
                    // have called it at all).
                    ("nil?", [])
                        if !call.safe_nav
                            && call.block.is_none()
                            && matches!(
                                self.out.calls.get(&cond.id),
                                Some(CallTarget::Method { method })
                                    if self.world.method(*method).owner == self.world.builtin.object
                                        && self.world.method(*method).is_native
                            ) =>
                    {
                        let nil = self.world.nil();
                        let without = recv_ty.without_nil(self.world.builtin.nil);
                        (t, vec![(key.clone(), nil)], vec![(key, without)])
                    }
                    ("is_a?", [_]) => {
                        let Some(CallTarget::IsA(target)) = self.out.calls.get(&cond.id).cloned()
                        else {
                            return (t, Vec::new(), Vec::new());
                        };
                        let (yes, no) = self.split_by_type(&recv_ty, &target);
                        (t, vec![(key.clone(), yes)], vec![(key, no)])
                    }
                    ("==", [Arg::Positional(arg)]) | ("!=", [Arg::Positional(arg)]) => {
                        let is_nil = matches!(arg.kind, ExprKind::Nil);
                        if !is_nil {
                            return self.equality_facts(t, call, arg, key, &recv_ty);
                        }
                        // A class's own `==` may say it equals nil.
                        if !self
                            .expand_members(&recv_ty)
                            .iter()
                            .all(|m| self.equality_trusted(m))
                        {
                            return (t, Vec::new(), Vec::new());
                        }
                        let nil = self.world.nil();
                        let without = recv_ty.without_nil(self.world.builtin.nil);
                        if call.name == "==" {
                            (t, vec![(key.clone(), nil)], vec![(key, without)])
                        } else {
                            (t, vec![(key.clone(), without)], vec![(key, nil)])
                        }
                    }
                    _ => (t, Vec::new(), Vec::new()),
                }
            }
            _ => {
                let t = self.check_expr(cond, None);
                (t, Vec::new(), Vec::new())
            }
        }
    }

    /// `x == true`, `x != Color::Red`: the value equal to a `true` or
    /// `false` literal is a `Bool`, and one equal to a data-less variant
    /// is that variant; one not equal to such a variant is not it.
    fn equality_facts(
        &mut self,
        t: Type,
        call: &Call,
        arg: &Expr,
        key: VarKey,
        recv_ty: &Type,
    ) -> (Type, Facts, Facts) {
        let (target, singleton) = match &arg.kind {
            ExprKind::True | ExprKind::False => (self.world.bool_(), false),
            _ => match self.out.const_targets.get(&arg.id) {
                Some(ConstTarget::VariantSingleton(id)) => (Type::class(*id), true),
                _ => return (t, Vec::new(), Vec::new()),
            },
        };
        // A value whose `==` a program may define (or that may be of a
        // subclass that does) can say it equals `true` without being it.
        let trusted = self
            .expand_members(&self.resolve(recv_ty))
            .iter()
            .all(|m| self.equality_trusted(m));
        if !trusted {
            return (t, Vec::new(), Vec::new());
        }
        let (yes, no) = self.split_by_type(recv_ty, &target);
        let equal = vec![(key.clone(), yes)];
        let unequal = if singleton {
            vec![(key, no)]
        } else {
            Vec::new()
        };
        if call.name == "==" {
            (t, equal, unequal)
        } else {
            (t, unequal, equal)
        }
    }

    /// Whether a value of type `m` compares with the built-in `==` and
    /// `!=`: its class cannot be subclassed (a built-in value class, a
    /// data type, an enum and its variants, declared together), and none
    /// of those classes has others, its own or an active extension's. A
    /// type that may be subclassed is not trusted: a subclass may be
    /// declared in a file compiled separately. A tuple is an `Array`.
    fn equality_trusted(&self, m: &Type) -> bool {
        let b = &self.world.builtin;
        let id = match m {
            Type::Class(id, _) => *id,
            Type::Tuple(_) => b.array,
            _ => return false,
        };
        let sealed = |c: ClassId| {
            self.world.is_value_class(c)
                || c == b.integer
                || matches!(
                    self.world.class(c).kind,
                    ClassKind::Data | ClassKind::Enum | ClassKind::Variant
                )
        };
        if !sealed(id) {
            return false;
        }
        // An enum's values are its variants'.
        let mut classes = vec![id];
        if self.world.class(id).kind == ClassKind::Enum {
            classes.extend(
                (0..self.world.classes.len() as ClassId)
                    .filter(|v| self.world.class(*v).variant_of == Some(id)),
            );
        }
        classes.iter().all(|c| {
            ["==", "!="].iter().all(|name| {
                self.world
                    .lookup_methods(&Type::class(*c), name)
                    .iter()
                    .all(|(mid, _)| self.world.method(*mid).is_native)
            })
        })
    }

    fn var_key(&self, e: &Expr) -> Option<VarKey> {
        match &e.kind {
            ExprKind::Local(name) => Some(VarKey::Local(name.clone())),
            ExprKind::IVar(name) => {
                let mutable = self
                    .env
                    .class_id
                    .and_then(|c| self.world.find_field(c, name))
                    .is_some_and(|(f, _)| f.mutable);
                if mutable {
                    None
                } else {
                    Some(VarKey::IVar(name.clone()))
                }
            }
            _ => None,
        }
    }

    /// Split a type into the part that is a `target` and the rest. A
    /// generic `target` without arguments (`in Box`, `when Box`) takes them
    /// from each member it narrows; where a member does not give them (an
    /// `Object`, a type not decided yet), only a class that admits no
    /// wrong value with `Object` arguments narrows (`guessed_args`), and
    /// other members stay as they are.
    pub fn split_by_type(&mut self, t: &Type, target: &Type) -> (Type, Type) {
        let t = self.resolve(t);
        // `in Type` (or `Type[X]`): the class values, `Type[Object]` when
        // no argument is given.
        let target = &match target {
            Type::Class(id, args) if *id == self.world.builtin.class_ => Type::type_of(
                args.first()
                    .cloned()
                    .unwrap_or_else(|| Type::class(self.world.builtin.object)),
            ),
            t => t.clone(),
        };
        let open = match target {
            Type::Class(id, args)
                if args.is_empty() && !self.world.class(*id).type_params.is_empty() =>
            {
                Some(*id)
            }
            _ => None,
        };
        let mut yes = Vec::new();
        let mut no = Vec::new();
        for m in self.expand_members(&t) {
            let tgt = match open {
                Some(id) => self
                    .class_type_from(id, &m)
                    .or_else(|| self.guessed_args(id)),
                None => Some(target.clone()),
            };
            if let Type::Var(_) = m {
                // Not decided yet: a test narrows inside its branch
                // without deciding it (see `fit_narrowing`).
                yes.push(tgt.unwrap_or_else(|| m.clone()));
                no.push(m);
                continue;
            }
            let Some(tgt) = tgt else {
                // Arguments unknown: the member, unnarrowed, if it may be
                // one.
                let id = open.unwrap();
                let may = match &m {
                    Type::Class(mid, _) => {
                        self.world.class_is_a(id, *mid)
                            || self.world.class(id).kind == ClassKind::Module
                            || self.world.class(*mid).kind == ClassKind::Module
                    }
                    // A type parameter may be anything.
                    Type::Param(_) => true,
                    // A class value is a `Type`.
                    Type::ClassObject(..) | Type::TypeOf(_) => {
                        id == self.world.builtin.class_ || id == self.world.builtin.object
                    }
                    _ => false,
                };
                if may {
                    yes.push(m.clone());
                }
                no.push(m);
                continue;
            };
            if self.world.is_subtype(&m, &tgt) {
                yes.push(m);
            } else if let Type::Param(p) = m {
                // A type parameter may be anything: still a `T`, and a
                // `tgt` too.
                yes.push(self.world.narrowed_param(p, &tgt));
                no.push(m);
            } else if open.is_some()
                && matches!((&m, &tgt), (Type::Class(mid, _), Type::Class(tid, _))
                    if *mid != *tid && self.world.class_is_a(*tid, *mid)
                        && !self.world.is_subtype(&tgt, &m))
            {
                // A `Base[Int]` that may be a `Box` whose arguments it does
                // not give: unnarrowed.
                yes.push(m.clone());
                no.push(m);
            } else if self.world.is_subtype(&tgt, &m) {
                // `Object` narrowed to `Int`: the member is a supertype.
                yes.push(tgt);
                no.push(m);
            } else if matches!((&m, &tgt), (Type::Class(mid, margs), Type::Class(tid, _))
                if self.world.class_is_a(*tid, *mid)
                    && margs.iter().any(|a| a.mentions_any_param() || a.has_vars()))
            {
                // A `Box[T]` that may be an `IntBox < Box[Int]`: its
                // arguments are not known here (`T` may be `Int`), so the
                // test can succeed, the value then being a `tgt`.
                yes.push(tgt);
                no.push(m);
            } else if let (Type::Class(mid, _), Type::Class(tid, _)) = (&m, &tgt) {
                // Unrelated classes may still overlap via a module.
                if self.world.class(*tid).kind == ClassKind::Module
                    || self.world.class(*mid).kind == ClassKind::Module
                {
                    yes.push(tgt.clone());
                }
                no.push(m);
            } else {
                no.push(m);
            }
        }
        (Type::union_of(yes), Type::union_of(no))
    }

    /// Union members, with enums expanded to their variants.
    pub fn expand_members(&self, t: &Type) -> Vec<Type> {
        let mut out = Vec::new();
        for m in t.members() {
            match &m {
                Type::Class(id, args) if self.world.class(*id).kind == ClassKind::Enum => {
                    for v in &self.world.class(*id).variants {
                        out.push(Type::Class(*v, args.clone()));
                    }
                }
                _ => out.push(m),
            }
        }
        out
    }

    fn check_if(
        &mut self,
        cond: &Expr,
        then: &[Expr],
        els: Option<&[Expr]>,
        expected: Option<&Type>,
    ) -> Type {
        self.check_if_as(cond, then, els, expected, true)
    }

    /// `if`; without `used`, its value is discarded and the branches'
    /// types are not joined (nil, or Nothing when neither ends).
    fn check_if_as(
        &mut self,
        cond: &Expr,
        then: &[Expr],
        els: Option<&[Expr]>,
        expected: Option<&Type>,
        used: bool,
    ) -> Type {
        let (ct, facts_true, facts_false) = self.check_cond(cond);
        match self.is_truthy_type(&ct) {
            Some(true) => self.warning("condition is always true", cond.span),
            Some(false) => self.warning("condition is always false", cond.span),
            None => {}
        }
        let before = self.snapshot();
        self.apply_facts(&facts_true);
        // An unused `if`'s branches end in unused statements (an
        // `elsif` is the `if` ending the else branch).
        self.next_body_void = !used;
        let tt = self.check_body(then, expected);
        self.next_body_void = false;
        let then_snap = self.snapshot();
        let then_dead = tt.is_nothing();
        self.restore(&before);
        self.apply_facts(&facts_false);
        let et = match els {
            Some(els) => {
                self.next_body_void = !used;
                let t = self.check_body(els, expected);
                self.next_body_void = false;
                t
            }
            None => self.world.nil(),
        };
        let else_dead = et.is_nothing();
        self.merge_with(&then_snap, then_dead, else_dead);
        if !used {
            return if then_dead && else_dead {
                Type::Nothing
            } else {
                self.world.nil()
            };
        }
        self.join(&tt, &et)
    }

    fn check_case_when(
        &mut self,
        subject: Option<&Expr>,
        whens: &[When],
        els: Option<&[Expr]>,
        expected: Option<&Type>,
    ) -> Type {
        let subject_ty = subject.map(|s| self.check_expr(s, None));
        let key = subject.and_then(|s| self.var_key(s));
        let mut result = Type::Nothing;
        let before = self.snapshot();
        let mut branch_snaps: Vec<(Snapshot, bool)> = Vec::new();
        let mut remaining = subject_ty.clone().map(|t| self.resolve(&t));
        for w in whens {
            self.restore(&before);
            if let Some(rem) = &remaining {
                if let Some(k) = &key {
                    self.narrow_subject(k, Some(rem.clone()));
                }
            }
            let mut narrowed_to = Vec::new();
            for c in &w.conds {
                let Arg::Positional(ce) = c else {
                    self.error("unsupported `when` condition", c.span());
                    continue;
                };
                let ct = self.check_expr(ce, None);
                let ct = self.resolve(&ct);
                if let (Some(st), Type::ClassObject(cid, _)) = (&subject_ty, &ct) {
                    let target = Type::class(*cid);
                    let st = st.clone();
                    self.check_testable(&st, &target, "when", ce.span);
                    let (yes, no) = self.split_by_type(&st, &target);
                    narrowed_to.push(yes);
                    if let Some(rem) = &remaining {
                        let (_, rest) = self.split_by_type(rem, &target);
                        remaining = Some(rest);
                    }
                    let _ = no;
                } else if let Some(st) = &subject_ty {
                    // Value comparison with `===`.
                    narrowed_to.push(self.resolve(st));
                }
            }
            if let (Some(k), false) = (&key, narrowed_to.is_empty()) {
                let t = Type::union_of(narrowed_to);
                self.narrow_subject(k, Some(t));
            }
            let bt = self.check_body(&w.body, expected);
            branch_snaps.push((self.snapshot(), bt.is_nothing()));
            result = self.join(&result, &bt);
        }
        self.restore(&before);
        let et = match els {
            Some(els) => {
                if let (Some(k), Some(rem)) = (&key, &remaining) {
                    self.narrow_subject(k, Some(rem.clone()));
                }
                self.check_body(els, expected)
            }
            // Type tests that cover the whole subject make the `case`
            // exhaustive.
            None if remaining.as_ref().is_some_and(|r| r.is_nothing()) => Type::Nothing,
            None => self.world.nil(),
        };
        let mut dead = et.is_nothing();
        result = self.join(&result, &et);
        for (snap, d) in branch_snaps.iter().rev() {
            self.merge_with(snap, *d, dead);
            dead = dead && *d;
        }
        result
    }

    fn check_begin(&mut self, block: &BeginBlock, expected: Option<&Type>) -> Type {
        // A `break` through an `ensure` that assigns leaves with what it
        // assigns.
        let ensures = block.ensure.as_ref().is_some_and(|e| {
            let mut assigned = Assigned::default();
            Self::assigned_names(e, &mut assigned);
            !assigned.names.is_empty()
                || assigned
                    .bangs
                    .iter()
                    .any(|(name, method)| self.bang_may_assign(name, method))
        }) as u32;
        self.env.loop_exits.ensures += ensures;
        // A body a rescue retries runs again, as a loop's does.
        if block.rescues.iter().any(|r| Self::mentions_retry(&r.body)) {
            self.prescan_repeated(
                block
                    .body
                    .iter()
                    .chain(block.rescues.iter().flat_map(|r| r.body.iter())),
                false,
            );
        }
        let before = self.snapshot();
        let bt = self.check_body(&block.body, expected);
        let body_dead = bt.is_nothing();
        let after_body = self.snapshot();
        let mut result = bt;
        let mut snaps = Vec::new();
        for r in &block.rescues {
            self.restore(&before);
            // Variables assigned in the body may or may not have been.
            self.widen_assigned(&block.body);
            self.unset_since(&before);
            let mut exc_ty = Type::Nothing;
            let mut class_ids = Vec::new();
            if r.classes.is_empty() {
                exc_ty = Type::class(self.world.builtin.standard_error);
                class_ids.push(self.world.builtin.standard_error);
            }
            for c in &r.classes {
                let scope = self.env.scope.clone();
                match self.resolve_type_expr(c, &scope) {
                    Some(t @ Type::Class(id, _)) if self.world.is_exception_class(id) => {
                        exc_ty = self.join(&exc_ty, &t);
                        class_ids.push(id);
                    }
                    Some(_) => self.error("`rescue` needs exception classes", c.span),
                    None => {}
                }
            }
            self.out.rescue_classes.insert(r.span, class_ids);
            // The clause's variable is its own, as a block's parameter:
            // declared fresh with the clause's classes, shadowing an outer
            // local of the name, and gone after the clause (docs/01 §12).
            let own = r
                .var
                .as_ref()
                .map(|var| self.declare_var(var, exc_ty.clone(), r.span).slot as usize);
            self.env.in_rescue += 1;
            let rt = self.check_body(&r.body, expected);
            self.env.in_rescue -= 1;
            if let Some(slot) = own {
                // (Its slot stays, for the code that refers to it; its name
                // no longer finds it.)
                let frame = self.env.frames.last_mut().unwrap();
                let hidden = format!("{} (rescue clause)", frame.vars.list[slot].name);
                frame.vars.rename(slot, hidden);
            }
            snaps.push((self.snapshot(), rt.is_nothing()));
            result = self.join(&result, &rt);
        }
        self.restore(&after_body);
        if let Some(else_body) = &block.else_body {
            if !body_dead {
                let et = self.check_body(else_body, expected);
                result = self.join(&result, &et);
            }
        }
        let mut dead = result.is_nothing();
        for (snap, d) in snaps.iter().rev() {
            self.merge_with(snap, *d, dead);
            dead = dead && *d;
        }
        self.env.loop_exits.ensures -= ensures;
        if let Some(ensure) = &block.ensure {
            let saved = self.snapshot();
            // It also runs when the body or a `rescue` raised part way
            // through: it starts as the `begin` did, with what they may
            // have assigned widened and what they declare unset.
            self.restore(&before);
            self.widen_assigned(&block.body);
            for r in &block.rescues {
                self.widen_assigned_except(&r.body, r.var.as_deref());
            }
            if let Some(x) = &block.else_body {
                self.widen_assigned(x);
            }
            self.unset_since(&before);
            let outer = self.env.ensure_assigns.replace(HashMap::default());
            self.check_body(ensure, None);
            let assigned =
                std::mem::replace(&mut self.env.ensure_assigns, outer).unwrap_or_default();
            // After it, as on the normal path, joined with what it
            // assigns; what it declares, as at its end; the fields it
            // assigns, no longer narrowed.
            let end = self.snapshot();
            self.restore(&saved);
            self.keep_since(&saved, &end);
            let mut in_ensure = Assigned::default();
            Self::assigned_names(ensure, &mut in_ensure);
            self.widen_fields(&in_ensure);
            let n = self.env.frames.len();
            for (&(fi, slot), t) in &assigned {
                if fi >= n || slot >= self.env.frames[fi].vars.len() {
                    continue;
                }
                let v = &self.env.frames[fi].vars[slot];
                let cur = v.narrowed.clone().unwrap_or_else(|| v.declared.clone());
                let mut j = self.world.join(&self.infer.resolve(&cur), t);
                // Its type at the end of the `ensure` holds too (that
                // started wider): the narrower of the two.
                if let Some(at_end) = end.0.get(fi).and_then(|f| f.get(slot)) {
                    let at_end = at_end.cloned().unwrap_or_else(|| v.declared.clone());
                    let at_end = self.infer.resolve(&at_end);
                    if self.world.is_subtype(&at_end, &j) {
                        j = at_end;
                    }
                }
                let t = Self::fit_narrowing(
                    &self.world,
                    &self.infer,
                    &self.env.frames[fi].vars[slot].declared,
                    j,
                );
                self.env.frames[fi].vars.set_narrowed(slot, t);
            }
            if let Some(rec) = &mut self.env.ensure_assigns {
                for (k, t) in assigned {
                    let j = match rec.get(&k) {
                        Some(old) => self.world.join(old, &t),
                        None => t,
                    };
                    rec.insert(k, j);
                }
            }
        }
        result
    }

    // ----- assignment ---------------------------------------------------------------

    fn check_assign(
        &mut self,
        expr: &Expr,
        target: &LValue,
        value: &Expr,
        _expected: Option<&Type>,
    ) -> Type {
        match target {
            LValue::Local { name, span } => {
                if let Some((depth, slot)) = self.lookup_var(name) {
                    if self.captured_across_task(depth) {
                        self.error(
                            format!(
                                "cannot assign to `{name}` from {}; it is captured by value",
                                self.task_block_name()
                            ),
                            *span,
                        );
                    }
                    let declared = {
                        let n = self.env.frames.len();
                        self.env.frames[n - 1 - depth].vars[slot].declared.clone()
                    };
                    let vt = self.check_expr(value, Some(&declared));
                    if !self.coerce(&vt, &declared) {
                        self.error(
                            format!(
                                "cannot assign {} to `{name}` of type {}",
                                self.name(&vt),
                                self.name(&declared)
                            ),
                            value.span,
                        );
                    }
                    self.out.var_refs.insert(
                        *span,
                        VarRef {
                            depth: depth as u32,
                            slot: slot as u32,
                        },
                    );
                    let narrowed = self.resolve(&vt);
                    self.set_narrowed(&VarKey::Local(name.clone()), Some(narrowed));
                    vt
                } else {
                    let vt = self.check_expr(value, None);
                    let declared = self.resolve(&vt);
                    let declared = if declared.is_nothing() {
                        self.world.nil()
                    } else {
                        declared
                    };
                    // `x = [1, "a"]`: the literal is a tuple, but the
                    // variable is an array of the union, narrowed to the
                    // tuple. Uses that follow see the tuple; a later
                    // `x = x.push(2)` is allowed and narrows it again.
                    if let (Type::Tuple(ts), ExprKind::Array(_)) = (&declared, &value.kind) {
                        let elem = self.world.tuple_element(ts);
                        let tuple = declared.clone();
                        self.declare_var(name, self.world.array_of(elem), *span);
                        self.set_narrowed(&VarKey::Local(name.clone()), Some(tuple));
                        return vt;
                    }
                    self.declare_var(name, declared, *span);
                    vt
                }
            }
            LValue::IVar(name) => {
                if !self.check_ivar_access(expr.span) {
                    return self.check_expr(value, None);
                }
                let Some(cid) = self.env.class_id else {
                    self.error("instance variables are not available here", expr.span);
                    return self.check_expr(value, None);
                };
                let Some((field, subst)) = self.world.find_field(cid, name) else {
                    self.error(format!("undeclared field `@{name}`"), expr.span);
                    return self.check_expr(value, None);
                };
                if !field.mutable && (!self.env.in_initialize || self.in_late_closure()) {
                    self.error(
                        if self.env.in_initialize {
                            format!("field `@{name}` is immutable: a closure that may run later, after `initialize`, cannot assign it; declare it with `var`")
                        } else {
                            format!("field `@{name}` is immutable; declare it with `var` or assign it in `initialize`")
                        },
                        expr.span,
                    );
                }
                let fty = field.ty.subst(&subst);
                let vt = self.check_expr(value, Some(&fty));
                if !self.coerce(&vt, &fty) {
                    self.error(
                        format!(
                            "cannot assign {} to `@{name}` of type {}",
                            self.name(&vt),
                            self.name(&fty)
                        ),
                        value.span,
                    );
                }
                let index = self.world.field_index(cid, name).unwrap();
                self.out.ivar_fields.insert(expr.id, index);
                self.env.assigned_fields.insert(name.clone());
                if !field.mutable {
                    let narrowed = self.resolve(&vt);
                    self.env.ivar_narrow.insert(name.clone(), narrowed);
                }
                vt
            }
            LValue::Const(name) => {
                self.error(format!("cannot reassign constant `{name}`"), expr.span);
                self.check_expr(value, None)
            }
            LValue::Attr {
                recv,
                name,
                safe_nav,
            } => {
                let call = Call {
                    recv: Some(recv.clone()),
                    name: format!("{name}="),
                    args: vec![Arg::Positional(value.clone())],
                    block: None,
                    safe_nav: *safe_nav,
                    has_parens: true,
                    type_args: vec![],
                };
                self.check_call(expr, &call, None);
                self.out
                    .node_types
                    .get(&value.id)
                    .cloned()
                    .unwrap_or(Type::Nothing)
            }
            LValue::Index { recv, args } => {
                let mut all = args.clone();
                all.push(Arg::Positional(value.clone()));
                let call = Call {
                    recv: Some(recv.clone()),
                    name: "[]=".to_string(),
                    args: all,
                    block: None,
                    safe_nav: false,
                    has_parens: true,
                    type_args: vec![],
                };
                self.check_call(expr, &call, None);
                self.out
                    .node_types
                    .get(&value.id)
                    .cloned()
                    .unwrap_or(Type::Nothing)
            }
        }
    }

    fn check_op_assign(
        &mut self,
        expr: &Expr,
        target: &LValue,
        op: OpAssign,
        value: &Expr,
    ) -> Type {
        // Type the current value of the target.
        let current = match target {
            LValue::Local { name, span } => match self.lookup_var(name) {
                Some((depth, slot)) => {
                    if self.captured_across_task(depth) {
                        self.error(
                            format!(
                                "cannot assign to `{name}` from {}; it is captured by value",
                                self.task_block_name()
                            ),
                            *span,
                        );
                    }
                    self.out.var_refs.insert(
                        *span,
                        VarRef {
                            depth: depth as u32,
                            slot: slot as u32,
                        },
                    );
                    self.var_type(depth, slot)
                }
                None => {
                    self.error(format!("undefined local variable `{name}`"), expr.span);
                    return Type::Nothing;
                }
            },
            LValue::IVar(name) => {
                let read = Expr {
                    id: expr.id,
                    span: expr.span,
                    kind: ExprKind::IVar(name.clone()),
                };
                let t = self.check_ivar_read(&read, name);
                if let Some(cid) = self.env.class_id {
                    if let Some((f, _)) = self.world.find_field(cid, name) {
                        if !f.mutable && (!self.env.in_initialize || self.in_late_closure()) {
                            self.error(format!("field `@{name}` is immutable"), expr.span);
                        }
                    }
                }
                t
            }
            LValue::Attr { recv, name, .. } => {
                let rt = self.check_expr(recv, None);
                let getter = Call {
                    recv: Some(recv.clone()),
                    name: name.clone(),
                    args: vec![],
                    block: None,
                    safe_nav: false,
                    has_parens: false,
                    type_args: vec![],
                };
                let _ = rt;
                let saved = self.take_union_record(expr.id);
                let t = self.check_call_with_types(expr, &getter, None, true);
                self.note_op_getter(expr.id, expr.span);
                self.restore_union_record(expr.id, saved);
                t
            }
            LValue::Index { recv, args } => {
                let getter = Call {
                    recv: Some(recv.clone()),
                    name: "[]".to_string(),
                    args: args.clone(),
                    block: None,
                    safe_nav: false,
                    has_parens: true,
                    type_args: vec![],
                };
                let saved = self.take_union_record(expr.id);
                let t = self.check_call_with_types(expr, &getter, None, true);
                self.note_op_getter(expr.id, expr.span);
                self.restore_union_record(expr.id, saved);
                t
            }
            LValue::Const(name) => {
                self.error(format!("cannot reassign constant `{name}`"), expr.span);
                return Type::Nothing;
            }
        };
        let current = self.resolve(&current);
        let result = match op {
            OpAssign::OrOr | OpAssign::AndAnd
                if self.has_logical_method(&current, op.as_str().trim_end_matches('=')) =>
            {
                // `x ||= v` is `x = x.||() { v }`: stored whatever it gives.
                let name = op.as_str().trim_end_matches('=');
                self.logical_method(expr, name, &current, value, None)
                    .unwrap_or(Type::Nothing)
            }
            OpAssign::OrOr => {
                // `x ||= v`: v is evaluated only when x is falsy.
                let vt = self.check_expr(value, Some(&current));
                let truthy = self.truthy_part(&current);
                self.join(&truthy, &vt)
            }
            OpAssign::AndAnd => {
                let vt = self.check_expr(value, Some(&current));
                let falsy = self.falsy_part(&current);
                self.join(&falsy, &vt)
            }
            _ => {
                let name = op.as_str().trim_end_matches('=').to_string();
                let vt = self.check_expr(value, None);
                self.out.calls.remove(&expr.id);
                let t = self.check_operator_call(expr, &current, &name, &vt, value);
                let found = match self.out.calls.get(&expr.id) {
                    Some(CallTarget::Method { method }) => Some(*method),
                    _ => None,
                };
                self.note_op_method(expr.id, true, found, expr.span);
                // A variable's operator in a block checked once per type: by
                // the type each check saw (the node's table is free, which
                // an attribute's or an index's writer takes).
                if let (Some(m), LValue::Local { .. } | LValue::IVar(_)) = (found, target) {
                    let ct = self.resolve(&current);
                    if !self.env.blocks.is_empty() && self.test_class(&ct).is_some() {
                        self.note_union_table(expr.id, vec![(ct, m)], expr.span);
                    }
                }
                t
            }
        };
        // Assign back.
        match target {
            LValue::Local { name, .. } => {
                let (depth, slot) = self.lookup_var(name).unwrap();
                let declared = {
                    let n = self.env.frames.len();
                    self.env.frames[n - 1 - depth].vars[slot].declared.clone()
                };
                if !self.coerce(&result, &declared) {
                    self.error(
                        format!(
                            "cannot assign {} to `{name}` of type {}",
                            self.name(&result),
                            self.name(&declared)
                        ),
                        expr.span,
                    );
                }
                let narrowed = self.resolve(&result);
                self.set_narrowed(&VarKey::Local(name.clone()), Some(narrowed));
            }
            LValue::IVar(name) => {
                if let Some(cid) = self.env.class_id {
                    if let Some((f, subst)) = self.world.find_field(cid, name) {
                        let fty = f.ty.subst(&subst);
                        if !self.coerce(&result, &fty) {
                            self.error(
                                format!(
                                    "cannot assign {} to `@{name}` of type {}",
                                    self.name(&result),
                                    self.name(&fty)
                                ),
                                expr.span,
                            );
                        }
                        self.env.assigned_fields.insert(name.clone());
                    }
                }
            }
            LValue::Attr { recv, name, .. } => {
                // Check that the setter accepts the result type.
                let rt = self.resolve(&self.out.node_types[&recv.id]);
                let setter = format!("{name}=");
                let cands = self.world.lookup_methods(&rt, &setter);
                if cands.is_empty() {
                    self.error(
                        format!("undefined method `{setter}` for {}", self.name(&rt)),
                        expr.span,
                    );
                } else {
                    self.out
                        .calls
                        .insert(expr.id, CallTarget::Method { method: cands[0].0 });
                    if !self.env.blocks.is_empty() && self.test_class(&rt).is_some() {
                        self.note_union_table(expr.id, vec![(rt.clone(), cands[0].0)], expr.span);
                    }
                }
            }
            LValue::Index { recv, .. } => {
                let rt = self.resolve(&self.out.node_types[&recv.id]);
                let cands = self.world.lookup_methods(&rt, "[]=");
                if cands.is_empty() {
                    let hint = self.immutable_hint(&rt, "[]=", Some(recv));
                    self.error(
                        format!("undefined method `[]=` for {}{hint}", self.name(&rt)),
                        expr.span,
                    );
                } else {
                    self.out
                        .calls
                        .insert(expr.id, CallTarget::Method { method: cands[0].0 });
                    if !self.env.blocks.is_empty() && self.test_class(&rt).is_some() {
                        self.note_union_table(expr.id, vec![(rt.clone(), cands[0].0)], expr.span);
                    }
                }
            }
            LValue::Const(_) => {}
        }
        result
    }

    /// Type of `lhs <op> rhs` given the operand types (for compound
    /// assignment).
    fn check_operator_call(
        &mut self,
        expr: &Expr,
        lhs: &Type,
        name: &str,
        rhs: &Type,
        rhs_expr: &Expr,
    ) -> Type {
        // `y += 1` on `?v | Int` is a use as an `Int`.
        let lhs = self.settle_vars(lhs);
        let cands = self.world.lookup_methods(&lhs, name);
        for (mid, subst) in cands {
            let m = self.world.method(mid).clone();
            let positional: Vec<&ParamInfo> = m
                .params
                .iter()
                .filter(|p| p.kind == ParamKind::Positional)
                .collect();
            if positional.len() != 1 || m.block.is_some() {
                continue;
            }
            let mut subst = subst;
            subst.insert(SELF_PARAM, lhs.clone());
            let pt = positional[0].ty.subst(&subst);
            let saved = self.infer.save();
            if self.coerce(rhs, &pt) {
                self.out
                    .calls
                    .insert(expr.id, CallTarget::Method { method: mid });
                self.note_static_call(expr, mid);
                return self.world.unvoid(&self.method_ret(mid).subst(&subst));
            }
            self.infer.restore(saved);
        }
        self.error(
            format!(
                "no method `{name}` on {} accepting {}",
                self.name(&lhs),
                self.name(rhs)
            ),
            rhs_expr.span,
        );
        Type::Nothing
    }

    fn check_multi_assign(&mut self, expr: &Expr, targets: &[MultiTarget], value: &Expr) -> Type {
        let vt = self.check_expr(value, None);
        let vt = self.resolve(&vt);
        self.assign_multi(targets, &vt, expr.span);
        vt
    }

    fn assign_multi(&mut self, targets: &[MultiTarget], vt: &Type, span: Span) {
        let splat_index = targets
            .iter()
            .position(|t| matches!(t, MultiTarget::Splat(_)));
        let elem_types: Vec<Type> = match vt {
            Type::Tuple(ts) => ts.clone(),
            Type::Class(id, args) if *id == self.world.builtin.array && args.len() == 1 => {
                vec![args[0].clone(); targets.len()]
            }
            _ => {
                self.error(
                    format!(
                        "cannot destructure {} (expected a tuple or array)",
                        self.name(vt)
                    ),
                    span,
                );
                vec![Type::Nothing; targets.len()]
            }
        };
        let array_elem = match vt {
            Type::Tuple(ts) => self.world.tuple_element(ts),
            Type::Class(_, args) if !args.is_empty() => args[0].clone(),
            _ => Type::Nothing,
        };
        let n_before = splat_index.unwrap_or(targets.len());
        let n_after = splat_index.map(|i| targets.len() - i - 1).unwrap_or(0);
        for (i, t) in targets.iter().enumerate() {
            let ty = if let Some(si) = splat_index {
                if i < si {
                    elem_types
                        .get(i)
                        .cloned()
                        .unwrap_or_else(|| self.world.nil())
                } else if i == si {
                    self.world.array_of(array_elem.clone())
                } else {
                    let from_end = targets.len() - i;
                    if elem_types.len() >= from_end + n_before {
                        elem_types[elem_types.len() - from_end].clone()
                    } else {
                        array_elem.clone()
                    }
                }
            } else {
                match vt {
                    Type::Tuple(ts) if i >= ts.len() => self.world.nil(),
                    _ => elem_types
                        .get(i)
                        .cloned()
                        .unwrap_or_else(|| self.world.nil()),
                }
            };
            let _ = n_after;
            match t {
                MultiTarget::Single(lv) | MultiTarget::Splat(Some(lv)) => {
                    self.assign_lvalue(lv, &ty, span)
                }
                MultiTarget::Splat(None) => {}
                MultiTarget::Nested(ts) => {
                    let rty = self.resolve(&ty);
                    self.assign_multi(ts, &rty, span);
                }
            }
        }
    }

    fn assign_lvalue(&mut self, lv: &LValue, ty: &Type, span: Span) {
        match lv {
            LValue::Local { name, span: vspan } => {
                if let Some((depth, slot)) = self.lookup_var(name) {
                    let declared = {
                        let n = self.env.frames.len();
                        self.env.frames[n - 1 - depth].vars[slot].declared.clone()
                    };
                    if !self.coerce(ty, &declared) {
                        self.error(
                            format!(
                                "cannot assign {} to `{name}` of type {}",
                                self.name(ty),
                                self.name(&declared)
                            ),
                            *vspan,
                        );
                    }
                    self.out.var_refs.insert(
                        *vspan,
                        VarRef {
                            depth: depth as u32,
                            slot: slot as u32,
                        },
                    );
                    let narrowed = self.resolve(ty);
                    self.set_narrowed(&VarKey::Local(name.clone()), Some(narrowed));
                } else {
                    let declared = self.resolve(ty);
                    self.declare_var(name, declared, *vspan);
                }
            }
            LValue::IVar(name) => {
                if !self.check_ivar_access(span) {
                    return;
                }
                let Some(cid) = self.env.class_id else {
                    self.error("instance variables are not available here", span);
                    return;
                };
                match self.world.find_field(cid, name) {
                    Some((f, subst)) => {
                        let fty = f.ty.subst(&subst);
                        if !f.mutable && (!self.env.in_initialize || self.in_late_closure()) {
                            self.error(format!("field `@{name}` is immutable"), span);
                        }
                        if !self.coerce(ty, &fty) {
                            self.error(
                                format!(
                                    "cannot assign {} to `@{name}` of type {}",
                                    self.name(ty),
                                    self.name(&fty)
                                ),
                                span,
                            );
                        }
                        self.env.assigned_fields.insert(name.clone());
                    }
                    None => self.error(format!("undeclared field `@{name}`"), span),
                }
            }
            _ => self.error("unsupported target in multiple assignment", span),
        }
    }

    // ----- calls -------------------------------------------------------------------

    /// `x.dup` of a class whose instances run `deinitialize`: what they
    /// own would be released twice (a subclass's is refused at run time).
    fn check_dup(&mut self, expr: &Expr, call: &Call) {
        let Some(CallTarget::Method { method }) = self.out.calls.get(&expr.id) else {
            return;
        };
        let m = self.world.method(*method);
        if m.name != "dup" || m.file != 0 || m.owner != self.world.builtin.object {
            return;
        }
        let rt = match &call.recv {
            Some(recv) => match self.out.node_types.get(&recv.id) {
                Some(rt) => self.infer.resolve(rt),
                None => return,
            },
            // An implicit `self`: the method's class (or a subclass).
            None => self.env.self_type.clone(),
        };
        let rt = rt.without_nil(self.world.builtin.nil);
        let Type::Class(cid, _) = rt else {
            return;
        };
        if self.world.deinitializer(cid).is_some() {
            let name = self.world.class(cid).name.clone();
            self.error(
                format!("cannot dup {name}: its class defines `deinitialize`, which would run for the copy too"),
                expr.span,
            );
        }
    }

    fn check_call(&mut self, expr: &Expr, call: &Call, expected: Option<&Type>) -> Type {
        self.check_call_with_types(expr, call, expected, false)
    }

    /// `quiet`: used when re-typing a getter for compound assignment (the
    /// receiver was already checked).
    fn check_call_with_types(
        &mut self,
        expr: &Expr,
        call: &Call,
        expected: Option<&Type>,
        _quiet: bool,
    ) -> Type {
        // Special forms.
        if call.recv.is_none() && call.name == "raise" {
            return self.check_raise(expr, call);
        }
        if let Some(recv) = &call.recv {
            match call.name.as_str() {
                // `x.is_a?(klass)` with a class value (not a type written as
                // a constant) is the method `Object#is_a?(klass: Class)`,
                // which tests at run time and narrows nothing.
                "is_a?"
                    if call.args.len() == 1
                        && call.block.is_none()
                        && matches!(&call.args[0], Arg::Positional(a)
                            if !matches!(a.kind, ExprKind::Const(_) | ExprKind::TypeApp(_))) => {}
                "is_a?" | "as" | "as?" if call.args.len() == 1 && call.block.is_none() => {
                    return self.check_type_test(expr, call, recv);
                }
                "respond_to?" if call.args.len() == 1 => {
                    let rt = self.check_expr(recv, None);
                    let rt = self.resolve(&rt);
                    let Arg::Positional(a) = &call.args[0] else {
                        self.error("respond_to? takes a symbol", expr.span);
                        return self.world.bool_();
                    };
                    let answer = match &a.kind {
                        ExprKind::Symbol(name) => !self.world.lookup_methods(&rt, name).is_empty(),
                        _ => {
                            self.error("respond_to? takes a symbol literal", a.span);
                            false
                        }
                    };
                    self.check_expr(a, None);
                    self.out.calls.insert(expr.id, CallTarget::Constant(answer));
                    return self.world.bool_();
                }
                _ => {}
            }
        }

        // `[a, b] <=> [c, d]` / `[a, b] == [c, d]`: compare element-wise as
        // tuples, so that each element only needs to be comparable with its
        // counterpart.
        if let (Some(recv), "<=>" | "==" | "!=", [Arg::Positional(arg)]) =
            (&call.recv, call.name.as_str(), call.args.as_slice())
        {
            if let (ExprKind::Array(xs), ExprKind::Array(ys)) = (&recv.kind, &arg.kind) {
                if xs.len() == ys.len() && call.block.is_none() {
                    return self.check_tuple_compare(expr, call, recv, xs, arg, ys);
                }
            }
        }

        // Receiver.
        let (recv_ty, implicit_self) = match &call.recv {
            Some(r) => {
                let t = self.check_expr(r, None);
                (self.resolve(&t), matches!(r.kind, ExprKind::SelfRef))
            }
            None => (self.env.self_type.clone(), true),
        };
        // `Array.build { }`: a generic class used without arguments gets
        // fresh inference variables for its parameters.
        let recv_ty = match recv_ty {
            Type::ClassObject(cid, args)
                if args.is_empty() && !self.world.class(cid).type_params.is_empty() =>
            {
                let n = self.world.class(cid).type_params.len();
                let fresh: Vec<Type> = (0..n).map(|_| self.infer.fresh()).collect();
                Type::ClassObject(cid, fresh)
            }
            t => t,
        };
        if recv_ty.is_nothing() {
            // Error already reported, or unreachable code.
            self.check_args_blindly(call);
            return Type::Nothing;
        }
        if let (Type::Tuple(lhs), "<=>" | "<" | "<=" | ">" | ">=", [Arg::Positional(arg)], None) = (
            &recv_ty,
            call.name.as_str(),
            call.args.as_slice(),
            &call.block,
        ) {
            return self.check_tuple_order(expr, call, lhs.clone(), arg);
        }

        // Safe navigation: `nil` passes through.
        let (recv_ty, nil_passthrough) = if call.safe_nav {
            let without = recv_ty.without_nil(self.world.builtin.nil);
            let had_nil = without != recv_ty;
            if !had_nil {
                self.warning("`&.` on a receiver that is never nil", expr.span);
            }
            if without.is_nothing() {
                // Always nil: the call never happens.
                self.check_args_blindly(call);
                return self.world.nil();
            }
            (without, had_nil)
        } else {
            (recv_ty, false)
        };

        let result = self.check_call_on(expr, call, &recv_ty, implicit_self, expected);
        // In a block, checked again for each type of what it is given: a
        // call may resolve differently each time (`union_calls`).
        let rt = self.resolve(&recv_ty);
        if !self.env.blocks.is_empty() && self.test_class(&rt).is_some() {
            if let (Some(CallTarget::Method { method }), false) = (
                self.out.calls.get(&expr.id),
                self.out.dynamic_calls.contains(&expr.id),
            ) {
                let m = *method;
                self.note_union_table(expr.id, vec![(rt, m)], expr.span);
            }
        }
        if nil_passthrough {
            let nil = self.world.nil();
            self.join(&result, &nil)
        } else {
            result
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn check_tuple_compare(
        &mut self,
        expr: &Expr,
        call: &Call,
        recv: &Expr,
        xs: &[Arg],
        arg: &Expr,
        ys: &[Arg],
    ) -> Type {
        let mut lhs = Vec::new();
        for x in xs {
            let Arg::Positional(e) = x else {
                self.error("unexpected argument form", x.span());
                return Type::Nothing;
            };
            let t = self.check_expr(e, None);
            lhs.push(self.resolve(&t));
        }
        let mut rhs = Vec::new();
        for (y, lt) in ys.iter().zip(lhs.iter()) {
            let Arg::Positional(e) = y else {
                self.error("unexpected argument form", y.span());
                return Type::Nothing;
            };
            let t = self.check_expr(e, Some(lt));
            rhs.push(self.resolve(&t));
        }
        self.record(recv.id, &Type::Tuple(lhs.clone()));
        self.record(arg.id, &Type::Tuple(rhs.clone()));
        let op = if call.name == "<=>" { "<=>" } else { "==" };
        let spans: Vec<Span> = xs.iter().map(|x| x.span()).collect();
        self.check_elementwise(op, &lhs, &rhs, &spans);
        // The runtime compares arrays element-wise.
        let arr = self.world.array_of(self.world.object());
        if let Some((mid, _)) = self.world.lookup_methods(&arr, &call.name).first() {
            self.out
                .calls
                .insert(expr.id, CallTarget::Method { method: *mid });
        }
        if op == "<=>" {
            self.world.int()
        } else {
            self.world.bool_()
        }
    }

    /// `t < u` for tuples `t` and `u` of one length: each element of `t`
    /// must compare (`<=>`) with the one of `u` at its position. Arrays of
    /// one comparable element type are `Comparable` through the prelude;
    /// a tuple's elements may differ in type, so it is checked here.
    fn check_tuple_order(&mut self, expr: &Expr, call: &Call, lhs: Vec<Type>, arg: &Expr) -> Type {
        let at = self.check_expr(arg, Some(&Type::Tuple(lhs.clone())));
        let at = self.resolve(&at);
        match &at {
            Type::Tuple(rhs) if rhs.len() == lhs.len() => {
                let rhs = rhs.clone();
                self.check_elementwise("<=>", &lhs, &rhs, &vec![arg.span; lhs.len()]);
            }
            _ => self.error(
                format!(
                    "cannot compare {} with {} using `{}`",
                    self.name(&Type::Tuple(lhs.clone())),
                    self.name(&at),
                    call.name
                ),
                arg.span,
            ),
        }
        // At run time a tuple is an array, compared element by element by
        // the method of `Comparable[Array[T]]` (any comparable `T`).
        let arr = self.world.array_of(self.world.int());
        if let Some((mid, _)) = self.world.lookup_methods(&arr, &call.name).first() {
            self.out
                .calls
                .insert(expr.id, CallTarget::Method { method: *mid });
        }
        if call.name == "<=>" {
            self.world.int()
        } else {
            self.world.bool_()
        }
    }

    fn check_elementwise(&mut self, op: &str, lhs: &[Type], rhs: &[Type], spans: &[Span]) {
        for ((lt, rt), span) in lhs.iter().zip(rhs.iter()).zip(spans.iter()) {
            let cands = self.world.lookup_methods(lt, op);
            let mut ok = false;
            for (mid, subst) in cands {
                let m = self.world.method(mid).clone();
                let positional: Vec<&ParamInfo> = m
                    .params
                    .iter()
                    .filter(|p| p.kind == ParamKind::Positional)
                    .collect();
                if positional.len() != 1 {
                    continue;
                }
                let mut subst = subst;
                subst.insert(SELF_PARAM, lt.clone());
                let pt = positional[0].ty.subst(&subst);
                let saved = self.infer.save();
                if self.coerce(rt, &pt) {
                    ok = true;
                    break;
                }
                self.infer.restore(saved);
            }
            if !ok {
                self.error(
                    format!(
                        "cannot compare {} with {} using `{op}`",
                        self.name(lt),
                        self.name(rt)
                    ),
                    *span,
                );
            }
        }
    }

    fn check_args_blindly(&mut self, call: &Call) {
        for a in &call.args {
            match a {
                Arg::Positional(e) | Arg::Splat(e) | Arg::DoubleSplat(e) | Arg::BlockPass(e) => {
                    self.check_expr(e, None);
                }
                Arg::Keyword { value, .. } => {
                    self.check_expr(value, None);
                }
            }
        }
    }

    /// A method named `name` declared by a common ancestor of every
    /// member class that none of `resolved` (the methods the members
    /// resolved to) belongs to: it is overridden by them, so a call
    /// recorded against it is dispatched on the receiver's class.
    fn common_ancestor_method(
        &self,
        members: &[Type],
        name: &str,
        resolved: &[Option<MethodId>],
    ) -> Option<MethodId> {
        let ids: Vec<ClassId> = members
            .iter()
            .map(|m| match self.resolve(m) {
                Type::Class(id, _) => Some(id),
                _ => None,
            })
            .collect::<Option<Vec<_>>>()?;
        let owners: Vec<ClassId> = resolved
            .iter()
            .flatten()
            .map(|m| self.world.method(*m).owner)
            .collect();
        let chains: Vec<Vec<ClassId>> = ids
            .iter()
            .map(|id| {
                self.world
                    .ancestors(*id, &[])
                    .into_iter()
                    .map(|(a, _)| a)
                    .collect()
            })
            .collect();
        for anc in &chains[0] {
            if !chains.iter().all(|c| c.contains(anc)) || owners.contains(anc) {
                continue;
            }
            if let Some(ms) = self.world.class(*anc).methods.get(name) {
                if let Some(m) = ms.first() {
                    return Some(*m);
                }
            }
        }
        None
    }

    fn check_call_on(
        &mut self,
        expr: &Expr,
        call: &Call,
        recv_ty: &Type,
        implicit_self: bool,
        expected: Option<&Type>,
    ) -> Type {
        let name = call.name.as_str();
        // `new` on a `Meta::ClassDef[C]` (a `static` class method's `self`,
        // docs/14) constructs `C`, as on the class.
        if name == "new" {
            if let Some(instance) = self.world.class_object_instance(recv_ty) {
                let class_object = Type::type_of(instance);
                return self.check_call_on(expr, call, &class_object, implicit_self, expected);
            }
        }
        // A method every object has (`to_s`, `nil?`, `==`) is called on a
        // value of a type not decided yet as on an Object, deciding
        // nothing. Another one, on `?v | T`, is a use as a `T`: it decides
        // `?v` as `T` (`(xs[0] || 0) + 1`).
        let as_object;
        let undecided = recv_ty.members().iter().any(|m| matches!(m, Type::Var(_)));
        let on_object = !self
            .world
            .lookup_methods(&self.world.object(), name)
            .is_empty();
        let settled;
        let recv_ty = if undecided && !on_object {
            settled = self.settle_vars(recv_ty);
            &settled
        } else {
            recv_ty
        };
        let recv_ty = if undecided && on_object {
            let object = self.world.object();
            as_object = Type::union_of(
                recv_ty
                    .members()
                    .into_iter()
                    .map(|m| {
                        if matches!(m, Type::Var(_)) {
                            object.clone()
                        } else {
                            m
                        }
                    })
                    .collect(),
            );
            &as_object
        } else {
            recv_ty
        };
        match recv_ty {
            Type::Union(members) => {
                // Each member must accept the call; the result is the join.
                let members = members.clone();
                let mut result = Type::Nothing;
                let mut targets: Vec<Option<MethodId>> = Vec::new();
                // `x.foo!` as `x = x.foo`: each member is checked with `x`
                // as it was, and `x` then holds any member's result.
                let bang = self.union_bang_place(call, &members, expr.span);
                let bang_saved = bang.as_ref().map(|k| self.narrowing_of(k));
                // The arguments are checked once per member, but a literal
                // has one representation: an integer literal the members
                // disagree on (`Float` for one, `Int` for another, as in
                // `x + 1` with `x: Int | Float`) is kept `Int`, and the
                // members are checked again under that.
                let saved_floats = std::mem::take(&mut self.out.float_literals);
                let ndiag = self.diagnostics.len();
                let ndiag_tables = self.table_mark();
                let mut per_member = Vec::new();
                for m in &members {
                    if let (Some(k), Some(saved)) = (&bang, &bang_saved) {
                        self.narrow_subject(k, saved.clone());
                    }
                    let t = self.check_call_on(expr, call, m, implicit_self, expected);
                    targets.push(match self.out.calls.get(&expr.id) {
                        Some(CallTarget::Method { method }) => Some(*method),
                        _ => None,
                    });
                    result = self.join(&result, &t);
                    per_member.push(std::mem::take(&mut self.out.float_literals));
                }
                let agreed = per_member.windows(2).all(|w| w[0] == w[1]);
                self.out.float_literals = saved_floats;
                if agreed {
                    if let Some(floats) = per_member.pop() {
                        self.out.float_literals.extend(floats);
                    }
                } else {
                    let all: rustc_hash::FxHashSet<NodeId> =
                        per_member.iter().flatten().copied().collect();
                    let added: Vec<NodeId> = all
                        .into_iter()
                        .filter(|id| self.int_literals.insert(*id))
                        .collect();
                    self.truncate_diagnostics(ndiag);
                    self.discard_tables(ndiag_tables);
                    result = Type::Nothing;
                    targets.clear();
                    for m in &members {
                        if let (Some(k), Some(saved)) = (&bang, &bang_saved) {
                            self.narrow_subject(k, saved.clone());
                        }
                        let t = self.check_call_on(expr, call, m, implicit_self, expected);
                        targets.push(match self.out.calls.get(&expr.id) {
                            Some(CallTarget::Method { method }) => Some(*method),
                            _ => None,
                        });
                        result = self.join(&result, &t);
                    }
                    for id in added {
                        self.int_literals.remove(&id);
                    }
                }
                if let Some(k) = &bang {
                    if self.out.bang_assign.contains(&expr.id) {
                        let t = self.resolve(&result);
                        self.set_narrowed(k, Some(t));
                    }
                }
                // The recorded target is the last member's; when the
                // members resolve to different methods, record one that
                // is dispatched on the receiver's class instead, and each
                // member's own for lowering to call.
                if let Some(first) = targets.first().copied().flatten() {
                    let differ = targets.iter().any(|t| *t != Some(first));
                    // (In a block, also when they agree: another check of
                    // it may find another method.)
                    if targets.iter().all(|t| t.is_some()) && !differ && !self.env.blocks.is_empty()
                    {
                        let table: Vec<(Type, MethodId)> = members
                            .iter()
                            .map(|m| self.resolve(m))
                            .zip(targets.iter().flatten().copied())
                            .collect();
                        self.note_union_table(expr.id, table, expr.span);
                    }
                    if targets.iter().all(|t| t.is_some()) && differ {
                        let table: Vec<(Type, MethodId)> = members
                            .iter()
                            .map(|m| self.resolve(m))
                            .zip(targets.iter().flatten().copied())
                            .collect();
                        self.note_union_table(expr.id, table, expr.span);
                        match self.common_ancestor_method(&members, name, &targets) {
                            Some(method) => {
                                self.out
                                    .calls
                                    .insert(expr.id, CallTarget::Method { method });
                            }
                            None => {
                                self.out.dynamic_calls.insert(expr.id);
                            }
                        }
                    }
                }
                result
            }
            Type::Var(_) => {
                self.error(
                    format!("cannot call `{name}` on a value whose type is not yet known; add a type annotation"),
                    expr.span,
                );
                self.check_args_blindly(call);
                Type::Nothing
            }
            Type::Proc(Some(_), ..) if name == "call" || name == "[]" => {
                self.error(
                    "a block with a receiver is run with `recv.instance_exec(&block)`",
                    expr.span,
                );
                self.check_args_blindly(call);
                Type::Nothing
            }
            // `f.call(x)`, `f.(x)` and `f[x]` all call the procedure.
            Type::Proc(None, params, ret, _) if name == "call" || name == "[]" => {
                let params = params.clone();
                let ret = self.world.unvoid(ret);
                let positional: Vec<&Expr> = call
                    .args
                    .iter()
                    .filter_map(|a| match a {
                        Arg::Positional(e) => Some(e),
                        _ => None,
                    })
                    .collect();
                if positional.len() != params.len() || positional.len() != call.args.len() {
                    self.error(
                        format!(
                            "procedure takes {} argument(s), {} given",
                            params.len(),
                            call.args.len()
                        ),
                        expr.span,
                    );
                    self.check_args_blindly(call);
                    return ret;
                }
                for (e, p) in positional.iter().zip(params.iter()) {
                    let t = self.check_expr(e, Some(p));
                    if !self.coerce(&t, p) {
                        self.error(
                            format!("expected {} but found {}", self.name(p), self.name(&t)),
                            e.span,
                        );
                    }
                }
                if call.block.is_some() {
                    self.error("a procedure call does not take a block", expr.span);
                }
                self.out.calls.insert(expr.id, CallTarget::ProcCall);
                ret
            }
            Type::Tuple(ts) if name == "[]" && call.args.len() == 1 && call.block.is_none() => {
                let ts = ts.clone();
                if let Arg::Positional(Expr {
                    kind: ExprKind::Int(lit),
                    ..
                }) = &call.args[0]
                {
                    if let Ok(i) = lit.digits.parse::<usize>() {
                        if let Some(t) = ts.get(i) {
                            self.check_args_blindly(call);
                            let elem = Type::union_of(ts.clone());
                            let arr = self.world.array_of(elem);
                            let cands = self.world.lookup_methods(&arr, "[]");
                            if let Some((mid, _)) = cands.first() {
                                self.out
                                    .calls
                                    .insert(expr.id, CallTarget::Method { method: *mid });
                            }
                            return t.clone();
                        }
                        self.error(
                            format!("tuple index {i} out of range for {}", self.name(recv_ty)),
                            expr.span,
                        );
                        return Type::Nothing;
                    }
                }
                let elem = Type::union_of(ts);
                let arr = self.world.array_of(elem);
                self.check_call_on(expr, call, &arr, implicit_self, expected)
            }
            Type::TypeOf(t) if name == "new" => {
                self.error(
                    format!(
                        "cannot construct a `{}`: what `initialize` takes depends on the class",
                        self.name(&Type::TypeOf(t.clone()))
                    ),
                    expr.span,
                );
                self.check_args_blindly(call);
                Type::Nothing
            }
            Type::ClassObject(cid, args) if name == "new" => {
                let cid = *cid;
                let args = args.clone();
                // `new` constructs the class that is written (`Point.new`,
                // `Array[Int].new`) or the one a class method was called
                // on (`new` in `def self.build`): a `Type[Point]` held in
                // a variable may be a subclass whose `initialize` takes
                // other arguments.
                let written = match &call.recv {
                    None => true,
                    Some(r) => {
                        matches!(r.kind, ExprKind::SelfRef)
                            || match self.out.const_targets.get(&r.id) {
                                Some(ConstTarget::Class(_)) => true,
                                // A constant that is an alias of a class
                                // (`P = Geometry::Point`, docs/01 §8).
                                Some(ConstTarget::Const(c)) => matches!(
                                    self.world.through_alias(Member::Const(*c)),
                                    Member::Class(_)
                                ),
                                _ => false,
                            }
                    }
                };
                if !written {
                    let hint = if cid == self.world.builtin.object {
                        String::new()
                    } else {
                        format!(" (`{}.new`)", self.world.class(cid).name)
                    };
                    self.error(
                        format!(
                            "cannot call `new` on a `{}` value: `new` constructs the class that is written{hint} or the receiver of a class method; the value may be a subclass whose `initialize` takes other arguments",
                            self.name(recv_ty)
                        ),
                        expr.span,
                    );
                    self.check_args_blindly(call);
                    return Type::Nothing;
                }
                // Prelude singletons named `new` take precedence.
                let cands = self.world.lookup_methods(recv_ty, "new");
                let own: Vec<_> = cands
                    .into_iter()
                    .filter(|(m, _)| self.world.method(*m).singleton)
                    .collect();
                if !own.is_empty() {
                    let t =
                        self.resolve_overloads(expr, call, recv_ty, own, implicit_self, expected);
                    self.check_class_bounds(&t, expr.span);
                    return t;
                }
                let t = self.check_constructor(expr, call, cid, &args, expected);
                // `def self.build = new`: the instance is of the class the
                // method is called on (a subclass, perhaps).
                if implicit_self && self.world.class(cid).kind == ClassKind::Class {
                    if let (Some(m), Some(CallTarget::Constructor { init, .. })) =
                        (self.env.method, self.out.calls.get(&expr.id).cloned())
                    {
                        if self.world.method(m).singleton {
                            self.out.self_new.insert(expr.id);
                            self.self_news
                                .push((cid, init, m, expr.span, self.env.file));
                            // In a class method with `Self` in its
                            // signature, the instance is a `Self`.
                            if self.env.self_opaque && self.env.receivers.is_empty() {
                                return Type::Param(SELF_PARAM);
                            }
                        }
                    }
                }
                t
            }
            _ => {
                let mut cands = self.world.lookup_methods(recv_ty, name);
                if call.recv.is_none()
                    && implicit_self
                    && !self.env.receivers.is_empty()
                    && !self.in_outer_self
                {
                    // Inside a block with a receiver: the enclosing selves,
                    // innermost first, answer what the receiver does not.
                    match self.outer_self_for(name) {
                        Some((outer, k)) if cands.is_empty() => {
                            self.bind_outer_self(expr, k);
                            self.in_outer_self = true;
                            let t = self.check_call_on(expr, call, &outer, true, expected);
                            self.in_outer_self = false;
                            return t;
                        }
                        // Nested blocks on the same class shadow each
                        // other on purpose; a different class is worth a word.
                        Some((outer, _)) if outer != *recv_ty => self.warning(
                            format!(
                                "`{name}` is a method of both the block's receiver {} and the enclosing {}; the receiver's is called",
                                self.name(recv_ty),
                                self.name(&outer)
                            ),
                            expr.span,
                        ),
                        _ => {}
                    }
                }
                if cands.is_empty() && call.recv.is_none() {
                    // Top-level functions of the file.
                    if let Some(fm) = self.file_main(self.env.file) {
                        let main = Type::class(fm);
                        cands = self.world.lookup_methods(&main, name);
                    }
                }
                if cands.is_empty() && !implicit_self {
                    if let Some(t) = self.check_bang_assign(expr, call, recv_ty, expected) {
                        return t;
                    }
                }
                if cands.is_empty() {
                    let msg = if call.recv.is_none() && call.args.is_empty() && !call.has_parens {
                        format!(
                            "undefined local variable or method `{name}` for {}",
                            self.name(recv_ty)
                        )
                    } else {
                        let hint = self.immutable_hint(recv_ty, name, call.recv.as_ref());
                        format!("undefined method `{name}` for {}{hint}", self.name(recv_ty))
                    };
                    self.error(msg, expr.span);
                    self.check_args_blindly(call);
                    return Type::Nothing;
                }
                self.resolve_overloads(expr, call, recv_ty, cands, implicit_self, expected)
            }
        }
    }

    /// For a destructive method missing on an immutable built-in type,
    /// the way to write it ("" otherwise).
    fn immutable_hint(&self, recv_ty: &Type, name: &str, recv: Option<&Expr>) -> String {
        let Type::Class(cid, _) = recv_ty else {
            return String::new();
        };
        let b = &self.world.builtin;
        let class = if *cid == b.array {
            "Array"
        } else if *cid == b.hash {
            "Hash"
        } else if *cid == b.set {
            "Set"
        } else if *cid == b.string {
            "String"
        } else if *cid == b.bytes {
            "Bytes"
        } else {
            return String::new();
        };
        let var = match recv.map(|r| &r.kind) {
            Some(ExprKind::Local(v)) => v.as_str(),
            _ => "x",
        };
        let instead = match (class, name) {
            ("Array", "<<") => format!("`{var} = {var}.push(value)`"),
            ("Array", "[]=") => format!("`{var} = {var}.set(index, value)`"),
            ("Hash", "[]=") => format!("`{var} = {var}.put(key, value)`"),
            ("Set", "<<") => format!("`{var} = {var}.add(value)`"),
            ("String" | "Bytes", "<<") => format!("`{var} = {var} + other`"),
            _ => return String::new(),
        };
        format!("; {class} is immutable: write {instead}, or build it with `{class}::Builder`")
    }

    /// `x.foo!(args)` where the receiver's type has no `foo!` but has
    /// `foo`, and `x` is a local or a field: `x = x.foo(args)`. Returns
    /// the assigned type, or `None` when the sugar does not apply.
    /// The place `x.foo!` on a union receiver assigns (`x`, or `@x`; the
    /// root of a chain `x.foo!.bar!`), when no member has a `foo!` of its
    /// own. Members that disagree on that are refused: some would call
    /// their `foo!` and others assign.
    fn union_bang_place(&mut self, call: &Call, members: &[Type], span: Span) -> Option<VarKey> {
        let plain = call.name.strip_suffix('!')?;
        if plain.is_empty() || call.name.ends_with("!=") {
            return None;
        }
        let own = members
            .iter()
            .any(|m| !self.world.lookup_methods(m, &call.name).is_empty());
        let sugar = members.iter().any(|m| {
            self.world.lookup_methods(m, &call.name).is_empty()
                && !self.world.lookup_methods(m, plain).is_empty()
        });
        if !sugar {
            return None;
        }
        if own {
            self.error(
                format!(
                    "`{}` is a method of some members of the union and `{plain}` of others; \
                     narrow the receiver first",
                    call.name
                ),
                span,
            );
            return None;
        }
        let mut root = call.recv.as_ref()?;
        while let ExprKind::Call(inner) = &root.kind {
            if !self.out.bang_assign.contains(&root.id) {
                break;
            }
            match inner.recv.as_ref() {
                Some(r) => root = r,
                None => break,
            }
        }
        match &root.kind {
            ExprKind::Local(name) => Some(VarKey::Local(name.clone())),
            ExprKind::IVar(name) => Some(VarKey::IVar(name.clone())),
            _ => None,
        }
    }

    /// The narrowing `key` has now (`None`: its declared type).
    fn narrowing_of(&self, key: &VarKey) -> Option<Type> {
        match key {
            VarKey::Local(name) => {
                let (depth, slot) = self.lookup_var(name)?;
                let n = self.env.frames.len();
                self.env.frames[n - 1 - depth].vars[slot].narrowed.clone()
            }
            VarKey::IVar(name) => self.env.ivar_narrow.get(name).cloned(),
        }
    }

    fn check_bang_assign(
        &mut self,
        expr: &Expr,
        call: &Call,
        recv_ty: &Type,
        expected: Option<&Type>,
    ) -> Option<Type> {
        let plain_name = call.name.strip_suffix('!')?;
        if plain_name.is_empty() || call.name.ends_with("!=") {
            return None;
        }
        let recv = call.recv.as_ref()?;
        if self.world.lookup_methods(recv_ty, plain_name).is_empty() {
            return None;
        }
        // The place: the receiver, or, in a chain `x.foo!.bar!`, the
        // place the inner call already assigned.
        let mut root = recv;
        while let ExprKind::Call(inner) = &root.kind {
            if !self.out.bang_assign.contains(&root.id) {
                break;
            }
            match inner.recv.as_ref() {
                Some(r) => root = r,
                None => break,
            }
        }
        let place: Option<LValue> = match &root.kind {
            ExprKind::Local(name) => Some(LValue::Local {
                name: name.clone(),
                span: root.span,
            }),
            ExprKind::IVar(name) => Some(LValue::IVar(name.clone())),
            _ => None,
        };
        let Some(place) = place else {
            self.error(
                format!(
                    "`{}` is not a method of {}; `.{}` assigns the result of `{plain_name}` back, but the receiver is not a variable or a field",
                    call.name,
                    self.name(recv_ty),
                    call.name
                ),
                expr.span,
            );
            self.check_args_blindly(call);
            return Some(Type::Nothing);
        };
        let plain = Call {
            name: plain_name.to_string(),
            ..call.clone()
        };
        let vt = self.check_call_on(expr, &plain, recv_ty, false, expected);
        if vt.is_nothing() {
            return Some(Type::Nothing);
        }
        self.out.bang_assign.insert(expr.id);
        // The store, as an assignment to the place would check it.
        match &place {
            LValue::Local { name, span } => {
                let Some((depth, slot)) = self.lookup_var(name) else {
                    return Some(vt);
                };
                if self.captured_across_task(depth) {
                    self.error(
                        format!(
                            "cannot assign to `{name}` from {}; it is captured by value",
                            self.task_block_name()
                        ),
                        *span,
                    );
                }
                let declared = {
                    let n = self.env.frames.len();
                    self.env.frames[n - 1 - depth].vars[slot].declared.clone()
                };
                if !self.coerce(&vt, &declared) {
                    self.error(
                        format!(
                            "`.{}` would assign {} to `{name}` of type {}",
                            call.name,
                            self.name(&vt),
                            self.name(&declared)
                        ),
                        expr.span,
                    );
                }
                let narrowed = self.resolve(&vt);
                self.set_narrowed(&VarKey::Local(name.clone()), Some(narrowed));
            }
            LValue::IVar(name) => {
                if !self.check_ivar_access(expr.span) {
                    return Some(Type::Nothing);
                }
                let Some(cid) = self.env.class_id else {
                    return Some(vt);
                };
                let Some((field, subst)) = self.world.find_field(cid, name) else {
                    return Some(vt);
                };
                if !field.mutable && (!self.env.in_initialize || self.in_late_closure()) {
                    self.error(
                        if self.env.in_initialize {
                            format!("field `@{name}` is immutable: a closure that may run later, after `initialize`, cannot assign it; declare it with `var`")
                        } else {
                            format!("field `@{name}` is immutable; declare it with `var` or assign it in `initialize`")
                        },
                        expr.span,
                    );
                }
                let fty = field.ty.subst(&subst);
                if !self.coerce(&vt, &fty) {
                    self.error(
                        format!(
                            "`.{}` would assign {} to `@{name}` of type {}",
                            call.name,
                            self.name(&vt),
                            self.name(&fty)
                        ),
                        expr.span,
                    );
                }
                // As an assignment to the field narrows it.
                self.env.assigned_fields.insert(name.clone());
                if !field.mutable {
                    let narrowed = self.resolve(&vt);
                    self.env.ivar_narrow.insert(name.clone(), narrowed);
                }
            }
            _ => {}
        }
        Some(vt)
    }

    /// Whether `a && b` (`name` is `&&` or `||`) on a value of type `t` is
    /// a call of `t`'s own operator: decided by the static type, like `!`,
    /// so that `&&` on `Bool`, on `nil`, on a union (`Foo?`: `x && x.foo`
    /// narrows `x`) or on a type that does not define it is the built-in
    /// short circuit, with no test at run time.
    fn has_logical_method(&mut self, t: &Type, name: &str) -> bool {
        let t = self.resolve(t);
        let Type::Class(id, _) = &t else {
            return false;
        };
        let b = &self.world.builtin;
        *id != b.bool_ && *id != b.nil && !self.world.lookup_methods(&t, name).is_empty()
    }

    /// `a && b` (`a || b`, `x &&= b`) as the call `a.&&() { b }` when `a`'s
    /// type defines the operator (`has_logical_method`): the method decides
    /// whether `b` runs, by yielding. The call is kept for lowering in
    /// `Output::logical_calls`; its block shares `b`'s nodes.
    fn logical_method(
        &mut self,
        expr: &Expr,
        name: &str,
        lhs: &Type,
        rhs: &Expr,
        expected: Option<&Type>,
    ) -> Option<Type> {
        let has = self.has_logical_method(lhs, name);
        // In a block checked once per type: a type's own `&&` for one check
        // and the built-in operator for another cannot both be lowered.
        if !self.env.blocks.is_empty() && !has {
            self.note_logical(expr, name, lhs, None);
        }
        if !has {
            return None;
        }
        let t = self.resolve(lhs);
        let call = Call {
            recv: None,
            name: name.to_string(),
            args: vec![],
            block: Some(Block {
                params: Params::empty(),
                body: vec![rhs.clone()],
                span: rhs.span,
                braces: true,
                ret: None,
            }),
            safe_nav: false,
            has_parens: true,
            type_args: vec![],
        };
        let rt = self.check_call_on(expr, &call, &t, false, expected);
        if !self.env.blocks.is_empty() {
            let found = match self.out.calls.get(&expr.id) {
                Some(CallTarget::Method { method }) => Some(*method),
                _ => None,
            };
            if let Some(m) = found {
                self.note_logical(expr, name, lhs, Some(m));
            }
        }
        let before = self.out.logical_calls.get(&expr.id).cloned();
        self.table_journal
            .push(TableUndo::LogicalCall(expr.id, before.map(Box::new)));
        self.out.logical_calls.insert(
            expr.id,
            Expr {
                id: expr.id,
                span: expr.span,
                kind: ExprKind::Call(Box::new(call)),
            },
        );
        Some(rt)
    }

    /// `!x` with a type of its own `!` (decided by the static type, so
    /// that every other `!` is a truthiness test with no check at run
    /// time): the call's type, or `None` for the truthiness test. On a
    /// union, each value uses its member's `!` when that member defines
    /// one and the built-in negation otherwise, so a value answers the
    /// same through `Cond` and `Cond | Nil`; the type test it takes is
    /// paid only where such a union is the static type.
    fn not_method(&mut self, expr: &Expr, operand: &Expr, t: &Type) -> Option<Type> {
        let t = self.resolve(t);
        let has_not = |c: &Self, m: &Type| !c.world.lookup_methods(m, "!").is_empty();
        if let Type::Union(members) = &t {
            let (with, without): (Vec<Type>, Vec<Type>) =
                members.iter().cloned().partition(|m| has_not(self, m));
            if with.is_empty() {
                return None;
            }
            if !without.is_empty() {
                let call = Call {
                    recv: Some(operand.clone()),
                    name: "!".to_string(),
                    args: vec![],
                    block: None,
                    safe_nav: false,
                    has_parens: true,
                    type_args: vec![],
                };
                let mut result = self.world.bool_();
                let mut targets = Vec::new();
                for m in with {
                    let rt = self.check_call_on(expr, &call, &m, false, None);
                    if let Some(CallTarget::Method { method }) = self.out.calls.get(&expr.id) {
                        targets.push((m, *method));
                    }
                    result = self.join(&result, &rt);
                }
                self.out.calls.remove(&expr.id);
                self.note_not_dispatch(expr.id, targets);
                return Some(result);
            }
        } else if !has_not(self, &t) {
            return None;
        }
        let call = Call {
            recv: Some(operand.clone()),
            name: "!".to_string(),
            args: vec![],
            block: None,
            safe_nav: false,
            has_parens: true,
            type_args: vec![],
        };
        let rt = self.check_call_on(expr, &call, &t, false, None);
        // In a block checked once per type, another check may find no
        // `!` (the built-in negation) or another: a test per type.
        if !self.env.blocks.is_empty() {
            // By member (a test of the class sees one), each its own `!`.
            let mut targets = Vec::new();
            for m in t.members() {
                if let Some((id, _)) = self.world.lookup_methods(&m, "!").into_iter().next() {
                    targets.push((m, id));
                }
            }
            self.note_not_dispatch(expr.id, targets);
        }
        Some(rt)
    }

    /// Record what a check of a block found for `a && b` (`method`, or
    /// the built-in operator): the built-in for one check and a method for
    /// another is an error; two types' own methods are called by name
    /// (an extension's is not found so: an error).
    fn note_logical(&mut self, expr: &Expr, name: &str, lhs: &Type, method: Option<MethodId>) {
        let before = self.logical_seen.get(&expr.id).cloned();
        self.table_journal
            .push(TableUndo::Logical(expr.id, before.clone()));
        let mut seen = before.unwrap_or_default();
        let previous = seen.method;
        match method {
            Some(m) => seen.method = Some(m),
            None => seen.builtin = true,
        }
        if !seen.settled {
            let message = if seen.builtin && seen.method.is_some() {
                Some(format!(
                    "cannot tell at run time whether `{name}` is a method of {} or the built-in operator (give the value one type first)",
                    self.name(lhs)
                ))
            } else if let (Some(p), Some(m)) = (previous, method) {
                let ext = |k: MethodId| self.world.method(k).extension.is_some();
                if p == m {
                    None
                } else if ext(p) || ext(m) {
                    Some(format!(
                        "cannot tell at run time which `{name}` to call: {} or {} (give the value one type first)",
                        self.method_label(p),
                        self.method_label(m)
                    ))
                } else {
                    // The classes' own: found by name.
                    self.out.dynamic_calls.insert(expr.id);
                    seen.settled = true;
                    None
                }
            } else {
                None
            };
            if let Some(message) = message {
                seen.settled = true;
                let d = Diagnostic::error(message, expr.span);
                self.ambiguous
                    .push((self.env.file, AmbiguousKey::Node(expr.id), d));
            }
        }
        self.logical_seen.insert(expr.id, seen);
    }

    /// Add to what `!x` tests (`Output::not_dispatch`): the types whose
    /// own `!` it calls, the built-in negation for any other.
    fn note_not_dispatch(&mut self, id: NodeId, targets: Vec<(Type, MethodId)>) {
        let entry = self.out.not_dispatch.entry(id).or_default();
        for (t, m) in targets {
            if !entry.iter().any(|(u, _)| *u == t) {
                entry.push((t, m));
            }
        }
    }

    /// The innermost enclosing `self` (outside the blocks with receivers
    /// the call sits in) that answers `name`, with its receiver level.
    fn outer_self_for(&mut self, name: &str) -> Option<(Type, usize)> {
        // `DslScope`: from a block on a marked receiver, the receivers of
        // enclosing blocks that are marked too are not implicit (the
        // lexical `self` always is).
        let dsl = self.world.top_class("DslScope");
        let marked = |world: &World, t: &Type| -> bool {
            matches!(t, Type::Class(c, _) if dsl.is_some_and(|d| world.class_is_a(*c, d)))
        };
        let inner_marked = marked(&self.world, &self.env.self_type.clone());
        for k in (0..self.env.receivers.len()).rev() {
            let outer = self.env.receivers[k].outer_self.clone();
            if inner_marked && k > 0 && marked(&self.world, &outer) {
                continue;
            }
            if !self.world.lookup_methods(&outer, name).is_empty() {
                return Some((outer, k));
            }
        }
        None
    }

    /// Route an implicit-self call to the `self` of receiver level `k`:
    /// that function keeps its `self` in a hidden frame slot the block
    /// reads like a captured variable.
    fn bind_outer_self(&mut self, expr: &Expr, k: usize) {
        let owner_frame = self.env.receivers[k].outer_frame;
        if self.env.lifted_frame.is_some_and(|lf| owner_frame < lf) {
            let name = match &expr.kind {
                ExprKind::Call(c) => c.name.clone(),
                _ => String::new(),
            };
            self.error(
                format!(
                    "`{name}` is a method of the enclosing `self`, which a block given to `def_method` cannot use: in the generated method, `self` is the receiver"
                ),
                expr.span,
            );
        }
        let frame = &mut self.env.frames[owner_frame];
        let slot = match frame.vars.iter().position(|v| v.name == SELF_SLOT) {
            Some(i) => i as u32,
            None => {
                frame.vars.push(VarInfo {
                    name: SELF_SLOT.to_string(),
                    declared: Type::Nothing,
                    narrowed: None,
                    listed: false,
                });
                frame.vars.len() as u32 - 1
            }
        };
        let owner = frame.owner;
        let depth = (self.env.frames.len() - 1 - owner_frame) as u32;
        self.out.var_refs.insert(expr.span, VarRef { depth, slot });
        self.out.self_slots.insert(owner, slot);
        self.out.outer_self_calls.insert(expr.id);
    }

    fn check_constructor(
        &mut self,
        expr: &Expr,
        call: &Call,
        cid: ClassId,
        args: &[Type],
        expected: Option<&Type>,
    ) -> Type {
        let class = self.world.class(cid).clone();
        if class.is_abstract || matches!(class.kind, ClassKind::Module | ClassKind::Enum) {
            self.error(format!("cannot instantiate `{}`", class.name), expr.span);
            self.check_args_blindly(call);
            return Type::Nothing;
        }
        if cid == self.world.builtin.quoted {
            self.error(
                "a `Quoted` is made from a block literal given for a `Quoted` block parameter (docs/14 §6), not with `new`",
                expr.span,
            );
            self.check_args_blindly(call);
            return Type::Nothing;
        }
        // Instantiate class parameters: explicit args, the expected type, or
        // fresh inference variables.
        let targs: Vec<Type> = if !args.is_empty() {
            args.to_vec()
        } else if let Some(Type::Class(eid, eargs)) = expected.map(|e| self.resolve(e)) {
            if eid == cid && eargs.len() == class.type_params.len() {
                eargs
            } else {
                class
                    .type_params
                    .iter()
                    .map(|_| self.infer.fresh())
                    .collect()
            }
        } else {
            class
                .type_params
                .iter()
                .map(|_| self.infer.fresh())
                .collect()
        };
        // Written arguments (`Acc[Other].new`) had their bounds checked
        // where they were resolved.
        // (Not those naming type parameters, which `check_bounds_deep`
        // leaves to the use.)
        let written = !args.is_empty()
            && !args.iter().any(|a| {
                let a = self.infer.resolve(a);
                a.has_vars() || a.mentions_any_param()
            });
        let instance = Type::Class(cid, targs.clone());
        let cands = self.world.lookup_methods(&instance, "initialize");
        // Only the class's own (or inherited) initialize, not Object's,
        // and only one that can assign the fields (docs/01 §3): a
        // superclass's when no class below it has fields of its own to
        // assign (a data type's or a variant's all are), a module's or an
        // extension's when the class has none at all.
        let mut cands: Vec<_> = cands
            .into_iter()
            .filter(|(m, _)| {
                let m = self.world.method(*m);
                !m.singleton && self.constructs(cid, m)
            })
            .collect();
        // The class's own `initialize` hides its ancestors' (docs/01 §9).
        if cands
            .iter()
            .any(|(m, _)| self.world.method(*m).owner == cid)
        {
            cands.retain(|(m, _)| self.world.method(*m).owner == cid);
        }
        if cands.is_empty() {
            if !call.args.is_empty() || call.block.is_some() {
                self.error(
                    format!("`{}` takes no constructor arguments", class.name),
                    expr.span,
                );
                self.check_args_blindly(call);
            }
            self.out.calls.insert(
                expr.id,
                CallTarget::Constructor {
                    class: cid,
                    init: None,
                },
            );
            return instance;
        }
        // Resolve against initialize's overloads but return the instance.
        let saved_len = self.out.calls.len();
        let _ = saved_len;
        let _ = self.resolve_overloads_as(expr, call, &instance, cands, true, None, true);
        let init = match self.out.calls.get(&expr.id) {
            Some(CallTarget::Method { method }) => Some(*method),
            _ => None,
        };
        // In a block checked once per type, another check may have chosen
        // another `initialize` (by the arguments' types): only the last is
        // recorded, so different ones are an error (`ambiguous_call`).
        if let (Some(m), false) = (init, self.env.blocks.is_empty()) {
            self.note_union_table(
                expr.id,
                vec![(Type::ClassObject(cid, Vec::new()), m)],
                expr.span,
            );
        }
        self.out
            .calls
            .insert(expr.id, CallTarget::Constructor { class: cid, init });
        if !written {
            self.check_class_bounds(&instance, expr.span);
        }
        instance
    }

    /// Check the bounds of a class's type parameters against the arguments
    /// of an instance type (`Channel[T <: Shareable]`).
    fn check_class_bounds(&mut self, instance: &Type, span: Span) {
        let Type::Class(cid, args) = self.resolve(instance) else {
            return;
        };
        let params = self.world.class(cid).type_params.clone();
        for (p, a) in params.iter().zip(args.iter()) {
            if a.has_vars() {
                continue;
            }
            // A bound may name the parameters (`T <: Addable[T]`).
            let subst = self.world.class_subst(cid, &args);
            for b in &p.bounds {
                let b = &b.subst(&subst);
                let ok = if matches!(b, Type::Class(bid, _) if *bid == self.world.builtin.shareable)
                {
                    self.world.is_shareable(a)
                } else {
                    self.world.is_subtype(a, b)
                };
                if !ok {
                    self.error(
                        format!(
                            "type argument {} for `{}` of `{}` must be {}",
                            self.world.type_name(a),
                            p.name,
                            self.world.class(cid).name,
                            self.world.type_name(b)
                        ),
                        span,
                    );
                }
            }
        }
    }

    /// Whether the code here may call a protected method of class (or
    /// module) `owner` on a receiver other than `self`: when `self` is an
    /// instance of `owner` or of a descendant (as in Ruby). A class
    /// method's `self` is a class, never such an instance.
    fn may_call_protected(&self, owner: ClassId) -> bool {
        if matches!(self.env.self_type, Type::ClassObject(..)) {
            return false;
        }
        self.env
            .class_id
            .is_some_and(|c| self.world.class_is_a(c, owner))
    }

    fn resolve_overloads(
        &mut self,
        expr: &Expr,
        call: &Call,
        recv_ty: &Type,
        cands: Vec<(MethodId, HashMap<TypeParamId, Type>)>,
        implicit_self: bool,
        expected: Option<&Type>,
    ) -> Type {
        self.resolve_overloads_as(expr, call, recv_ty, cands, implicit_self, expected, false)
    }

    #[allow(clippy::too_many_arguments)]
    fn resolve_overloads_as(
        &mut self,
        expr: &Expr,
        call: &Call,
        recv_ty: &Type,
        cands: Vec<(MethodId, HashMap<TypeParamId, Type>)>,
        implicit_self: bool,
        expected: Option<&Type>,
        is_init: bool,
    ) -> Type {
        // Pre-type arguments that do not benefit from an expected type.
        let mut pre: HashMap<NodeId, Type> = HashMap::default();
        for a in &call.args {
            let e = match a {
                Arg::Positional(e) | Arg::Splat(e) | Arg::DoubleSplat(e) => e,
                Arg::Keyword { value, .. } => value,
                Arg::BlockPass(_) => continue,
            };
            if !Self::needs_expectation(e) {
                let t = self.check_expr(e, None);
                pre.insert(e.id, t);
            }
        }
        self.resolve_pretyped(
            expr,
            call,
            recv_ty,
            cands,
            implicit_self,
            expected,
            is_init,
            &pre,
        )
    }

    /// `resolve_overloads_as` once the arguments that need no expected
    /// type are typed (`pre`).
    #[allow(clippy::too_many_arguments)]
    fn resolve_pretyped(
        &mut self,
        expr: &Expr,
        call: &Call,
        recv_ty: &Type,
        cands: Vec<(MethodId, HashMap<TypeParamId, Type>)>,
        implicit_self: bool,
        expected: Option<&Type>,
        is_init: bool,
        pre: &HashMap<NodeId, Type>,
    ) -> Type {
        let block_given =
            call.block.is_some() || call.args.iter().any(|a| matches!(a, Arg::BlockPass(_)));
        let single = cands.len() == 1;
        let diags_at_entry = self.diagnostics.len();
        let mut failures: Vec<String> = Vec::new();
        // With several candidates, each is tried and its checks undone
        // (docs/01 §9), from the last to the first; `pick_overload` chooses
        // among those that fit, and the one chosen must be the last
        // checked, so that what its checks record stands: the first
        // candidate's (the usual winner) are kept, any other is checked
        // again. One that a fit at the literals' defaults beats is not
        // tried.
        let block_arity = Self::block_arity(call);
        let inferring = pre.values().any(|t| self.infer.resolve(t).has_vars());
        let mut fits: Vec<(usize, MethodId, bool)> = Vec::new();
        let mut kept: Option<KeptFirst> = None;
        for (index, (mid, class_subst)) in cands.iter().enumerate().rev() {
            if !single
                && !inferring
                && fits
                    .iter()
                    .any(|f| !f.2 && self.beats((f.0, f.1), (index, *mid), &cands, block_arity))
            {
                continue;
            }
            let m = self.world.method(*mid).clone();
            // `initialize` runs only from `new` and from `super` in an
            // `initialize` (docs/01 §3): called otherwise, on any
            // receiver, it would write a made object's immutable fields
            // again, and a superclass's could re-enter a subclass's.
            if m.name == "initialize" && !m.singleton && !is_init {
                failures.push(
                    "`initialize` is called only by `new` and by `super` in `initialize`"
                        .to_string(),
                );
                continue;
            }
            // Visibility.
            if m.visibility == Visibility::Private && !implicit_self && !is_init {
                failures.push(format!("`{}` is private", m.name));
                continue;
            }
            if m.visibility == Visibility::Protected
                && !implicit_self
                && !self.may_call_protected(m.owner)
            {
                failures.push(format!(
                    "`{}` is protected: it is called on another receiver only from an instance of {}",
                    m.name,
                    self.world.class(m.owner).name
                ));
                continue;
            }
            if m.block.is_some() != block_given && !(m.block_optional && !block_given) {
                failures.push(if m.block.is_some() {
                    format!("{} requires a block", self.signature(&m))
                } else {
                    format!("{} does not take a block", self.signature(&m))
                });
                continue;
            }
            let saved_infer = self.infer.save();
            let saved_diags = self.diagnostics.len();
            let saved_diags_tables = self.table_mark();
            // Instantiate.
            let mut subst = class_subst.clone();
            // A call on `self` in a method with `Self` in its signature
            // keeps `Self` opaque (`dup` gives a `Self`).
            let bound_self = if implicit_self && self.self_is_opaque_for(recv_ty) {
                Type::Param(SELF_PARAM)
            } else {
                Self::self_binding(&self.world, &m, recv_ty)
            };
            subst.insert(SELF_PARAM, bound_self);
            let mut method_vars = Vec::new();
            if !call.type_args.is_empty() && call.type_args.len() != m.type_params.len() {
                failures.push(format!(
                    "{} takes {} type argument(s)",
                    self.signature(&m),
                    m.type_params.len()
                ));
                continue;
            }
            for (i, tp) in m.type_params.iter().enumerate() {
                let t = if let Some(te) = call.type_args.get(i) {
                    let scope = self.env.scope.clone();
                    self.resolve_type_expr(te, &scope).unwrap_or(Type::Nothing)
                } else {
                    self.infer.fresh()
                };
                method_vars.push((tp.clone(), t.clone()));
                subst.insert(tp.id, t);
            }
            // `U >: T`: without a type argument, `U` is `T` joined with
            // what the arguments pass for it (`[1].push("a")` is an
            // `Array[Int | String]`), not just the first of these.
            for tp in &m.type_params {
                let Some(lower) = &tp.lower else {
                    continue;
                };
                if call.type_args.is_empty() {
                    let lower = self.infer.resolve(&lower.subst(&subst));
                    let t = self.widen_from_args(call, &m, tp.id, lower, pre);
                    for (vtp, vt) in method_vars.iter_mut() {
                        if vtp.id == tp.id {
                            *vt = t.clone();
                        }
                    }
                    subst.insert(tp.id, t);
                }
            }
            match self.try_candidate(expr, call, &m, &subst, pre, expected, single) {
                Ok(ret) => {
                    // With several candidates, an error inside the block
                    // (its result has the wrong type, say) rules this one
                    // out rather than being reported as the final word:
                    // `sum { |x| x * 0.5 }` must reach the Float overload.
                    if !single {
                        let block_error = self.diagnostics[saved_diags..]
                            .iter()
                            .find(|(_, d)| d.is_error())
                            .map(|(_, d)| d.message.clone());
                        if let Some(message) = block_error {
                            self.infer.restore(saved_infer);
                            self.truncate_diagnostics(saved_diags);
                            self.discard_tables(saved_diags_tables);
                            failures.push(format!("{}: {message}", self.signature(&m)));
                            continue;
                        }
                    }
                    // Bounds of method type parameters.
                    let mut ok = true;
                    for (tp, t) in &method_vars {
                        // A bound is a use: `?v | Int` sorted is an `Int`.
                        let rt = if tp.bounds.is_empty() {
                            self.infer.resolve(t)
                        } else {
                            self.settle_vars(t)
                        };
                        if let Some(lower) = &tp.lower {
                            let lower = self.infer.resolve(&lower.subst(&subst));
                            if !self.coerce(&lower, &rt) {
                                ok = false;
                                self.error(
                                    format!(
                                        "type argument {} for `{}` is not a supertype of {}",
                                        self.name(&rt),
                                        tp.name,
                                        self.name(&lower)
                                    ),
                                    expr.span,
                                );
                            }
                        }
                        for b in &tp.bounds {
                            let b = b.subst(&subst);
                            if !self.coerce(&rt, &b) {
                                ok = false;
                                self.error(
                                    format!(
                                        "type argument {} for `{}` does not satisfy the bound {}",
                                        self.name(&rt),
                                        tp.name,
                                        self.name(&b)
                                    ),
                                    expr.span,
                                );
                            }
                        }
                    }
                    // Bounds of the extension's parameters.
                    if let Some(ext) = m.extension {
                        let ext = self.world.extensions[ext as usize].clone();
                        for tp in &ext.type_params {
                            let Some(t) = subst.get(&tp.id).cloned() else {
                                continue;
                            };
                            let rt = if tp.bounds.is_empty() {
                                self.infer.resolve(&t)
                            } else {
                                self.settle_vars(&t)
                            };
                            for b in &tp.bounds {
                                let b = b.subst(&subst);
                                if !self.coerce(&rt, &b) {
                                    ok = false;
                                    if single {
                                        self.error(
                                            format!(
                                                "`{}` requires {} to be {} (found {})",
                                                m.name,
                                                tp.name,
                                                self.name(&b),
                                                self.name(&rt)
                                            ),
                                            expr.span,
                                        );
                                    }
                                }
                            }
                        }
                    }
                    if !ok && !single {
                        self.infer.restore(saved_infer);
                        self.truncate_diagnostics(saved_diags);
                        self.discard_tables(saved_diags_tables);
                        failures.push(format!("{}: type bounds not satisfied", self.signature(&m)));
                        continue;
                    }
                    if single {
                        return self.finish_call(expr, call, &m, ret);
                    }
                    // An integer literal given another type than its
                    // default (`1` as a `Float`) puts it a level down.
                    let converted = self.table_journal[saved_diags_tables.0..]
                        .iter()
                        .any(|u| matches!(u, TableUndo::Literal(_, _, true)));
                    fits.push((index, *mid, converted));
                    if index == 0 {
                        kept = Some((ret, saved_infer, saved_diags, saved_diags_tables));
                    } else {
                        self.infer.restore(saved_infer);
                        self.truncate_diagnostics(saved_diags);
                        self.discard_tables(saved_diags_tables);
                    }
                    continue;
                }
                Err(reason) => {
                    if !single {
                        self.infer.restore(saved_infer);
                        self.truncate_diagnostics(saved_diags);
                        self.discard_tables(saved_diags_tables);
                    }
                    failures.push(reason);
                }
            }
        }
        if !fits.is_empty() {
            fits.reverse();
            let (mut winner, mut rivals) = self.pick_overload(&fits, &cands, block_arity);
            // An argument whose type is still to be inferred fits every
            // overload, binding it: the first that fits takes it, as the
            // checks of the arguments cannot tell them apart.
            if inferring {
                let best_level = fits.iter().any(|f| !f.2);
                if let Some(f) = fits.iter().find(|f| f.2 != best_level) {
                    winner = f.1;
                }
                rivals.clear();
            }
            let t = match kept {
                Some((ret, ..)) if winner == cands[0].0 => {
                    let m = self.world.method(winner).clone();
                    self.finish_call(expr, call, &m, ret)
                }
                kept => {
                    // The first candidate's checks, kept, give way.
                    if let Some((_, infer, diags, tables)) = kept {
                        self.infer.restore(infer);
                        self.truncate_diagnostics(diags);
                        self.discard_tables(tables);
                    }
                    let cand = cands.iter().find(|(m, _)| *m == winner).cloned().unwrap();
                    self.resolve_pretyped(
                        expr,
                        call,
                        recv_ty,
                        vec![cand],
                        implicit_self,
                        expected,
                        is_init,
                        pre,
                    )
                }
            };
            if !rivals.is_empty() {
                let mut names: Vec<String> = std::iter::once(winner)
                    .chain(rivals)
                    .map(|m| self.signature(self.world.method(m)))
                    .collect();
                names.dedup();
                self.error(
                    format!(
                        "the call of `{}` is ambiguous: these overloads fit it equally (pass arguments of the types of one):\n    {}",
                        call.name,
                        names.join("\n    ")
                    ),
                    expr.span,
                );
            }
            return t;
        }
        // Tried from the last: listed in declaration order.
        failures.reverse();
        if !single || cands.is_empty() {
            // A method and the one it overrides can fail for the same
            // reason: say it once.
            let mut seen = HashSet::default();
            failures.retain(|f| seen.insert(f.clone()));
            let recv_name = self.name(recv_ty);
            let arg_desc = self.describe_args(call, pre);
            self.error(
                format!(
                    "no overload of `{}` on {recv_name} matches ({arg_desc}):\n    {}",
                    call.name,
                    failures.join("\n    ")
                ),
                expr.span,
            );
        } else if self.diagnostics.len() == diags_at_entry {
            // The single candidate failed a check before its arguments
            // were tried (visibility, block, `initialize`), which
            // reported nothing: say why here.
            self.error(failures.join("; "), expr.span);
        }
        // Still type the block for its own diagnostics.
        if let Some(b) = &call.block {
            let fresh = self.infer.fresh();
            let params: Vec<Type> = b.params.list.iter().map(|_| self.infer.fresh()).collect();
            self.check_block(
                expr.id,
                b,
                &Type::Proc(None, params, Box::new(fresh), false),
            );
        }
        Type::Nothing
    }

    /// What a call that a method was chosen for gives.
    fn finish_call(&mut self, expr: &Expr, call: &Call, m: &MethodInfo, ret: Type) -> Type {
        self.out
            .calls
            .insert(expr.id, CallTarget::Method { method: m.id });
        self.note_static_call(expr, m.id);
        if m.is_static {
            // The chosen candidate's type arguments.
            let trials = std::mem::take(&mut self.type_args_trials);
            if let Some((_, _, args)) = trials
                .into_iter()
                .rev()
                .find(|(id, mid, _)| *id == expr.id && *mid == m.id)
            {
                self.out.type_args.insert(expr.id, args);
            }
        }
        // `loop { }` without `break` never returns.
        let broken = self.breaking_blocks.get(&expr.id).cloned();
        if m.name == "loop"
            && m.owner == self.world.builtin.kernel
            && call.block.is_some()
            && broken.is_none()
        {
            return Type::Nothing;
        }
        // A `break` in the block gives the call its value.
        if let Some(t) = broken {
            return self.join(&ret, &t);
        }
        ret
    }

    /// The parameters of a call's literal block, for telling overloads
    /// that differ only in theirs apart (`&:name` and `|*xs|` take one).
    fn block_arity(call: &Call) -> Option<usize> {
        match &call.block {
            Some(b) if b.params.list.iter().any(|p| p.kind == ParamKind::Rest) => Some(1),
            Some(b) => Some(
                b.params
                    .list
                    .iter()
                    .filter(|p| p.kind != ParamKind::Block)
                    .count(),
            ),
            None if call.args.iter().any(|a| matches!(a, Arg::BlockPass(_))) => Some(1),
            None => None,
        }
    }

    /// Among the overloads that fit a call (`(index, method, converted)`,
    /// in the candidates' order: a subclass's first), the one it calls
    /// (docs/01 §9): those that fit with every integer literal at its
    /// default type come first; among them, the one that `beats` the
    /// others. The rest are the ones that fit as well as the winner: the
    /// call is ambiguous.
    fn pick_overload(
        &self,
        fits: &[(usize, MethodId, bool)],
        cands: &[(MethodId, HashMap<TypeParamId, Type>)],
        block_arity: Option<usize>,
    ) -> (MethodId, Vec<MethodId>) {
        let best_level = fits.iter().any(|f| !f.2);
        let level: Vec<&(usize, MethodId, bool)> =
            fits.iter().filter(|f| f.2 != best_level).collect();
        let top: Vec<MethodId> = level
            .iter()
            .filter(|x| {
                !level
                    .iter()
                    .any(|y| self.beats((y.0, y.1), (x.0, x.1), cands, block_arity))
            })
            .map(|x| x.1)
            .collect();
        let winner = top.first().copied().unwrap_or(level[0].1);
        (winner, top.into_iter().skip(1).collect())
    }

    /// Whether candidate `x` (its index and method) is chosen over `y`
    /// at the same literal level: it is more specific; or, as specific,
    /// its block takes as many parameters as the call's (`block_arity`),
    /// or else the fewest more than it,
    /// or it is an extension's method in scope beside the class's own, or
    /// it comes first from another owner (an override, a subclass's).
    fn beats(
        &self,
        x: (usize, MethodId),
        y: (usize, MethodId),
        cands: &[(MethodId, HashMap<TypeParamId, Type>)],
        block_arity: Option<usize>,
    ) -> bool {
        let (a, b) = (self.world.method(x.1), self.world.method(y.1));
        let (sa, sb) = (&cands[x.0].1, &cands[y.0].1);
        let (ab, ba) = (
            self.as_specific(a, sa, b, sb),
            self.as_specific(b, sb, a, sa),
        );
        if ab != ba {
            return ab;
        }
        if !ab {
            return false;
        }
        // The block's arity: the same as the call's first, then the
        // fewest above it (`{ "0" }` takes `(String)` over `(String,
        // MatchData)`).
        let rank = |m: &MethodInfo| match (&m.block, block_arity) {
            (Some((_, Type::Proc(_, ps, _, _))), Some(n)) if ps.len() == n => Some(0),
            (Some((_, Type::Proc(_, ps, _, _))), Some(n)) if ps.len() > n => Some(ps.len()),
            _ => None,
        };
        match (rank(a), rank(b)) {
            (Some(x), Some(y)) if x != y => return x < y,
            (Some(_), None) => return true,
            (None, Some(_)) => return false,
            _ => {}
        }
        if a.owner == b.owner && a.extension.is_some() != b.extension.is_some() {
            return a.extension.is_some();
        }
        a.owner != b.owner && x.0 < y.0
    }

    /// Whether `a` is at least as specific as `b`: every call `a` takes,
    /// `b` takes (each parameter's type within `b`'s, positional ones by
    /// place, keyword ones by name), with the receiver's type arguments
    /// (`sa`, `sb`) in; a type parameter of `b`'s own takes anything,
    /// wherever it appears.
    fn as_specific(
        &self,
        a: &MethodInfo,
        sa: &HashMap<TypeParamId, Type>,
        b: &MethodInfo,
        sb: &HashMap<TypeParamId, Type>,
    ) -> bool {
        let own: Vec<TypeParamId> = b.type_params.iter().map(|p| p.id).collect();
        fn within(c: &Checker, own: &[TypeParamId], t: &Type, u: &Type) -> bool {
            match (t, u) {
                (_, Type::Param(p)) if own.contains(p) => true,
                (Type::Class(x, xs), Type::Class(y, ys))
                    if x == y && xs.len() == ys.len() && !xs.is_empty() =>
                {
                    xs.iter().zip(ys).all(|(t, u)| within(c, own, t, u))
                }
                _ => t == u || c.world.is_subtype(t, u),
            }
        }
        let ty = |t: &Type, s: &HashMap<TypeParamId, Type>| self.infer.resolve(&t.subst(s));
        // A rest parameter's type is the array of its elements'.
        let elem = |t: Type| match t {
            Type::Class(c, args) if c == self.world.builtin.array && args.len() == 1 => {
                args[0].clone()
            }
            t => t,
        };
        fn of(m: &MethodInfo, k: ParamKind) -> Vec<&ParamInfo> {
            m.params.iter().filter(|p| p.kind == k).collect()
        }
        let (pa, pb) = (of(a, ParamKind::Positional), of(b, ParamKind::Positional));
        let (ra, rb) = (of(a, ParamKind::Rest), of(b, ParamKind::Rest));
        let (ka, kb) = (of(a, ParamKind::KeywordOnly), of(b, ParamKind::KeywordOnly));
        let (xa, xb) = (of(a, ParamKind::KeywordRest), of(b, ParamKind::KeywordRest));
        if (!ra.is_empty() && rb.is_empty()) || (!xa.is_empty() && xb.is_empty()) {
            return false;
        }
        let fits = |p: &ParamInfo, u: &Type| within(self, &own, &ty(&p.ty, sa), u);
        let positional = match rb.first() {
            Some(r) => {
                let r = elem(ty(&r.ty, sb));
                pa.len() >= pb.len()
                    && pa.iter().enumerate().all(|(i, p)| {
                        let u = pb.get(i).map_or(r.clone(), |q| ty(&q.ty, sb));
                        fits(p, &u)
                    })
                    && ra
                        .iter()
                        .all(|p| within(self, &own, &elem(ty(&p.ty, sa)), &r))
            }
            None => {
                pa.len() == pb.len() && pa.iter().zip(&pb).all(|(p, q)| fits(p, &ty(&q.ty, sb)))
            }
        };
        positional
            && ka.len() == kb.len()
            && ka.iter().all(|p| {
                kb.iter()
                    .find(|q| q.name == p.name)
                    .is_some_and(|q| fits(p, &ty(&q.ty, sb)))
            })
    }

    fn describe_args(&self, call: &Call, pre: &HashMap<NodeId, Type>) -> String {
        let mut parts = Vec::new();
        for a in &call.args {
            match a {
                Arg::Positional(e) => parts.push(
                    pre.get(&e.id)
                        .or_else(|| self.out.node_types.get(&e.id))
                        .map(|t| self.name(t))
                        .unwrap_or_else(|| match e.kind {
                            // Typed only against a parameter, which no
                            // overload got to.
                            ExprKind::Int(_) => "Int".to_string(),
                            ExprKind::Nil => "Nil".to_string(),
                            _ => "?".to_string(),
                        }),
                ),
                Arg::Splat(e) => parts.push(format!(
                    "*{}",
                    pre.get(&e.id)
                        .map(|t| self.name(t))
                        .unwrap_or_else(|| "?".to_string())
                )),
                Arg::DoubleSplat(_) => parts.push("**".to_string()),
                Arg::Keyword { name, value, .. } => parts.push(format!(
                    "{name}: {}",
                    pre.get(&value.id)
                        .map(|t| self.name(t))
                        .unwrap_or_else(|| "?".to_string())
                )),
                Arg::BlockPass(_) => parts.push("&block".to_string()),
            }
        }
        if call.block.is_some() {
            parts.push("{ block }".to_string());
        }
        parts.join(", ")
    }

    pub fn signature(&self, m: &MethodInfo) -> String {
        let mut parts: Vec<String> = m
            .params
            .iter()
            .map(|p| {
                let prefix = match p.kind {
                    ParamKind::Rest => "*",
                    ParamKind::KeywordRest => "**",
                    _ => "",
                };
                let default = if p.default.is_some() { " = ..." } else { "" };
                // `*values: T` is declared with the element type and
                // held as `Array[T]` (`**opts: T` as `Hash[Symbol, T]`).
                let ty = match (&p.kind, &p.ty) {
                    (ParamKind::Rest, Type::Class(_, args)) if args.len() == 1 => &args[0],
                    (ParamKind::KeywordRest, Type::Class(_, args)) if args.len() == 2 => &args[1],
                    _ => &p.ty,
                };
                format!("{prefix}{}: {}{default}", p.name, self.world.type_name(ty))
            })
            .collect();
        if let Some((name, t)) = &m.block {
            let name = if name == "&" { "" } else { name.as_str() };
            parts.push(format!("&{name}: {}", self.world.type_name(t)));
        }
        let ret = self.world.type_name(&m.ret);
        format!("{}({}) -> {}", m.name, parts.join(", "), ret)
    }

    /// Expressions whose type depends on the expected type.
    /// The type a lower-bounded method type parameter `param` takes: its
    /// bound joined with the types the arguments give it, as far as
    /// they are known before the call is checked (an argument typed only
    /// against its parameter, such as `[]`, is checked against the
    /// result instead).
    fn widen_from_args(
        &mut self,
        call: &Call,
        m: &MethodInfo,
        param: TypeParamId,
        lower: Type,
        pre: &HashMap<NodeId, Type>,
    ) -> Type {
        if matches!(lower, Type::Var(_)) {
            return lower;
        }
        let positional: Vec<&ParamInfo> = m
            .params
            .iter()
            .filter(|p| p.kind == ParamKind::Positional)
            .collect();
        let rest = m.params.iter().find(|p| p.kind == ParamKind::Rest);
        let mut next = 0;
        let mut result = lower.clone();
        for a in &call.args {
            let (param_ty, e) = match a {
                Arg::Positional(e) => {
                    let ty = if let Some(p) = positional.get(next) {
                        next += 1;
                        p.ty.clone()
                    } else if let Some(r) = rest {
                        match &r.ty {
                            Type::Class(_, args) if args.len() == 1 => args[0].clone(),
                            t => t.clone(),
                        }
                    } else {
                        continue;
                    };
                    (ty, e)
                }
                Arg::Keyword { name, value, .. } => {
                    match m.params.iter().find(|p| &p.name == name) {
                        Some(p) => (p.ty.clone(), value),
                        None => continue,
                    }
                }
                _ => continue,
            };
            let arg_ty = match (&e.kind, pre.get(&e.id)) {
                (_, Some(t)) => self.infer.resolve(t),
                (ExprKind::Lambda(_), None) => continue,
                // An integer literal fits a numeric bound as it is.
                (ExprKind::Int(_), None) => {
                    let int = self.world.int();
                    let saved = self.infer.save();
                    let fits = self.coerce(&int, &result)
                        || matches!(&result, Type::Class(c, _) if *c == self.world.builtin.integer || *c == self.world.builtin.float);
                    self.infer.restore(saved);
                    if fits {
                        continue;
                    }
                    int
                }
                // A literal typed against its parameter: typed here on
                // its own, as overloads try arguments.
                _ => {
                    let saved = self.infer.save();
                    let saved_diags = self.diagnostics.len();
                    let saved_diags_tables = self.table_mark();
                    let t = self.check_expr(e, None);
                    let t = self.infer.resolve(&t);
                    self.infer.restore(saved);
                    self.truncate_diagnostics(saved_diags);
                    self.discard_tables(saved_diags_tables);
                    if t.has_vars() {
                        continue;
                    }
                    t
                }
            };
            for t in Self::at_param(&param_ty, &arg_ty, param) {
                let saved = self.infer.save();
                let fits = self.coerce(&t, &result);
                self.infer.restore(saved);
                if !fits {
                    result = self.join(&result, &t);
                }
            }
        }
        result
    }

    /// The parts of `arg` that stand where `param_ty` has the type
    /// parameter `param` (`Array[U]` against `Array[String]` gives
    /// `String`).
    fn at_param(param_ty: &Type, arg: &Type, param: TypeParamId) -> Vec<Type> {
        match (param_ty, arg) {
            (Type::Param(p), _) if *p == param => vec![arg.clone()],
            (Type::Class(c, ps), Type::Class(d, args)) if c == d && ps.len() == args.len() => ps
                .iter()
                .zip(args)
                .flat_map(|(p, a)| Self::at_param(p, a, param))
                .collect(),
            _ => Vec::new(),
        }
    }

    fn needs_expectation(e: &Expr) -> bool {
        matches!(
            e.kind,
            ExprKind::Array(_)
                | ExprKind::Hash(_)
                | ExprKind::Lambda(_)
                | ExprKind::Nil
                | ExprKind::Int(_)
                | ExprKind::Range { .. }
        )
    }

    /// Whether `&:name` can call `method`: with no argument and no block,
    /// and with the bounds of its extension's parameters holding under
    /// `subst`, with the error a call would report.
    fn symbol_callable(
        &mut self,
        method: MethodId,
        subst: &HashMap<TypeParamId, Type>,
        name: &str,
    ) -> Result<(), String> {
        let m = self.world.method(method);
        let needs_argument = m.params.iter().any(|p| {
            matches!(p.kind, ParamKind::Positional | ParamKind::KeywordOnly) && p.default.is_none()
        });
        if needs_argument || (m.block.is_some() && !m.block_optional) {
            return Err(format!(
                "`{name}` needs {} (`&:{name}` calls it with none)",
                if needs_argument {
                    "an argument"
                } else {
                    "a block"
                }
            ));
        }
        let Some(ext) = m.extension else {
            return Ok(());
        };
        let ext = self.world.extensions[ext as usize].clone();
        for tp in &ext.type_params {
            let Some(t) = subst.get(&tp.id).cloned() else {
                continue;
            };
            let rt = if tp.bounds.is_empty() {
                self.infer.resolve(&t)
            } else {
                self.settle_vars(&t)
            };
            for b in &tp.bounds {
                let b = b.subst(subst);
                if !self.coerce(&rt, &b) {
                    return Err(format!(
                        "`{name}` requires {} to be {} (found {}) (in `&:{name}`)",
                        tp.name,
                        self.name(&b),
                        self.name(&rt)
                    ));
                }
            }
        }
        Ok(())
    }

    /// Try to apply a method to the call's arguments. Returns the return type
    /// (with the substitution applied) or a reason for failure.
    #[allow(clippy::too_many_arguments)]
    fn try_candidate(
        &mut self,
        expr: &Expr,
        call: &Call,
        m: &MethodInfo,
        subst: &HashMap<TypeParamId, Type>,
        pre: &HashMap<NodeId, Type>,
        expected: Option<&Type>,
        report: bool,
    ) -> Result<Type, String> {
        if m.is_static {
            let args = subst.iter().map(|(k, v)| (*k, v.clone())).collect();
            self.type_args_trials.push((expr.id, m.id, args));
        }
        // Match arguments to parameters.
        let positional: Vec<usize> = m
            .params
            .iter()
            .enumerate()
            .filter(|(_, p)| p.kind == ParamKind::Positional)
            .map(|(i, _)| i)
            .collect();
        let rest = m.params.iter().position(|p| p.kind == ParamKind::Rest);
        let kwrest = m
            .params
            .iter()
            .position(|p| p.kind == ParamKind::KeywordRest);
        let mut bound: HashMap<usize, Vec<MatchedArg>> = HashMap::default();
        let mut next_pos = 0;
        let mut has_splat = false;
        for a in &call.args {
            match a {
                Arg::Positional(e) => {
                    if let Some(&pi) = positional.get(next_pos) {
                        next_pos += 1;
                        bound.entry(pi).or_default().push(MatchedArg {
                            param_ty: m.params[pi].ty.subst(subst),
                            arg: e,
                            pre_type: pre.get(&e.id).cloned(),
                        });
                    } else if let Some(ri) = rest {
                        let elem = match m.params[ri].ty.subst(subst) {
                            Type::Class(_, args) if args.len() == 1 => args[0].clone(),
                            t => t,
                        };
                        bound.entry(ri).or_default().push(MatchedArg {
                            param_ty: elem,
                            arg: e,
                            pre_type: pre.get(&e.id).cloned(),
                        });
                    } else {
                        return Err(format!(
                            "{} takes {} positional argument(s)",
                            self.signature(m),
                            positional.len()
                        ));
                    }
                }
                Arg::Splat(e) => {
                    has_splat = true;
                    let Some(ri) = rest else {
                        return Err(format!(
                            "{} does not take a variable number of arguments",
                            self.signature(m)
                        ));
                    };
                    bound.entry(ri).or_default().push(MatchedArg {
                        param_ty: m.params[ri].ty.subst(subst),
                        arg: e,
                        pre_type: pre.get(&e.id).cloned(),
                    });
                }
                Arg::Keyword { name, value, .. } => {
                    let found = m.params.iter().position(|p| {
                        &p.name == name
                            && matches!(p.kind, ParamKind::Positional | ParamKind::KeywordOnly)
                    });
                    match found {
                        Some(pi) if !bound.contains_key(&pi) => {
                            bound.entry(pi).or_default().push(MatchedArg {
                                param_ty: m.params[pi].ty.subst(subst),
                                arg: value,
                                pre_type: pre.get(&value.id).cloned(),
                            });
                        }
                        Some(_) => return Err(format!("argument `{name}` given twice")),
                        None => match kwrest {
                            Some(ki) => {
                                let elem = match m.params[ki].ty.subst(subst) {
                                    Type::Class(_, args) if args.len() == 2 => args[1].clone(),
                                    t => t,
                                };
                                bound.entry(ki).or_default().push(MatchedArg {
                                    param_ty: elem,
                                    arg: value,
                                    pre_type: pre.get(&value.id).cloned(),
                                });
                            }
                            None => {
                                return Err(format!(
                                    "{} has no parameter `{name}`",
                                    self.signature(m)
                                ))
                            }
                        },
                    }
                }
                Arg::DoubleSplat(e) => {
                    let Some(ki) = kwrest else {
                        return Err(format!("{} does not take `**`", self.signature(m)));
                    };
                    bound.entry(ki).or_default().push(MatchedArg {
                        param_ty: m.params[ki].ty.subst(subst),
                        arg: e,
                        pre_type: pre.get(&e.id).cloned(),
                    });
                }
                Arg::BlockPass(_) => {}
            }
        }
        // Missing required parameters.
        for (i, p) in m.params.iter().enumerate() {
            if bound.contains_key(&i) || p.default.is_some() {
                continue;
            }
            match p.kind {
                ParamKind::Rest | ParamKind::KeywordRest | ParamKind::Block => continue,
                ParamKind::Positional if has_splat => continue,
                _ => {
                    return Err(format!(
                        "{} is missing the argument `{}`",
                        self.signature(m),
                        p.name
                    ))
                }
            }
        }
        // Type the arguments.
        for (pi, matched) in &bound {
            for ma in matched {
                let expected_ty = ma.param_ty.clone();
                let actual = match &ma.pre_type {
                    Some(t) => t.clone(),
                    None => self.check_expr(ma.arg, Some(&expected_ty)),
                };
                let p = &m.params[*pi];
                let ok = self.coerce(&actual, &expected_ty);
                if !ok {
                    let msg = format!(
                        "argument `{}` of {} expects {} but found {}",
                        p.name,
                        self.signature(m),
                        self.name(&expected_ty),
                        self.name(&actual)
                    );
                    if report {
                        self.error(msg.clone(), ma.arg.span);
                    }
                    return Err(msg);
                }
            }
        }
        // The return type, unified with the expected type first so that it
        // can drive inference inside the block (`Array.build { |out| ... }`
        // where the result type is known).
        // A caller sees a `Void` result as `Nil`.
        let ret = self.world.unvoid(&self.method_ret(m.id)).subst(subst);
        if let Some(e) = expected {
            let r = self.infer.resolve(&ret);
            if r.has_vars() {
                let saved = self.infer.save();
                if !self.coerce(&r, e) {
                    self.infer.restore(saved);
                }
            }
        }
        // Block.
        if let Some((_, block_ty)) = &m.block {
            let block_ty = block_ty.subst(subst);
            if let Some(b) = &call.block {
                let resolved = self.infer.resolve(&block_ty);
                let is_task = Self::runs_block_in_task(&self.world, m);
                // `&: (A) -> R using M`: the block literal sees the
                // method's extensions.
                let active_len = self.world.active_extensions.len();
                for e in m.block_usings.clone() {
                    if !self.world.active_extensions.contains(&e) {
                        self.world.active_extensions.push(e);
                    }
                }
                // A named `&block` may be kept (an anonymous one is only
                // yielded to; a native that keeps its block names it).
                self.env.next_block_escapes = m.block.as_ref().is_some_and(|(n, _)| n != "&");
                // A block given to `Meta::ClassDef`'s generating natives
                // becomes a method's body (docs/14 §5).
                self.env.next_block_lifted =
                    m.is_native && m.owner == self.world.builtin.meta_classdef;
                // `&cond: Quoted[P]`: the block is checked as a `P` and
                // given as its tree (docs/14 §6).
                // Recorded through the journal, so that a trial of an
                // overload that loses leaves nothing behind and one kept
                // keeps it (`discard_tables`).
                let before = (
                    self.out.quoted_blocks.get(&expr.id).copied(),
                    self.quoted_seen.get(&expr.id).copied(),
                    self.quoted_conflicts.get(&expr.id).copied(),
                );
                self.table_journal
                    .push(TableUndo::Quoted(expr.id, before.0, before.1, before.2));
                let (resolved, quoted) = match &resolved {
                    Type::Class(c, args) if *c == self.world.builtin.quoted && args.len() == 1 => {
                        let p = self.infer.resolve(&args[0]);
                        let receiver = matches!(&p, Type::Proc(Some(_), ..));
                        self.out.quoted_blocks.insert(expr.id, receiver);
                        (p, true)
                    }
                    _ => {
                        self.out.quoted_blocks.remove(&expr.id);
                        (resolved, false)
                    }
                };
                if self
                    .quoted_seen
                    .insert(expr.id, quoted)
                    .is_some_and(|q| q != quoted)
                {
                    self.quoted_conflicts
                        .insert(expr.id, (self.env.file, expr.span));
                }
                self.check_block_as(expr.id, b, &resolved, is_task);
                if quoted {
                    self.check_quotable_block(b);
                }
                self.env.next_block_lifted = false;
                self.world.active_extensions.truncate(active_len);
            } else if let Some(Arg::BlockPass(e)) =
                call.args.iter().find(|a| matches!(a, Arg::BlockPass(_)))
            {
                match &e.kind {
                    ExprKind::Symbol(name) => {
                        // `&:name`: the block calls `name` on its argument.
                        let resolved = self.infer.resolve(&block_ty);
                        if matches!(&resolved, Type::Class(c, _) if *c == self.world.builtin.quoted)
                        {
                            let msg = format!(
                                "`&:{name}` cannot be given for a `Quoted` block parameter: write the block (`{{ |x| x.{name} }}`)"
                            );
                            if report {
                                self.error(msg.clone(), e.span);
                            }
                            return Err(msg);
                        }
                        let Type::Proc(_, params, ret, _) = resolved else {
                            return Err("invalid block type".to_string());
                        };
                        if params.len() != 1 {
                            return Err(format!("`&:{name}` needs a block with one parameter"));
                        }
                        let recv = self.infer.resolve(&params[0]);
                        let cands = self.world.lookup_methods(&recv, name);
                        // The first callable with no argument or block whose
                        // extension's bounds the receiver satisfies, as a
                        // call chooses (`sum` of an `Enumerable[T <: Int]` or
                        // `[T <: Float]`, not the one taking a block).
                        let mut bound_error = None;
                        let mut chosen = None;
                        for (m, ms) in &cands {
                            // A rejected candidate leaves no binding behind.
                            let saved = self.infer.save();
                            match self.symbol_callable(*m, ms, name) {
                                Ok(()) => {
                                    chosen = Some((*m, ms.clone()));
                                    break;
                                }
                                Err(msg) => {
                                    self.infer.restore(saved);
                                    bound_error.get_or_insert(msg);
                                }
                            }
                        }
                        if let (None, Some(msg)) = (&chosen, bound_error) {
                            if report {
                                self.error(msg.clone(), e.span);
                            }
                            return Err(msg);
                        }
                        let Some((mid, msubst)) = chosen else {
                            let msg = format!(
                                "undefined method `{name}` for {} (in `&:{name}`)",
                                self.name(&recv)
                            );
                            if report {
                                self.error(msg.clone(), e.span);
                            }
                            return Err(msg);
                        };
                        // `initialize` runs only from `new` and `super`
                        // (docs/01 §3).
                        if name == "initialize" && !self.world.method(mid).singleton {
                            let msg = format!(
                                "`initialize` is called only by `new` and by `super` in `initialize` (in `&:{name}`)"
                            );
                            if report {
                                self.error(msg.clone(), e.span);
                            }
                            return Err(msg);
                        }
                        // As Ruby's `Symbol#to_proc`, only a public method.
                        let visibility = self.world.method(mid).visibility;
                        if visibility != Visibility::Public {
                            let msg = format!(
                                "`{name}` is {} for {}: `&:{name}` calls only public methods",
                                if visibility == Visibility::Private {
                                    "private"
                                } else {
                                    "protected"
                                },
                                self.name(&recv)
                            );
                            if report {
                                self.error(msg.clone(), e.span);
                            }
                            return Err(msg);
                        }
                        let mut msubst = msubst;
                        msubst.insert(SELF_PARAM, recv.clone());
                        let r = self.world.unvoid(&self.method_ret(mid)).subst(&msubst);
                        // Given where a `Void` result is expected, the
                        // call's value is discarded, as the block's would be.
                        let discard = self.infer.resolve(&ret) == Type::Void;
                        if !discard && !self.coerce(&r, &ret) {
                            let msg = format!(
                                "`&:{name}` returns {} but {} was expected",
                                self.name(&r),
                                self.name(&ret)
                            );
                            if report {
                                self.error(msg.clone(), e.span);
                            }
                            return Err(msg);
                        }
                        // Checked again (a union receiver's members, a block
                        // once per type) with another method: called by
                        // name, which an extension's is not found by.
                        if let Some(BlockPass::Symbol(_, before, discarded)) =
                            self.out.block_pass.get(&e.id)
                        {
                            let before = *before;
                            // One procedure serves every check: it cannot
                            // both keep the value and give nil.
                            if *discarded != discard {
                                let d = Diagnostic::error(
                                    format!(
                                        "cannot tell at run time whether `&:{name}` gives the value of `{name}` or nil: one method takes a block whose result is `Void`, another one whose result is used (give the value one type first, or write the block)"
                                    ),
                                    e.span,
                                );
                                self.ambiguous
                                    .push((self.env.file, AmbiguousKey::Node(e.id), d));
                            }
                            if before != mid && !self.out.varied_symbols.contains(&e.id) {
                                self.out.varied_symbols.insert(e.id);
                                self.table_journal.push(TableUndo::VariedSymbol(e.id));
                                let ext = |m: MethodId| self.world.method(m).extension.is_some();
                                if ext(before) || ext(mid) {
                                    let (wb, wm) =
                                        (self.method_label(before), self.method_label(mid));
                                    let d = Diagnostic::error(
                                        format!(
                                            "cannot tell at run time which `{name}` `&:{name}` calls: {wb} or {wm} (give the value one type first)"
                                        ),
                                        e.span,
                                    );
                                    self.ambiguous.push((
                                        self.env.file,
                                        AmbiguousKey::Node(e.id),
                                        d,
                                    ));
                                }
                            }
                        }
                        let before = self.out.block_pass.get(&e.id).cloned();
                        self.table_journal.push(TableUndo::BlockPass(e.id, before));
                        self.out
                            .block_pass
                            .insert(expr.id, BlockPass::Symbol(name.clone(), mid, discard));
                        // Also by the symbol itself, for the lowering.
                        self.out
                            .block_pass
                            .insert(e.id, BlockPass::Symbol(name.clone(), mid, discard));
                        self.note_static_call(e, mid);
                        self.record(e.id, &self.world.symbol());
                    }
                    // The method's anonymous block, passed on: only to a
                    // method that does not keep it either, and not from a
                    // closure that may run later.
                    ExprKind::Local(name)
                        if name == "&"
                            && (m.block.as_ref().is_some_and(|(n, _)| n != "&")
                                || self.in_late_closure()
                                || Self::runs_block_in_task(&self.world, m)) =>
                    {
                        let msg = if Self::runs_block_in_task(&self.world, m) {
                            format!(
                                "the method's block (`&`) cannot be passed to `{}`, which runs it in a task: a block passed on is not checked as a task's",
                                m.name
                            )
                        } else if self.in_late_closure() {
                            "the method's block (`&`) cannot be passed on from a closure that may run later: name the block parameter (`&blk`) to keep it".to_string()
                        } else {
                            format!(
                                "the method's block (`&`) cannot be passed to `{}`, which may keep it: name the block parameter (`&blk`) to keep it",
                                m.name
                            )
                        };
                        if report {
                            self.error(msg.clone(), e.span);
                        }
                        return Err(msg);
                    }
                    _ => {
                        // `&block` may be `nil` when the callee's block may be
                        // left out.
                        let block_ty = if m.block_optional {
                            self.world.nilable(block_ty.clone())
                        } else {
                            block_ty.clone()
                        };
                        let t = self.check_expr(e, Some(&block_ty));
                        if !self.coerce(&t, &block_ty) {
                            let msg = format!(
                                "block argument has type {} but {} was expected",
                                self.name(&t),
                                self.name(&block_ty)
                            );
                            if report {
                                self.error(msg.clone(), e.span);
                            }
                            return Err(msg);
                        }
                        self.out.block_pass.insert(expr.id, BlockPass::Proc);
                    }
                }
            }
        }
        Ok(ret)
    }

    /// `static(call)` (docs/14 §8): the call of a `static def`, of a
    /// dependency, with constant receiver and arguments, whose result can
    /// be baked: checked as the call, then recorded for the runner.
    fn check_static_expr(&mut self, expr: &Expr, inner: &Expr, expected: Option<&Type>) -> Type {
        // A block given to `def_method` is copied into the generated
        // method, not lowered where it is: its value would be its call.
        if self.env.lifted_frame.is_some() {
            self.error(
                "`static(...)` cannot be used in a block given to `def_method`: compute the value in the `static def` and use it in the block (it is baked)",
                expr.span,
            );
        }
        let saved = self.static_expr_call.replace(inner.id);
        let t = self.check_expr(inner, expected);
        self.static_expr_call = saved;
        let ExprKind::Call(call) = &inner.kind else {
            self.error(
                "`static(...)` takes a call of a `static def`, run at compile time (docs/14 §8)",
                inner.span,
            );
            return t;
        };
        let errors_before = self.error_count();
        let Some(CallTarget::Method { method }) = self.out.calls.get(&inner.id).cloned() else {
            self.error(
                format!(
                    "`static(...)` takes a call of a `static def`; `{}` is not one",
                    call.name
                ),
                inner.span,
            );
            return t;
        };
        let m = self.world.method(method).clone();
        if !m.is_static || m.is_native {
            self.error(
                format!(
                    "`static(...)` takes a call of a `static def`; `{}` is not one",
                    m.name
                ),
                inner.span,
            );
            return t;
        }
        // The staging rule of `static` statements (docs/14 §2).
        let allowed = match self.repl_unit {
            Some((file, base)) => {
                if m.file == file && m.span.start >= base {
                    Err("this input".to_string())
                } else {
                    Ok(())
                }
            }
            None => self.world.static_callee_allowed(self.env.file, m.file),
        };
        if let Err(why) = allowed {
            self.error(
                format!("`{}` is a `static def` of {why}: `static(...)` runs only those of the cogs (or required files) this file depends on", m.name),
                inner.span,
            );
            return t;
        }
        // An implicit receiver names the class it is written in, whose
        // class method it must be.
        let class = self.env.class_id.unwrap_or(self.world.builtin.object);
        match &call.recv {
            Some(r) => self.check_static_constant(r),
            None if m.singleton => {}
            None => self.error(
                format!(
                    "`static({})`: the receiver of an instance `static def` is written, a constant",
                    call.name
                ),
                inner.span,
            ),
        }
        for a in &call.args {
            match a {
                Arg::Positional(x) => self.check_static_constant(x),
                Arg::BlockPass(x) if matches!(x.kind, ExprKind::Symbol(_)) => {}
                _ => self.error(
                    "`static(...)` takes positional arguments, constants",
                    inner.span,
                ),
            }
        }
        let rt = self.resolve(&t);
        if !self.bakeable_type(&rt) {
            self.error(
                format!("`static(...)` gives a {}, which cannot be baked into the program: its value must be a literal, a class or `data` of such (docs/14 §5)", self.world.type_name(&rt)),
                expr.span,
            );
        }
        if self.error_count() == errors_before {
            self.out
                .static_exprs
                .insert(expr.id, (self.env.file, class, inner.clone()));
        }
        t
    }

    /// A receiver or argument of `static(...)`: a literal (of constants),
    /// a constant, a class, or another `static(...)`.
    fn check_static_constant(&mut self, e: &Expr) {
        let ok = match &e.kind {
            ExprKind::Nil
            | ExprKind::True
            | ExprKind::False
            | ExprKind::Int(_)
            | ExprKind::Float(_)
            | ExprKind::Bytes(_)
            | ExprKind::Symbol(_)
            | ExprKind::Static(_)
            | ExprKind::TypeApp(_) => true,
            ExprKind::Str(parts) | ExprKind::Regexp { parts, .. } => {
                parts.iter().all(|p| matches!(p, StrPart::Lit(_)))
            }
            ExprKind::Const(_) => self.out.const_targets.contains_key(&e.id),
            ExprKind::Array(items) => {
                for a in items {
                    match a {
                        Arg::Positional(x) => self.check_static_constant(x),
                        _ => self.error("a splat is not a constant", e.span),
                    }
                }
                true
            }
            ExprKind::Hash(entries) => {
                for h in entries {
                    match h {
                        HashEntry::Pair { key, value } => {
                            self.check_static_constant(key);
                            self.check_static_constant(value);
                        }
                        HashEntry::DoubleSplat(_) => {
                            self.error("a double splat is not a constant", e.span)
                        }
                    }
                }
                true
            }
            ExprKind::Range { lo, hi, .. } => {
                for x in lo.iter().chain(hi.iter()) {
                    self.check_static_constant(x);
                }
                true
            }
            _ => false,
        };
        if !ok {
            self.error(
                "`static(...)`'s receiver and arguments are constants: literals, constants, classes and `static(...)` (docs/14 §8)",
                e.span,
            );
        }
    }

    /// A block given as a `Quoted` (docs/14 §6) holds only what
    /// `Meta::Expr` represents: each other construct is an error at its
    /// node. The constants whose values become literals of the tree are
    /// noted (`Output::quoted_lits`); checked after the block, so that
    /// their types are known.
    fn check_quotable_block(&mut self, b: &Block) {
        for p in &b.params.list {
            if p.kind != quarz_syntax::ast::ParamKind::Positional || p.default.is_some() {
                self.error(
                    "a quoted block takes plain parameters (no defaults, `*rest`, keywords or `&block`)",
                    p.span,
                );
            }
        }
        for e in &b.body {
            self.check_quotable(e);
        }
    }

    fn check_quotable(&mut self, e: &Expr) {
        let refuse = |what: &str| -> String {
            format!(
                "{what} cannot be quoted: a block given as a `Quoted` holds literals, variables, `self`, calls, `&&`, `||`, `!`, `if` and blocks (docs/14 §6)"
            )
        };
        let what: &str = match &e.kind {
            ExprKind::Nil
            | ExprKind::True
            | ExprKind::False
            | ExprKind::SelfRef
            | ExprKind::Int(_)
            | ExprKind::Float(_)
            | ExprKind::Bytes(_)
            | ExprKind::Symbol(_)
            | ExprKind::Local(_)
            | ExprKind::IVar(_)
            // A value computed at compile time: a literal of the tree.
            | ExprKind::Static(_) => return,
            ExprKind::Str(parts) => {
                for part in parts {
                    if let StrPart::Interp(x) = part {
                        self.check_quotable(x);
                    }
                }
                return;
            }
            ExprKind::Regexp { parts, .. } => {
                if parts.iter().all(|p| matches!(p, StrPart::Lit(_))) {
                    return;
                }
                "an interpolated regexp"
            }
            ExprKind::Array(items) => {
                for a in items {
                    match a {
                        Arg::Positional(x) => self.check_quotable(x),
                        _ => self.error(refuse("a splat"), e.span),
                    }
                }
                return;
            }
            ExprKind::Hash(entries) => {
                for h in entries {
                    match h {
                        HashEntry::Pair { key, value } => {
                            self.check_quotable(key);
                            self.check_quotable(value);
                        }
                        HashEntry::DoubleSplat(_) => self.error(refuse("a double splat"), e.span),
                    }
                }
                return;
            }
            ExprKind::Const(_) => {
                // A constant whose value is a literal, a class or data is
                // part of the tree; any other is read at the call.
                let t = self.out.node_types.get(&e.id).cloned();
                let lit = match self.out.const_targets.get(&e.id) {
                    Some(ConstTarget::Class(_) | ConstTarget::VariantSingleton(_)) => true,
                    Some(ConstTarget::Const(_)) => t.is_some_and(|t| self.bakeable_type(&t)),
                    None => false,
                };
                if lit {
                    self.out.quoted_lits.insert(e.id);
                }
                return;
            }
            ExprKind::Call(call) => {
                // A call that did not type-check was reported already.
                let Some(target) = self.out.calls.get(&e.id) else {
                    return;
                };
                let ok = matches!(
                    target,
                    CallTarget::Method { .. } | CallTarget::Constructor { .. }
                );
                if !ok {
                    let message = refuse(&format!("`{}` here", call.name));
                    self.error(message, e.span);
                    return;
                } else if call.safe_nav {
                    "`&.`"
                } else {
                    if let Some(r) = &call.recv {
                        self.check_quotable(r);
                    }
                    for a in &call.args {
                        match a {
                            Arg::Positional(x) => self.check_quotable(x),
                            // `&:name`: a block calling `name`.
                            Arg::BlockPass(x) if matches!(x.kind, ExprKind::Symbol(_)) => {}
                            Arg::BlockPass(_) => {
                                self.error(refuse("a block passed with `&`"), e.span)
                            }
                            Arg::Keyword { span, .. } => {
                                self.error(refuse("a keyword argument"), *span)
                            }
                            Arg::Splat(_) | Arg::DoubleSplat(_) => {
                                self.error(refuse("a splat"), e.span)
                            }
                        }
                    }
                    if let Some(b) = &call.block {
                        self.check_quotable_block(b);
                    }
                    return;
                }
            }
            ExprKind::And(a, b) | ExprKind::Or(a, b) => {
                self.check_quotable(a);
                self.check_quotable(b);
                return;
            }
            ExprKind::Not(a) => {
                self.check_quotable(a);
                return;
            }
            ExprKind::If { cond, then, els } => {
                self.check_quotable(cond);
                for x in then.iter().chain(els.iter().flatten()) {
                    self.check_quotable(x);
                }
                if then.len() > 1 || els.as_ref().is_some_and(|x| x.len() > 1) {
                    "a branch of several statements"
                } else {
                    return;
                }
            }
            // The expansion the checker chose (`ast::ForExpr`): calls with
            // blocks.
            ExprKind::For(f) => {
                let x = if self.out.for_loops.contains(&e.id) {
                    &f.each
                } else {
                    &f.comprehension
                };
                self.check_quotable(x);
                return;
            }
            ExprKind::DSymbol(_) => "an interpolated symbol",
            ExprKind::Range { .. } => "a range",
            ExprKind::Lambda(_) => "a lambda",
            ExprKind::Magic(_) => "a `__FILE__`-style name",
            ExprKind::TypeApp(_) => "a type",
            ExprKind::MethodRef { .. } => "a method reference",
            ExprKind::Yield(_) => "`yield`",
            ExprKind::Super { .. } => "`super`",
            ExprKind::Assign { .. }
            | ExprKind::OpAssign { .. }
            | ExprKind::MultiAssign { .. }
            | ExprKind::TypedDecl { .. } => "an assignment",
            ExprKind::While { .. } => "a loop",
            ExprKind::Case { .. } | ExprKind::CaseIn { .. } => "`case`",
            ExprKind::MatchPattern { .. } => "a pattern match",
            ExprKind::Begin(_) => "`begin`",
            ExprKind::Return(_) => "`return`",
            ExprKind::Break(_) => "`break`",
            ExprKind::Next(_) => "`next`",
            ExprKind::Retry => "`retry`",
            ExprKind::Seq(_) => "a sequence",
            _ => "a declaration",
        };
        self.error(refuse(what), e.span);
    }

    /// Check a block against the procedure type it is passed as.
    fn check_block(&mut self, call_id: NodeId, block: &Block, proc_ty: &Type) {
        self.check_block_as(call_id, block, proc_ty, false)
    }

    fn check_block_as(&mut self, call_id: NodeId, block: &Block, proc_ty: &Type, is_task: bool) {
        let Type::Proc(recv, params, ret, shareable) = proc_ty else {
            self.error("internal: block type is not a procedure", block.span);
            return;
        };
        let shareable = *shareable && !is_task;
        if shareable {
            self.out.shareable_procs.insert(call_id);
        }
        let lifted = std::mem::take(&mut self.env.next_block_lifted);
        if lifted {
            self.out.lifted_blocks.insert(call_id, proc_ty.clone());
            // The generated method's parameters are the block's, plain.
            if let Some(p) = block
                .params
                .list
                .iter()
                .find(|p| p.kind != ParamKind::Positional || p.default.is_some())
            {
                self.error(
                    "a block given to `def_method` takes plain parameters only (no `*rest`, keywords, defaults or `&block`): they become the generated method's",
                    p.span,
                );
            }
        }
        let params = params.clone();
        let ret = (**ret).clone();
        self.widen_assigned(&block.body);
        self.prescan_repeated(&block.body, true);
        // A block the method may keep may run later, as a lambda may.
        let escapes = std::mem::take(&mut self.env.next_block_escapes);
        let late =
            (escapes && !shareable && !is_task).then(|| self.enter_late_closure(&block.body));
        // A task's block copies the locals it captures, but reads `self`'s
        // fields live, as their declared types (as a late closure does).
        let saved_ivars =
            (late.is_none() && (is_task || shareable) && !self.fields_fixed_at_construction())
                .then(|| std::mem::take(&mut self.env.ivar_narrow));
        // A block with a receiver runs with `self` = the receiver: the
        // enclosing `self` stays reachable for calls it alone answers.
        let receiver = recv.as_ref().map(|t| self.resolve(t));
        let saved_self = self.enter_receiver(receiver.as_ref());
        // `retry` belongs directly in a rescue clause, not in a block or
        // lambda there (docs/01 §12).
        let saved_rescue = std::mem::take(&mut self.env.in_rescue);
        self.env.frames.push(Frame {
            vars: Vars::default(),
            is_block: true,
            owner: SelfOwner::Block(call_id),
        });
        let saved_task_frame = (self.env.task_frame, self.env.task_shareable_proc);
        // The block of the call in `static(...)`: as a task's, where any
        // capture is refused (`check_task_capture`, `check_task_self`).
        let in_static = self.static_expr_call == Some(call_id);
        let saved_static = self.env.static_frame;
        if is_task || shareable || lifted || in_static {
            self.env.task_frame = Some(self.env.frames.len() - 1);
            self.env.task_shareable_proc = shareable;
        }
        if in_static {
            self.env.static_frame = self.env.task_frame;
        }
        // A lifted block's body is run-time code (the generated method's),
        // whatever the `static def` around it may call.
        let saved_lifted = (self.env.lifted_frame, self.env.is_static);
        if lifted {
            self.env.lifted_frame = Some(self.env.frames.len() - 1);
            self.env.is_static = false;
        }
        self.env.blocks.push(BlockCtx {
            ret: ret.clone(),
            breaks: Vec::new(),
            is_lambda: false,
            // A task's block runs elsewhere, later: the method's block may
            // not be live there either.
            escapes: escapes || is_task || shareable || lifted,
            lifted,
        });
        // `break` and `next` in a block leave the block, not a loop
        // around it.
        let saved_loop = (
            std::mem::take(&mut self.env.loop_depth),
            std::mem::take(&mut self.env.loop_exits),
        );
        // Parameters: destructure a single tuple parameter over several
        // block parameters.
        let declared: Vec<&Param> = block
            .params
            .list
            .iter()
            .filter(|p| p.kind != ParamKind::Block)
            .collect();
        let mut param_types: Vec<Type> = params.clone();
        if declared.len() > 1 && params.len() == 1 {
            match self.infer.resolve(&params[0]) {
                Type::Tuple(ts) => {
                    param_types = ts;
                    self.out.block_destructure.insert(call_id, declared.len());
                }
                // An array is spread over the parameters, as in Ruby.
                Type::Class(id, args) if id == self.world.builtin.array && args.len() == 1 => {
                    param_types = vec![args[0].clone(); declared.len()];
                    self.out.block_destructure.insert(call_id, declared.len());
                }
                _ => {}
            }
        }
        if declared.len() > param_types.len() {
            self.error(
                format!(
                    "block takes {} parameter(s) but {} are declared",
                    param_types.len(),
                    declared.len()
                ),
                block.span,
            );
        }
        for (i, p) in declared.iter().enumerate() {
            let mut t = param_types
                .get(i)
                .cloned()
                .unwrap_or_else(|| self.world.nil());
            if let Some(te) = &p.ty {
                let scope = self.env.scope.clone();
                if let Some(annotated) = self.resolve_type_expr(te, &scope) {
                    if !self.coerce(&t, &annotated) {
                        self.error(
                            format!(
                                "block parameter `{}` is annotated {} but receives {}",
                                p.name,
                                self.name(&annotated),
                                self.name(&t)
                            ),
                            te.span,
                        );
                    }
                    t = annotated;
                }
            }
            if p.kind == ParamKind::Rest {
                t = self.world.array_of(t);
            }
            self.declare_var(&p.name, t, p.span);
        }
        let void = self.infer.resolve(&ret) == Type::Void;
        self.next_body_void = void;
        let bt = self.check_body(&block.body, if void { None } else { Some(&ret) });
        self.mark_discarded(block.body.last(), void);
        // A task's result reaches the task that awaits it.
        if is_task && !void && !bt.is_nothing() {
            let rt = self.resolve(&bt);
            if !rt.has_vars() && !self.world.is_shareable(&rt) {
                let span = block.body.last().map(|e| e.span).unwrap_or(block.span);
                self.error(
                    format!(
                        "a task block returns the non-shareable type {}, but its value \
                         passes to the task that awaits it",
                        self.world.type_name(&rt)
                    ),
                    span,
                );
            }
        }
        // A block lifted to a method's body that never returns (it only
        // raises: `return` and `break` it cannot use, and a `next`
        // would have typed the result) gives the method the result type
        // `Nothing` (docs/14 §5), rather than one nothing settles.
        // The result is bound to `Nothing` (not only recorded so): a
        // `next` whose value's type is settled later in the `static
        // def` then has to be `Nothing` too, an error otherwise.
        if lifted && bt.is_nothing() && matches!(self.infer.resolve(&ret), Type::Var(_)) {
            self.coerce(&ret, &Type::Nothing);
        }
        if !void && !bt.is_nothing() && !self.coerce(&bt, &ret) {
            let span = block.body.last().map(|e| e.span).unwrap_or(block.span);
            self.error(
                format!(
                    "block returns {} but {} was expected",
                    self.name(&bt),
                    self.name(&ret)
                ),
                span,
            );
        }
        let frame = self.env.frames.pop().unwrap();
        self.env.in_rescue = saved_rescue;
        self.note_frame_vars(&frame);
        let breaks = self.env.blocks.pop().unwrap().breaks;
        if let Some((first, rest)) = breaks.split_first() {
            let t = rest.iter().fold(first.clone(), |a, b| self.join(&a, b));
            self.breaking_blocks.insert(call_id, t);
        } else {
            self.breaking_blocks.remove(&call_id);
        }
        (self.env.loop_depth, self.env.loop_exits) = saved_loop;
        (self.env.task_frame, self.env.task_shareable_proc) = saved_task_frame;
        self.env.static_frame = saved_static;
        (self.env.lifted_frame, self.env.is_static) = saved_lifted;
        self.leave_receiver(saved_self);
        self.out
            .frame_sizes
            .insert(call_id, frame.vars.len() as u32);
        if let Some(ivars) = saved_ivars {
            self.env.ivar_narrow = ivars;
        }
        match late {
            Some(snap) => self.leave_late_closure(&snap, &block.body),
            None => self.widen_assigned(&block.body),
        }
    }

    /// Make `recv` the `self` of the block being checked (nothing for
    /// `None`); returns what `leave_receiver` restores.
    #[allow(clippy::type_complexity)]
    fn enter_receiver(
        &mut self,
        recv: Option<&Type>,
    ) -> Option<(Type, Option<ClassId>, bool, HashMap<String, Type>)> {
        let recv = recv?;
        // Another object's fields are not being initialized, nor narrowed.
        let in_initialize = std::mem::take(&mut self.env.in_initialize);
        let ivar_narrow = std::mem::take(&mut self.env.ivar_narrow);
        let outer_self = std::mem::replace(&mut self.env.self_type, recv.clone());
        let class = match recv {
            Type::Class(id, _) => Some(*id),
            _ => None,
        };
        let outer_class = std::mem::replace(&mut self.env.class_id, class);
        self.env.receivers.push(ReceiverCtx {
            outer_self: outer_self.clone(),
            outer_frame: self.env.frames.len() - 1,
        });
        Some((outer_self, outer_class, in_initialize, ivar_narrow))
    }

    #[allow(clippy::type_complexity)]
    fn leave_receiver(
        &mut self,
        saved: Option<(Type, Option<ClassId>, bool, HashMap<String, Type>)>,
    ) {
        if let Some((self_type, class_id, in_initialize, ivar_narrow)) = saved {
            self.env.receivers.pop();
            self.env.self_type = self_type;
            self.env.class_id = class_id;
            self.env.in_initialize = in_initialize;
            self.env.ivar_narrow = ivar_narrow;
        }
    }

    /// Fields are reachable only from their class's own body: inside a
    /// block with another receiver, `@x` is an error.
    /// Whether `self` here is the `self` of the code around the innermost
    /// `spawn` (or `Task.blocking`) block, captured by it (and not the
    /// receiver of a block run with `instance_exec` inside the task).
    fn self_crosses_task(&self) -> bool {
        match self.env.task_frame {
            // A block given to `def_method` has a receiver: its `self` is
            // the generated method's, not captured.
            Some(tf) => !self.env.receivers.iter().any(|r| {
                r.outer_frame >= tf
                    || (self.env.lifted_frame == Some(tf) && r.outer_frame + 1 == tf)
            }),
            None => false,
        }
    }

    /// A task block captures `self` like a variable: it must be Shareable.
    fn check_task_self(&mut self, what: &str, span: Span) {
        if !self.self_crosses_task() {
            return;
        }
        if self.env.static_frame.is_some() && self.env.static_frame == self.env.task_frame {
            self.error(
                format!("a block in `static(...)` captures nothing: {what} is not a constant (docs/14 §8)"),
                span,
            );
            return;
        }
        let t = self.resolve(&self.env.self_type.clone());
        if t.has_vars() || self.world.is_shareable(&t) {
            return;
        }
        self.error(
            format!(
                "{what} has the non-shareable type {} and cannot be captured by {}",
                self.world.type_name(&t),
                self.task_capture_name()
            ),
            span,
        );
    }

    fn check_ivar_access(&mut self, span: Span) -> bool {
        self.check_task_self("`self` (for its instance variables)", span);
        if !self.env.receivers.is_empty() && self.env.class_id != self.env.lexical_class {
            let recv = self.name(&self.env.self_type.clone());
            self.error(
                format!("instance variables of {recv} are not accessible from this block (it runs with `self` = {recv})"),
                span,
            );
            return false;
        }
        // In a class method or a class body, `self` is the class: it has
        // no fields.
        if self.env.receivers.is_empty()
            && matches!(self.env.self_type, Type::ClassObject(..) | Type::TypeOf(_))
        {
            self.error(
                "instance variables are not available here: `self` is a class (in a class method or a class body)",
                span,
            );
            return false;
        }
        true
    }

    fn check_lambda(&mut self, id: NodeId, block: &Block, expected: Option<&Type>) -> Type {
        // The expected procedure, also as the one procedure of a union
        // (an optional argument, `f: ((A) -> R)? = nil`).
        let expected_proc_type = match expected.map(|e| self.resolve(e)) {
            Some(Type::Union(ms)) => {
                let mut procs = ms.into_iter().filter(|m| matches!(m, Type::Proc(..)));
                match (procs.next(), procs.next()) {
                    (Some(p), None) => Some(p),
                    _ => None,
                }
            }
            other => other,
        };
        let (expected_recv, expected_proc, shareable) = match expected_proc_type {
            Some(Type::Proc(rc, ps, r, sh)) => (rc.map(|t| *t), Some((ps, *r)), sh),
            _ => (None, None, false),
        };
        self.widen_assigned(&block.body);
        self.prescan_repeated(&block.body, true);
        // A lambda may run later, after what it captures has changed (a
        // shareable one copies what it captures, and assigns none of it).
        let late = (!shareable).then(|| self.enter_late_closure(&block.body));
        // A shareable one reads `self`'s fields live, as a task's block.
        let saved_ivars = (shareable && !self.fields_fixed_at_construction())
            .then(|| std::mem::take(&mut self.env.ivar_narrow));
        let mut param_types = Vec::new();
        let saved_self = self.enter_receiver(expected_recv.as_ref());
        // `retry` belongs directly in a rescue clause, not in a block or
        // lambda there (docs/01 §12).
        let saved_rescue = std::mem::take(&mut self.env.in_rescue);
        self.env.frames.push(Frame {
            vars: Vars::default(),
            is_block: true,
            owner: SelfOwner::Block(id),
        });
        // Where a shareable procedure is expected, the lambda is one: it
        // copies what it captures, which must be Shareable.
        let saved_task_frame = (self.env.task_frame, self.env.task_shareable_proc);
        if shareable {
            self.out.shareable_procs.insert(id);
            self.env.task_frame = Some(self.env.frames.len() - 1);
            self.env.task_shareable_proc = true;
        }
        // `->(x: Int) -> R { }`: the declared result, else the expected
        // one, else inferred from the body.
        let declared = block.ret.as_ref().map(|te| {
            let scope = self.env.scope.clone();
            self.resolve_result_type_expr(te, &scope)
                .unwrap_or(Type::Nothing)
        });
        let ret_var = match (&declared, &expected_proc) {
            (Some(d), _) => d.clone(),
            (None, Some((_, r))) => r.clone(),
            (None, None) => self.infer.fresh(),
        };
        self.env.blocks.push(BlockCtx {
            ret: ret_var.clone(),
            breaks: Vec::new(),
            is_lambda: true,
            escapes: true,
            lifted: false,
        });
        // `break` and `next` here do not leave a loop around the lambda.
        let saved_loop = (
            std::mem::take(&mut self.env.loop_depth),
            std::mem::take(&mut self.env.loop_exits),
        );
        for (i, p) in block.params.list.iter().enumerate() {
            let t = match &p.ty {
                Some(te) => {
                    let scope = self.env.scope.clone();
                    self.resolve_type_expr(te, &scope).unwrap_or(Type::Nothing)
                }
                None => match expected_proc.as_ref().and_then(|(ps, _)| ps.get(i)) {
                    Some(t) => t.clone(),
                    None => {
                        self.error(
                            format!("lambda parameter `{}` needs a type", p.name),
                            p.span,
                        );
                        Type::Nothing
                    }
                },
            };
            param_types.push(t.clone());
            self.declare_var(&p.name, t, p.span);
        }
        let void = self.infer.resolve(&ret_var) == Type::Void;
        self.next_body_void = void;
        let bt = self.check_body(
            &block.body,
            if declared.is_some() && !void {
                Some(&ret_var)
            } else {
                None
            },
        );
        self.mark_discarded(block.body.last(), void);
        if !void && !bt.is_nothing() && !self.coerce(&bt, &ret_var) {
            self.error(
                format!(
                    "lambda returns {} but {} was expected",
                    self.name(&bt),
                    self.name(&ret_var)
                ),
                block.span,
            );
        }
        (self.env.task_frame, self.env.task_shareable_proc) = saved_task_frame;
        (self.env.loop_depth, self.env.loop_exits) = saved_loop;
        let frame = self.env.frames.pop().unwrap();
        self.env.in_rescue = saved_rescue;
        self.note_frame_vars(&frame);
        self.env.blocks.pop();
        self.leave_receiver(saved_self);
        if let Some(ivars) = saved_ivars {
            self.env.ivar_narrow = ivars;
        }
        if let Some(snap) = late {
            self.leave_late_closure(&snap, &block.body);
        }
        self.out.frame_sizes.insert(id, frame.vars.len() as u32);
        let ret = self.infer.resolve(&ret_var);
        Type::Proc(
            expected_recv.map(Box::new),
            param_types,
            Box::new(ret),
            shareable,
        )
    }

    fn check_yield(&mut self, expr: &Expr, args: &[Arg]) -> Type {
        if self.env.lifted_frame.is_some() {
            self.error(
                "`yield` in a block given to `def_method`: the generated method has no block to yield to",
                expr.span,
            );
        }
        // The method's anonymous block runs only while the method does.
        if self.in_late_closure() && self.lookup_var("&").is_some() {
            self.error(
                "`yield` in a closure that may run later: the method's block may be gone by then; name the block parameter (`&blk`) to keep it, and call it",
                expr.span,
            );
        }
        let bt = self.env.block_type.clone();
        // A `Quoted` is a value, not run with `yield` (docs/14 §6).
        let quoted = self.world.builtin.quoted;
        if matches!(&bt, Some(Type::Class(c, _)) if *c == quoted) {
            self.error(
                "`yield` cannot run a `Quoted` block: run its closure with `block.proc.call(...)`",
                expr.span,
            );
            self.check_args_blindly(&Call {
                recv: None,
                name: String::new(),
                args: args.to_vec(),
                block: None,
                safe_nav: false,
                has_parens: true,
                type_args: Vec::new(),
            });
            return Type::Nothing;
        }
        let Some(bt) = bt.filter(|_| !self.env.block_optional) else {
            if self.env.block_optional {
                self.error(
                    "`yield` cannot run an optional block; call it with `block.call` where it is not `nil`",
                    expr.span,
                );
            } else {
                self.error("`yield` in a method without a block parameter", expr.span);
            }
            self.check_args_blindly(&Call {
                recv: None,
                name: String::new(),
                args: args.to_vec(),
                block: None,
                safe_nav: false,
                has_parens: true,
                type_args: vec![],
            });
            return Type::Nothing;
        };
        let Type::Proc(recv, params, ret, _) = bt else {
            return Type::Nothing;
        };
        if recv.is_some() {
            self.error(
                "`yield` cannot run a block with a receiver; name the block parameter and call `recv.instance_exec(&name)`",
                expr.span,
            );
            self.check_args_blindly(&Call {
                recv: None,
                name: String::new(),
                args: args.to_vec(),
                block: None,
                safe_nav: false,
                has_parens: true,
                type_args: vec![],
            });
            return Type::Nothing;
        }
        let positional: Vec<&Expr> = args
            .iter()
            .filter_map(|a| match a {
                Arg::Positional(e) => Some(e),
                _ => None,
            })
            .collect();
        if positional.len() != params.len() {
            self.error(
                format!(
                    "the block takes {} argument(s), `yield` passes {}",
                    params.len(),
                    positional.len()
                ),
                expr.span,
            );
            for e in positional {
                self.check_expr(e, None);
            }
            return self.world.unvoid(&ret);
        }
        for (e, p) in positional.iter().zip(params.iter()) {
            let t = self.check_expr(e, Some(p));
            if !self.coerce(&t, p) {
                self.error(
                    format!(
                        "`yield` passes {} where the block expects {}",
                        self.name(&t),
                        self.name(p)
                    ),
                    e.span,
                );
            }
        }
        self.world.unvoid(&ret)
    }

    fn check_super(&mut self, expr: &Expr, args: Option<&[Arg]>, block: Option<&Block>) -> Type {
        let Some(mid) = self.env.method else {
            self.error("`super` outside of a method", expr.span);
            return Type::Nothing;
        };
        let m = self.world.method(mid).clone();
        if m.name == "initialize" && !m.singleton && !self.env.blocks.is_empty() {
            // A block or lambda may run after `initialize` (its callee or
            // a field may keep it) and would then assign the immutable
            // inherited fields again (as Swift's `super.init`; docs/01 §3).
            self.error(
                "`super` in `initialize` must be called directly, not from a block or lambda",
                expr.span,
            );
            self.check_args_blindly(&Call {
                recv: None,
                name: m.name.clone(),
                args: args.map(|a| a.to_vec()).unwrap_or_default(),
                block: block.cloned(),
                safe_nav: false,
                has_parens: true,
                type_args: vec![],
            });
            return Type::Nothing;
        }
        let owner = m.owner;
        // The definitions the method hides: those of the first owner after
        // its own group in the lookup order that has the method (an
        // ancestor's own and its extensions' in scope; for an extension's
        // method, its target's own first, as `super` in a Ruby refinement,
        // docs/01 §7), chosen among as a call's overloads are (docs/01 §9);
        // none further, as Ruby's `super`.
        let self_ty = self.env.self_type.clone();
        // An extension is not active in its own body unless `using`-ed
        // there: its method is listed (as the group to pass) only while it
        // is, last among the extensions in scope.
        let own_ext = m
            .extension
            .filter(|e| !self.world.active_extensions.contains(e));
        if let Some(e) = own_ext {
            self.world.active_extensions.push(e);
        }
        let found = self.world.lookup_methods(&self_ty, &m.name);
        if own_ext.is_some() {
            self.world.active_extensions.pop();
        }
        let mut after_own = false;
        let mut next_owner = None;
        let mut cands = Vec::new();
        for (c, subst) in found {
            let cm = self.world.method(c);
            let own_group = match m.extension {
                Some(e) => cm.extension == Some(e),
                None => cm.owner == owner && cm.extension.is_none(),
            };
            if own_group {
                after_own = true;
                continue;
            }
            if !after_own || cm.singleton != m.singleton {
                continue;
            }
            if *next_owner.get_or_insert(cm.owner) != cm.owner {
                break;
            }
            cands.push((c, subst));
        }
        if cands.is_empty() {
            self.error(format!("no superclass method `{}`", m.name), expr.span);
            return Type::Nothing;
        }
        let call = Call {
            recv: None,
            name: m.name.clone(),
            args: match args {
                Some(a) => a.to_vec(),
                None => {
                    // zsuper: forward the parameters, each read as a
                    // local of its own node (the ids are outside the
                    // file's range, and nothing is recorded for them
                    // beyond this resolution).
                    let local = |i: usize, name: &str| Expr {
                        id: u32::MAX - 1 - i as u32,
                        span: expr.span,
                        kind: ExprKind::Local(name.to_string()),
                    };
                    let mut forwarded: Vec<Arg> = m
                        .params
                        .iter()
                        .enumerate()
                        .map(|(i, p)| {
                            let e = local(i, &p.name);
                            match p.kind {
                                ParamKind::KeywordOnly => Arg::Keyword {
                                    name: p.name.clone(),
                                    value: e,
                                    span: expr.span,
                                },
                                ParamKind::Rest => Arg::Splat(e),
                                ParamKind::KeywordRest => Arg::DoubleSplat(e),
                                ParamKind::Positional | ParamKind::Block => Arg::Positional(e),
                            }
                        })
                        .collect();
                    // The method's block too (`&` when anonymous), unless
                    // the `super` has one of its own. An optional block
                    // is not written: the superclass may take none, and
                    // one that takes an optional block gets it at run
                    // time all the same.
                    if let (Some((name, _)), false, None) = (&m.block, m.block_optional, block) {
                        forwarded.push(Arg::BlockPass(local(m.params.len(), name)));
                    }
                    forwarded
                }
            },
            block: block.cloned(),
            safe_nav: false,
            has_parens: true,
            type_args: vec![],
        };
        let t = self.resolve_overloads_as(
            expr,
            &call,
            &self_ty,
            cands,
            true,
            None,
            m.name == "initialize",
        );
        if let Some(CallTarget::Method { method }) = self.out.calls.get(&expr.id).cloned() {
            self.out.calls.insert(expr.id, CallTarget::Super { method });
        }
        if m.name == "initialize" {
            // The superclass initialize assigned its fields, perhaps other
            // values than the ones narrowed before (the class's own it
            // cannot assign).
            for name in self.inherited_fields() {
                self.env.ivar_narrow.remove(&name);
                self.env.assigned_fields.insert(name);
            }
        }
        t
    }

    fn check_raise(&mut self, expr: &Expr, call: &Call) -> Type {
        if let Some(b) = &call.block {
            self.error("`raise` takes no block", b.span);
        }
        let args: Vec<&Expr> = call
            .args
            .iter()
            .filter_map(|a| match a {
                Arg::Positional(e) => Some(e),
                _ => None,
            })
            .collect();
        if call.args.is_empty() {
            // The parser gives a bare `raise` in a `rescue` clause the
            // exception to re-raise.
            self.error("a bare `raise` re-raises only inside `rescue`", expr.span);
            return Type::Nothing;
        }
        if args.len() != call.args.len() || args.len() > 2 {
            self.error(
                "`raise` takes an exception class, an exception, or a message",
                expr.span,
            );
            self.check_args_blindly(call);
            return Type::Nothing;
        }
        let first = self.check_expr(args[0], None);
        let first = self.resolve(&first);
        let mut new = None;
        match &first {
            Type::ClassObject(cid, _) => {
                let cid = *cid;
                if let Some(msg) = args.get(1) {
                    let t = self.check_expr(msg, None);
                    let s = self.world.string();
                    if !self.coerce(&t, &s) {
                        self.error("the exception message must be a String", msg.span);
                    }
                }
                if !self.world.is_exception_class(cid) {
                    self.error(
                        format!("`{}` is not an exception class", self.world.class(cid).name),
                        args[0].span,
                    );
                } else if !self.names_class(args[0]) {
                    // A `Type[E]` value may be a subclass whose
                    // `initialize` takes other arguments (as for `new`).
                    self.error(
                        "cannot raise a class value: its `initialize` is not known; raise the class by name or build the exception",
                        args[0].span,
                    );
                } else if self.world.class(cid).is_abstract {
                    self.error(
                        format!("cannot instantiate `{}`", self.world.class(cid).name),
                        args[0].span,
                    );
                } else if self.has_own_new(cid) {
                    // (`raise` builds with `initialize`, not a `new` the
                    // class defines.)
                    self.error(
                        format!(
                            "`{0}` defines or inherits `self.new`: build the exception (`{0}.new(...)`) and raise it",
                            self.world.class(cid).name
                        ),
                        args[0].span,
                    );
                } else {
                    // Built as `K.new(message)`; without one, as
                    // `K.new("K")`, or `K.new()` when `initialize` takes
                    // no String but needs nothing (`SystemExit`).
                    let with_message = args.len() > 1;
                    let found = match self.initialize_taking_string(cid) {
                        Some(init) => Some((cid, init, true)),
                        None if !with_message => self
                            .initialize_taking_nothing(cid)
                            .map(|init| (cid, init, false)),
                        None => None,
                    };
                    let name = self.world.class(cid).name.clone();
                    match found {
                        Some(n) => new = Some(n),
                        None if with_message => self.error(
                            format!("`raise {name}, message` builds `{name}.new(message)`, but `{name}#initialize` does not take one String: build the exception and raise it"),
                            args[0].span,
                        ),
                        None => self.error(
                            format!("`raise {name}` builds `{name}.new(\"{name}\")` or `{name}.new`, but `{name}#initialize` takes neither: build the exception and raise it"),
                            args[0].span,
                        ),
                    }
                }
            }
            Type::Class(cid, _) if *cid == self.world.builtin.string => {
                if args.len() > 1 {
                    self.error("`raise` with a message takes no second argument", expr.span);
                }
            }
            Type::Class(cid, _) if self.world.is_exception_class(*cid) => {
                if args.len() > 1 {
                    self.error(
                        "`raise` with an exception object takes no second argument",
                        expr.span,
                    );
                }
            }
            // `rescue IOError, SystemCallError => e` then `raise e`, and
            // `error: E` with `E <: Exception` (`extension Result[T, E <: Exception]`).
            Type::Union(_) | Type::Param(_)
                if self
                    .world
                    .is_subtype(&first, &Type::class(self.world.builtin.exception)) =>
            {
                if args.len() > 1 {
                    self.error(
                        "`raise` with an exception object takes no second argument",
                        expr.span,
                    );
                }
            }
            _ => self.error(format!("cannot raise {}", self.name(&first)), args[0].span),
        }
        self.out.calls.insert(expr.id, CallTarget::Raise { new });
        Type::Nothing
    }

    /// Whether `e` names a class (or an alias of one), rather than giving
    /// a class value that may be a subclass.
    fn names_class(&self, e: &Expr) -> bool {
        match self.out.const_targets.get(&e.id) {
            Some(ConstTarget::Class(_)) => true,
            Some(ConstTarget::Const(c)) => {
                matches!(
                    self.world.through_alias(Member::Const(*c)),
                    Member::Class(_)
                )
            }
            _ => false,
        }
    }

    /// The `initialize` a `cid.new()` runs, when one needs no argument.
    fn initialize_taking_nothing(&self, cid: ClassId) -> Option<MethodId> {
        let mut cur = Some(cid);
        while let Some(c) = cur {
            let class = self.world.class(c);
            if let Some(ids) = class.methods.get("initialize") {
                return ids.iter().copied().find(|&m| {
                    self.world.method(m).params.iter().all(|p| {
                        p.default.is_some()
                            || matches!(p.kind, ParamKind::Rest | ParamKind::KeywordRest)
                    })
                });
            }
            cur = class.superclass.as_ref().and_then(|t| match t {
                Type::Class(id, _) => Some(*id),
                _ => None,
            });
        }
        None
    }

    /// Whether `cid` or a superclass defines a singleton `new`.
    fn has_own_new(&self, cid: ClassId) -> bool {
        let mut cur = Some(cid);
        while let Some(c) = cur {
            let class = self.world.class(c);
            if class.singleton_methods.contains_key("new") {
                return true;
            }
            cur = class.superclass.as_ref().and_then(|t| match t {
                Type::Class(id, _) => Some(*id),
                _ => None,
            });
        }
        false
    }

    /// The `initialize` a `cid.new(message)` runs, when one takes a single
    /// positional String (its other parameters optional): of a class's
    /// own overloads, one taking exactly a String first, as overload
    /// resolution picks.
    fn initialize_taking_string(&self, cid: ClassId) -> Option<MethodId> {
        let s = self.world.string();
        let mut cur = Some(cid);
        while let Some(c) = cur {
            let class = self.world.class(c);
            if let Some(ids) = class.methods.get("initialize") {
                let fits = |m: MethodId| {
                    let params = &self.world.method(m).params;
                    params.first().is_some_and(|p| {
                        p.kind == ParamKind::Positional && self.world.is_subtype(&s, &p.ty)
                    }) && params[1..].iter().all(|p| {
                        p.default.is_some()
                            || matches!(p.kind, ParamKind::Rest | ParamKind::KeywordRest)
                    })
                };
                // The most specific: one whose String parameter's type is
                // within every other fitting one's (as `new` resolves).
                let fitting: Vec<MethodId> = ids.iter().copied().filter(|&m| fits(m)).collect();
                let first_ty = |m: MethodId| self.world.method(m).params[0].ty.clone();
                return fitting
                    .iter()
                    .copied()
                    .find(|&m| {
                        fitting
                            .iter()
                            .all(|&o| self.world.is_subtype(&first_ty(m), &first_ty(o)))
                    })
                    .or_else(|| fitting.first().copied());
            }
            cur = class.superclass.as_ref().and_then(|t| match t {
                Type::Class(id, _) => Some(*id),
                _ => None,
            });
        }
        None
    }

    fn check_type_test(&mut self, expr: &Expr, call: &Call, recv: &Expr) -> Type {
        let rt = self.check_expr(recv, None);
        let Arg::Positional(arg) = &call.args[0] else {
            self.error("expected a type", call.args[0].span());
            return Type::Nothing;
        };
        let scope = self.env.scope.clone();
        let target = match &arg.kind {
            ExprKind::Const(path) => {
                let te = TypeExpr {
                    span: arg.span,
                    kind: TypeExprKind::Named {
                        path: path.clone(),
                        args: vec![],
                    },
                };
                self.resolve_type_expr(&te, &scope)
            }
            ExprKind::TypeApp(te) => self.resolve_type_expr(te, &scope),
            _ => {
                self.error("expected a type", arg.span);
                None
            }
        };
        let Some(target) = target else {
            return Type::Nothing;
        };
        self.record(
            arg.id,
            &Type::ClassObject(
                target.class_id().unwrap_or(self.world.builtin.object),
                vec![],
            ),
        );
        let rt = self.resolve(&rt);
        self.check_testable(&rt, &target, &call.name, arg.span);
        let checked = rt.members().iter().any(|m| {
            target
                .members()
                .iter()
                .any(|t| self.may_be_of_class(m, t) && !self.world.is_subtype(m, t))
        });
        if checked {
            self.out.element_tests.insert(expr.id);
        }
        match call.name.as_str() {
            "is_a?" => {
                self.out.calls.insert(expr.id, CallTarget::IsA(target));
                self.world.bool_()
            }
            "as" => {
                let (yes, _) = self.split_by_type(&rt, &target);
                if yes.is_nothing() {
                    self.warning(
                        format!(
                            "{} is never {}; `as` will always raise",
                            self.name(&rt),
                            self.name(&target)
                        ),
                        expr.span,
                    );
                }
                self.out.calls.insert(
                    expr.id,
                    CallTarget::As {
                        ty: target.clone(),
                        optional: false,
                    },
                );
                target
            }
            _ => {
                self.out.calls.insert(
                    expr.id,
                    CallTarget::As {
                        ty: target.clone(),
                        optional: true,
                    },
                );
                self.world.nilable(target)
            }
        }
    }
}

impl Checker {
    /// `x.as(T)`/`x.is_a?(T)` check at run time the class, and the
    /// elements of built-in collections and tuples. Other type arguments
    /// (`Box[Int]`, a procedure's parameters) are not checked, so a value
    /// that may be of the class must already be of the type.
    pub(crate) fn check_testable(&mut self, rt: &Type, target: &Type, op: &str, span: Span) {
        let rt = self.resolve(rt);
        // Against `Shareable` (or a module that promises it), the run-time
        // test sees the class only: of a value Shareable by its arguments
        // or elements (`[counter]` is an `Array`, which includes
        // `Shareable`), it would answer yes (docs/03).
        for tm in target.members() {
            let Type::Class(tid, _) = &tm else { continue };
            let tid = *tid;
            let promising = tid == self.world.builtin.shareable
                || (self.world.class(tid).kind == ClassKind::Module
                    && self.world.shareable_promise(tid).is_some());
            if !promising {
                continue;
            }
            for m in rt.members() {
                if self.world.is_subtype(&m, &tm)
                    || !self.may_be_of_class(&m, &tm)
                    || !self.shareable_by_args(&m)
                {
                    continue;
                }
                self.error(
                    format!(
                        "`{op}` cannot be checked at run time against {}: whether a value of type {} is Shareable depends on what it holds, which the test does not see",
                        self.name(&tm),
                        self.name(&m)
                    ),
                    span,
                );
                return;
            }
        }
        for tm in target.members() {
            if !self.unverifiable(&tm) {
                continue;
            }
            for m in rt.members() {
                if self.world.is_subtype(&m, &tm) || !self.may_be_of_class(&m, &tm) {
                    continue;
                }
                self.error(
                    format!(
                        "`{op}` cannot check at run time that a value of type {} is a {} (type arguments are not known then)",
                        self.name(&m),
                        self.name(&tm)
                    ),
                    span,
                );
                return;
            }
        }
    }

    /// Whether a value of type `t` may be one whose Shareability depends on
    /// its arguments or elements, which a run-time class test does not see:
    /// a collection, a tuple, a generic `data` type or enum, or what may
    /// hold one (`Object`, a module, a parameter not bounded Shareable).
    fn shareable_by_args(&mut self, t: &Type) -> bool {
        let b = self.world.builtin.clone();
        match t {
            Type::Class(id, args) => {
                let class = self.world.class(*id);
                *id == b.object
                    || class.kind == ClassKind::Module
                    || (!args.is_empty()
                        && (self.world.is_value_class(*id)
                            || matches!(
                                class.kind,
                                ClassKind::Data | ClassKind::Enum | ClassKind::Variant
                            )))
            }
            Type::Tuple(_) => true,
            Type::Param(_) => !self.world.is_shareable(t),
            Type::Union(ms) => ms.clone().iter().any(|m| self.shareable_by_args(m)),
            _ => false,
        }
    }

    /// Whether the run-time test of `t` leaves part of it unchecked: a
    /// type parameter as an argument (the elements' `T` is not known at
    /// run time), or arguments of a class other than the built-in
    /// collections (whose elements are checked), except `Object` for a
    /// covariant parameter.
    fn unverifiable(&self, t: &Type) -> bool {
        let b = &self.world.builtin;
        let object = |a: &Type| matches!(a, Type::Class(id, _) if *id == b.object);
        match t {
            Type::Class(id, args) if [b.array, b.set, b.hash, b.range].contains(id) => {
                args.iter().any(|a| !object(a) && self.unverifiable_arg(a))
            }
            Type::Class(id, args) => args
                .iter()
                .enumerate()
                .any(|(i, a)| !(object(a) && self.world.param_admits_object(*id, i))),
            // A class value is tested as "a class": `Type[Object]` only.
            Type::ClassObject(id, _) => *id != b.object,
            Type::Tuple(ts) | Type::Union(ts) => ts.iter().any(|m| self.unverifiable(m)),
            Type::Proc(..) => true,
            // A type parameter is not known at run time (`o.as(T)`).
            Type::Param(_) | Type::TypeOf(_) => true,
            Type::Nothing | Type::Void | Type::Var(_) => false,
        }
    }

    /// `unverifiable` for a type argument or element type: a type
    /// parameter there is not known at run time.
    fn unverifiable_arg(&self, t: &Type) -> bool {
        match t {
            Type::Param(_) => true,
            Type::Union(ms) | Type::Tuple(ms) => ms.iter().any(|m| self.unverifiable_arg(m)),
            _ => self.unverifiable(t),
        }
    }

    /// Whether a value of type `m` may pass the class test of `t`.
    fn may_be_of_class(&self, m: &Type, t: &Type) -> bool {
        let class_of = |t: &Type| match t {
            Type::Class(id, _) => Some(*id),
            Type::Tuple(_) => Some(self.world.builtin.array),
            Type::Proc(..) => Some(self.world.builtin.proc_),
            _ => None,
        };
        match (m, t) {
            (Type::Param(_) | Type::Var(_), _) | (_, Type::Param(_)) => true,
            (Type::ClassObject(..) | Type::TypeOf(_), Type::ClassObject(..) | Type::TypeOf(_)) => {
                true
            }
            // `in Type`: a class value is an instance of `Type`; an
            // `Object` or a `Type` may hold one.
            (Type::ClassObject(..) | Type::TypeOf(_), Type::Class(id, _))
            | (Type::Class(id, _), Type::ClassObject(..) | Type::TypeOf(_)) => {
                *id == self.world.builtin.class_ || *id == self.world.builtin.object
            }
            _ => match (class_of(m), class_of(t)) {
                (Some(mc), Some(tc)) => {
                    self.world.class_is_a(mc, tc)
                        || self.world.class_is_a(tc, mc)
                        || self.world.class(mc).kind == ClassKind::Module
                        || self.world.class(tc).kind == ClassKind::Module
                }
                _ => false,
            },
        }
    }

    /// Narrowings established when `value` matches `pattern`, with pattern
    /// variables declared. Used by `in` conditions and `=>`.
    fn check_pattern_facts(&mut self, pattern: &Pattern, value_ty: &Type, value: &Expr) -> Facts {
        let narrowed = self.check_pattern(pattern, value_ty);
        match self.var_key(value) {
            // A pattern that rebinds the subject leaves it the binding's
            // type (`bound_if_matched`).
            Some(VarKey::Local(n)) if pattern.binds(&n) => Vec::new(),
            Some(key) => vec![(key, narrowed)],
            None => Vec::new(),
        }
    }
}

// Re-export for the pattern module.
pub(crate) use VarKey as PatternVarKey;

impl Checker {
    pub(crate) fn declare_pattern_var(&mut self, name: &str, ty: Type, span: Span) {
        let existing = self.lookup_var(name).filter(|(depth, slot)| {
            !(*depth == 0 && self.env.pattern_base.is_some_and(|base| *slot >= base))
        });
        if let Some((depth, slot)) = existing {
            // Re-binding an existing variable: it must accept the type.
            let declared = {
                let n = self.env.frames.len();
                self.env.frames[n - 1 - depth].vars[slot].declared.clone()
            };
            if !self.coerce(&ty, &declared) {
                self.error(
                    format!(
                        "pattern binds `{name}` to {} but it has type {}",
                        self.name(&ty),
                        self.name(&declared)
                    ),
                    span,
                );
            }
            self.out.var_refs.insert(
                span,
                VarRef {
                    depth: depth as u32,
                    slot: slot as u32,
                },
            );
            let narrowed = self.resolve(&ty);
            self.set_narrowed(&PatternVarKey::Local(name.to_string()), Some(narrowed));
        } else {
            let declared = self.resolve(&ty);
            self.declare_var(name, declared, span);
        }
    }

    pub(crate) fn report(&mut self, message: impl Into<String>, span: Span) {
        self.error(message, span);
    }

    pub(crate) fn warn(&mut self, message: impl Into<String>, span: Span) {
        self.warning(message, span);
    }

    pub(crate) fn type_name(&self, t: &Type) -> String {
        self.name(t)
    }

    pub(crate) fn resolve_ty(&self, t: &Type) -> Type {
        self.resolve(t)
    }

    pub(crate) fn join_types(&mut self, a: &Type, b: &Type) -> Type {
        self.join(a, b)
    }

    pub(crate) fn check_expr_pub(&mut self, e: &Expr, expected: Option<&Type>) -> Type {
        self.check_expr(e, expected)
    }

    pub(crate) fn check_case_in(
        &mut self,
        subject: &Expr,
        arms: &[InArm],
        els: Option<&[Expr]>,
        expected: Option<&Type>,
        span: Span,
    ) -> Type {
        let st = self.check_expr(subject, None);
        let st = self.resolve(&st);
        // A `Self` (`case self` in a method returning `Self`) is matched
        // as a value of the receiver's class where a pattern names a class
        // or variant (an enum's `case self` covers its variants); other
        // patterns (a binding, `nil`, an array) keep `Self`. (Not in a
        // block with a receiver, whose `self_type` is the receiver's.)
        let st_class = if st.mentions_param(SELF_PARAM)
            && self.env.receivers.is_empty()
            && !matches!(self.env.self_type, Type::ClassObject(..))
        {
            let subst: HashMap<TypeParamId, Type> = [(SELF_PARAM, self.env.self_type.clone())]
                .into_iter()
                .collect();
            st.subst(&subst)
        } else {
            st.clone()
        };
        fn names_class(p: &Pattern) -> bool {
            match &p.kind {
                PatternKind::Const(_)
                | PatternKind::ConstArray(..)
                | PatternKind::ConstHash(..) => true,
                PatternKind::Alt(ps) => ps.iter().any(names_class),
                PatternKind::Capture(p, _) => names_class(p),
                _ => false,
            }
        }
        // (The subject stays `Self` then: what a pattern narrows a value
        // of the class to is no `Self`.)
        let key = if st_class == st {
            self.var_key(subject)
        } else {
            None
        };
        let before = self.snapshot();
        let mut remaining: Vec<Type> = self.expand_members(&st_class);
        let mut result = Type::Nothing;
        let mut snaps = Vec::new();
        let saved_base = self.env.pattern_base;
        self.env.pattern_base = Some(self.env.frames.last().unwrap().vars.len());
        // Existing locals an earlier arm's pattern bound: that arm may
        // have failed after binding them (or its guard), so the later arms,
        // the `else` and what follows see either type.
        let mut rebound: Vec<(usize, usize, Type)> = Vec::new();
        // Fields a failed guard changed, with what it left them (none:
        // their declared types).
        let mut ivars_assigned: Vec<(String, Option<Type>)> = Vec::new();
        let mut subject_rebound = false;
        for arm in arms {
            self.restore(&before);
            self.widen_rebound(&rebound);
            self.widen_ivars(&ivars_assigned);
            let at_arm = self.snapshot();
            let on = if names_class(&arm.pattern) {
                &st_class
            } else {
                &st
            };
            let narrowed = self.check_pattern(&arm.pattern, on);
            // (A pattern that rebinds the subject, `in L::Cons(_, l)` on
            // `l`, leaves it the binding's type; after an arm that may
            // have, the subject is no longer the value matched.)
            match &key {
                Some(VarKey::Local(n)) if subject_rebound || arm.pattern.binds(n) => {
                    subject_rebound = true;
                }
                Some(k) => self.narrow_subject(k, Some(narrowed)),
                None => {}
            }
            if let Some(g) = &arm.guard {
                let (_, ft, ff) = self.check_cond(&g.cond);
                // (Where it fails, as a later arm sees it: what it bound
                // or assigned too.)
                let at_guard = self.snapshot();
                self.apply_facts(if g.negate { &ft } else { &ff });
                for (fi, slot, _, _, now) in self.rebound_since(&at_arm) {
                    rebound.push((fi, slot, now));
                }
                for n in self.ivars_changed_since(&at_arm) {
                    let t = self.env.ivar_narrow.get(&n).cloned();
                    ivars_assigned.push((n, t));
                }
                self.restore(&at_guard);
                self.apply_facts(if g.negate { &ff } else { &ft });
            } else {
                remaining.retain(|m| !self.pattern_covers(&arm.pattern, m));
            }
            for (fi, slot, _, _, now) in self.rebound_since(&at_arm) {
                rebound.push((fi, slot, now));
            }
            let bt = self.check_body(&arm.body, expected);
            snaps.push((self.snapshot(), bt.is_nothing()));
            result = self.join(&result, &bt);
        }
        self.env.pattern_base = saved_base;
        self.restore(&before);
        self.widen_rebound(&rebound);
        self.widen_ivars(&ivars_assigned);
        let et = match els {
            Some(els) => {
                if let Some(k) = key.as_ref().filter(|_| !subject_rebound) {
                    let rem = Type::union_of(remaining.clone());
                    self.narrow_subject(k, Some(rem));
                }
                self.check_body(els, expected)
            }
            None => {
                // Whether a type not decided yet is covered is not known
                // here: a value no arm matches raises NoMatchingPatternError.
                remaining.retain(|m| !matches!(self.resolve(m), Type::Var(_)));
                if !remaining.is_empty() {
                    let names: Vec<String> = remaining.iter().map(|t| self.name(t)).collect();
                    // A union lists its alternatives explicitly, so a
                    // missing one is an error; for a single open type
                    // (numbers, strings, open classes) it is a warning.
                    let closed = remaining.iter().all(|t| self.is_closed_type(t))
                        || self.expand_members(&st).len() > 1;
                    let msg = format!("`case` does not cover: {}", names.join(", "));
                    if closed {
                        self.error(format!("{msg} (add an `in` arm or `else`)"), span);
                    } else {
                        self.warning(
                            format!("{msg}; a NoMatchingPatternError is raised at run time"),
                            span,
                        );
                    }
                }
                Type::Nothing
            }
        };
        let mut dead = et.is_nothing();
        result = self.join(&result, &et);
        for (snap, d) in snaps.iter().rev() {
            self.merge_with(snap, *d, dead);
            dead = dead && *d;
        }
        result
    }

    /// Types whose set of values is fully known to the checker, so that an
    /// uncovered one is an error rather than a warning.
    fn is_closed_type(&self, t: &Type) -> bool {
        match t {
            Type::Class(id, _) => {
                let class = self.world.class(*id);
                // Values of these types can be enumerated by patterns;
                // numbers and strings cannot, so a missing case there is a
                // run-time error (warning only).
                matches!(
                    class.kind,
                    ClassKind::Data | ClassKind::Variant | ClassKind::Enum
                ) || [self.world.builtin.nil, self.world.builtin.bool_].contains(id)
            }
            // A tuple of closed types (`[Bool, Color]`) can be covered;
            // one with a number, a string or an array in it is open.
            Type::Tuple(ts) => ts
                .iter()
                .all(|t| t.members().iter().all(|m| self.is_closed_type(m))),
            _ => false,
        }
    }
}

impl Checker {
    pub fn into_output(mut self) -> (World, Output, Vec<(u32, Diagnostic)>) {
        self.flush_ambiguous();
        (self.world, self.out, self.diagnostics)
    }

    pub(crate) fn resolve_path_pub(
        &mut self,
        namespace: Option<ClassId>,
        path: &ConstPath,
        span: Span,
    ) -> Option<Member> {
        self.resolve_path(namespace, path, span)
    }

    pub(crate) fn current_namespace(&self) -> Option<ClassId> {
        self.env.scope.namespace
    }
}

/// The parts of a method's class its checking reads.
struct OwnerInfo {
    type_params: Vec<crate::world::TypeParamInfo>,
    kind: ClassKind,
    usings: Vec<ExtensionId>,
    parent: Option<ClassId>,
}

impl crate::StaticHost for Checker {
    fn world(&self) -> &World {
        &self.world
    }
    fn output(&self) -> &Output {
        &self.out
    }
    fn ensure_method_checked(&mut self, mid: MethodId) {
        Checker::ensure_method_checked(self, mid)
    }
    fn ensure_const_checked(&mut self, cid: ConstId) {
        let span = self.world.consts[cid as usize].span;
        self.const_type(cid, span);
    }
    fn prepare(&mut self) {
        self.check_field_defaults();
    }
    fn error_count(&self) -> usize {
        Checker::error_count(self)
    }
    fn pending_classes(&self) -> Vec<ClassId> {
        self.pending_statement_classes()
    }
    fn add_generated(&mut self, info: MethodInfo) -> Result<MethodId, String> {
        // What the name demands (the declarer's rules for a written one).
        if let Some(why) = crate::declare::method_name_rule(
            &self.world,
            &info.name,
            info.singleton,
            &info.params,
            info.block.as_ref().map(|(_, t)| t),
            info.owner,
        ) {
            return Err(why);
        }
        let class = self.world.class(info.owner);
        let table = if info.singleton {
            &class.singleton_methods
        } else {
            &class.methods
        };
        if let Some(existing) = table.get(&info.name).and_then(|ids| ids.first()) {
            let m = self.world.method(*existing);
            let how = if m.generated.is_some() {
                " (generated by an earlier `static` statement)"
            } else {
                ""
            };
            return Err(format!(
                "`{}` already has a {}method `{}`{how}",
                class.name,
                if info.singleton { "class " } else { "" },
                info.name
            ));
        }
        Ok(self.world.add_method(info))
    }
    fn add_generated_field(&mut self, class: ClassId, field: FieldInfo) -> Result<(), String> {
        let info = self.world.class(class);
        if info.kind != ClassKind::Class {
            return Err(format!(
                "`{}` is not a class: fields are generated into classes only",
                info.name
            ));
        }
        if let Some((existing, _)) = self
            .world
            .all_fields(class)
            .into_iter()
            .find(|(f, _)| f.name == field.name)
        {
            let how = if existing.baked_default.is_some() {
                " (generated by an earlier `static` statement)"
            } else {
                ""
            };
            return Err(format!(
                "`{}` already has a field `@{}`{how}",
                info.name, field.name
            ));
        }
        self.world.class_mut(class).fields.push(field);
        // The field comes after the class's own, so what was checked so
        // far keeps its field indices (`Output::ivar_fields`), except in
        // the subclasses, whose own fields come after it now: their
        // methods checked before (a `static` statement reached one) are
        // checked again when next needed.
        let count = self.world.methods.len();
        for mid in 0..count as MethodId {
            let m = self.world.method(mid);
            if m.owner != class
                && m.checked
                && m.body.is_some()
                && self.world.class_is_a(m.owner, class)
            {
                self.world.method_mut(mid).checked = false;
            }
        }
        Ok(())
    }
    fn recheck_classes(&mut self, classes: &[ClassId]) {
        let world = std::mem::take(&mut self.world);
        let mut declarer = crate::declare::Declarer::with_world(world);
        declarer.recheck_classes(classes);
        self.diagnostics.append(&mut declarer.diagnostics);
        self.world = std::mem::take(&mut declarer.world);
        self.world.freeze_ancestors(true);
    }
}
