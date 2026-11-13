//! Type checking of method bodies, constant initializers and the main
//! program (phase 3).

use std::rc::Rc;

use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};

use rustc_hash::FxHashMap;

use quarz_syntax::ast::*;
use quarz_syntax::token::OpAssign;
use quarz_syntax::{Diagnostic, Severity, Span};

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

/// A call's record kept apart from its node's own (`calls`,
/// `union_calls`, `union_conflicts`, `dynamic_calls`): a compound
/// assignment's logical call (`o.c ||= v` through the value's own `||`),
/// whose node's record is the writer's.
#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct CallRecord {
    pub target: Option<CallTarget>,
    pub table: Option<Vec<(Type, MethodId)>>,
    pub conflict: bool,
    pub dynamic: bool,
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
    /// `recv.instance_exec(args, k: v, &b)` with keyword arguments: the
    /// block run with `self` = the receiver (docs/01 §9).
    InstanceExec,
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
    /// For a subclass that inherits a class method calling `new`: the
    /// `initialize` of its own (of the first class from it that has one)
    /// that takes what `new` passes for the parent's `init` (`None`:
    /// nothing), the first of its overloads that does
    /// (`check_inherited_constructors`): `(subclass, init, chosen)`. The
    /// runtime builds the subclass with it (`RtClass::inherited_inits`).
    /// Computed for the whole program on every check, not kept per file.
    #[serde(default)]
    pub inherited_inits: Vec<(ClassId, Option<MethodId>, MethodId)>,
    /// An op-assignment's target (`x += e`), the type of its current value
    /// the operator was checked with (for `quarz check --tree`).
    #[serde(default)]
    pub op_targets: FxHashMap<NodeId, Type>,
    /// A block literal's declared result type (`do |x| -> T ... end`), by
    /// the node id of the call it is given to (for `quarz check --tree`).
    #[serde(default)]
    pub block_results: FxHashMap<NodeId, Type>,
    pub calls: FxHashMap<NodeId, CallTarget>,
    pub const_targets: FxHashMap<NodeId, ConstTarget>,
    /// Variable occurrences (uses and definitions) keyed by their span.
    pub var_refs: FxHashMap<Span, VarRef>,
    /// Implicit-self calls inside a block with a receiver that go to an
    /// enclosing `self` instead: the receiver of the call is read from
    /// the hidden slot `var_refs[span]`.
    pub outer_self_calls: rustc_hash::FxHashSet<NodeId>,
    /// For each of `outer_self_calls`, how many blocks with a receiver
    /// out the `self` it reaches is (1: the receiver of the block around
    /// the innermost one; past the outermost, the lexical `self`): a
    /// quoted tree's `SelfRef(depth)` (docs/14 §6).
    #[serde(default)]
    pub outer_self_depths: FxHashMap<NodeId, u32>,
    /// Calls whose block literal is checked with a receiver
    /// (`T.() -> R`): a quoted tree counts them for `SelfRef(depth)`.
    #[serde(default)]
    pub receiver_blocks: rustc_hash::FxHashSet<NodeId>,
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
    /// The methods a call's checks found, each once, in the order found,
    /// where `union_calls` holds no table that says so: a call in
    /// `union_conflicts` (called by name), `&:name` on a union of class
    /// objects. For a quoted tree's `Call#methods` (docs/14 §6).
    #[serde(default)]
    pub union_methods: HashMap<NodeId, Vec<MethodId>>,
    /// Nodes whose checks (a block's, once per type of what it is given)
    /// typed them differently: `node_types` holds the last one's, so
    /// nothing is specialized for it.
    pub varied_types: rustc_hash::FxHashSet<NodeId>,
    /// `&:name` symbols, and `recv.:name` references, whose checks (a
    /// block's, once per type of what it is given) found different
    /// methods: called by name.
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
    /// `a != b` where an extension's `==` (with a `Bool` result) is the
    /// method `a == b` finds and the extension defines no `!=` that fits:
    /// `!(a == b)`, the node's `calls` entry being that `==` (true), or
    /// the `!=` found (false, recorded to tell the checks of a block).
    pub ne_negated: HashMap<NodeId, bool>,
    pub op_operators: HashMap<NodeId, MethodId>,
    /// A compound assignment's reader on a union receiver (`o.w += 1` on
    /// `Cat | Dog`): its table and conflict flag, as `union_calls` and
    /// `union_conflicts` are for a call (which hold the writer's).
    pub op_getter_tables: HashMap<NodeId, (Vec<(Type, MethodId)>, bool)>,
    /// A compound assignment's logical call (`o.c ||= v` through the
    /// value's own `||`): its record, apart from the writer's.
    pub op_logical_calls: HashMap<NodeId, CallRecord>,
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
    /// Calls on a class written by name (`C.tag`) resolved, where `using`
    /// is in effect, to a class method of a module an active scoped or
    /// conditional extension brought to that class: run as that method
    /// (`CallKind::Function`), not dispatched on the class object, where
    /// the class side's order (the extension's module after the chain)
    /// would find another (#580, docs/01 §7).
    pub lexical_class_calls: rustc_hash::FxHashSet<NodeId>,
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
    /// Of those, the blocks given to `def_initialize`, by their call: the
    /// class whose fields the block was checked to assign (the bound of
    /// the class generated into, docs/14 §5), for the statement to check
    /// the class it ran on against.
    #[serde(default)]
    pub init_blocks: FxHashMap<NodeId, ClassId>,
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
    /// The type arguments a call of a generic method (not a `static def`)
    /// was resolved with: the method's own type parameters, bound (what
    /// `--tree` shows, for the Lean model's conformance translator).
    #[serde(default)]
    pub call_type_args: FxHashMap<NodeId, TypeArgs>,
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
    /// `!x` nodes some check of which took the built-in negation (a value
    /// of a member without `!`, or of a type a block's other check saw):
    /// with `not_dispatch`, the built-in runs for some values.
    #[serde(default)]
    pub not_builtin: rustc_hash::FxHashSet<NodeId>,
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

/// The rule `compare_self_uses` reports.
const UNION_SELF_RULE: &str = "a block given to a union receiver must";

/// An implicit call in a block given to a union receiver, as one
/// member's check saw it (`Checker::self_uses`): the `self` it reads, as
/// the frame whose `self` that is (the block's own, for a call on it; the
/// one whose hidden slot a call falling through reads, `bind_outer_self`),
/// that `self`'s type, and the name called. Its method is the call's
/// record once checked. (The members' checks push the same frames: their
/// blocks differ only in having a receiver or not.)
#[derive(Clone, Debug)]
struct SelfUse {
    id: NodeId,
    span: Span,
    name: String,
    frame: usize,
    self_ty: Type,
    /// Whether it fell through to an enclosing `self` (not the block's).
    fell: bool,
    method: Option<MethodId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub(crate) enum VarKey {
    Local(String),
    IVar(String),
}

pub(crate) type Facts = Vec<(VarKey, Type)>;

/// The nodes of the arguments a compound assignment's writer is checked
/// with (`[]=(index..., value)`), counting down from this one, outside
/// every file's range and the zsuper locals'.
const OP_VALUE_ID: NodeId = u32::MAX - 0x10000;

/// The node of a call checked only to see which method it resolves to
/// (`Checker::probe_method`), outside every file's range.
const PROBE_ID: NodeId = u32::MAX - 0x20000;

/// `Checker::union_symbol`'s answer: the method the procedure calls (the
/// common one, or the first member's where a table chooses), each member
/// with its own method and substitution, and the table of the members'
/// methods to choose by the argument's class when they differ.
type UnionSymbol = (
    MethodId,
    Vec<(Type, MethodId, HashMap<TypeParamId, Type>)>,
    Option<Vec<(Type, MethodId)>>,
);

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
    /// Whether `self` is a `Self` (an instance method's, or a generic
    /// module's `static def`'s, whose `Self` is its receiver), not a class
    /// whose instances `Self` stands for (a class method's, a class's
    /// `static def`'s).
    self_is_self: bool,
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
    /// Checking a `case/in` arm's pattern: the names it binds are the
    /// arm's own (`declare_pattern_var`).
    arm_local: bool,
    /// Inside an alternative pattern, which binds no names.
    in_alternative: u32,
    /// The innermost scope within a frame (a `case/in` arm, a rescue
    /// clause) that a declaration (`y := e`, `y: T = e`) is in, when it is
    /// not the frame's own (`check_typed_decl`).
    decl_scope: Option<DeclScope>,
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
    /// ... given to `def_initialize`: an `initialize`'s body.
    next_block_init: bool,
    /// ... given to a generating call on another class's `Meta::ClassDef`
    /// than the `static def`'s own `self`.
    next_block_foreign: bool,
    /// The innermost lifted block is such a one: its `Self` is that
    /// class, not the `static def`'s.
    lifted_foreign: bool,
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
    /// The next block runs in another task: a task's block, or
    /// `Task.timeout`'s (the caller's, for captures, but run in a child).
    next_block_elsewhere: Option<String>,
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
    /// A node's `Output::union_methods` before a change.
    UnionMethods(NodeId, Option<Vec<MethodId>>),
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
    /// A call's fall-through to an enclosing `self` (`bind_outer_self`)
    /// before a check recorded one: in `outer_self_calls`, its depth, the
    /// variable reference at its span.
    OuterSelf(NodeId, Span, bool, Option<u32>, Option<VarRef>),
    /// An entry of `Checker::self_uses`, at this index.
    SelfUse(usize),
    /// A node marked in `Output::not_builtin`.
    NotBuiltin(NodeId),
    /// A call's `Output::quoted_blocks` entry and `Checker::quoted_seen`
    /// before a check changed them (docs/14 §6).
    Quoted(NodeId, Option<bool>, Option<bool>, Option<(u32, Span)>),
    /// A call's `Output::receiver_blocks` membership before a check
    /// changed it.
    ReceiverBlock(NodeId, bool),
    /// `Checker::logical_seen` of a node before a check changed it.
    Logical(NodeId, Option<LogicalSeen>),
    /// `Output::logical_calls` of a node before a check changed it.
    LogicalCall(NodeId, Option<Box<Expr>>),
    /// A symbol marked in `Output::varied_symbols`.
    VariedSymbol(NodeId),
    /// A `&:name` symbol's record before a check recorded another.
    BlockPass(NodeId, Option<BlockPass>),
    /// A `recv.:name`'s method before a check recorded another (a
    /// discarded trial's must not count as an earlier check's).
    MethodRefCall(NodeId, Option<CallTarget>),
    /// A call noted in `Output::static_calls` (a discarded trial's must
    /// not be reported).
    StaticCall((u32, Span, MethodId)),
    /// One more `Checker::extension_ambiguities` (#577): a discarded
    /// trial's does not count.
    ExtensionAmbiguity,
    /// A call marked in `Output::lexical_class_calls` (#580).
    LexicalClassCall(NodeId),
    /// A node's type before a check in a block recorded another.
    NodeType(NodeId, Option<Type>),
    /// An `!=`'s `Output::ne_negated` entry before a check changed it.
    NeNegated(NodeId, Option<bool>),
    /// A compound assignment's reader record (`Output::op_getter_tables`)
    /// before a check changed it.
    OpGetterTable(NodeId, Option<(Vec<(Type, MethodId)>, bool)>),
    /// A compound assignment's logical call record
    /// (`Output::op_logical_calls`) before a check changed it.
    OpLogicalCall(NodeId, Option<CallRecord>),
    /// A `def_method` block's `Output::lifted_blocks` entry before a check
    /// recorded another (and `Checker::lifted_seen` got one more).
    Lifted(NodeId, Option<Type>),
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
    /// A call of `new` with no receiver was seen outside the body's blocks
    /// (`Checker::calls_new`).
    implicit_new: bool,
    /// The names called with no receiver or on `self`, blocks included
    /// (`Checker::self_calls`).
    self_calls: HashSet<String>,
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
    /// Where the first `super` is (`Checker::first_super`).
    super_span: Option<Span>,
    /// Walking for `widen_assigned`, which acts at once on the variables
    /// in scope at the start: a scope's own declarations (`y := e`) are
    /// left out of it (`Checker::assigned_names_scope`).
    widening: bool,
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
        Checker::assigned_names_scope(&block.body, self);
        self.closure_depth -= 1;
        self.escaping -= escapes as u32;
        self.known = known;
    }
}

#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
struct LoopExits {
    /// The narrowings at each `break`.
    breaks: Vec<Snapshot>,
    /// The types of the breaks' values (`Nil` for a bare `break`): the
    /// loop's value when one leaves it.
    break_types: Vec<Type>,
    /// A `break` runs an `ensure` on its way out, which the narrowings
    /// at it do not show.
    through_ensure: bool,
    skipped: bool,
    /// The `begin` blocks with an `ensure` around the point being checked.
    ensures: u32,
}

/// A scope within a frame (`Env::decl_scope`): the frame, its first slot,
/// and the slots of the variables declared in it, hidden when it ends.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
struct DeclScope {
    frame: usize,
    start: usize,
    declared: Vec<usize>,
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
    /// A block given to `def_initialize`, the body of an `initialize`:
    /// what is outside it is not in that `initialize` (a late closure
    /// around it, `in_late_closure`).
    init: bool,
    /// The block of the call in `static(...)`, run at compile time
    /// (docs/14 §8).
    static_call: bool,
    /// A block run in another task (`Task.spawn`, `Task.timeout`), with
    /// the call's name: `return` and `break` cannot leave the code
    /// around it.
    task: Option<String>,
    /// A block written where a `shareable` procedure type is expected: it
    /// may run in another task or after its method has returned, so
    /// `return` and `break` cannot leave the code around it either (a
    /// task's says so with `task`).
    shareable: bool,
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
            Type::Proc(rc, ps, r, sh, kws) => Type::Proc(
                rc.as_ref().map(|t| Box::new(self.resolve(t))),
                ps.iter().map(|p| self.resolve(p)).collect(),
                Box::new(self.resolve(r)),
                *sh,
                ProcKw::map(kws, |t| self.resolve(t)),
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
    generated_news: Vec<(ClassId, ClassId, MethodId, Option<MethodId>)>,
    repl_ctor_marks: (usize, usize, usize),
    runtime_tests: Vec<RuntimeTest>,
    repl_test_marks: (usize, usize, usize),
}

/// Where a declaration that makes a run-time test unanswerable is reported
/// instead of the test (#515, (A)): one of the program using the test's
/// cog (another group than the test's), or of a later REPL input (the
/// classes and extensions from these indices on).
#[derive(Clone, Copy)]
enum DeclaredIn {
    OtherGroup(Option<UnitGroup>),
    ReplInput(u32, u32),
}

/// `Checker::untestable_against`'s answer: a class a value may be of whose
/// membership the table does not answer exactly, with its arguments.
type Untestable = Option<(ClassId, Vec<Type>)>;

/// A run-time test against a module the checker accepted (#515), for the
/// REPL to check again when a later input declares classes or extensions.
#[derive(Clone, Debug)]
struct RuntimeTest {
    rt: Type,
    target: Type,
    op: String,
    place: String,
}

/// Why a call of `deinitialize` is refused (docs/03 §4).
const DEINITIALIZE_CALLED: &str =
    "`deinitialize` runs when the object is released; it cannot be called";

/// The deepest `coerce` recursion: a defensive limit (see
/// `World::is_subtype`).
const COERCE_DEPTH: u32 = 256;

pub struct Checker {
    /// The extensions a `using` inside the bodies being checked made
    /// active (scoped as `World::active_extensions`): a `super` in an
    /// extension's method under one of the same class is an error (#593).
    local_usings: Vec<ExtensionId>,
    /// While a bare `super`'s call is resolved: how many variables it
    /// forwards (the parameters, then the block), read as the method's
    /// own (`zsuper_local`).
    zsuper_forwards: Option<usize>,
    /// The arguments a compound assignment's writer is checked with,
    /// already typed: `OP_VALUE_ID - i` is the `i`th's node.
    op_values: Vec<Type>,
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
    /// The method a block literal is being checked for, named in the
    /// error when the block's declared result does not fit it.
    block_callee: Option<String>,
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
    /// The span of the expression `check_expr` records, for a refusal in
    /// `record` (#515).
    recording_span: Span,
    /// `untestable_against`'s answers, per static type and module.
    untestable_memo: std::cell::RefCell<HashMap<(String, ClassId, bool), Untestable>>,
    op_given_up: rustc_hash::FxHashSet<(NodeId, bool)>,
    /// `&:name` nodes some check of which had a class object for the
    /// receiver: found differently by another check, they cannot be called
    /// by name (whichever check came first).
    symbol_on_class_object: rustc_hash::FxHashSet<NodeId>,
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
    /// A `def_method` block's procedure types, one per check (the
    /// enclosing block's, once per type), with its span: compared when its
    /// frame's types are resolved, since the generated method has one.
    lifted_seen: FxHashMap<NodeId, (Vec<Type>, Span, String)>,
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
    /// The REPL's top-level environment, kept across inputs.
    repl_env: Option<Env>,
    /// Methods currently being checked (to detect inference cycles).
    in_progress: Vec<MethodId>,
    /// While re-checking an implicit-self call on an enclosing `self`: that
    /// call (its arguments are other calls, which fall through as any,
    /// #336).
    in_outer_self: Option<NodeId>,
    /// The call being re-checked so (noted once, `note_self_use`).
    outer_recheck: Option<NodeId>,
    /// While checking a call with a block on a union receiver, once per
    /// member: which `self` each implicit call in it went to
    /// (`note_self_use`), compared across the members.
    self_uses: Vec<SelfUse>,
    /// How many such calls are being checked.
    union_block_calls: usize,
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
    /// The element types of empty literals no variable holds yet: a join
    /// decides them from the other side, and a task block's literal result
    /// as `Nothing` (docs/03).
    literal_vars: HashSet<InferVar>,
    /// Checking a type argument against its method's bound
    /// (`decide_literals_for` decides nothing there).
    checking_bound: bool,
    /// The method an overloaded call chose, by the call's node
    /// (`resolve_pretyped`).
    last_winner: Option<(NodeId, MethodId)>,
    /// How many calls `extension_ambiguity` reported (#577): a `for` whose
    /// `each` form is ambiguous keeps that error rather than its fallback.
    extension_ambiguities: usize,
    self_news: Vec<SelfNew>,
    /// The generated methods building their receiver's class
    /// (`StaticHost::generated_new`): class generated into, the class
    /// `new` was checked for, the method, the `initialize` it passes
    /// arguments for. A `def_initialize` into that class later checks
    /// them again (docs/14 §5).
    generated_news: Vec<(ClassId, ClassId, MethodId, Option<MethodId>)>,
    /// In the REPL, how many `self_news` sites and classes the inherited
    /// constructor check has seen: an input checks its new classes
    /// against every site and its new sites against every class, the
    /// pairs before it being checked already; and how many witnesses
    /// (`World::class_ext_impls`): a new one may pin an old site for an
    /// old class, so every pair is checked again (#504).
    repl_ctor_marks: (usize, usize, usize),
    /// The run-time tests against a module accepted so far, for the REPL:
    /// a later input that makes one unanswerable is refused there (#515).
    runtime_tests: Vec<RuntimeTest>,
    /// The REPL's tests, classes and extensions before the current input.
    repl_test_marks: (usize, usize, usize),
    /// `check_constructor` for `Self.new` (`check_self_new`): an abstract
    /// class may be built, the receiver's class being concrete.
    constructing_self: bool,
    /// Class methods called with an abstract class written as the
    /// receiver: (method, class, span, file) (`check_call`).
    abstract_receivers: Vec<(MethodId, ClassId, Span, u32)>,
    /// A module or abstract class written as the argument of a `Type[T]`
    /// parameter: (the class, `T`'s bound, the argument's span, the file),
    /// refused at the end of the check if a class method of the bound runs
    /// on it what needs an includer or a concrete class (#509).
    abstract_type_args: Vec<(ClassId, ClassId, String, Span, u32)>,
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
    pub fn new(mut world: World, file_mains: Vec<Option<ClassId>>) -> Checker {
        world.file_mains = file_mains.clone();
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
            self_is_self: false,
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
            arm_local: false,
            in_alternative: 0,
            decl_scope: None,
            task_frame: None,
            task_shareable_proc: false,
            reassigned: None,
            late_assigned: Rc::default(),
            never_narrow: Rc::default(),
            next_block_escapes: false,
            next_block_elsewhere: None,
            lifted_frame: None,
            static_frame: None,
            next_block_lifted: false,
            next_block_init: false,
            next_block_foreign: false,
            lifted_foreign: false,
        };
        Checker {
            zsuper_forwards: None,
            op_values: Vec::new(),
            op_seen: HashMap::default(),
            logical_seen: HashMap::default(),
            reused_files: Default::default(),
            static_done: Vec::new(),
            quoted_seen: HashMap::default(),
            static_expr_call: None,
            block_callee: None,
            quoted_conflicts: HashMap::default(),
            repl_unit: None,
            recording_span: Span::empty(0),
            untestable_memo: Default::default(),
            op_given_up: Default::default(),
            symbol_on_class_object: Default::default(),
            world,
            diagnostics: Vec::new(),
            local_usings: Vec::new(),
            ambiguous: Vec::new(),
            table_journal: Vec::new(),
            kept_ambiguous: Vec::new(),
            body_diagnostics: Vec::new(),
            rescued: Vec::new(),
            out: Output::default(),
            infer: InferTable::default(),
            env,
            touched: Vec::new(),
            lifted_seen: FxHashMap::default(),
            type_args_trials: Vec::new(),
            frame_vars: Vec::new(),
            breaking_blocks: HashMap::default(),
            temp_stmts: Vec::new(),
            repl_env: None,
            in_progress: Vec::new(),
            in_outer_self: None,
            outer_recheck: None,
            self_uses: Vec::new(),
            union_block_calls: 0,
            defaults_checked: HashSet::default(),
            init_checked: HashSet::default(),
            int_literals: Default::default(),
            coerce_depth: 0,
            coerce_open: Vec::new(),
            literal_vars: HashSet::default(),
            checking_bound: false,
            last_winner: None,
            extension_ambiguities: 0,
            self_news: Vec::new(),
            generated_news: Vec::new(),
            repl_ctor_marks: (0, 0, 0),
            runtime_tests: Vec::new(),
            repl_test_marks: (0, 0, 0),
            constructing_self: false,
            abstract_receivers: Vec::new(),
            abstract_type_args: Vec::new(),
            stmt_unused: false,
            next_body_void: false,
        }
    }

    // ----- diagnostics -----------------------------------------------------

    fn error(&mut self, message: impl Into<String>, span: Span) {
        let mut message = message.into();
        // A type not decided yet (`?0`) where a Shareable is required is
        // an error (docs/03): say what to write.
        // (Only where a Shareable is what was expected, and the type found
        // is the one not decided.)
        let expected_shareable = [
            "expects Shareable but found ",
            "of type Shareable",
            "but Shareable was expected",
            "does not satisfy the bound Shareable",
        ]
        .iter()
        .any(|p| message.contains(p));
        let undecided = message
            .as_bytes()
            .windows(2)
            .any(|w| w[0] == b'?' && w[1].is_ascii_digit());
        if undecided && expected_shareable && !message.contains("not yet known") {
            message.push_str(" (the type is not yet known here, and it must be Shareable: annotate it, as `a: Array[Int] = []`)");
        }
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
        self.world.file_main(file)
    }

    /// Register the pseudo-class of a file loaded after construction (a
    /// `require` in the REPL).
    pub fn add_file_main(&mut self, file: u32, main: ClassId) {
        let index = file as usize;
        if self.world.file_mains.len() <= index {
            self.world.file_mains.resize(index + 1, None);
        }
        self.world.file_mains[index] = Some(main);
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
        self.check_abstract_receivers();
        self.check_abstract_type_args();
    }

    /// `J.run` where `run` calls `new` on its receiver and `J` is abstract:
    /// it would instantiate `J` (#423). (A `Type[J]` value holding `J`
    /// raises `TypeError` at run time instead.)
    fn check_abstract_receivers(&mut self) {
        let saved = self.env.file;
        for (m, cid, span, file) in std::mem::take(&mut self.abstract_receivers) {
            if !self.world.method(m).builds_self {
                continue;
            }
            self.env.file = file;
            let (class, name) = (
                self.world.class(cid).name.clone(),
                self.world.method(m).name.clone(),
            );
            self.error(
                format!(
                    "cannot call `{class}.{name}`: `{name}` calls `new` on its receiver, and `{class}` is abstract; call it on a concrete subclass"
                ),
                span,
            );
        }
        self.env.file = saved;
    }

    /// A module or an abstract class written as the argument of a
    /// `Type[T]` parameter, `T`'s bound having a class method that on it
    /// needs a class including the module (`MethodInfo::needs_includer`)
    /// or a concrete class (abstract, or calling `new`,
    /// `MethodInfo::builds_self`): refused as the call written on it is
    /// (#494, #423). A value reaching the parameter through a `Type[M]`
    /// variable keeps the run-time errors (#509; #510 is the principled
    /// fix).
    fn check_abstract_type_args(&mut self) {
        let saved = self.env.file;
        for (cid, bound, param, span, file) in std::mem::take(&mut self.abstract_type_args) {
            // What `t.m` runs on the class written, for each class method
            // `m` of the bound: the witness its conformance recorded
            // (`witness_for`), else the class-side dispatch
            // (`World::class_side_dispatch`, over `class_side_order`, what
            // `Interp::class_side_override` walks: an abstract method passed
            // over to what implements it), else `m` (#536 step 2).
            let mut bound_methods: Vec<MethodId> = Vec::new();
            for a in self.world.class_side_order(bound) {
                let mut ids: Vec<MethodId> = self
                    .world
                    .class(a)
                    .singleton_methods
                    .values()
                    .flatten()
                    .copied()
                    .filter(|m| self.world.method(*m).owner == a)
                    .collect();
                ids.sort();
                bound_methods.extend(ids);
            }
            let module = self.world.class(cid).kind == ClassKind::Module;
            let found = bound_methods.iter().find_map(|&bm| {
                let runs = self
                    .witness_for(cid, bm)
                    .or_else(|| self.world.class_side_dispatch(cid, bm))
                    .unwrap_or(bm);
                let mi = self.world.method(runs);
                let why = if module {
                    mi.needs_includer.clone()?
                } else if mi.is_abstract {
                    "is abstract".to_string()
                } else if mi.builds_self {
                    "calls `new` on its receiver".to_string()
                } else {
                    return None;
                };
                Some((mi.name.clone(), why))
            });
            let Some((name, why)) = found else { continue };
            self.env.file = file;
            let class = self.world.class(cid).name.clone();
            let (what, fix) = if module {
                ("the module", format!("a class that includes `{class}`"))
            } else {
                ("the abstract class", "a concrete subclass".to_string())
            };
            self.error(
                format!(
                    "cannot pass {what} `{class}` itself as `Type[{param}]`: `{param}`'s class method `{name}` {why}, and through it would run as `{class}.{name}`; pass {fix}"
                ),
                span,
            );
        }
        self.env.file = saved;
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
            // The superclass and the modules included, whose
            // arguments may be the class's own parameters (`G[U] < H[U]`):
            // a parameter meets a bound its own bounds imply.
            let span = c.span;
            let heads: Vec<Type> = c.superclass.iter().chain(&c.includes).cloned().collect();
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
    /// on (a superclass, the modules included), whose
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
            Type::Proc(rc, ps, r, _, kws) => {
                if let Some(rc) = rc {
                    self.check_bounds_deep(rc, span);
                }
                ps.iter()
                    .chain(kws.iter().map(|k| &k.ty))
                    .for_each(|p| self.check_bounds_deep(p, span));
                self.check_bounds_deep(r, span);
            }
            Type::Nothing | Type::Void | Type::Param(_) | Type::Var(_) => {}
        }
    }

    /// A class method that calls `new` on its receiver builds an instance
    /// of each subclass it is called on: a subclass that inherits the
    /// method must accept the same arguments in its `initialize` (keep
    /// it, or add only optional parameters), or override the method.
    ///
    /// Whether `own`, the `initialize` `sub` builds itself with, takes
    /// what `new` passes for `init`, both seen from `sub` (the
    /// superclasses' type arguments substituted: `IntBox < Box[Int]`
    /// takes `Int` where `Box#initialize` takes `T`).
    fn inherited_init_fits(&self, sub: ClassId, init: Option<MethodId>, own: MethodId) -> bool {
        let params: Vec<Type> = self
            .world
            .class(sub)
            .type_params
            .iter()
            .map(|p| Type::Param(p.id))
            .collect();
        let ancestors = self.world.ancestors(sub, &params);
        let seen = |m: MethodId| -> MethodInfo {
            let mut m = self.world.method(m).clone();
            let Some((_, args)) = ancestors.iter().find(|(c, _)| *c == m.owner) else {
                return m;
            };
            let map: HashMap<TypeParamId, Type> = self
                .world
                .class(m.owner)
                .type_params
                .iter()
                .zip(args)
                .map(|(p, a)| (p.id, a.clone()))
                .collect();
            for x in &mut m.params {
                x.ty = x.ty.subst(&map);
            }
            if let Some((_, b)) = &mut m.block {
                *b = b.subst(&map);
            }
            m
        };
        self.initialize_fits(init.map(seen).as_ref(), &seen(own))
    }

    /// Whether `initialize` `s` takes what `new` passes for `init` (`None`:
    /// nothing): `init`'s positional parameters, by name too (a call may
    /// pass them by keyword), as types that hold them and optional where
    /// they were; its keywords by name; its `*rest`, `**opts` and block
    /// (`MethodInfo::block`); and only optional parameters besides.
    fn initialize_fits(&self, init: Option<&MethodInfo>, s: &MethodInfo) -> bool {
        let Some(p) = init else {
            return s.params.iter().all(|b| b.default.is_some());
        };
        let holds = |a: &ParamInfo, b: &ParamInfo| {
            a.name == b.name
                && (a.ty == b.ty || self.world.is_subtype(&a.ty, &b.ty))
                && (a.default.is_none() || b.default.is_some())
        };
        let of = |m: &MethodInfo, k: ParamKind| -> Vec<ParamInfo> {
            m.params.iter().filter(|x| x.kind == k).cloned().collect()
        };
        let (pp, sp) = (of(p, ParamKind::Positional), of(s, ParamKind::Positional));
        if pp.len() > sp.len()
            || !pp.iter().zip(&sp).all(|(a, b)| holds(a, b))
            || !sp[pp.len()..].iter().all(|b| b.default.is_some())
        {
            return false;
        }
        let (pk, sk) = (of(p, ParamKind::KeywordOnly), of(s, ParamKind::KeywordOnly));
        if !pk.iter().all(|a| sk.iter().any(|b| holds(a, b)))
            || !sk
                .iter()
                .all(|b| b.default.is_some() || pk.iter().any(|a| a.name == b.name))
        {
            return false;
        }
        // A block: a required one only where `new` must give one; one
        // `new` may give (`init` takes one), a subclass's of a type that
        // holds it, optional where `init`'s is (a subclass taking none
        // ignores it).
        match (&p.block, &s.block) {
            (None, Some(_)) if !s.block_optional => return false,
            (Some((_, a)), Some((_, b)))
                if !(a == b || self.world.is_subtype(a, b))
                    || (p.block_optional && !s.block_optional) =>
            {
                return false
            }
            _ => {}
        }
        // (What `*rest` or `**opts` passes, the subclass's takes.)
        [ParamKind::Rest, ParamKind::KeywordRest]
            .into_iter()
            .all(|k| {
                of(p, k).first().is_none_or(|a| {
                    of(s, k)
                        .first()
                        .is_some_and(|b| a.ty == b.ty || self.world.is_subtype(&a.ty, &b.ty))
                })
            })
    }

    fn check_inherited_constructors(&mut self) {
        self.check_inherited_constructors_from((0, 0));
    }

    /// As `check_inherited_constructors`, for the pairs of a site and a
    /// class not both seen before (`marks`: the sites and classes seen).
    /// Whether class `sid` or a superclass includes module `m` itself
    /// (its own includes, through what they include): the module's class
    /// methods then go by ordinary dispatch, not by witnesses (#504).
    fn includes_itself(&self, sid: ClassId, m: ClassId) -> bool {
        // (`World::class_side_order`: the class side dispatch walks.)
        self.world.class(m).kind == ClassKind::Module
            && self.world.class_side_order(sid).contains(&m)
    }

    /// Whether class `sid` conforms to module `m` through an extension's
    /// include (recorded witnesses, for the class, a superclass, or a
    /// module one of them includes), whatever extensions are active.
    fn conforms_by_extension(&self, sid: ClassId, m: ClassId) -> bool {
        self.world.class_ext_impls.iter().any(|w| {
            self.extension_may_reach(w.ext, sid)
                && self.world.ancestor_ids(w.module).contains(&m)
                && self.world.class_side_owner(sid, w.class).is_some()
        })
    }

    /// The class at which dispatch through `Type[M]` starts for class
    /// `sid` and a class method named `name`, when a fixed witness of that
    /// name (an extension's own, or a class's) runs for it: the witness's
    /// class, or the class in `sid`'s chain that includes the module the
    /// witness was recorded for (#504).
    fn witness_floor(&self, sid: ClassId, name: &str) -> Option<ClassId> {
        // (Of several witnesses of the name, for different modules, the
        // highest: below it some witness may run instead of the class's
        // own.)
        let chain = self.world.superclass_chain(sid);
        let floors: Vec<ClassId> = self
            .world
            .class_ext_impls
            .iter()
            .filter_map(|w| {
                let mm = self.world.method(w.method);
                if w.by == w.method
                    || mm.name != name
                    || self.includes_itself(sid, mm.owner)
                    || self.witness_for(sid, w.method) != Some(w.by)
                {
                    return None;
                }
                self.world.class_side_owner(sid, w.class)
            })
            .collect();
        floors
            .into_iter()
            .max_by_key(|f| chain.iter().position(|c| c == f).unwrap_or(0))
    }

    /// Whether extension `ext`'s conformance may hold for class `sid` (its
    /// target, a subclass, or a class including the target module): false
    /// only when `sid`'s instantiation of the target is known (no type
    /// parameters), the target's parameters are invariant (no `Type[S] <:
    /// Type[Box[Int]]` through variance), no bound names a module (which an
    /// extension active elsewhere may meet), and a bound of the
    /// conditional extension fails for it (#516).
    fn extension_may_reach(&self, ext: ExtensionId, sid: ClassId) -> bool {
        let e = &self.world.extensions[ext as usize];
        if e.type_params.iter().all(|tp| tp.bounds.is_empty())
            || self
                .world
                .class(e.target)
                .type_params
                .iter()
                .any(|tp| tp.variance != Variance::Invariant)
        {
            return true;
        }
        let Some((_, targs)) = self
            .world
            .ancestors_with_no_extensions(sid)
            .into_iter()
            .find(|(k, _)| *k == e.target)
        else {
            return true;
        };
        // (A bound naming a module may be met through an extension active
        // elsewhere, where the witness runs: counted as met.)
        let module_bound = e.type_params.iter().any(|tp| {
            tp.bounds.iter().any(|b| {
                matches!(b, Type::Class(c, _) if self.world.class(*c).kind == ClassKind::Module)
            })
        });
        module_bound
            || targs.iter().any(|t| t.has_params())
            || self.world.extension_bounds_hold(e, &targs)
    }

    /// The witness the runtime runs for module class method `mid` on class
    /// `sid` (`Interp::class_witness`): recorded for the nearest class up
    /// the chain, or for a module it includes itself (last first), before
    /// its superclass.
    fn witness_for(&self, sid: ClassId, mid: MethodId) -> Option<MethodId> {
        let at = |k: ClassId| {
            self.world
                .class_ext_impls
                .iter()
                .find(|w| w.class == k && w.method == mid)
                .map(|w| w.by)
        };
        // (`World::class_side_order`, the runtime's order too.)
        self.world.class_side_order(sid).into_iter().find_map(at)
    }

    fn check_inherited_constructors_from(&mut self, marks: (usize, usize)) {
        let (sites_seen, classes_seen) = marks;
        let new_sites: HashSet<(ClassId, MethodId, u32, Option<MethodId>)> = self
            .self_news
            .get(sites_seen..)
            .unwrap_or(&[])
            .iter()
            .map(|s| (s.0, s.2, s.3.start, s.1))
            .collect();
        // (Kept: a later unit's subclasses inherit them too, as the
        // prelude's do a program's, `PreludeState::self_news`.)
        let mut sites = self.self_news.clone();
        sites.sort_by_key(|s| (s.0, s.2, s.3.start, s.1));
        sites.dedup_by_key(|s| (s.0, s.2, s.3.start, s.1));
        let mut reported = HashSet::default();
        for (cid, init, method, span, _) in sites {
            let site_new = new_sites.contains(&(cid, method, span.start, init));
            let mname = self.world.method(method).name.clone();
            // How the method and its `new` are named: `C.build`'s `new`, or
            // `Self.new` in `C#copy`.
            let singleton = self.world.method(method).singleton;
            let (sep, new_in) = if singleton {
                (".", "`new`")
            } else {
                ("#", "`Self.new`")
            };
            let nclasses = self.world.classes.len() as ClassId;
            for sid in 0..nclasses {
                if !site_new && (sid as usize) < classes_seen {
                    continue;
                }
                // (Or conforming to the module through an extension, which
                // need not be active here: its witnesses run anywhere,
                // #504.)
                if sid == cid
                    // (A `data` type and an enum's variant too, made by their
                    // generated `initialize`, #527.)
                    || !matches!(
                        self.world.class(sid).kind,
                        ClassKind::Class | ClassKind::Data | ClassKind::Variant
                    )
                    || !(self.world.class_is_a(sid, cid) || self.conforms_by_extension(sid, cid))
                {
                    continue;
                }
                // The class methods and initialize between the subclass
                // and the class that calls `new`.
                let mut overrides = false;
                // The overrides on the way, nearest first: a `super` in each
                // reaches the method's `new` with `sid` for `self`.
                let mut chain: Vec<MethodId> = Vec::new();
                let mut own_init: Option<Vec<MethodId>> = None;
                // A module's class method (#494): only the class methods
                // before the module on the class side take its place (an
                // extension's include brings it too, #504).
                let module_site = self.world.class(cid).kind == ClassKind::Module
                    && self.world.method(method).singleton;
                // A class that conforms to the module through an extension
                // only: its witness takes the module's place (#504), none
                // of its own class methods otherwise (an extension takes
                // no part in dispatch, docs/01 §7).
                let via_extension = module_site && !self.includes_itself(sid, cid);
                // A class method that is a witness of an extension's
                // conformance runs, through `Type[M]`, for every subclass
                // whose witness it is, as the runtime picks it
                // (`witness_for`): no class method of the subclass excuses
                // it (witnesses are fixed, #504).
                let pinned = self.world.class_ext_impls.iter().any(|w| {
                    w.by == method
                        && w.by != w.method
                        && !self.includes_itself(sid, self.world.method(w.method).owner)
                        && self.witness_for(sid, w.method) == Some(method)
                });
                // An extension's class method is bound statically (docs/01
                // §7): a call of it runs it for every class it reaches,
                // whatever class methods of its name they declare, so none
                // excuses its `new` (#526, decided 2026-11-13: checked
                // against the target and every class a call can reach, its
                // subclasses or, for a module, the classes including it).
                let from_extension = self.world.method(method).extension.is_some();
                let mut past_module = via_extension || pinned || from_extension;
                // Through `Type[M]` a fixed witness of this name runs for
                // `sid`, so dispatch starts at the witness's class: classes
                // below it do not take this method's place (a `super` in
                // the witness reaches it with `sid` for `self`, #514's
                // review). `None`: no such witness.
                let floor = self.witness_floor(sid, &mname);
                // (The witness of an extension's conformance takes the
                // module's place, #504; a default is the module's own.)
                if let Some(by) = self
                    .witness_for(sid, method)
                    .filter(|&b| via_extension && b != method)
                {
                    overrides = true;
                    chain.push(by);
                }
                let mut cur = Some(sid);
                while let Some(c) = cur {
                    if c == cid {
                        break;
                    }
                    let class = self.world.class(c);
                    if own_init.is_none() {
                        own_init = class
                            .methods
                            .get("initialize")
                            .filter(|ids| !ids.is_empty())
                            .cloned();
                    }
                    // (Overridden, the method may still be reached through
                    // `super`: its `initialize` is still looked for.)
                    // An override is an overload of the method's signature
                    // (another signature leaves the method reached). Its
                    // `super` is any `super` of the class's methods of that
                    // name (`super(args)` may choose another overload of
                    // the parent's: counted, conservatively).
                    let site = self.world.method(method);
                    // (`Self.new` in an instance method: its overrides are
                    // instance methods.)
                    let table = if site.singleton {
                        &class.singleton_methods
                    } else {
                        &class.methods
                    };
                    // (`c` strictly below the witness's class.)
                    let below_floor = floor
                        .is_some_and(|f| c != f && self.world.superclass_chain(c).contains(&f));
                    if let Some(ids) = table.get(&mname).filter(|_| !past_module && !below_floor) {
                        if ids.iter().any(|&o| self.replaces_at_run_time(o, site.id)) {
                            overrides = true;
                            let with_super = ids
                                .iter()
                                .copied()
                                .find(|&o| Self::first_super(self.world.method(o)).is_some());
                            chain.push(with_super.unwrap_or(ids[0]));
                        }
                    }
                    // (Above the class that includes the module, the module's
                    // class method comes first.)
                    if module_site && self.world.class_side_owner(sid, cid) == Some(c) {
                        past_module = true;
                    }
                    cur = class.superclass.as_ref().and_then(|t| match t {
                        Type::Class(id, _) => Some(*id),
                        _ => None,
                    });
                }
                // A class the runtime builds (`World::built_by_runtime`):
                // the `new` reaching it would build no value of it (#535),
                // reached as the method itself or through `super` from
                // every override on the way.
                if self.world.built_by_runtime(sid)
                    && (!overrides
                        || chain
                            .iter()
                            .all(|&o| Self::first_super(self.world.method(o)).is_some()))
                {
                    if reported.insert((sid, method)) {
                        let (sname, cname) = (
                            self.world.class(sid).name.clone(),
                            self.world.class(cid).name.clone(),
                        );
                        self.diagnostics.push((
                            self.world.method(method).file,
                            Diagnostic::error(
                                format!("{new_in} in `{cname}{sep}{mname}` reaches `{sname}`, whose values the runtime makes (`{sname}` is not built with `new`): do not make `{sname}` conform to `{cname}`, or override `{mname}` for it"),
                                span,
                            ),
                        ));
                    }
                    continue;
                }
                let Some(sinit) = own_init else {
                    continue;
                };
                // An override that calls `super` runs the method's `new` on
                // the subclass: its choice is recorded where one fits (no
                // error where none does: the override need not call it).
                if overrides {
                    if let Some(&chosen) = sinit
                        .iter()
                        .find(|&&o| self.inherited_init_fits(sid, init, o))
                    {
                        self.record_inherited_init(sid, init, chosen);
                        continue;
                    }
                    // None fits: refused at the `super` that would reach it,
                    // if every override on the way calls `super`.
                    let supers: Vec<Option<Span>> = chain
                        .iter()
                        .map(|&o| Self::first_super(self.world.method(o)))
                        .collect();
                    if let (Some(Some(at)), true) =
                        (supers.first(), supers.iter().all(|s| s.is_some()))
                    {
                        if reported.insert((sid, method)) {
                            let near = self.world.method(chain[0]).clone();
                            let (sname, cname, oname) = (
                                self.world.class(sid).name.clone(),
                                self.world.class(cid).name.clone(),
                                self.world.class(near.owner).name.clone(),
                            );
                            let iname = init
                                .map(|i| self.world.class(self.world.method(i).owner).name.clone())
                                .unwrap_or_else(|| cname.clone());
                            self.diagnostics.push((
                                near.file,
                                Diagnostic::error(
                                    format!("`super` in `{oname}{sep}{mname}` runs {new_in} in `{cname}{sep}{mname}` with `{sname}` for `self`, but `{sname}#initialize` does not take its arguments: keep the parameters of `{iname}#initialize` in an `initialize` of `{sname}`, or do not call `super`"),
                                    *at,
                                ),
                            ));
                        }
                    }
                    continue;
                }
                if reported.contains(&(sid, method)) {
                    continue;
                }
                let s = self.world.method(sinit[0]).clone();
                // The first of its overloads that takes the arguments: the
                // one `new` runs for it (recorded for the runtime).
                if let Some(&chosen) = sinit
                    .iter()
                    .find(|&&o| self.inherited_init_fits(sid, init, o))
                {
                    self.record_inherited_init(sid, init, chosen);
                    continue;
                }
                // (Each `new` of the method is checked; one error each.)
                if reported.insert((sid, method)) {
                    let (sname, cname) = (
                        self.world.class(sid).name.clone(),
                        self.world.class(cid).name.clone(),
                    );
                    // (Whose `initialize` `new` was checked against: a
                    // module without one, `Object`'s.)
                    let iname = init
                        .map(|i| self.world.class(self.world.method(i).owner).name.clone())
                        .unwrap_or_else(|| {
                            if self.world.class(cid).kind == ClassKind::Module {
                                "Object".to_string()
                            } else {
                                cname.clone()
                            }
                        });
                    // (Generated, docs/14 §5: reported at the statement.)
                    let what = {
                        let oname = &self.world.class(s.owner).name;
                        let base = if s.owner == sid {
                            format!("`{sname}#initialize`")
                        } else {
                            format!("`{oname}#initialize`, which `{sname}` builds with")
                        };
                        match (s.generated.is_some(), s.owner == sid) {
                            (true, true) => format!("{base}, generated by `def_initialize` in this `static` statement,"),
                            (true, false) => format!("{base} (generated by `def_initialize` in this `static` statement),"),
                            (false, false) => format!("{base},"),
                            (false, true) => base,
                        }
                    };
                    self.diagnostics.push((
                        s.file,
                        Diagnostic::error(
                            if from_extension && !via_extension && !pinned {
                                // (Bound statically: a class method of the
                                // class's own does not replace it, #526.)
                                format!("{what} does not take the arguments of {new_in} in the extension's `{cname}{sep}{mname}`, which runs for `{sname}` wherever it is called (an extension's method is bound statically, so a class method of `{sname}`'s own does not replace it): keep the parameters of `{iname}#initialize`, their names and whether they are optional (adding only optional ones), or build `{sname}` outside the extension")
                            } else if via_extension || pinned {
                                // (Witnesses are fixed: a subclass's own class
                                // method does not replace one, #504.)
                                format!("{what} does not take the arguments of {new_in} in `{cname}{sep}{mname}`, which runs for `{sname}` through its conformance by an extension: keep the parameters of `{iname}#initialize`, their names and whether they are optional (adding only optional ones), or make `{sname}` conform on its own (its own `include` of the module)")
                            } else {
                                format!("{what} does not take the arguments of {new_in} in `{cname}{sep}{mname}`, which `{sname}` inherits: keep the parameters of `{iname}#initialize`, their names and whether they are optional (adding only optional ones), or override `{}{mname}` in `{sname}`", if singleton { "self." } else { "" })
                            },
                            s.span,
                        ),
                    ));
                }
            }
        }
    }

    /// Whether class method `o` takes the place of `site` for its class at
    /// run time: the override table (`World::overrides`).
    fn replaces_at_run_time(&self, o: MethodId, site: MethodId) -> bool {
        self.world.overrides(o).contains(&site)
    }

    /// Where the first `super` in `m`'s body is, if any.
    fn first_super(m: &MethodInfo) -> Option<Span> {
        let body = m.body.as_ref()?.body.as_ref()?;
        let mut a = Assigned::default();
        Self::assigned_names(body, &mut a);
        a.super_span
    }

    /// Record that `sub` is built with `chosen` where `new` passes what
    /// `init` takes (`Output::inherited_inits`), once.
    fn record_inherited_init(&mut self, sub: ClassId, init: Option<MethodId>, chosen: MethodId) {
        let entry = (sub, init, chosen);
        let list = &mut self.out.inherited_inits;
        list.retain(|(c, i, _)| (*c, *i) != (sub, init));
        list.push(entry);
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

    /// The definite initialization of a block given to `def_initialize`
    /// (docs/14 §5), as of a written `initialize` of a class below
    /// `bound` (see `init`): every field of `bound` to assign, on every
    /// path, before the object is used. The class generated into may
    /// have more, which the block cannot name: the statement refuses one
    /// without a default.
    fn check_init_block(&mut self, call_id: NodeId, block: &Block, bound: ClassId) {
        let (required, _) = self.required_fields(bound);
        let own = std::collections::BTreeSet::new();
        let (errors, usable_after, usable_on_entry) = {
            let calls = |id: NodeId| self.out.calls.get(&id).cloned();
            let world = &self.world;
            let uses_self = |mid: MethodId| !world.takes_no_self(mid);
            let diverges = |mid: MethodId| world.method(mid).ret.is_nothing();
            let mut c = crate::init::InitCheck::new(&required, &own, &calls, &uses_self, &diverges);
            c.lifted_block(&block.body, block.span);
            (c.errors, c.usable_after, c.usable_on_entry)
        };
        for (msg, span) in errors {
            self.error(msg, span);
        }
        self.out.usable_after.extend(usable_after);
        if usable_on_entry {
            self.out.usable_on_entry.insert(SelfOwner::Block(call_id));
        }
        for (f, _) in self.world.all_fields(bound) {
            if !f.has_default()
                && !f.mutable
                && !required.contains(&f.name)
                && !self.env.assigned_fields.contains(&f.name)
            {
                self.error(
                    format!(
                        "field `@{}` must be assigned in the generated `initialize`",
                        f.name
                    ),
                    block.span,
                );
            }
        }
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
            // (In the class's own file: see `check_default_uses`.)
            let file = class.file;
            self.error_in(
                file,
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
            let uses_self = |mid: MethodId| !world.takes_no_self(mid);
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
        // In the class's own file, not the unit being checked (a required
        // standard library's, #405).
        let file = self.world.class(cid).file;
        for (msg, span) in errors {
            self.error_in(file, msg, span);
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
            let saved_active = std::mem::take(self.world.active_extensions.get_mut());
            for f in &class.fields {
                let Some(d) = &f.default else {
                    continue;
                };
                *self.world.active_extensions.get_mut() =
                    self.world
                        .extensions_active_at(Some(cid), class.file, d.span.start);
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
            *self.world.active_extensions.get_mut() = saved_active;
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
        for (i, expr) in body.iter().enumerate() {
            // (A `using` is in effect from its statement on.)
            *self.world.active_extensions.get_mut() =
                self.world.file_extensions(file, expr.span.start);
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
        // A subclass declared in this input that inherits a class method
        // calling `new`, or an instance method calling `Self.new`, needs
        // an `initialize` that takes its arguments, as in a program (a
        // failed input is discarded, so what passed stays checked).
        let (sites, classes, witnesses) = self.repl_ctor_marks;
        let marks = if self.world.class_ext_impls.len() == witnesses {
            (sites, classes)
        } else {
            (0, 0)
        };
        self.check_inherited_constructors_from(marks);
        self.check_abstract_receivers();
        self.check_abstract_type_args();
        self.recheck_runtime_tests();
        self.repl_ctor_marks = (
            self.self_news.len(),
            self.world.classes.len(),
            self.world.class_ext_impls.len(),
        );
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
            file_mains: self.world.file_mains.clone(),
            self_news: self.self_news.clone(),
            generated_news: self.generated_news.clone(),
            repl_ctor_marks: self.repl_ctor_marks,
            runtime_tests: self.runtime_tests.clone(),
            repl_test_marks: self.repl_test_marks,
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
        self.world.file_mains = s.file_mains;
        self.self_news = s.self_news;
        self.generated_news = s.generated_news;
        self.repl_ctor_marks = s.repl_ctor_marks;
        self.runtime_tests = s.runtime_tests;
        self.repl_test_marks = s.repl_test_marks;
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
                TableUndo::OuterSelf(id, span, was, depth, var) => {
                    if !was {
                        self.out.outer_self_calls.remove(&id);
                    }
                    match depth {
                        Some(d) => self.out.outer_self_depths.insert(id, d),
                        None => self.out.outer_self_depths.remove(&id),
                    };
                    match var {
                        Some(v) => self.out.var_refs.insert(span, v),
                        None => self.out.var_refs.remove(&span),
                    };
                }
                TableUndo::SelfUse(i) => {
                    self.self_uses.truncate(i);
                }
                TableUndo::NotBuiltin(id) => {
                    self.out.not_builtin.remove(&id);
                }
                TableUndo::ReceiverBlock(id, was) => {
                    if was {
                        self.out.receiver_blocks.insert(id);
                    } else {
                        self.out.receiver_blocks.remove(&id);
                    }
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
                TableUndo::ExtensionAmbiguity => {
                    self.extension_ambiguities -= 1;
                }
                TableUndo::LexicalClassCall(id) => {
                    self.out.lexical_class_calls.remove(&id);
                }
                TableUndo::StaticCall(entry) => {
                    if let Some(i) = self.out.static_calls.iter().rposition(|e| *e == entry) {
                        self.out.static_calls.remove(i);
                    }
                }
                TableUndo::MethodRefCall(id, c) => {
                    match c {
                        Some(c) => self.out.calls.insert(id, c),
                        None => self.out.calls.remove(&id),
                    };
                }
                TableUndo::NodeType(id, t) => {
                    match t {
                        Some(t) => self.out.node_types.insert(id, t),
                        None => self.out.node_types.remove(&id),
                    };
                }
                TableUndo::NeNegated(id, t) => {
                    match t {
                        Some(t) => self.out.ne_negated.insert(id, t),
                        None => self.out.ne_negated.remove(&id),
                    };
                }
                TableUndo::OpGetterTable(id, t) => {
                    match t {
                        Some(t) => self.out.op_getter_tables.insert(id, t),
                        None => self.out.op_getter_tables.remove(&id),
                    };
                }
                TableUndo::OpLogicalCall(id, t) => {
                    match t {
                        Some(t) => self.out.op_logical_calls.insert(id, t),
                        None => self.out.op_logical_calls.remove(&id),
                    };
                }
                TableUndo::Lifted(id, t) => {
                    match t {
                        Some(t) => self.out.lifted_blocks.insert(id, t),
                        None => self.out.lifted_blocks.remove(&id),
                    };
                    if let Some((seen, ..)) = self.lifted_seen.get_mut(&id) {
                        seen.pop();
                    }
                }
                TableUndo::UnionMethods(id, ms) => {
                    match ms {
                        Some(ms) => self.out.union_methods.insert(id, ms),
                        None => self.out.union_methods.remove(&id),
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

    /// A call on a class written by name (`C`, `Mod::C`, `Box[Int]`) whose
    /// winner is a class method of a module an active scoped or
    /// conditional extension brought to the class
    /// (`World::resolution_sources`): run as that method, #580.
    fn note_lexical_class_call(
        &mut self,
        expr: &Expr,
        call: &Call,
        recv_ty: &Type,
        winner: MethodId,
    ) {
        let by_name = call
            .recv
            .as_ref()
            .is_some_and(|r| matches!(r.kind, ExprKind::Const(_) | ExprKind::TypeApp(_)));
        let Type::ClassObject(id, args) = self.infer.resolve(recv_ty) else {
            return;
        };
        let m = self.world.method(winner);
        // (An abstract one is a requirement: dispatch finds its witness.)
        if !by_name || !m.singleton || m.extension.is_some() || m.is_abstract {
            return;
        }
        // (A module an active scoped or conditional extension brought,
        // `World::resolution_sources`; a top-level extension's keeps the
        // witness rule, decided in `witness_matrix_abstract`.)
        let brought = self
            .world
            .resolution_sources(id, &args)
            .into_iter()
            .any(|(k, _, e)| k == m.owner && e.is_some());
        if brought && self.out.lexical_class_calls.insert(expr.id) {
            self.table_journal
                .push(TableUndo::LexicalClassCall(expr.id));
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
            self.table_journal.push(TableUndo::StaticCall(entry));
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
        let stmts = self.superclass_first(stmts);
        // The classes one of whose statements failed: their class-end
        // hooks do not run (what they combine is incomplete).
        let mut failed: HashSet<ClassId> = HashSet::default();
        for (i, stmt) in stmts {
            // Done once it ran: until then its class, and the classes
            // under it, may still get members from it
            // (`pending_statement_classes`).
            let errors_before = self.error_count();
            if let Some(callee) = self.check_static_stmt(&stmt) {
                if let Some(r) = runner.as_deref_mut() {
                    if let Err(failure) = r.run(self, &stmt, callee) {
                        self.static_failure(&stmt, failure);
                    }
                }
            }
            if self.error_count() > errors_before {
                failed.insert(stmt.class);
            }
            self.static_done[i] = true;
            // The class's last statement: the hooks its statements
            // registered run, before the checks deferred past them.
            let last = !self.world.static_stmts.iter().enumerate().any(|(j, s)| {
                s.class == stmt.class && !self.static_done.get(j).copied().unwrap_or(false)
            });
            if last && !failed.contains(&stmt.class) {
                if let Some(r) = runner.as_deref_mut() {
                    if let Err((at, failure)) = r.class_end(self, &stmt) {
                        self.static_failure(&at, failure);
                    }
                }
            }
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

    /// A statement's failure, reported at it with its notes.
    fn static_failure(&mut self, stmt: &StaticStmt, failure: crate::StaticFailure) {
        let mut message = failure.message;
        for note in failure.notes {
            message.push('\n');
            message.push_str(&note);
        }
        self.error_in(stmt.file, message, stmt.span);
    }

    /// The statements `stmts` (in file name order, then text order) in
    /// the order they run (docs/14 §2): a class's or module's after every
    /// statement among them of its ancestors (superclasses and the
    /// modules it includes, transitively), so that its own
    /// see what theirs generated; otherwise in the order given.
    fn superclass_first(&self, stmts: Vec<(usize, StaticStmt)>) -> Vec<(usize, StaticStmt)> {
        let mut ancestors: HashMap<ClassId, HashSet<ClassId>> = HashMap::default();
        for (_, stmt) in &stmts {
            ancestors
                .entry(stmt.class)
                .or_insert_with(|| self.statement_ancestors(stmt.class));
        }
        let mut todo: Vec<Option<(usize, StaticStmt)>> = stmts.into_iter().map(Some).collect();
        let mut out = Vec::with_capacity(todo.len());
        while out.len() < todo.len() {
            // The first statement left none of whose class's ancestors
            // has one left. The hierarchy has no cycle; were there one,
            // the first left would run.
            let waits = |c: ClassId, todo: &[Option<(usize, StaticStmt)>]| {
                let own = &ancestors[&c];
                todo.iter()
                    .flatten()
                    .any(|(_, s)| s.class != c && own.contains(&s.class))
            };
            let pick = (0..todo.len())
                .find(|&k| matches!(&todo[k], Some((_, s)) if !waits(s.class, &todo)))
                .or_else(|| (0..todo.len()).find(|&k| todo[k].is_some()))
                .expect("a statement left");
            out.push(todo[pick].take().expect("not taken"));
        }
        out
    }

    /// The classes and modules a class's statements run after (docs/14
    /// §2): its superclasses and the modules it includes,
    /// theirs, and so on.
    fn statement_ancestors(&self, class: ClassId) -> HashSet<ClassId> {
        let mut seen: HashSet<ClassId> = HashSet::default();
        let mut stack = vec![class];
        while let Some(c) = stack.pop() {
            let info = self.world.class(c);
            let edges = info.superclass.iter().chain(&info.includes);
            for t in edges {
                if let Type::Class(id, _) = t {
                    if *id != class && seen.insert(*id) {
                        stack.push(*id);
                    }
                }
            }
        }
        seen
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

    /// How a class reaches a module's macro (docs/14 §2): any `include`
    /// for a module without type parameters (`self: Meta::ClassDef[Self]`
    /// holds on any class); for a generic one, `include M[A]` in the
    /// class or an ancestor `A` itself, so that the `Meta::ClassDef[A]`
    /// the body was checked with holds for the class the statement runs
    /// on. Anything else is refused, with why.
    fn include_route(&self, class: ClassId, module: ClassId, name: &str) -> Result<(), String> {
        let mname = self.world.class(module).name.clone();
        if self.world.class(module).type_params.is_empty() {
            return Ok(());
        }
        for a in self.world.ancestor_ids(class) {
            let c = self.world.class(a);
            if c.kind == ClassKind::Module {
                continue;
            }
            for t in &c.includes {
                if let Type::Class(id, args) = t {
                    if *id == module {
                        return match args.first() {
                            // The class's own instance type, as `include`
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
                                "`{name}` is a macro of the module `{mname}`, which `{}` includes as `{}`: a statement runs it only through `include {mname}[{}]`, the class itself as its first type argument",
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
            "`{name}` is a macro of the module `{mname}`, which the class reaches only through another module: include `{mname}` itself"
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
        let active =
            self.world
                .extensions_active_at(Some(stmt.class), stmt.file, stmt.expr.span.start);
        let saved_active = std::mem::replace(self.world.active_extensions.get_mut(), active);
        let t = self.check_expr(&stmt.expr, None);
        let _ = self.settle_vars(&t);
        *self.world.active_extensions.get_mut() = saved_active;
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
        if !m.is_static || !m.singleton || m.is_native {
            let message = {
                format!(
                    "a statement in a class body must call a `static def` class method; `{}` is not one",
                    m.name
                )
            };
            self.error_in(stmt.file, message, stmt.span);
            return None;
        }
        if self.world.class(m.owner).kind == ClassKind::Module {
            // A module's macro (docs/14 §2), through `include`: a generic
            // module's `self` is its first type parameter's
            // `Meta::ClassDef`, which the class must be (or descend from)
            // where it runs.
            if let Err(message) = self.include_route(stmt.class, m.owner, &m.name) {
                self.error_in(stmt.file, message, stmt.span);
                return None;
            }
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
            self_is_self: false,
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
            arm_local: false,
            in_alternative: 0,
            decl_scope: None,
            task_frame: None,
            task_shareable_proc: false,
            reassigned: None,
            late_assigned: Rc::default(),
            never_narrow: Rc::default(),
            next_block_escapes: false,
            next_block_elsewhere: None,
            lifted_frame: None,
            static_frame: None,
            next_block_lifted: false,
            next_block_init: false,
            next_block_foreign: false,
            lifted_foreign: false,
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
        // Only what this frame recorded: its variables are its own table's
        // (a frame checked inside another one, a constant checked lazily,
        // numbers its variables from 0 too, and an entry another frame
        // left with a variable unbound must not take this one's binding).
        let touched = std::mem::take(&mut self.touched);
        for id in touched {
            if let Some((seen, span, callee)) = self.lifted_seen.remove(&id) {
                let seen: Vec<Type> = seen.iter().map(|t| self.infer.resolve(t)).collect();
                // (One not inferred is `static_run`'s to report.)
                let mut seen = seen.into_iter().filter(|t| !t.has_vars());
                let first = seen.next();
                if let (Some(first), Some(other)) =
                    (first.clone(), seen.find(|t| Some(t) != first.as_ref()))
                {
                    self.error(
                        format!(
                            "the block given to {callee} has a type for each check of the block around it ({} and {}): the generated method has one",
                            self.name(&first),
                            self.name(&other)
                        ),
                        span,
                    );
                }
            }
            if let Some(t) = self.out.node_types.get(&id) {
                let r = self.infer.resolve(t);
                self.out.node_types.insert(id, r);
            }
            for t in [
                self.out.lifted_blocks.get_mut(&id),
                self.out.op_targets.get_mut(&id),
                self.out.block_results.get_mut(&id),
            ]
            .into_iter()
            .flatten()
            {
                if t.has_vars() {
                    *t = self.infer.resolve(t);
                }
            }
            for args in [
                self.out.call_type_args.get_mut(&id),
                self.out.type_args.get_mut(&id),
            ]
            .into_iter()
            .flatten()
            {
                for (_, t) in args.iter_mut() {
                    if t.has_vars() {
                        *t = self.infer.resolve(t);
                    }
                }
            }
            // Call targets with types (is_a?, as) are resolved too.
            match self.out.calls.get(&id).cloned() {
                Some(CallTarget::IsA(t)) => {
                    let r = self.infer.resolve(&t);
                    self.out.calls.insert(id, CallTarget::IsA(r));
                }
                Some(CallTarget::As { ty, optional }) => {
                    let r = self.infer.resolve(&ty);
                    self.out
                        .calls
                        .insert(id, CallTarget::As { ty: r, optional });
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
                    // (Told apart at run time by a class test, #515.)
                    let types = vec![self.infer.resolve(b), self.infer.resolve(t)];
                    let span = self.recording_span;
                    self.implicit_types_check(&types, "a block checked once per type", span);
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
        let self_type = if info.singleton
            && info.is_static
            && !info.is_native
            && class.kind == ClassKind::Module
        {
            // A module's macro runs on a class that includes it (docs/14
            // §2): a generic module's on its first type parameter, which
            // `include M[C]` makes the class; another's on `Self`.
            let on = match class.type_params.first() {
                Some(p) => Type::Param(p.id),
                None => Type::Param(SELF_PARAM),
            };
            Type::Class(self.world.builtin.meta_classdef, vec![on])
        } else if info.singleton && info.is_static && !info.is_native {
            // A `static` class method runs on the class being declared:
            // `self` is its `Meta::ClassDef` (docs/14).
            Type::Class(self.world.builtin.meta_classdef, vec![instance.clone()])
        } else if let (true, Some(ext)) = (info.singleton, info.extension) {
            // An extension's class method: the class as the extension
            // names it (`extension Box[T]`: its `T`, not the class's).
            let e = &self.world.extensions[ext as usize];
            Type::ClassObject(e.target, e.target_args.clone())
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
        // A signature with `Self`: the body sees `Self` as opaque, and a
        // `Self` written in it (a block's `-> Self`, a local's type) is
        // that one, the signature's, not the class.
        let opaque = Self::mentions_self(&info);
        // (In a class method, `Self` is its instances, as in its
        // signature, docs/02 §1.)
        // (A class's `static def self.`, whose `self` is a
        // `Meta::ClassDef`, likewise.)
        let body_self = match &self_type {
            Type::ClassObject(c, args) if info.singleton => Type::Class(*c, args.clone()),
            Type::Class(c, args) if info.singleton && *c == self.world.builtin.meta_classdef => {
                args.first().cloned().unwrap_or_else(|| self_type.clone())
            }
            t => t.clone(),
        };
        let scope = TypeScope {
            namespace,
            params,
            self_type: (!opaque).then_some(body_self),
        };
        let mut env = self.fresh_env(self_type.clone(), Some(owner), Some(mid), scope, info.file);
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
        env.self_is_self = Self::self_binding(&self.world, &info, &self_type) == self_type;
        // (A class's `static def self.` binds it too: its `type` is a
        // `Type[Self]`, `Self` a subclass of the class.)
        let static_class = info.singleton
            && info.is_static
            && !info.is_native
            && matches!(&self_type, Type::Class(c, _) if *c == self.world.builtin.meta_classdef);
        let bound = (opaque || static_class).then(|| {
            match Self::self_binding(&self.world, &info, &self_type) {
                // (A module's macro on `Meta::ClassDef[Self]`: `Self` is a
                // class including the module, #494.)
                Type::Param(SELF_PARAM) => instance.clone(),
                b => b,
            }
        });
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
        // Active extensions: those where the method is written (an
        // extension's method: in the extension's module).
        let lexical = match info.extension {
            Some(e) => self.world.extensions[e as usize].module,
            None => Some(owner),
        };
        let active = self
            .world
            .extensions_active_at(lexical, info.file, info.span.start);

        let saved_env = std::mem::replace(&mut self.env, env);
        let saved_infer = std::mem::take(&mut self.infer);
        let saved_touched = std::mem::take(&mut self.touched);
        let saved_frame_vars = std::mem::take(&mut self.frame_vars);
        let saved_temp_stmts = std::mem::take(&mut self.temp_stmts);
        let saved_active = std::mem::replace(self.world.active_extensions.get_mut(), active);

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

        // `deinitialize`: its `super` once per path, as `initialize`'s
        // (docs/01 §3), and nothing else to check there.
        if info.name == "deinitialize" && !info.singleton {
            let none = std::collections::BTreeSet::new();
            let errors = {
                let calls = |id: NodeId| self.out.calls.get(&id).cloned();
                let uses_self = |_: MethodId| false;
                let diverges = |mid: MethodId| self.world.method(mid).ret.is_nothing();
                let mut c =
                    crate::init::InitCheck::new(&none, &none, &calls, &uses_self, &diverges);
                c.what = "deinitialize";
                c.method(&[], &body, info.span);
                c.errors
            };
            for (msg, span) in errors {
                self.error(msg, span);
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
                // or a top-level `def` (which take no `self`; a method an
                // `extension Kernel` adds does) may read the object's
                // fields.
                let uses_self = |mid: MethodId| !world.takes_no_self(mid);
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
        *self.world.active_extensions.get_mut() = saved_active;
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
        let active = self
            .world
            .extensions_active_at(info.owner, info.file, value.span.start);
        let saved_active = std::mem::replace(self.world.active_extensions.get_mut(), active);
        let t = self.check_expr(&value, None);
        *self.world.active_extensions.get_mut() = saved_active;
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
                self.decide_literals_for(*eid, aargs);
                let resolved: Vec<Type> = aargs.iter().map(|t| self.infer.resolve(t)).collect();
                if !self.world.keeps_shareable(*aid, &resolved, *eid) {
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
            // A cog's root module as a value is a `Cog` (docs/10 §6).
            (Type::ClassObject(c, _), Type::Class(eid, _))
                if *eid == self.world.builtin.cog && self.world.class(*c).cog.is_some() =>
            {
                true
            }
            (Type::ClassObject(..) | Type::TypeOf(_), Type::Class(eid, eargs))
                if *eid == self.world.builtin.class_ =>
            {
                match (actual.instance_of(), eargs.first()) {
                    (Some(a), Some(e)) => self.coerce(&a, e),
                    _ => true,
                }
            }
            // A class value is a `Type`, and so what `Type` includes: a
            // `Shareable`.
            (Type::ClassObject(..) | Type::TypeOf(_), Type::Class(eid, _))
                if self.world.type_includes(*eid) =>
            {
                true
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
                self.decide_literals_for(*eid, &[Type::union_of(xs.clone())]);
                let elems = self.infer.resolve(&Type::union_of(xs.clone()));
                self.world.class_is_a(array, *eid)
                    && self.world.keeps_shareable(array, &[elems], *eid)
            }
            (Type::Proc(ra, ps, r, sa, ka), Type::Proc(rb, qs, s, sb, kb)) => {
                // A shareable procedure is a procedure; not the reverse.
                if ps.len() != qs.len() || (*sb && !*sa) {
                    return false;
                }
                // Keywords by name (docs/02 §9), contravariant.
                let Some(pairs) = ProcKw::accepts(ka, kb) else {
                    return false;
                };
                let pairs: Vec<(Type, Type)> = pairs
                    .into_iter()
                    .map(|(v, t)| (v.clone(), t.clone()))
                    .collect();
                for (v, t) in &pairs {
                    if !self.coerce(t, v) {
                        return false;
                    }
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
        // A literal's element types beside decided ones (`cond ? [1] :
        // []`): of the other's type (`bind_literals`).
        if !self.literal_vars.is_empty() && (ra.has_vars() || rb.has_vars()) {
            self.bind_literals(&ra, &rb);
            let (ra, rb) = (self.infer.resolve(&ra), self.infer.resolve(&rb));
            return self.world.join(&ra, &rb);
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
        // (A type `nil` or a `Bool` may be a value of: `Object`, or a
        // module they include, `Shareable`.)
        if t.members().iter().any(|m| {
            matches!(m, Type::Param(_) | Type::Var(_)) || self.may_hold_falsy(m) != (false, false)
        }) {
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
            } else if let Type::Var(_) = m {
                // Not decided yet: it may become `Nil` or `Bool`, so it
                // stays, as itself (as `is_truthy_type` leaves it open).
                out.push(m);
            } else if let Type::Param(p) = m {
                // `T` may be `Bool` or `Int?`: it stays, as itself.
                if self.world.param_may_be_falsy(p) {
                    out.push(m);
                }
            } else {
                // A type `nil` or a `Bool` may be a value of (`Object`, a
                // module they include): those.
                let (nil, bool_) = self.may_hold_falsy(&m);
                if nil {
                    out.push(self.world.nil());
                }
                if bool_ {
                    out.push(self.world.bool_());
                }
            }
        }
        Type::union_of(out)
    }

    /// Whether `nil` and a `Bool` may be values of `m`, a type other than
    /// `Nil`, `Bool` and a parameter (as the Lean model decides it): by
    /// the subtype check, so `Object` and a module they include
    /// (`Shareable`) hold them, and a class does not.
    fn may_hold_falsy(&self, m: &Type) -> (bool, bool) {
        if self.world.is_nil_type(m)
            || matches!(m, Type::Class(id, _) if *id == self.world.builtin.bool_)
            || matches!(m, Type::Param(_) | Type::Var(_) | Type::Nothing)
        {
            return (false, false);
        }
        (
            self.world.is_subtype(&self.world.nil(), m),
            self.world.is_subtype(&self.world.bool_(), m),
        )
    }

    // ----- variables -------------------------------------------------------------

    /// Record a union call's table (`Output::union_calls`), merged with
    /// those of earlier checks of the same call: kept only while each
    /// member is a class a test tells apart from the others (not two
    /// instances of one generic class, not a class and its subclass) and
    /// every check agrees on each member's method.
    fn note_union_table(&mut self, id: NodeId, table: Vec<(Type, MethodId)>, span: Span) {
        self.implicit_test_check(&table, "a call on a union", span);
        // (What this and the earlier checks found, kept for a call that
        // goes by name: `union_methods`.)
        let found: Vec<MethodId> = self
            .out
            .union_calls
            .get(&id)
            .into_iter()
            .flatten()
            .chain(&table)
            .map(|(_, m)| *m)
            .collect();
        self.note_union_table_in(id, table, span);
        if self.out.union_conflicts.contains(&id) {
            self.note_union_methods(id, found);
        }
    }

    /// Add `found` to node `id`'s `Output::union_methods`.
    fn note_union_methods(&mut self, id: NodeId, found: Vec<MethodId>) {
        let before = self.out.union_methods.get(&id).cloned();
        let mut ms = before.clone().unwrap_or_default();
        for m in found {
            if !ms.contains(&m) {
                ms.push(m);
            }
        }
        if before.as_ref() != Some(&ms) {
            self.table_journal.push(TableUndo::UnionMethods(id, before));
            self.out.union_methods.insert(id, ms);
        }
    }

    fn note_union_table_in(&mut self, id: NodeId, table: Vec<(Type, MethodId)>, span: Span) {
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
        // Class objects, which no class test tells apart, whose class
        // methods all override one: the table is kept as found, and the
        // call is lowered as a call of that one, which runs the receiver's
        // own (`World::overridden_class_method`).
        if self.world.class_object_base(&merged).is_some() {
            self.out.union_calls.insert(id, merged);
            return;
        }
        let mut by_class: Vec<(ClassId, Type, MethodId)> = Vec::new();
        for (t, m) in &merged {
            // A member a class test cannot tell (a type parameter) is
            // tested by the class whose method it found (its bound's).
            let tested;
            let (c, t) = match self.test_class(t) {
                Some(c) => (c, t),
                None if matches!(t, Type::Param(_)) && !self.world.method(*m).singleton => {
                    let owner = self.world.method(*m).owner;
                    tested = Type::Class(owner, Vec::new());
                    (owner, &tested)
                }
                // (A member no class test tells, an unresolved type: an
                // error where the checks found different methods and a
                // lookup by name would not find the right one, as for two
                // members of one class.)
                None => {
                    // (The pair `ambiguous_call` reports, if any.)
                    let wrong = |n: MethodId, m: MethodId| {
                        let (ni, mi) = (self.world.method(n), self.world.method(m));
                        ni.extension.is_some()
                            || mi.extension.is_some()
                            || (!ni.is_native && !mi.is_native)
                    };
                    let other = merged
                        .iter()
                        .filter(|(_, n)| n != m)
                        .find(|(_, n)| wrong(*n, *m))
                        .or_else(|| merged.iter().find(|(_, n)| n != m));
                    match other {
                        Some((u, n)) => {
                            let (u, n) = (u.clone(), *n);
                            let t = t.clone();
                            self.ambiguous_call(id, &u, &t, n, *m, span);
                        }
                        None => {
                            self.out.union_conflicts.insert(id);
                        }
                    }
                    return;
                }
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

    /// A `Meta::ClassDef[T]` member of a union receiver and a class-object
    /// member that can hold the same class value (a class related to `T`,
    /// any class for `Type`, a module, a type parameter's; any for a `T`
    /// that is not a concrete class) whose methods differ (`targets`, per
    /// member; a class object never finds a `Meta::ClassDef` method, so
    /// one found by both is not one): their indices (#491).
    fn classdef_ambiguity(
        &self,
        members: &[Type],
        targets: &[Option<MethodId>],
    ) -> Option<(usize, usize)> {
        self.classdef_overlaps(members)
            .into_iter()
            .find(|&(a, k)| targets.get(a) != targets.get(k))
    }

    /// The pairs of a `Meta::ClassDef[T]` member of a union receiver and a
    /// class-object member that can hold the same class value, as
    /// `classdef_ambiguity` takes them.
    fn classdef_overlaps(&self, members: &[Type]) -> Vec<(usize, usize)> {
        let mut out = Vec::new();
        let b = &self.world.builtin;
        // The class a class value of the member is of (or below), `None`
        // for any class value; not a class value at all: not listed.
        let held = |t: &Type| -> Option<Option<ClassId>> {
            let of = |c: ClassId| {
                (c != b.object && self.world.class(c).kind != ClassKind::Module).then_some(c)
            };
            match self.resolve(t) {
                Type::ClassObject(c, _) => Some(of(c)),
                Type::Class(c, args) if c == b.class_ => match args.first() {
                    Some(Type::Class(a, _)) => Some(of(*a)),
                    _ => Some(None),
                },
                Type::TypeOf(_) => Some(None),
                _ => None,
            }
        };
        for (a, ma) in members.iter().enumerate() {
            let Type::Class(c, args) = self.resolve(ma) else {
                continue;
            };
            if c != b.meta_classdef {
                continue;
            }
            let t = match args.first() {
                Some(Type::Class(t, _)) if *t != b.object => Some(*t),
                _ => None,
            };
            for (k, mb) in members.iter().enumerate() {
                let Some(x) = held(mb) else {
                    continue;
                };
                let overlap = match (t, x) {
                    (Some(t), Some(x)) => {
                        self.world.class_is_a(t, x) || self.world.class_is_a(x, t)
                    }
                    _ => true,
                };
                if overlap {
                    out.push((a, k));
                }
            }
        }
        out
    }

    /// In a block given to a call on a union receiver with a
    /// `Meta::ClassDef` member and a class object that can hold the same
    /// value (`r.instance_exec { def_method(...) }`): an implicit call on
    /// the block's own `self` that the two members' checks answer with
    /// different methods is refused, as the call itself would be (#491).
    fn check_classdef_block(&mut self, members: &[Type], recv: &Type, uses: &[(usize, usize)]) {
        for (a, k) in self.classdef_overlaps(members) {
            let (Some(&ra), Some(&rk)) = (uses.get(a), uses.get(k)) else {
                continue;
            };
            let own = |r: (usize, usize)| r.0..r.1.min(self.self_uses.len());
            let found = own(ra).find_map(|i| {
                let u = &self.self_uses[i];
                if u.fell || u.method.is_none() {
                    return None;
                }
                own(rk)
                    .map(|j| &self.self_uses[j])
                    .find(|v| v.id == u.id && !v.fell && v.method.is_some())
                    .filter(|v| v.method != u.method)
                    .map(|_| (u.name.clone(), u.span))
            });
            if let Some((name, span)) = found {
                let msg = self.classdef_ambiguity_msg(&name, &name, recv, &members[a], &members[k]);
                self.error(msg, span);
                return;
            }
        }
    }

    /// The error for a call `what` (of method `name`) that
    /// `classdef_ambiguity` refuses.
    fn classdef_ambiguity_msg(
        &self,
        what: &str,
        name: &str,
        recv: &Type,
        classdef: &Type,
        other: &Type,
    ) -> String {
        let (c, o) = (self.world.type_name(classdef), self.world.type_name(other));
        format!(
            "`{what}` on {}: a class value may be both the {c} and a {o}, which find different `{name}` methods, and no run-time test tells which one the value stands for; narrow the receiver first (`if r.is_a?({o})` or a `case`)",
            self.name(recv)
        )
    }

    /// The class a run-time class test sees for a value of type `t`.
    /// Whether a check of a block (once per type) records its method for
    /// receiver type `t` (`note_union_table`): a class a run-time test
    /// tells, or a type parameter (tested by the class whose method it
    /// found).
    fn union_testable(&self, t: &Type) -> bool {
        self.test_class(t).is_some() || matches!(t, Type::Param(_))
    }

    fn test_class(&self, t: &Type) -> Option<ClassId> {
        let b = &self.world.builtin;
        match t {
            Type::Class(c, _) => Some(*c),
            Type::Tuple(_) => Some(b.array),
            Type::Proc(..) => Some(b.proc_),
            // (`Type[T]` is a class object as `Type[Foo]` is: two of them
            // a test cannot tell apart.)
            Type::ClassObject(..) | Type::TypeOf(_) => Some(b.class_),
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

    /// Check a compound assignment's logical call (`x.||() { v }` of
    /// `x ||= v`, the value's own `||`) on the node, whose record (the
    /// writer's) is set aside: its own record from earlier checks
    /// (`Output::op_logical_calls`) is put there for the check, and kept
    /// apart after it.
    fn check_op_logical(&mut self, expr: &Expr, name: &str, current: &Type, value: &Expr) -> Type {
        let id = expr.id;
        let writer = self.take_union_record(id);
        let writer_call = self.out.calls.remove(&id);
        let writer_dynamic = self.out.dynamic_calls.remove(&id);
        let before = self.out.op_logical_calls.remove(&id);
        self.table_journal
            .push(TableUndo::OpLogicalCall(id, before.clone()));
        if let Some(r) = &before {
            self.restore_union_record(id, (r.table.clone(), r.conflict));
            if let Some(t) = &r.target {
                self.out.calls.insert(id, t.clone());
            }
            if r.dynamic {
                self.out.dynamic_calls.insert(id);
            }
        }
        let t = self
            .logical_method(expr, name, current, value, None)
            .unwrap_or(Type::Nothing);
        let (table, conflict) = self.take_union_record(id);
        let record = CallRecord {
            target: self.out.calls.remove(&id),
            table,
            conflict,
            dynamic: self.out.dynamic_calls.remove(&id),
        };
        self.out.op_logical_calls.insert(id, record);
        self.restore_union_record(id, writer);
        if let Some(c) = writer_call {
            self.out.calls.insert(id, c);
        }
        if writer_dynamic {
            self.out.dynamic_calls.insert(id);
        }
        t
    }

    /// Check a compound assignment's reader (`w` of `o.w += 1`) on the
    /// node, whose `union_calls` record (the writer's) is set aside: its
    /// own record from earlier checks (`Output::op_getter_tables`) is put
    /// there for the check to merge into, and kept after it.
    fn check_op_reader(&mut self, expr: &Expr, getter: &Call) -> Type {
        let id = expr.id;
        let before = self.out.op_getter_tables.remove(&id);
        self.table_journal
            .push(TableUndo::OpGetterTable(id, before.clone()));
        if let Some((table, conflict)) = before {
            self.restore_union_record(id, ((!table.is_empty()).then_some(table), conflict));
        }
        let t = self.check_call_with_types(expr, getter, None, true);
        let (table, conflict) = self.take_union_record(id);
        if table.is_some() || conflict {
            self.out
                .op_getter_tables
                .insert(id, (table.unwrap_or_default(), conflict));
        }
        self.note_op_getter(id, expr.span);
        t
    }

    /// A compound assignment's reader, resolved just now (a union's
    /// members answering differently are chosen by the receiver's class,
    /// `Output::op_getter_tables`).
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

    /// A variable a bare `super` forwards: the method's parameter (or
    /// block) itself, whatever hides its name where the `super` is (a
    /// block's parameter or `:=`, a pattern's binding), as the lowering
    /// forwards it. Its slots are the method frame's first.
    fn zsuper_local(&self, id: NodeId) -> Option<(usize, usize)> {
        let count = self.zsuper_forwards?;
        let i = (u32::MAX - 1).checked_sub(id)? as usize;
        (i < count).then(|| (self.env.frames.len() - 1, i))
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
        self.bake_refusal(t).is_none()
    }

    /// Why a value of type `t` cannot be baked (`bakeable_type`): `None`
    /// when it can; an empty reason for what is not a literal or data;
    /// for a `data` type or enum with a field that is not Shareable, that
    /// field (every bakeable value is Shareable, as a `Lit`'s `value` is
    /// typed).
    fn bake_refusal(&mut self, t: &Type) -> Option<String> {
        let t = self.resolve(t);
        match &t {
            Type::Nothing | Type::Void | Type::Var(_) | Type::Param(_) => None,
            Type::ClassObject(_, _) | Type::TypeOf(_) => None,
            Type::Union(ms) | Type::Tuple(ms) => {
                ms.clone().iter().find_map(|m| self.bake_refusal(m))
            }
            Type::Proc(..) => Some(String::new()),
            // A field handle names a field: its type arguments are no
            // values (docs/14 §5).
            Type::Class(id, _)
                if *id == self.world.builtin.meta_field_ref
                    || *id == self.world.builtin.meta_method =>
            {
                None
            }
            Type::Class(id, args) => {
                let id = *id;
                let b = &self.world.builtin;
                let literal = [
                    b.nil, b.bool_, b.int, b.integer, b.float, b.string, b.symbol, b.regexp,
                    b.bytes, b.array, b.hash, b.range, b.class_,
                ]
                .contains(&id);
                let class = self.world.class(id);
                let data = matches!(
                    class.kind,
                    ClassKind::Data | ClassKind::Enum | ClassKind::Variant
                );
                if !(literal || data || id == b.object || class.kind == ClassKind::Module) {
                    return Some(String::new());
                }
                if data && self.world.shareable_violation(id).is_some() {
                    return Some(self.unshareable_field(id));
                }
                args.clone().iter().find_map(|a| self.bake_refusal(a))
            }
        }
    }

    /// What makes the `data` type, enum or variant `id` not Shareable,
    /// for `bake_refusal`: "`W` holds `@o: Object`, which is not
    /// Shareable, so its values cannot be baked".
    fn unshareable_field(&mut self, id: ClassId) -> String {
        let class = self.world.class(id).clone();
        let name = class.name.clone();
        let enum_params = class
            .variant_of
            .map(|e| self.world.class(e).type_params.clone());
        let erase: rustc_hash::FxHashMap<TypeParamId, Type> = class
            .type_params
            .iter()
            .chain(enum_params.iter().flatten())
            .map(|p| (p.id, Type::Nothing))
            .collect();
        for (f, subst) in self.world.all_fields(id) {
            let ty = f.ty.subst(&subst).subst(&erase);
            if !self.world.is_shareable(&ty) {
                return format!(
                    "`{name}` holds `@{}: {}`, which is not Shareable, so its values cannot be baked",
                    f.name,
                    self.world.type_name(&ty)
                );
            }
        }
        for v in class.variants.clone() {
            if self.world.shareable_violation(v).is_some() {
                return self.unshareable_field(v);
            }
        }
        let why = self.world.shareable_violation(id).unwrap_or_default();
        format!("`{name}` cannot be baked: {why}")
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
        // (From outside the block of `static(...)`, whatever task or
        // shareable block inside it captures it.)
        let at = self.env.frames.len() - 1 - depth;
        if self.env.static_frame.is_some_and(|sf| at < sf) {
            self.error(
                format!("a block in `static(...)` captures nothing: `{name}` is not a constant (docs/14 §8)"),
                span,
            );
            return;
        }
        let rt = self.resolve(t);
        // Not decided yet: what decides it later may not be Shareable,
        // and the task has it already (docs/03).
        if rt.has_vars() {
            // (A block given to `def_method` bakes what it captures: no
            // other task has it.)
            let lifted =
                self.env.lifted_frame.is_some() && self.env.lifted_frame == self.env.task_frame;
            if !lifted && self.world.refuse_undecided() {
                self.error(
                    format!("the type of `{name}` is not yet known here, but {} must have a Shareable one: annotate it (as `{name}: Array[Int] = []`)", self.task_capture_name()),
                    span,
                );
            }
            return;
        }
        if self.env.lifted_frame.is_some() && self.env.lifted_frame == self.env.task_frame {
            // (`type`'s `Self` is the class the `static def` runs on: in a
            // method generated into another class, it is not that `Self`.)
            if self.env.lifted_foreign && rt.mentions_param(SELF_PARAM) {
                self.error(
                    format!(
                        "`{name}` has type {}, of the class this `static def` runs on, but the method is generated into another class: generate it from that class's own `static def` (`type` is the class its statement runs on)",
                        self.world.type_name(&rt)
                    ),
                    span,
                );
                return;
            }
            if let Some(why) = self.bake_refusal(&rt) {
                let why = if why.is_empty() {
                    String::new()
                } else {
                    format!(" ({why})")
                };
                self.error(
                    format!(
                        "`{name}` has type {}, whose values cannot be baked into a generated method{why}; a block given to `def_method` captures only immutable values (literals, classes, `data` of Shareable fields)",
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

    /// `y: T = e` and `y := e`: a new variable in the innermost scope (the
    /// frame's, or a `case/in` arm's or rescue clause's), hiding one of the
    /// name in an outer scope; one already in this scope is an error.
    fn check_typed_decl(
        &mut self,
        expr: &Expr,
        name: &str,
        ty: Option<&TypeExpr>,
        value: &Expr,
    ) -> Type {
        // The value first: it reads an outer variable of the name.
        let (declared, narrowed, result) = match ty {
            Some(ty) => {
                let scope = self.env.scope.clone();
                let Some(declared) = self.resolve_type_expr(ty, &scope) else {
                    self.check_expr(value, None);
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
                let narrowed = self.resolve(&vt);
                (declared.clone(), narrowed, declared)
            }
            // The value's type, as for a new name assigned with `=`.
            None => {
                let vt = self.check_expr(value, None);
                let t = self.resolve(&vt);
                let t = if t.is_nothing() { self.world.nil() } else { t };
                // `x := [1, "a"]`: an array of the union, narrowed to the
                // tuple (as `x = [1, "a"]` is).
                let declared = match (&t, &value.kind) {
                    (Type::Tuple(ts), ExprKind::Array(_)) => {
                        self.world.array_of(self.world.tuple_element(ts))
                    }
                    _ => t.clone(),
                };
                (declared, t, vt)
            }
        };
        let frame = self.env.frames.len() - 1;
        let start = match &self.env.decl_scope {
            Some(s) if s.frame == frame => s.start,
            _ => 0,
        };
        if self.env.frames[frame]
            .vars
            .find(name)
            .is_some_and(|slot| slot >= start)
        {
            self.error(
                format!(
                    "`{name}` is already declared in this scope; a local variable's type is fixed at its declaration"
                ),
                expr.span,
            );
        }
        let slot = self.declare_var(name, declared, expr.span).slot as usize;
        if let Some(s) = self.env.decl_scope.as_mut().filter(|s| s.frame == frame) {
            s.declared.push(slot);
        }
        self.set_narrowed(&VarKey::Local(name.to_string()), Some(narrowed));
        result
    }

    /// Check `f` as a scope within the frame (a `case/in` arm's body, a
    /// rescue clause's) starting at slot `start`: the variables declared
    /// in it are hidden after it (their slots stay, for the code that
    /// refers to them).
    fn in_decl_scope<R>(&mut self, start: usize, f: impl FnOnce(&mut Self) -> R) -> R {
        let saved = self.enter_decl_scope(start);
        let r = f(self);
        self.leave_decl_scope(saved);
        r
    }

    /// Begin a scope within the frame at slot `start` (`in_decl_scope`);
    /// returns what `leave_decl_scope` restores.
    fn enter_decl_scope(&mut self, start: usize) -> Option<DeclScope> {
        let frame = self.env.frames.len() - 1;
        self.env.decl_scope.replace(DeclScope {
            frame,
            start,
            declared: Vec::new(),
        })
    }

    fn leave_decl_scope(&mut self, saved: Option<DeclScope>) {
        let scope = std::mem::replace(&mut self.env.decl_scope, saved).unwrap();
        let vars = &mut self.env.frames[scope.frame].vars;
        for slot in scope.declared {
            let hidden = format!("{} (declared in a scope that ended)", vars.list[slot].name);
            vars.rename(slot, hidden);
        }
    }

    /// A variable holds a value of type `t`: its literals' element types
    /// are no longer decided where they are joined (`literal_vars`).
    fn held(&mut self, t: &Type) {
        if self.literal_vars.is_empty() {
            return;
        }
        let mut found = Vec::new();
        Self::vars_in(&self.infer.resolve(t), &mut found);
        for v in found {
            self.literal_vars.remove(&v);
        }
    }

    fn vars_in(t: &Type, out: &mut Vec<InferVar>) {
        match t {
            Type::Var(v) => out.push(*v),
            Type::Class(_, args) | Type::ClassObject(_, args) => {
                args.iter().for_each(|x| Self::vars_in(x, out))
            }
            Type::Union(ms) | Type::Tuple(ms) => ms.iter().for_each(|x| Self::vars_in(x, out)),
            Type::TypeOf(x) => Self::vars_in(x, out),
            Type::Proc(rc, ps, r, _, kws) => {
                rc.iter().for_each(|x| Self::vars_in(x, out));
                ps.iter().for_each(|x| Self::vars_in(x, out));
                kws.iter().for_each(|k| Self::vars_in(&k.ty, out));
                Self::vars_in(r, out);
            }
            _ => {}
        }
    }

    /// Decide `a`'s literal element types (`literal_vars`) from `b` where
    /// both have the same shape: `cond ? [1] : []`, `[[1]]` and `[[]]`.
    /// Seen as `Shareable` (or a promising module), a literal's element
    /// types no variable holds are decided as `Nothing`: nothing can add
    /// to it later (`ch.send(c ? [] : [])`).
    fn decide_literals_for(&mut self, target: ClassId, args: &[Type]) {
        if self.literal_vars.is_empty()
            || self.checking_bound
            || !self.shareable_target(&Type::class(target))
        {
            return;
        }
        let mut found = Vec::new();
        for a in args {
            Self::vars_in(&self.infer.resolve(a), &mut found);
        }
        for v in found {
            if self.literal_vars.contains(&v) {
                self.infer.bind(v, Type::Nothing);
            }
        }
    }

    fn bind_literals(&mut self, a: &Type, b: &Type) {
        let (a, b) = (self.infer.resolve(a), self.infer.resolve(b));
        match (&a, &b) {
            (Type::Var(v), t) | (t, Type::Var(v)) if self.literal_vars.contains(v) => {
                match t {
                    Type::Var(w) if self.literal_vars.contains(w) && w != v => {
                        // Two empty literals: one type, decided together.
                        self.infer.bind(*v, t.clone());
                    }
                    t if !t.has_vars() => {
                        let t = self.world.erase_narrowed(t);
                        self.infer.bind(*v, t);
                    }
                    _ => {}
                }
            }
            (Type::Class(c1, a1), Type::Class(c2, a2)) if c1 == c2 && a1.len() == a2.len() => {
                for (x, y) in a1.clone().iter().zip(a2.clone().iter()) {
                    self.bind_literals(x, y);
                }
            }
            _ => {}
        }
    }

    fn declare_var(&mut self, name: &str, ty: Type, span: Span) -> VarRef {
        self.held(&ty);
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
        if let Some(t) = &t {
            self.held(t);
        }
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
        // matched (a fact), and its old one where it did not: a failed
        // match leaves it as it was (the run time puts back what it bound,
        // docs/01 §11).
        for (fi, slot, name, before, now) in self.rebound_since(snap) {
            facts.push((VarKey::Local(name), now));
            self.env.frames[fi].vars.set_narrowed(slot, Some(before));
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
            Type::Proc(rc, ps, r, _, kws) => {
                if let Some(rc) = rc {
                    self.settle_in(rc);
                }
                ps.iter().for_each(|p| self.settle_in(p));
                kws.iter().for_each(|k| self.settle_in(&k.ty));
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

    /// `assigned_names` over a scope's body (the one `widen_assigned`
    /// begins with, a block's, a `case/in` arm's, a rescue clause's): in
    /// the walk for `widen_assigned` (`Assigned::widening`), from a
    /// declaration directly in it (`y := e`) to its end, `y` is that
    /// scope's own variable, not the one of the name in scope at the
    /// start, which is all that walk acts on. Every other walk keeps what
    /// it learns by name for the whole body (`scan_closures`,
    /// `prescan_repeated`), the declared variable's own included: there a
    /// declaration counts against the name, which only widens or pins
    /// more. (So does a declaration deeper, in an `if`'s body.)
    fn assigned_names_scope(exprs: &[Expr], out: &mut Assigned) {
        if !out.widening {
            return Self::assigned_names(exprs, out);
        }
        for (i, e) in exprs.iter().enumerate() {
            if let ExprKind::TypedDecl { name, value, .. } = &e.kind {
                Self::assigned_names_expr(value, out);
                out.scoped(name, |out| {
                    out.add(name);
                    Self::assigned_names_scope(&exprs[i + 1..], out);
                });
                return;
            }
            Self::assigned_names_expr(e, out);
        }
    }

    /// Whether a rescue clause's body assigns its variable `v` (or rebinds
    /// it by a bang).
    fn clause_reassigns(v: &str, body: &[Expr]) -> bool {
        let mut probe = Assigned::default();
        Self::assigned_names_scope(body, &mut probe);
        probe.names.contains(v) || probe.bangs.iter().any(|(n, _)| n == v)
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
                // (Not in a block: its receiver may be another's.)
                if call.recv.is_none() && call.name == "new" && out.closure_depth == 0 {
                    out.implicit_new = true;
                }
                if call
                    .recv
                    .as_ref()
                    .is_none_or(|r| matches!(r.kind, ExprKind::SelfRef))
                {
                    out.self_calls.insert(call.name.clone());
                }
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
                    Self::assigned_names_scope(&a.body, out);
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
                    // (The clause's variable is its own, docs/01 §12: the
                    // walk for `widen_assigned` leaves it out, as a
                    // declaration's; every other walk keeps what it learns
                    // by name, so a closure capturing it narrowed sees it
                    // reassigned, `assigned_names_scope`.)
                    match &r.var {
                        Some(v) if out.widening => {
                            out.scoped(v, |out| Self::assigned_names_scope(&r.body, out))
                        }
                        // Reassigned in its clause: a local the clause
                        // binds and assigns, so a closure capturing it
                        // narrowed sees it change. Otherwise the clause's
                        // own, as a block's parameter (another clause's of
                        // the name counts nothing against it).
                        // (So does a clause that runs again, in a loop or by
                        // `retry`: each run rebinds the one variable.)
                        Some(v)
                            if Self::clause_reassigns(v, &r.body) || out.repeat > 0 || retried =>
                        {
                            out.repeat += retried as u32;
                            out.add(v);
                            Self::assigned_names_scope(&r.body, out);
                            out.repeat -= retried as u32;
                        }
                        Some(v) => out.scoped(v, |out| Self::assigned_names_scope(&r.body, out)),
                        None => Self::assigned_names_scope(&r.body, out),
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
                out.super_span.get_or_insert(e.span);
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

    /// Whether `body` calls `new` with no receiver, outside its blocks and
    /// lambdas (a class method's `new` builds its receiver's class:
    /// `MethodInfo::builds_self`; in a block, whose receiver may be
    /// another object, it is left to the run-time check).
    pub(crate) fn calls_new(body: &[Expr]) -> bool {
        let mut a = Assigned::default();
        Self::assigned_names(body, &mut a);
        a.implicit_new
    }

    /// The names `body` calls with no receiver or on `self`, in its blocks
    /// too (`MethodInfo::needs_includer`).
    pub(crate) fn self_calls(body: &[Expr]) -> HashSet<String> {
        let mut a = Assigned::default();
        Self::assigned_names(body, &mut a);
        a.self_calls
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
        // What the body assigns un-narrows the variables in scope now, at
        // its start: one it declares (`y := e`) is not yet, and assigning
        // it does not change the outer `y` (`assigned_names_scope`).
        let mut assigned = Assigned {
            widening: true,
            ..Assigned::default()
        };
        match own {
            Some(v) => assigned.scoped(v, |a| Self::assigned_names_scope(body, a)),
            None => Self::assigned_names_scope(body, &mut assigned),
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
    /// Whether `m` runs its block in a task (`Task.spawn`, `Task::Scope#spawn`,
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
        self.env
            .blocks
            .iter()
            .rev()
            .take_while(|b| !b.init)
            .any(|b| b.is_lambda || b.escapes)
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

    /// The error for a module's class method that depends on the class
    /// including the module (`MethodInfo::needs_includer`), called (or
    /// referred to) on the module `cid` itself (#494).
    fn module_call_refusal(&self, cid: ClassId, method: MethodId) -> Option<String> {
        let m = self.world.method(method);
        let why = m.needs_includer.as_ref()?;
        if self.world.class(cid).kind != ClassKind::Module || !m.singleton {
            return None;
        }
        let (module, name) = (&self.world.class(cid).name, &m.name);
        Some(format!(
            "cannot call `{module}.{name}` on the module itself: `{name}` {why}; call it on a class that includes `{module}`"
        ))
    }

    /// Whether `Self` appears in the method's signature.
    pub(crate) fn mentions_self(m: &MethodInfo) -> bool {
        let is = |t: &Type| t.mentions_param(SELF_PARAM);
        m.params.iter().any(|p| is(&p.ty))
            || m.block.as_ref().is_some_and(|(_, t)| is(t))
            || is(&m.ret)
    }

    /// Whether the code is a class's `static def self.` (its own `self`,
    /// a `Meta::ClassDef` of the class), outside blocks.
    fn static_class_self(&self) -> bool {
        self.env.is_static
            && self.env.receivers.is_empty()
            && self
                .env
                .method
                .is_some_and(|m| self.world.method(m).singleton)
            && matches!(&self.env.self_type, Type::Class(c, _) if *c == self.world.builtin.meta_classdef)
    }

    /// Whether `self` is the method's own `self` with the opaque type
    /// `Self` (an instance method whose signature mentions `Self`, outside
    /// blocks run with another receiver).
    fn self_is_opaque(&self) -> bool {
        // (A class method's `self`, a class, is no `Self`: its instances
        // are; nor is a class's `static def`'s, a `Meta::ClassDef`.)
        self.env.self_opaque && self.own_self() && self.env.self_is_self
    }

    /// Whether `self` here is the method's own: no block with a receiver
    /// is around, or the innermost is a block lifted to a generated
    /// method, whose receiver is that method's `self` (docs/14 §5).
    fn own_self(&self) -> bool {
        match (self.env.receivers.last(), self.env.lifted_frame) {
            (None, _) => true,
            (Some(r), Some(lf)) => r.outer_frame + 1 == lf,
            _ => false,
        }
    }

    /// Whether a call with an implicit or explicit `self` receiver of type
    /// `recv` binds `Self` opaquely: an instance method's `self`, or a
    /// class method's receiver (whose instances `Self` stands for).
    fn self_is_opaque_for(&self, recv: &Type, m: &MethodInfo) -> bool {
        // (On a class, `Self` stays opaque for a class method of it, `new`
        // or `build`, whose `Self` is the class's instances; an instance
        // method of `Type` or `Object`, `dup` say, binds it to the class.)
        self.env.self_opaque
            && self.own_self()
            && (*recv == Type::Param(SELF_PARAM) || *recv == self.env.self_type)
            && (self.env.self_is_self || m.singleton)
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
        let active_len = self.world.active_extensions.get_mut().len();
        let local_len = self.local_usings.len();
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
        self.world.active_extensions.get_mut().truncate(active_len);
        self.local_usings.truncate(local_len);
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
                    if !self.world.active_extensions.get_mut().contains(&e) {
                        self.local_usings.push(e);
                        self.world.active_extensions.get_mut().push(e);
                    }
                }
            }
            Some(_) => self.error(format!("`using {path}`: not a module"), span),
            None => {}
        }
    }

    // ----- expressions --------------------------------------------------------

    pub fn check_expr(&mut self, expr: &Expr, expected: Option<&Type>) -> Type {
        // An argument of a compound assignment's writer, already typed
        // (nothing is recorded for its node).
        if let Some(t) = OP_VALUE_ID
            .checked_sub(expr.id)
            .and_then(|i| self.op_values.get(i as usize))
        {
            return t.clone();
        }
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
        self.recording_span = expr.span;
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
            let ambiguities = self.extension_ambiguities;
            self.check_expr(&f.each, None);
            let failed = self.diagnostics[reported..]
                .iter()
                .any(|(_, d)| d.is_error());
            // (An ambiguous `each`, #577: its error, not the fallback's.)
            if !failed || self.extension_ambiguities > ambiguities {
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
                if self.function_self() {
                    self.error(
                        "a function has no `self`: pass what it needs as an argument (a top-level `def` is a function, not a method of an object)",
                        expr.span,
                    );
                    return Type::Nothing;
                }
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
                let range = Type::Class(self.world.builtin.range, vec![t.clone()]);
                self.check_range_bound(&t, expr.span);
                range
            }
            Lambda(block) => self.check_lambda(expr.id, block, expected),
            Local(name) => match self.zsuper_local(expr.id).or_else(|| self.lookup_var(name)) {
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
                let uses = self.self_uses.len();
                let t = self.check_call(expr, call, expected);
                // `x.is_a?(k)` with a class value (`Object#is_a?`): against
                // a type parameter's class value, checked as a test against
                // each module the parameter may be (#598).
                if let (Some(recv), "is_a?", [Arg::Positional(a)]) =
                    (&call.recv, call.name.as_str(), call.args.as_slice())
                {
                    if !matches!(a.kind, ExprKind::Const(_) | ExprKind::TypeApp(_)) {
                        let rt = self.out.node_types.get(&recv.id).cloned();
                        let at = self.out.node_types.get(&a.id).cloned();
                        if let (Some(rt), Some(at)) = (rt, at) {
                            let (rt, at) = (self.resolve(&rt), self.resolve(&at));
                            self.check_testable_param(&rt, &at, "is_a?", a.span);
                        }
                    }
                }
                if self.self_uses.len() > uses {
                    let method = match self.out.calls.get(&expr.id) {
                        Some(CallTarget::Method { method }) => Some(*method),
                        _ => None,
                    };
                    for u in &mut self.self_uses[uses..] {
                        if u.id == expr.id && u.method.is_none() {
                            u.method = method;
                        }
                    }
                }
                self.check_dup(expr, call);
                // `bump` in a `Task.spawn` block in a method of a mutable
                // class: a call on the captured `self` (a call to a
                // built-in `Kernel` function such as `puts`, or to a
                // top-level `def`, does not use it; one an `extension
                // Kernel` adds does).
                // (A call that fell through to an enclosing `self` was
                // checked where it bound it, `bind_outer_self`.)
                if call.recv.is_none() && !self.out.outer_self_calls.contains(&expr.id) {
                    if let Some(CallTarget::Method { method }) = self.out.calls.get(&expr.id) {
                        let method = *method;
                        if !self.world.takes_no_self(method) {
                            let what = format!("calling `{}` uses `self`, which", call.name);
                            self.check_task_self(&what, expr.span);
                        } else if self.env.static_frame.is_some()
                            && self.world.class(self.world.method(method).owner).kind
                                == ClassKind::Main
                        {
                            // A function has no `self`: one compiled before
                            // this file (of a cog or required file it
                            // depends on) captures nothing; one of its own
                            // is not compiled yet when the block runs
                            // (docs/14 §8), also from a block with a
                            // receiver inside the static block.
                            let m = self.world.method(method).clone();
                            if let Err(why) = self.static_stage(&m) {
                                self.error(
                                    format!("`{}` is a function of {why}, not yet compiled when `static(...)` runs: only functions of the cogs (or required files) this file depends on can be called here (docs/14 §8)", call.name),
                                    expr.span,
                                );
                            }
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
                let (mid, subst) = match self.by_name_choice(&rt, mid, &cands) {
                    Ok(m) => cands
                        .iter()
                        .find(|(k, _)| *k == m)
                        .cloned()
                        .unwrap_or((mid, subst)),
                    Err((a, b, ea, eb)) => {
                        self.extension_ambiguity(name, a, b, ea, eb, expr.span);
                        return Type::Nothing;
                    }
                };
                let m = self.world.method(mid).clone();
                // Visibility, as a call's (#582): a private method only on
                // `self`, a protected one also from an instance of its
                // class.
                let on_self = matches!(recv.kind, ExprKind::SelfRef);
                if m.visibility == quarz_syntax::ast::Visibility::Private && !on_self {
                    self.error(
                        format!(
                            "`{name}` is private (in `.:{name}`): it is referenced only on `self`"
                        ),
                        expr.span,
                    );
                    return Type::Nothing;
                }
                if m.visibility == quarz_syntax::ast::Visibility::Protected
                    && !on_self
                    && !self.may_call_protected(m.owner)
                {
                    self.error(
                        format!(
                            "`{name}` is protected (in `.:{name}`): it is referenced on another receiver only from an instance of {}",
                            self.world.class(m.owner).name
                        ),
                        expr.span,
                    );
                    return Type::Nothing;
                }
                // `initialize` runs only from `new` and `super` (docs/01
                // §3): a reference to it would run it on a made object.
                if name == "initialize" && !m.singleton {
                    self.error(
                        "`initialize` is called only by `new` and by `super` in `initialize` (in `.:initialize`)",
                        expr.span,
                    );
                    return Type::Nothing;
                }
                // `JSON.decode[T]` takes `T` written at its call, which a
                // reference cannot give.
                if crate::json_decode::is_decode(&self.world, &m) {
                    self.error(
                        format!(
                            "`JSON.{name}` takes the type to decode into written at the call: call it (`JSON.{name}[Args](text)`), there is no reference to it"
                        ),
                        expr.span,
                    );
                    return Type::Nothing;
                }
                if name == "deinitialize" && !m.singleton {
                    self.error(
                        format!("{DEINITIALIZE_CALLED} (in `.:deinitialize`)"),
                        expr.span,
                    );
                    return Type::Nothing;
                }
                // (`M.:make` on the module itself, as the call `M.make`.)
                if let Some(ConstTarget::Class(c)) = self.out.const_targets.get(&recv.id).cloned() {
                    if let Some(msg) = self.module_call_refusal(c, mid) {
                        self.error(msg, expr.span);
                        return Type::Nothing;
                    }
                }
                let mut subst = subst;
                subst.insert(SELF_PARAM, Self::self_binding(&self.world, &m, &rt));
                let params: Vec<Type> = m
                    .params
                    .iter()
                    .filter(|p| p.kind == ParamKind::Positional)
                    .map(|p| p.ty.subst(&subst))
                    .collect();
                // The method's required keywords are the handle's (docs/02
                // §9); one with a default stays out of its type, and the
                // handle takes the default.
                let keywords: Vec<ProcKw> = m
                    .params
                    .iter()
                    .filter(|p| p.kind == ParamKind::KeywordOnly && p.default.is_none())
                    .map(|p| ProcKw {
                        name: p.name.clone(),
                        ty: p.ty.subst(&subst),
                        required: true,
                    })
                    .collect();
                let ret = self.method_ret(mid).subst(&subst);
                // A block checked once per type of what it is given may
                // find another method each time: the reference chooses by
                // the receiver's class at run time (`union_calls`, as a
                // call does).
                if !self.env.blocks.is_empty() && self.union_testable(&rt) {
                    self.note_union_table(expr.id, vec![(rt.clone(), mid)], expr.span);
                }
                let before = self.out.calls.get(&expr.id).cloned();
                self.table_journal
                    .push(TableUndo::MethodRefCall(expr.id, before));
                self.out
                    .calls
                    .insert(expr.id, CallTarget::Method { method: mid });
                self.note_static_call(expr, mid);
                Type::Proc(None, params, Box::new(ret), false, ProcKw::sorted(keywords))
            }
            Yield(args) => self.check_yield(expr, args),
            Super { args, block } => self.check_super(expr, args.as_deref(), block.as_deref()),
            Assign { target, value } => self.check_assign(expr, target, value, expected),
            OpAssign { target, op, value } => self.check_op_assign(expr, target, *op, value),
            MultiAssign { targets, value } => self.check_multi_assign(expr, targets, value),
            TypedDecl { name, ty, value } => self.check_typed_decl(expr, name, ty.as_ref(), value),
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
                // The loop's value is `nil` when its condition ends it, else
                // a `break`'s value: a loop with no normal exit has only the
                // breaks' types (`Nothing` with none).
                let mut t = if infinite {
                    Type::Nothing
                } else {
                    self.world.nil()
                };
                for b in &exits.break_types {
                    t = self.join(&t, b);
                }
                t
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
                // A `return` leaves the innermost lambda around it, through
                // the blocks inside that lambda (as at run time); else the
                // method. A block given to `def_method` or to `static(...)`'s
                // call with no lambda inside it around the `return` cannot
                // be left that way.
                let lambda_at = self.env.blocks.iter().rposition(|b| b.is_lambda);
                let left = |pos: Option<usize>| match (pos, lambda_at) {
                    (Some(p), Some(l)) => l < p,
                    (Some(_), None) => true,
                    (None, _) => false,
                };
                let past_lifted = left(self.env.blocks.iter().rposition(|b| b.lifted));
                let past_static = left(self.env.blocks.iter().rposition(|b| b.static_call));
                let past_task = left(self.env.blocks.iter().rposition(|b| b.task.is_some()));
                let past_shareable = left(self.env.blocks.iter().rposition(|b| b.shareable));
                if past_lifted {
                    self.error(
                        "`return` in a block given to `def_method`: the block becomes the generated method's body, whose value is its last expression",
                        expr.span,
                    );
                    if let Some(v) = value {
                        self.check_expr(v, None);
                    }
                    return Type::Nothing;
                }
                // The block of `static(...)`'s call runs at compile time,
                // where the code around it is not running (docs/14 §8).
                if past_static {
                    self.error(
                        "`return` in the block of `static(...)`'s call: it runs at compile time, where the code around it is not running to return from (give the value as the block's last expression, or `next` it)",
                        expr.span,
                    );
                    if let Some(v) = value {
                        self.check_expr(v, None);
                    }
                    return Type::Nothing;
                }
                // A task's block runs in another task, where the method
                // (or lambda) around it is not running.
                if past_task {
                    self.error(
                        "`return` in a task's block: it runs in another task, where the method around it is not running to return from (give the value as the block's last expression, or `next` it)",
                        expr.span,
                    );
                    if let Some(v) = value {
                        self.check_expr(v, None);
                    }
                    return Type::Nothing;
                }
                // So may a block given where a `shareable` procedure type
                // is expected: the method may run it in a task of its own,
                // or after it has returned.
                if past_shareable {
                    self.error(
                        "`return` cannot leave a shareable block: it may run in another task or after its method has returned; use `next value`",
                        expr.span,
                    );
                    if let Some(v) = value {
                        self.check_expr(v, None);
                    }
                    return Type::Nothing;
                }
                if let Some(l) = lambda_at {
                    let ret = self.env.blocks[l].ret.clone();
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
                // A task's block runs in another task: there is no call
                // around it to leave (its value is the task's result).
                let task = self.env.blocks.last().and_then(|b| b.task.clone());
                if let (0, Some(name)) = (self.env.loop_depth, task) {
                    self.error(
                        format!("`break` cannot leave `{name}`: its block runs in another task; use `next value` for the task's result"),
                        expr.span,
                    );
                    if let Some(v) = value {
                        self.check_expr(v, None);
                    }
                    return Type::Nothing;
                }
                if self.env.loop_depth == 0 && self.env.blocks.last().is_some_and(|b| b.shareable) {
                    self.error(
                        "`break` cannot leave a shareable block: it may run in another task or after its method has returned; use `next value`",
                        expr.span,
                    );
                    if let Some(v) = value {
                        self.check_expr(v, None);
                    }
                    return Type::Nothing;
                }
                let t = match value {
                    Some(v) => self.check_expr(v, None),
                    None => self.world.nil(),
                };
                if self.env.loop_depth > 0 {
                    let snap = self.snapshot();
                    self.env.loop_exits.breaks.push(snap);
                    self.env.loop_exits.break_types.push(t);
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
                        "`retry` outside of a rescue clause (it must be directly in one, not in a block or an `ensure` body)",
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
                    // (Those an interpolation can call: no argument nor block.)
                    let cands: Vec<_> = self
                        .world
                        .lookup_methods(&m, "to_s")
                        .into_iter()
                        .filter(|(id, subst)| {
                            let m = self.world.method(*id);
                            m.params.is_empty()
                                && m.block.is_none()
                                && self.extension_bounds_hold(*id, subst)
                        })
                        .collect();
                    let to_s = cands.first().map(|(m, _)| *m);
                    // (Two active extensions' modules both giving it, #577.)
                    let to_s = match to_s.map(|t| self.by_name_choice(&m, t, &cands)) {
                        Some(Err((a, b, ea, eb))) => {
                            self.extension_ambiguity("to_s", a, b, ea, eb, e.span);
                            continue;
                        }
                        Some(Ok(t)) => Some(t),
                        None => None,
                    };
                    // (Called directly when the run time's lookup by name
                    // would not find it: an extension's own `to_s`, or a
                    // module's that only an active scoped or conditional
                    // extension includes, outside `RtClass::lookup`;
                    // docs/01 §7: the `to_s` found for the type here.)
                    let found = to_s.filter(|m| {
                        let mi = self.world.method(*m);
                        mi.extension.is_some()
                            || !self.world.lookup_ancestors(cid).contains(&mi.owner)
                    });
                    self.note_interp_to_s(e.id, cid, found, e.span);
                }
            }
        }
    }

    fn check_array(&mut self, items: &[Arg], expected: Option<&Type>, span: Span) -> Type {
        // Where a `Shareable` (or a module promising it) is expected, an
        // array of Shareable values: an empty one, or one of empty ones,
        // is no type left undecided (no variable holds the literal).
        if let Some(e) = expected {
            if self.shareable_target(e) {
                let t = Type::Class(self.world.builtin.array, vec![e.clone()]);
                return self.check_array(items, Some(&t), span);
            }
        }
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
            // (A literal's own: decided where it is joined or ends a task
            // block, until a variable holds it.)
            if let Type::Var(v) = elem {
                self.literal_vars.insert(v);
            }
        }
        self.world.array_of(elem)
    }

    /// Decide the variables left in `t` as `Nothing` (a literal's element
    /// types, when no variable holds it).
    fn decide_as_nothing(&mut self, t: &Type) {
        fn vars(t: &Type, out: &mut Vec<InferVar>) {
            match t {
                Type::Var(v) => out.push(*v),
                Type::Class(_, args) | Type::ClassObject(_, args) => {
                    args.iter().for_each(|x| vars(x, out))
                }
                Type::Union(ms) | Type::Tuple(ms) => ms.iter().for_each(|x| vars(x, out)),
                _ => {}
            }
        }
        let mut found = Vec::new();
        vars(t, &mut found);
        for v in found {
            self.infer.bind(v, Type::Nothing);
        }
    }

    /// Whether `t` is `Shareable` or a module promising it: what a literal
    /// expected there holds must be Shareable (`check_array`,
    /// `check_hash`).
    fn shareable_target(&self, t: &Type) -> bool {
        let t = self.infer.resolve(t).without_nil(self.world.builtin.nil);
        match t {
            Type::Class(id, _) => {
                id == self.world.builtin.shareable
                    || (self.world.class(id).kind == ClassKind::Module
                        && self.world.shareable_promise(id).is_some())
            }
            _ => false,
        }
    }

    fn check_hash(&mut self, entries: &[HashEntry], expected: Option<&Type>) -> Type {
        if let Some(e) = expected {
            if self.shareable_target(e) {
                let t = Type::Class(self.world.builtin.hash, vec![e.clone(), e.clone()]);
                return self.check_hash(entries, Some(&t));
            }
        }
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
            if let Type::Var(v) = kt {
                self.literal_vars.insert(v);
            }
        }
        if vt.is_nothing() {
            vt = self.infer.fresh();
            if let Type::Var(v) = vt {
                self.literal_vars.insert(v);
            }
        }
        self.world.hash_of(kt, vt)
    }

    /// `World::find_field` as seen from where it is read: the class's type
    /// parameters are the arguments of `self`'s type when that is the class
    /// (in a method of an extension of it, `extension Box[U]` of `class
    /// Box[T]`, the extension's: `@x: T` is a `U` there; in a block run
    /// with another `Box[String]` for `self`, `String`), else the method's
    /// own (its class's, or an extension's for an opaque `Self`).
    fn find_field_here(
        &self,
        cid: ClassId,
        name: &str,
    ) -> Option<(FieldInfo, HashMap<TypeParamId, Type>)> {
        let (field, subst) = self.world.find_field(cid, name)?;
        let args = match &self.env.self_type {
            Type::Class(c, args) if *c == cid => Some(args.clone()),
            _ => self
                .env
                .method
                .and_then(|m| self.world.method(m).extension)
                .map(|e| &self.world.extensions[e as usize])
                .filter(|e| e.target == cid)
                .map(|e| e.target_args.clone()),
        };
        let Some(args) = args else {
            return Some((field, subst));
        };
        let map: HashMap<TypeParamId, Type> = self
            .world
            .class(cid)
            .type_params
            .iter()
            .map(|p| p.id)
            .zip(args)
            .collect();
        let mut composed: HashMap<TypeParamId, Type> =
            subst.iter().map(|(k, v)| (*k, v.subst(&map))).collect();
        for (k, v) in map {
            composed.entry(k).or_insert(v);
        }
        Some((field, composed))
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
        let Some((field, subst)) = self.find_field_here(cid, name) else {
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
            self.world.resolve_absolute(namespace, &path.names[0])
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
            } else if matches!(&tgt, Type::ClassObject(tid, _) if self.class_value_may_be(&m, *tid))
            {
                // A class value that may be of the class: a `Type[M]` of a
                // module, a `Type[T]`, a `Cog` (a `Type` subclass).
                yes.push(tgt.clone());
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

    /// Whether a value of type `m`, not a `Type[C]` nor a supertype of
    /// one, may still be a class value whose class is `<= c`: through a
    /// module (`Type[Tagged]` holding a `Model`), a type parameter
    /// (`Type[T]`), or a subclass of `Type` (`Cog`).
    fn class_value_may_be(&self, m: &Type, c: ClassId) -> bool {
        match m {
            Type::ClassObject(mid, _) => {
                self.world.class(*mid).kind == ClassKind::Module
                    || self.world.class(c).kind == ClassKind::Module
            }
            Type::TypeOf(_) => true,
            Type::Class(mid, _) => self.world.class_is_a(*mid, self.world.builtin.class_),
            _ => false,
        }
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
                    // (A type parameter's class value: a test, #598.)
                    let st2 = self.resolve(st);
                    self.check_testable_param(&st2, &ct, "when", ce.span);
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
                        // A `rescue` class is a run-time test as `is_a?` is
                        // (docs/02 §7, #533): of a raised value, of any
                        // exception class, it sees the class only.
                        let raised = Type::class(self.world.builtin.exception);
                        self.check_testable(&raised, &t, "rescue", c.span);
                        exc_ty = self.join(&exc_ty, &t);
                        class_ids.push(id);
                    }
                    // (`Self` of a method whose signature mentions it: the
                    // class or a subclass, not known which.)
                    Some(Type::Param(SELF_PARAM)) => self.error(
                        "`rescue Self` names no class here: in a method whose signature mentions `Self`, `Self` is the class or a subclass, not known which (name the class)",
                        c.span,
                    ),
                    Some(_) => self.error("`rescue` needs exception classes", c.span),
                    None => {}
                }
            }
            self.out.rescue_classes.insert(r.span, class_ids);
            // The clause's variable is its own, as a block's parameter:
            // declared fresh with the clause's classes, shadowing an outer
            // local of the name, and gone after the clause (docs/01 §12).
            let clause_start = self.env.frames.last().unwrap().vars.len();
            let own = r
                .var
                .as_ref()
                .map(|var| self.declare_var(var, exc_ty.clone(), r.span).slot as usize);
            self.env.in_rescue += 1;
            // (A scope of its own, for what it declares: `y := e`.)
            let rt = self.in_decl_scope(clause_start, |c| c.check_body(&r.body, expected));
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
            // Not in the clause it may be nested in: a `retry` there would
            // restart a `begin` the jump through the `ensure` has left.
            let rescuing = std::mem::take(&mut self.env.in_rescue);
            self.check_body(ensure, None);
            self.env.in_rescue = rescuing;
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
        self.refuse_index_block(target);
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
                let Some((field, subst)) = self.find_field_here(cid, name) else {
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
                    function: false,
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
                    function: false,
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

    /// A block given in an index assignment's target (`g[0, &f] = v`,
    /// `g[0, &f] += 1`): refused, as Ruby does (it was dropped).
    fn refuse_index_block(&mut self, target: &LValue) {
        if let LValue::Index { args, .. } = target {
            if let Some(a) = args.iter().find(|a| matches!(a, Arg::BlockPass(_))) {
                self.error(
                    "a block cannot be given in an index assignment (`[]=` takes none here): call a method of another name with it",
                    a.span(),
                );
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
        self.refuse_index_block(target);
        // `o&.w += 1` on an `o` that may be nil: nil then.
        let mut safe_nil = false;
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
                    if let Some((f, _)) = self.find_field_here(cid, name) {
                        if !f.mutable && (!self.env.in_initialize || self.in_late_closure()) {
                            self.error(format!("field `@{name}` is immutable"), expr.span);
                        }
                    }
                }
                t
            }
            LValue::Attr {
                recv,
                name,
                safe_nav,
            } => {
                let rt = self.check_expr(recv, None);
                // `o&.w += 1`: read and written on `o` not nil (the reader's
                // receiver, already typed so).
                // (`self&.w`: `self` itself, never nil, whose private
                // reader it may call.)
                let rt = self.resolve(&rt);
                let nil = self.world.builtin.nil;
                if *safe_nav && !rt.is_nothing() {
                    safe_nil = rt
                        .members()
                        .iter()
                        .any(|m| matches!(m, Type::Class(c, _) if *c == nil));
                    if !safe_nil {
                        self.warning("`&.` on a receiver that is never nil", expr.span);
                    }
                    // Always nil: nothing is read or written.
                    if rt.without_nil(nil).is_nothing() {
                        self.check_expr(value, None);
                        return self.world.nil();
                    }
                }
                let on = if *safe_nav && !rt.is_nothing() && !matches!(recv.kind, ExprKind::SelfRef)
                {
                    Some(Expr {
                        id: OP_VALUE_ID,
                        span: recv.span,
                        kind: ExprKind::Nil,
                    })
                    .map(|e| (e, rt.without_nil(nil)))
                } else {
                    None
                };
                let getter = Call {
                    recv: Some(match &on {
                        Some((e, _)) => e.clone(),
                        None => recv.clone(),
                    }),
                    name: name.clone(),
                    args: vec![],
                    block: None,
                    safe_nav: false,
                    function: false,
                    has_parens: false,
                    type_args: vec![],
                };
                let saved_values = on
                    .as_ref()
                    .map(|(_, t)| std::mem::replace(&mut self.op_values, vec![t.clone()]));
                let saved = self.take_union_record(expr.id);
                let t = self.check_op_reader(expr, &getter);
                self.restore_union_record(expr.id, saved);
                if let Some(v) = saved_values {
                    self.op_values = v;
                }
                t
            }
            LValue::Index { recv, args } => {
                let getter = Call {
                    recv: Some(recv.clone()),
                    name: "[]".to_string(),
                    args: args.clone(),
                    block: None,
                    safe_nav: false,
                    function: false,
                    has_parens: true,
                    type_args: vec![],
                };
                let saved = self.take_union_record(expr.id);
                let t = self.check_op_reader(expr, &getter);
                self.restore_union_record(expr.id, saved);
                t
            }
            LValue::Const(name) => {
                self.error(format!("cannot reassign constant `{name}`"), expr.span);
                return Type::Nothing;
            }
        };
        let current = self.resolve(&current);
        // (A block checked more than once: what any check saw.)
        let seen = match self.out.op_targets.get(&expr.id).cloned() {
            Some(old) if old != current => self.join(&old, &current),
            _ => current.clone(),
        };
        self.out.op_targets.insert(expr.id, seen);
        // The built-in `||=`/`&&=` in a block checked once per type, where
        // another check may take a type's own operator: noted, as `a || b`
        // is (`note_logical`).
        if let OpAssign::OrOr | OpAssign::AndAnd = op {
            let name = op.as_str().trim_end_matches('=');
            if !self.env.blocks.is_empty() && !self.has_logical_method(&current, name) {
                self.note_logical(expr, name, &current, None);
            }
        }
        let result = match op {
            OpAssign::OrOr | OpAssign::AndAnd
                if self.has_logical_method(&current, op.as_str().trim_end_matches('=')) =>
            {
                // `x ||= v` is `x = x.||() { v }`: stored whatever it gives.
                let name = op.as_str().trim_end_matches('=');
                self.check_op_logical(expr, name, &current, value)
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
                    if let Some((f, subst)) = self.find_field_here(cid, name) {
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
                        // Narrowed to what it now holds, as by `@x = v`
                        // (`@x &&= nil` leaves no `Int`).
                        if !f.mutable {
                            let narrowed = self.resolve(&result);
                            self.env.ivar_narrow.insert(name.clone(), narrowed);
                        }
                    }
                }
            }
            LValue::Attr {
                recv,
                name,
                safe_nav,
            } => {
                // Check that the setter accepts the result type.
                let rt = self.resolve(&self.out.node_types[&recv.id]);
                let rt = if *safe_nav {
                    rt.without_nil(self.world.builtin.nil)
                } else {
                    rt
                };
                let setter = format!("{name}=");
                self.check_op_writer(expr, recv, &rt, &setter, &[], &result);
            }
            LValue::Index { recv, args } => {
                let rt = self.resolve(&self.out.node_types[&recv.id]);
                if self.world.lookup_methods(&rt, "[]=").is_empty() && !matches!(rt, Type::Union(_))
                {
                    let hint = self.immutable_hint(&rt, "[]=", Some(recv));
                    self.error(
                        format!("undefined method `[]=` for {}{hint}", self.name(&rt)),
                        expr.span,
                    );
                } else {
                    self.check_op_writer(expr, recv, &rt, "[]=", args, &result);
                }
            }
            LValue::Const(_) => {}
        }
        if safe_nil {
            let nil = self.world.nil();
            return self.join(&result, &nil);
        }
        result
    }

    /// Check a compound assignment's writer as the call it is
    /// (`w=(value)`, `[]=(args..., value)`, the value already typed), on
    /// `rt`: overloads, defaults, rest parameters and type parameters as
    /// for `o.w = v`, and on a union each member's own, chosen by the
    /// receiver's class (`union_calls`). The node's `calls` entry is the
    /// writer.
    #[allow(clippy::too_many_arguments)]
    fn check_op_writer(
        &mut self,
        expr: &Expr,
        recv: &Expr,
        rt: &Type,
        setter: &str,
        args: &[Arg],
        value: &Type,
    ) {
        // The index arguments as the reader's check typed them (evaluated
        // once, before the value), then the value.
        let mut types: Vec<Type> = Vec::new();
        let mut typed = |e: &Expr, t: Type| {
            types.push(t);
            Expr {
                id: OP_VALUE_ID - (types.len() as u32 - 1),
                span: e.span,
                kind: ExprKind::Nil,
            }
        };
        let ty = |e: &Expr| {
            self.out
                .node_types
                .get(&e.id)
                .map(|t| self.infer.resolve(t))
                .unwrap_or(Type::Nothing)
        };
        let mut all: Vec<Arg> = Vec::new();
        for a in args {
            all.push(match a {
                Arg::Positional(e) => Arg::Positional(typed(e, ty(e))),
                Arg::Splat(e) => Arg::Splat(typed(e, ty(e))),
                Arg::DoubleSplat(e) => Arg::DoubleSplat(typed(e, ty(e))),
                Arg::Keyword {
                    name,
                    value: e,
                    span,
                } => Arg::Keyword {
                    name: name.clone(),
                    value: typed(e, ty(e)),
                    span: *span,
                },
                other => other.clone(),
            });
        }
        all.push(Arg::Positional(typed(expr, value.clone())));
        let call = Call {
            recv: Some(recv.clone()),
            name: setter.to_string(),
            args: all,
            block: None,
            safe_nav: false,
            function: false,
            has_parens: true,
            type_args: vec![],
        };
        let saved = std::mem::replace(&mut self.op_values, types);
        self.out.calls.remove(&expr.id);
        // (`self.w += 1` may call a private writer, as `self.w = v`.)
        let implicit_self = matches!(recv.kind, ExprKind::SelfRef);
        self.check_call_on(expr, &call, rt, implicit_self, None);
        self.op_values = saved;
        // In a block checked once per type, as a call's (`check_call`).
        if !self.env.blocks.is_empty() && self.union_testable(rt) {
            if let (Some(CallTarget::Method { method }), false) = (
                self.out.calls.get(&expr.id),
                self.out.dynamic_calls.contains(&expr.id),
            ) {
                let m = *method;
                self.note_union_table(expr.id, vec![(rt.clone(), m)], expr.span);
            }
        }
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
        // The overload `x op v` would call (#586): among those whose one
        // parameter takes the right-hand side, the one `pick_overload`
        // chooses (the most specific, then the override rule), tried
        // first below; equally fitting ones are ambiguous, as for a call.
        let mut fits: Vec<(usize, MethodId, bool)> = Vec::new();
        for (index, (mid, subst)) in cands.iter().enumerate() {
            let m = self.world.method(*mid);
            let positional: Vec<&ParamInfo> = m
                .params
                .iter()
                .filter(|p| p.kind == ParamKind::Positional)
                .collect();
            if positional.len() != 1 || m.block.is_some() {
                continue;
            }
            let mut subst = subst.clone();
            subst.insert(SELF_PARAM, lhs.clone());
            let pt = positional[0].ty.subst(&subst);
            let saved = self.infer.save();
            if self.coerce(rhs, &pt) {
                fits.push((index, *mid, false));
            }
            self.infer.restore(saved);
        }
        let mut cands = cands;
        // (Chosen as a call chooses: then not to be chosen again by name.)
        let mut chosen: Option<MethodId> = None;
        if fits.len() > 1 {
            let ext_src = self.extension_sources(&lhs);
            let (winner, rivals) = self.pick_overload(&fits, &cands, None, &ext_src);
            if rivals.is_empty() {
                chosen = Some(winner);
            }
            if !rivals.is_empty() {
                // (Two active extensions' modules: the call's message,
                // #577; others that fit equally: ambiguous as a call.)
                let tied: Vec<(MethodId, HashMap<TypeParamId, Type>)> =
                    fits.iter().map(|(ix, _, _)| cands[*ix].clone()).collect();
                if let Err((a, b, ea, eb)) = self.by_name_choice(&lhs, winner, &tied) {
                    self.extension_ambiguity(name, a, b, ea, eb, expr.span);
                    return Type::Nothing;
                }
                let names: Vec<String> = std::iter::once(winner)
                    .chain(rivals)
                    .map(|k| self.signature(&self.world.method(k).clone()))
                    .collect();
                self.error(
                    format!(
                        "the call of `{name}` in `{name}=` is ambiguous: these overloads fit it equally (pass a right-hand side of the type of one):\n    {}",
                        names.join("\n    ")
                    ),
                    expr.span,
                );
                return Type::Nothing;
            }
            if let Some(at) = cands.iter().position(|(k, _)| *k == winner) {
                let w = cands.remove(at);
                cands.insert(0, w);
            }
        }
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
                // (Two active extensions' modules both giving one whose
                // parameter takes the right-hand side, #577.)
                let rhs_now = self.infer.resolve(rhs);
                let all: Vec<_> = self
                    .world
                    .lookup_methods(&lhs, name)
                    .into_iter()
                    .filter(|(k, _)| chosen.is_none_or(|c| c == *k))
                    .filter(|(k, ks)| {
                        let km = self.world.method(*k);
                        let ps: Vec<&ParamInfo> = km
                            .params
                            .iter()
                            .filter(|p| p.kind == ParamKind::Positional)
                            .collect();
                        let mut ks = ks.clone();
                        ks.insert(SELF_PARAM, lhs.clone());
                        ps.len() == 1
                            && km.block.is_none()
                            && self.world.is_subtype(&rhs_now, &ps[0].ty.subst(&ks))
                    })
                    .collect();
                let (mid, mut subst) = match self.by_name_choice(&lhs, mid, &all) {
                    Ok(k) if k == mid => (mid, subst),
                    Ok(k) => all
                        .iter()
                        .find(|(x, _)| *x == k)
                        .cloned()
                        .unwrap_or((mid, subst)),
                    Err((a, b, ea, eb)) => {
                        self.extension_ambiguity(name, a, b, ea, eb, expr.span);
                        return Type::Nothing;
                    }
                };
                subst.insert(SELF_PARAM, lhs.clone());
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
                match self.find_field_here(cid, name) {
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
                        if !f.mutable {
                            let narrowed = self.resolve(ty);
                            self.env.ivar_narrow.insert(name.clone(), narrowed);
                        }
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

    /// `Kernel.name(...)`: the built-in `Kernel` function, called as a
    /// function wherever it is written, a file's top-level `def` of the
    /// name notwithstanding (docs/01 §1). `None` for any other call.
    fn check_kernel_call(
        &mut self,
        expr: &Expr,
        call: &Call,
        expected: Option<&Type>,
    ) -> Option<Type> {
        let recv = call.recv.as_ref()?;
        if !matches!(&recv.kind, ExprKind::Const(path) if path.names.last().map(String::as_str) == Some("Kernel"))
        {
            return None;
        }
        let kernel = self.world.builtin.kernel;
        // (No `extension Kernel` declares a module method of a built-in
        // function's name: `Declarer::declare_method` refuses it.)
        let on = Type::class(kernel);
        let cands: Vec<_> = self
            .world
            .lookup_methods(&on, &call.name)
            .into_iter()
            .filter(|(m, _)| {
                let m = self.world.method(*m);
                m.is_native && m.owner == kernel
            })
            .collect();
        // (Another name is a method of the module object, `Kernel.inspect`,
        // found as usual.)
        if cands.is_empty() {
            return None;
        }
        let rt = self.check_expr(recv, None);
        let rt = self.resolve(&rt);
        if !matches!(rt, Type::ClassObject(c, _) if c == kernel) {
            // A constant `Kernel` of another namespace: an ordinary call,
            // whose receiver is checked again (a constant read, recorded
            // the same).
            return None;
        }
        let t = self.resolve_overloads(expr, call, &on, cands, true, expected);
        // In a block checked once per type, the overload may differ
        // (`union_calls`, as for any call).
        if !self.env.blocks.is_empty() && self.union_testable(&rt) {
            if let Some(CallTarget::Method { method }) = self.out.calls.get(&expr.id) {
                let m = *method;
                self.note_union_table(expr.id, vec![(rt, m)], expr.span);
            }
        }
        Some(t)
    }

    /// `::name(...)`: a function, the file's top-level `def`s of the name
    /// first, then the built-in `Kernel` functions, wherever it is written
    /// (docs/01 §1); never a method of `self`, an `Object` method or one an
    /// `extension Kernel` adds.
    fn check_function_call(&mut self, expr: &Expr, call: &Call, expected: Option<&Type>) -> Type {
        let fm = self.file_main(self.env.file);
        let on = Type::class(fm.unwrap_or(self.world.builtin.object));
        // As an implicit call at the file's top level finds them (the
        // `def`s it sees, its cog's, first, hiding a built-in of the same
        // signature, then the built-in's other overloads), but only the
        // functions.
        let cands = self.function_candidates(&call.name);
        if cands.is_empty() {
            self.error(
                format!(
                    "`::{}` calls a built-in function or a top-level `def` of this cog, and there is none named `{}`",
                    call.name, call.name
                ),
                expr.span,
            );
            self.check_args_blindly(call);
            return Type::Nothing;
        }
        self.resolve_overloads(expr, call, &on, cands, true, expected)
    }

    fn check_call(&mut self, expr: &Expr, call: &Call, expected: Option<&Type>) -> Type {
        let t = self.check_call_with_types(expr, call, expected, false);
        // A class method called on an abstract class written as its
        // receiver (`J.run`): refused at the end of the check if the
        // method calls `new` on its receiver (#423), which may be checked
        // after this call.
        if let (Some(r), Some(CallTarget::Method { method })) =
            (&call.recv, self.out.calls.get(&expr.id).cloned())
        {
            let written = match self.out.const_targets.get(&r.id) {
                Some(ConstTarget::Class(c)) => Some(*c),
                Some(ConstTarget::Const(c)) => match self.world.through_alias(Member::Const(*c)) {
                    Member::Class(c) => Some(c),
                    _ => None,
                },
                _ => None,
            };
            if let Some(cid) = written {
                if self.world.class(cid).is_abstract && self.world.method(method).singleton {
                    self.abstract_receivers
                        .push((method, cid, expr.span, self.env.file));
                }
                if let Some(msg) = self.module_call_refusal(cid, method) {
                    self.error(msg, expr.span);
                }
            }
        }
        self.check_hash_include(expr, call);
        // A module or abstract class written as the argument of a
        // `Type[T]` parameter whose `T` is bounded (#509).
        match self.out.calls.get(&expr.id).cloned() {
            Some(CallTarget::Method { method })
            | Some(CallTarget::Constructor {
                init: Some(method), ..
            }) => self.note_abstract_type_args(method, &call.args),
            _ => {}
        }
        t
    }

    /// A Hash's `include?` and `member?` test whether a pair is an element
    /// (`Enumerable`'s meaning, #622): on a receiver statically a
    /// `Hash[K, V]` or `Hash::Builder[K, V]`, an argument whose static type
    /// cannot be a `[K, V]` (`split_by_type` gives nothing of it, as a
    /// run-time type test decides) is refused, pointing at `key?`. It errs
    /// towards accepting: a type not yet inferred, and any type a pair may
    /// be (`Object`, a type parameter, a union with a tuple), pass; a union
    /// or subclass receiver is not looked at.
    fn check_hash_include(&mut self, expr: &Expr, call: &Call) {
        if call.name != "include?" && call.name != "member?" {
            return;
        }
        let (Some(recv), [arg]) = (&call.recv, call.args.as_slice()) else {
            return;
        };
        let value = match arg {
            Arg::Positional(e) => e,
            Arg::Keyword { name, value, .. } if name == "value" => value,
            _ => return,
        };
        if !matches!(
            self.out.calls.get(&expr.id),
            Some(CallTarget::Method { .. })
        ) {
            return;
        }
        let (Some(rt), Some(at)) = (
            self.out.node_types.get(&recv.id).cloned(),
            self.out.node_types.get(&value.id).cloned(),
        ) else {
            return;
        };
        let rt = self.resolve(&rt);
        let at = self.resolve(&at);
        let Type::Class(c, args) = &rt else {
            return;
        };
        if (*c != self.world.builtin.hash && *c != self.world.builtin.hash_builder)
            || args.len() != 2
            || at.has_vars()
            || args.iter().any(|t| t.has_vars())
        {
            return;
        }
        let pair = Type::Tuple(args.clone());
        let (yes, _) = self.split_by_type(&at, &pair);
        if yes.is_nothing() {
            self.error(
                format!(
                    "a Hash's `{}` tests whether a pair is an element; use `key?` for a key",
                    call.name
                ),
                expr.span,
            );
        }
    }

    /// Record, for `check_abstract_type_args`, the arguments of a call of
    /// `method` (a method, a constructor's `initialize`, a `super` target)
    /// written as a module or an abstract class for a `Type[T]` parameter
    /// (`Type[T]?` too), positional or by keyword, whose `T` (the method's
    /// or its class's) has class bounds: one record per bound.
    fn note_abstract_type_args(&mut self, method: MethodId, args: &[Arg]) {
        let m = self.world.method(method).clone();
        let owner_params = self.world.class(m.owner).type_params.clone();
        let mut pairs: Vec<(&ParamInfo, &Expr)> = Vec::new();
        let mut positional = m
            .params
            .iter()
            .filter(|p| !matches!(p.kind, ParamKind::KeywordOnly | ParamKind::Block))
            .peekable();
        for a in args {
            match a {
                Arg::Positional(e) => {
                    // (A `*rest` takes every later positional argument.)
                    let p = match positional.peek() {
                        Some(p) if p.kind == ParamKind::Rest => Some(*p),
                        _ => positional.next(),
                    };
                    if let Some(p) = p {
                        pairs.push((p, e));
                    }
                }
                Arg::Keyword { name, value, .. } => {
                    if let Some(p) = m.params.iter().find(|p| &p.name == name) {
                        pairs.push((p, value));
                    }
                }
                _ => break,
            }
        }
        for (p, e) in pairs {
            // (`Type[T]`, or with `Nil` beside it; a `*rest`'s element.)
            let ty = match (&p.kind, &p.ty) {
                (ParamKind::Rest, Type::Class(a, args))
                    if *a == self.world.builtin.array && args.len() == 1 =>
                {
                    args[0].clone()
                }
                _ => p.ty.clone(),
            };
            let tp = ty.members().into_iter().find_map(|t| match t {
                Type::TypeOf(inner) => match *inner {
                    Type::Param(tp) => Some(tp),
                    _ => None,
                },
                _ => None,
            });
            let Some(tp) = tp else { continue };
            let Some(info) = m
                .type_params
                .iter()
                .chain(&owner_params)
                .find(|i| i.id == tp)
            else {
                continue;
            };
            let written = match self.out.const_targets.get(&e.id) {
                Some(ConstTarget::Class(c)) => Some(*c),
                Some(ConstTarget::Const(c)) => match self.world.through_alias(Member::Const(*c)) {
                    Member::Class(c) => Some(c),
                    _ => None,
                },
                _ => None,
            };
            let Some(cid) = written else { continue };
            let c = self.world.class(cid);
            if c.kind != ClassKind::Module && !c.is_abstract {
                continue;
            }
            // (Its class bounds, and those of a type parameter it is bounded
            // by: `T <: U`, `U <: Named`.)
            let params: Vec<&TypeParamInfo> = m.type_params.iter().chain(&owner_params).collect();
            let mut todo: Vec<&Type> = info.bounds.iter().collect();
            let mut seen: Vec<TypeParamId> = vec![tp];
            while let Some(b) = todo.pop() {
                match b {
                    Type::Class(bound, _) => self.abstract_type_args.push((
                        cid,
                        *bound,
                        info.name.clone(),
                        e.span,
                        self.env.file,
                    )),
                    Type::Param(u) if !seen.contains(u) => {
                        seen.push(*u);
                        if let Some(ui) = params.iter().find(|i| i.id == *u) {
                            todo.extend(ui.bounds.iter());
                        }
                    }
                    _ => {}
                }
            }
        }
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
        // An operator method takes no keyword argument (docs/01 §9): its
        // parameters' names are not part of what callers write. (`p[1,
        // k: 2]` calls a procedure, by its receiver's type:
        // `check_call_on`.)
        if quarz_syntax::positional_only_name(&call.name)
            && !(call.name == "[]" && call.recv.is_some())
        {
            if let Some(Arg::Keyword { value, .. }) =
                call.args.iter().find(|a| matches!(a, Arg::Keyword { .. }))
            {
                self.error(
                    format!(
                        "`{}` takes no keyword arguments: an operator's are positional",
                        call.name
                    ),
                    value.span,
                );
            }
        }
        // `Self.new(...)` in an instance method (docs/01 §9).
        if call.name == "new"
            && call.recv.as_ref().is_some_and(|r| {
                matches!(&r.kind, ExprKind::Const(p) if !p.absolute && !p.cog && p.names == ["Self"])
            })
        {
            return self.check_self_new(expr, call, expected);
        }
        // Special forms.
        if call.recv.is_none() && call.name == "raise" {
            return self.check_raise(expr, call);
        }
        if call.function {
            return self.check_function_call(expr, call, expected);
        }
        if let Some(t) = self.check_kernel_call(expr, call, expected) {
            return t;
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

        // (Called by name after an earlier check of the call, on a union
        // whose members found different methods: this check's method is
        // still one the table must choose for its type.)
        let dynamic_before = self.out.dynamic_calls.contains(&expr.id);
        // (What earlier checks of an `!=` recorded on its node, which a
        // check of it as `!(a == b)` starts from.)
        let ne_before = (call.name == "!=").then(|| {
            (
                self.out.union_calls.get(&expr.id).cloned(),
                self.out.union_conflicts.contains(&expr.id),
                self.out.dynamic_calls.contains(&expr.id),
            )
        });
        // (Earlier checks took it as `!(a == b)`: their records are the
        // `==`'s, which this check's `!=` must not be merged into; they
        // are restored for its own check as `==`.)
        if ne_before.is_some() && self.out.ne_negated.get(&expr.id) == Some(&true) {
            self.restore_union_record(expr.id, (None, false));
            self.out.dynamic_calls.remove(&expr.id);
        }
        let result = self.check_call_on(expr, call, &recv_ty, implicit_self, expected);
        // `type` in a class's `static def`: the class it runs on, as a
        // class value whose instances are `Self` (docs/14 §4), so that a
        // block given to `def_method` that captures it builds the class
        // generated into (`cls.rebuild(...)` giving `Self`).
        let result = match self.out.calls.get(&expr.id) {
            // (On the `static def`'s own `self` only: another class's
            // `Meta::ClassDef` is that class, not `Self`.)
            Some(CallTarget::Method { method })
                if call.name == "type"
                    && self.world.method(*method).owner == self.world.builtin.meta_classdef
                    && self.static_class_self()
                    && call
                        .recv
                        .as_ref()
                        .is_none_or(|r| matches!(r.kind, ExprKind::SelfRef)) =>
            {
                Type::TypeOf(Box::new(Type::Param(SELF_PARAM)))
            }
            _ => result,
        };
        let result = match (
            call.name.as_str(),
            call.args.as_slice(),
            &call.recv,
            ne_before,
        ) {
            ("!=", [Arg::Positional(arg)], Some(_), Some(before)) if call.block.is_none() => {
                self.ne_by_extension_eq(expr, &recv_ty, arg, result, before)
            }
            _ => result,
        };
        // In a block, checked again for each type of what it is given: a
        // call may resolve differently each time (`union_calls`).
        let rt = self.resolve(&recv_ty);
        if !self.env.blocks.is_empty() && self.union_testable(&rt) {
            let dynamic = self.out.dynamic_calls.contains(&expr.id) && !dynamic_before;
            if let (Some(CallTarget::Method { method }), false) =
                (self.out.calls.get(&expr.id), dynamic)
            {
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

    /// `a != b` where, for a type of `a`, `a == b` takes an extension's
    /// `==` and `a != b` no extension's `!=` (docs/01 §3): the call is
    /// `!(a == b)` (`Output::ne_negated`), checked as that `==` (on a
    /// union, per member: the others' `Object#!=` is `!(a == b)` too) and
    /// refused where the result is not a `Bool`, or where a member's own
    /// `!=` would be bypassed.
    fn ne_by_extension_eq(
        &mut self,
        expr: &Expr,
        recv_ty: &Type,
        arg: &Expr,
        result: Type,
        records: (Option<Vec<(Type, MethodId)>>, bool, bool),
    ) -> Type {
        // (Only where an extension in scope defines an `==` of its own.)
        let any = self.world.active_extension_ids().iter().any(|e| {
            self.world.extensions[*e as usize]
                .methods
                .get("==")
                .is_some_and(|ms| ms.iter().any(|m| !self.world.method(*m).is_native))
        });
        if !any && !self.out.ne_negated.contains_key(&expr.id) {
            return result;
        }
        let Some(at) = self.out.node_types.get(&arg.id).cloned() else {
            return result;
        };
        let at = self.resolve(&at);
        let recv_ty = self.resolve(recv_ty);
        let members = recv_ty.members();
        let mut negate = false;
        let mut own_ne = None;
        for m in &members {
            let eq = self.probe_method(m, "==", &at);
            let ne = self.probe_method(m, "!=", &at);
            let ext =
                |k: Option<MethodId>, w: &World| k.is_some_and(|k| w.method(k).extension.is_some());
            if ext(eq, &self.world) && !ext(ne, &self.world) {
                negate = true;
            }
            // A class's own `!=` (not `Object#!=`, which is `!(a == b)`).
            if let Some(k) = ne {
                let ki = self.world.method(k);
                if ki.extension.is_none() && !ki.is_native {
                    own_ne = Some(m.clone());
                }
            }
        }
        let before = self.out.ne_negated.get(&expr.id).copied();
        if before.is_some_and(|b| b != negate) {
            self.error(
                "cannot tell at run time whether `!=` is an extension's `!(a == b)` or the class's own (give the value one type first)",
                expr.span,
            );
        }
        self.table_journal
            .push(TableUndo::NeNegated(expr.id, before));
        self.out.ne_negated.insert(expr.id, negate);
        if !negate {
            return result;
        }
        if let (Some(m), true) = (own_ne, members.len() > 1) {
            self.error(
                format!(
                    "`!=` on {} is `!(a == b)` for a type whose `==` is an extension's, but {} has a `!=` of its own: define `!=` in the extension",
                    self.name(&recv_ty),
                    self.name(&m)
                ),
                expr.span,
            );
            return result;
        }
        // Checked again as `a == b`, the operands as typed.
        let call = Call {
            recv: Some(Expr {
                id: OP_VALUE_ID,
                span: expr.span,
                kind: ExprKind::Nil,
            }),
            name: "==".to_string(),
            args: vec![Arg::Positional(Expr {
                id: OP_VALUE_ID - 1,
                span: arg.span,
                kind: ExprKind::Nil,
            })],
            block: None,
            safe_nav: false,
            function: false,
            has_parens: true,
            type_args: vec![],
        };
        let saved = std::mem::replace(&mut self.op_values, vec![recv_ty.clone(), at]);
        // (The node's records as earlier checks left them: this check's
        // `!=` is replaced, theirs kept, as a block checked once per type
        // needs.)
        let (table, conflict, dynamic) = records;
        self.restore_union_record(expr.id, (table, conflict));
        if dynamic {
            self.out.dynamic_calls.insert(expr.id);
        } else {
            self.out.dynamic_calls.remove(&expr.id);
        }
        self.out.calls.remove(&expr.id);
        let eq_ty = self.check_call_on(expr, &call, &recv_ty, false, None);
        self.op_values = saved;
        // (Never called by name: that would be `!=`, then negated.)
        debug_assert!(
            !self.out.dynamic_calls.contains(&expr.id)
                || self.out.union_calls.contains_key(&expr.id)
        );
        let eq_ty = self.resolve(&eq_ty);
        let bool_ = self.world.bool_();
        if !self.world.is_subtype(&eq_ty, &bool_) {
            self.error(
                format!(
                    "`!=` on {} is `!(a == b)`, but the extension's `==` returns {}: define `!=` in the extension",
                    self.name(&recv_ty),
                    self.name(&eq_ty)
                ),
                expr.span,
            );
            return result;
        }
        bool_
    }

    /// The method `recv.name(arg)` resolves to on a value of type `recv`
    /// with an argument of type `arg`, as the call would choose it,
    /// leaving no trace of the trial.
    fn probe_method(&mut self, recv: &Type, name: &str, arg: &Type) -> Option<MethodId> {
        let id = PROBE_ID;
        let call = Call {
            recv: Some(Expr {
                id: OP_VALUE_ID,
                span: Span::new(0, 0),
                kind: ExprKind::Nil,
            }),
            name: name.to_string(),
            args: vec![Arg::Positional(Expr {
                id: OP_VALUE_ID - 1,
                span: Span::new(0, 0),
                kind: ExprKind::Nil,
            })],
            block: None,
            safe_nav: false,
            function: false,
            has_parens: true,
            type_args: vec![],
        };
        let probe = Expr {
            id,
            span: Span::new(0, 0),
            kind: ExprKind::Nil,
        };
        let saved = std::mem::replace(&mut self.op_values, vec![recv.clone(), arg.clone()]);
        let mark = self.table_mark();
        let ndiag = self.diagnostics.len();
        let infer = self.infer.save();
        let touched = self.touched.len();
        self.check_call_on(&probe, &call, recv, false, None);
        let found = match self.out.calls.remove(&id) {
            Some(CallTarget::Method { method }) => Some(method),
            _ => None,
        };
        self.discard_tables(mark);
        self.truncate_diagnostics(ndiag);
        self.infer.restore(infer);
        self.touched.truncate(touched);
        self.op_values = saved;
        self.out.union_calls.remove(&id);
        self.out.union_conflicts.remove(&id);
        self.out.dynamic_calls.remove(&id);
        self.out.node_types.remove(&id);
        self.out.type_args.remove(&id);
        self.out.call_type_args.remove(&id);
        found
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
        let resolved: Vec<MethodId> = resolved.iter().flatten().copied().collect();
        // An extension's method overrides nothing by dispatch: a call of
        // the ancestor's would not run it.
        if resolved
            .iter()
            .any(|&r| self.world.method(r).extension.is_some())
        {
            return None;
        }
        // Each resolved method with those it overrides, as the runtime
        // dispatches (the override table, `World::overrides`).
        let overridden: Vec<Vec<MethodId>> = resolved
            .iter()
            .map(|&r| {
                let mut set = vec![r];
                set.extend(self.world.overrides(r));
                set
            })
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
        // The most derived ancestor's method of the name, among its
        // overloads the one every member's method is or overrides (the
        // one the call resolved against for each): a call of it
        // dispatches to each member's own.
        for anc in &chains[0] {
            if !chains.iter().all(|c| c.contains(anc)) {
                continue;
            }
            if let Some(ms) = self.world.class(*anc).methods.get(name) {
                if let Some(m) = ms
                    .iter()
                    .copied()
                    .find(|m| overridden.iter().all(|set| set.contains(m)))
                {
                    return Some(m);
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
        // (`Object#instance_exec`, the native: a method of the name a
        // class declares is called as any.)
        if name == "instance_exec"
            && call.args.iter().any(|a| matches!(a, Arg::Keyword { .. }))
            && {
                let found = self.world.lookup_methods(recv_ty, name);
                !found.is_empty()
                    && found.iter().all(|(m, _)| {
                        let m = self.world.method(*m);
                        m.is_native && m.owner == self.world.builtin.object
                    })
            }
        {
            return self.check_instance_exec_kw(expr, call, recv_ty, expected);
        }
        if name == "[]" && !matches!(self.resolve(recv_ty), Type::Proc(..) | Type::Union(_)) {
            if let Some(Arg::Keyword { value, .. }) =
                call.args.iter().find(|a| matches!(a, Arg::Keyword { .. }))
            {
                self.error(
                    "`[]` takes no keyword arguments: an operator's are positional",
                    value.span,
                );
            }
        }
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
                // (A block's: which `self` each implicit call in it goes
                // to, per member, `self_uses`.)
                let with_block = call.block.is_some();
                self.union_block_calls += with_block as usize;
                // (The block's frame, once entered.)
                let block_frame = self.env.frames.len();
                let mut uses = Vec::new();
                // (An implicit call on a `self` that is a union, in a block
                // whose receiver type is one, `T.()` with `T = P | Q`:
                // whether each member's check fell through to an
                // enclosing `self`, and to which slot, #335.)
                // (Not when the union is an enclosing `self` the call fell
                // through to, already bound to its slot, #429.)
                let on_union_self = call.recv.is_none() && self.in_outer_self != Some(expr.id);
                let mut falls = Vec::new();
                for m in &members {
                    if let (Some(k), Some(saved)) = (&bang, &bang_saved) {
                        self.narrow_subject(k, saved.clone());
                    }
                    let start = self.self_uses.len();
                    if on_union_self {
                        self.out.outer_self_calls.remove(&expr.id);
                        self.out.outer_self_depths.remove(&expr.id);
                    }
                    let t = self.check_call_on(expr, call, m, implicit_self, expected);
                    if on_union_self {
                        falls.push(self.fell_through(expr));
                    }
                    uses.push((start, self.self_uses.len()));
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
                    uses.clear();
                    falls.clear();
                    for m in &members {
                        if let (Some(k), Some(saved)) = (&bang, &bang_saved) {
                            self.narrow_subject(k, saved.clone());
                        }
                        let start = self.self_uses.len();
                        if on_union_self {
                            self.out.outer_self_calls.remove(&expr.id);
                            self.out.outer_self_depths.remove(&expr.id);
                        }
                        let t = self.check_call_on(expr, call, m, implicit_self, expected);
                        if on_union_self {
                            falls.push(self.fell_through(expr));
                        }
                        uses.push((start, self.self_uses.len()));
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
                // The compiled call reads one `self` for every member: the
                // members must all fall through to the same one, or none.
                if let Some(k) = falls.iter().position(|f| *f != falls[0]) {
                    let what = |f: &Option<VarRef>, m: &Type| match f {
                        Some(_) => format!(
                            "falls through to the enclosing `self` for {}",
                            self.world.type_name(m)
                        ),
                        None => format!("is the receiver's own for {}", self.world.type_name(m)),
                    };
                    let (a, b) = (what(&falls[0], &members[0]), what(&falls[k], &members[k]));
                    self.error(
                        format!(
                            "`{name}` {a} and {b}: a block whose receiver is a union must resolve its calls the same way for every member; write the receiver (`self.{name}`, or the enclosing one), or narrow the receiver with `case`",
                            name = call.name
                        ),
                        expr.span,
                    );
                }
                if with_block {
                    self.union_block_calls -= 1;
                    self.check_classdef_block(&members, recv_ty, &uses);
                    self.compare_self_uses(call, &members, &uses, block_frame);
                    if self.union_block_calls == 0 {
                        self.self_uses.clear();
                    }
                }
                if let Some(k) = &bang {
                    if self.out.bang_assign.contains(&expr.id) {
                        let t = self.resolve(&result);
                        self.set_narrowed(k, Some(t));
                    }
                }
                // A `Meta::ClassDef[T]` member and a class object that can
                // hold the same class value: no run-time test tells which
                // one the value stands for, so a call they answer with
                // different methods is refused (#491).
                if let Some((a, b)) = self.classdef_ambiguity(&members, &targets) {
                    let msg =
                        self.classdef_ambiguity_msg(name, name, recv_ty, &members[a], &members[b]);
                    self.error(msg, expr.span);
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
            Type::Proc(None, params, ret, _, kws) if name == "call" || name == "[]" => {
                let (params, kws) = (params.clone(), kws.clone());
                let ret = self.world.unvoid(ret);
                self.check_proc_args(&call.args, &params, &kws, expr.span, false);
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
                // In a class method, `new` builds the receiver's class, which
                // may be a concrete subclass of an abstract one (#423), or,
                // in a module's, a class that includes it (#494).
                let kind = self.world.class(cid).kind;
                let builds = kind == ClassKind::Class || kind == ClassKind::Module;
                let in_class_method = implicit_self
                    && self.own_self()
                    && builds
                    && self
                        .env
                        .method
                        .is_some_and(|m| self.world.method(m).singleton);
                if in_class_method {
                    self.constructing_self = true;
                }
                let t = self.check_constructor(expr, call, cid, &args, expected);
                // `def self.build = new`: the instance is of the class the
                // method is called on (a subclass, perhaps).
                if implicit_self && builds {
                    if let (Some(m), Some(CallTarget::Constructor { init, .. })) =
                        (self.env.method, self.out.calls.get(&expr.id).cloned())
                    {
                        if self.world.method(m).singleton {
                            self.out.self_new.insert(expr.id);
                            // (In a block lifted to a generated class
                            // method, the method the subclasses inherit is
                            // that one, not the `static def`: recorded when
                            // it is generated, `StaticHost::generated_new`.)
                            if self.env.lifted_frame.is_none() {
                                self.self_news
                                    .push((cid, init, m, expr.span, self.env.file));
                            }
                            // In a class method with `Self` in its
                            // signature, the instance is a `Self`; in a
                            // module's, always (no value is a module's).
                            if (self.env.self_opaque || kind == ClassKind::Module)
                                && self.own_self()
                            {
                                return Type::Param(SELF_PARAM);
                            }
                        }
                    }
                }
                t
            }
            _ => {
                let mut cands = self.world.lookup_methods(recv_ty, name);
                // `Foo.bar(args)`: a public function of the cog whose root
                // module `Foo` is (docs/10 §6), called as a function.
                // (Written so: a constant path or `cog`, not a value of the
                // module's type, which the call would not evaluate.)
                let by_name = !call.safe_nav
                    && call
                        .recv
                        .as_ref()
                        .is_some_and(|r| matches!(r.kind, ExprKind::Const(_)));
                if let Type::ClassObject(root, _) = recv_ty {
                    if by_name && self.world.class(*root).cog.is_some() {
                        let (public, private) = self.cog_functions(*root, name);
                        if !public.is_empty() {
                            cands = public
                                .into_iter()
                                .map(|m| (m, HashMap::default()))
                                .collect();
                        } else if cands.is_empty() {
                            let module = self.world.class(*root).name.clone();
                            let msg = if private {
                                format!("`{name}` is private to cog `{module}`; declare it `public def {name}`")
                            } else {
                                let names = self.cog_public_names(*root);
                                let listed = if names.is_empty() {
                                    "it has none".to_string()
                                } else {
                                    format!("its public functions: {}", names.join(", "))
                                };
                                format!("no function `{name}` in cog `{module}` ({listed})")
                            };
                            self.error(msg, expr.span);
                            self.check_args_blindly(call);
                            return Type::Nothing;
                        }
                    }
                }
                // An implicit call finds a method of `self` first (its
                // own, inherited or from a module); `Kernel`'s built-in
                // functions are not methods of it, and come after the
                // cog's top-level `def`s (docs/01 §1).
                let no_method = cands.is_empty();
                // (Not for the call being re-checked on an enclosing `self`
                // itself; its arguments and block fall through as any,
                // #336.)
                if call.recv.is_none() && implicit_self && self.outer_recheck != Some(expr.id) {
                    let falls = no_method
                        && !self.env.receivers.is_empty()
                        && self.in_outer_self != Some(expr.id);
                    let fell = match falls {
                        true => self.outer_self_for(name),
                        false => None,
                    };
                    let fallen = fell.is_some();
                    // The frame whose `self` is read: the hidden slot's, or
                    // the one whose receiver block gave the current `self`.
                    let (frame, self_ty) = match fell {
                        Some((outer, k)) => (self.env.receivers[k].outer_frame, outer),
                        None => {
                            let own = self.env.receivers.last().map_or(0, |r| r.outer_frame + 1);
                            (own, recv_ty.clone())
                        }
                    };
                    self.note_self_use(expr.id, expr.span, name, frame, self_ty, fallen);
                }
                if call.recv.is_none()
                    && implicit_self
                    && !self.env.receivers.is_empty()
                    && self.in_outer_self != Some(expr.id)
                {
                    // Inside a block with a receiver: the enclosing selves,
                    // innermost first, answer what the receiver does not.
                    match self.outer_self_for(name) {
                        Some((outer, k)) if no_method => {
                            self.bind_outer_self(expr, k);
                            let outer_saved = self.in_outer_self.replace(expr.id);
                            let recheck = self.outer_recheck.replace(expr.id);
                            let t = self.check_call_on(expr, call, &outer, true, expected);
                            self.outer_recheck = recheck;
                            self.in_outer_self = outer_saved;
                            return t;
                        }
                        // Nested blocks on the same class shadow each
                        // other on purpose; a different class is worth a word,
                        // where its method is another declaration than the
                        // receiver's (not one both inherit: `to_s`, `hash`).
                        // (A union `self`: any member's own method.)
                        Some((outer, _))
                            if outer != *recv_ty
                                && match &outer {
                                    Type::Union(ms) => ms.clone(),
                                    t => vec![t.clone()],
                                }
                                .iter()
                                .any(|o| {
                                    !self
                                        .world
                                        .lookup_methods(o, name)
                                        .iter()
                                        .all(|(m, _)| cands.iter().any(|(c, _)| c == m))
                                }) =>
                        {
                            self.warning(
                            format!(
                                "`{name}` is a method of both the block's receiver {} and the enclosing {}; the receiver's is called",
                                self.name(recv_ty),
                                self.name(&outer)
                            ),
                            expr.span,
                        )
                        }
                        _ => {}
                    }
                }
                // In a module's macro, `self` is the class that includes
                // the module (docs/14 §2), whose class object has the
                // module's class methods: an implicit call finds them.
                if cands.is_empty() && call.recv.is_none() && implicit_self {
                    if let Some(own) = self.module_static_self(&self.env.self_type.clone()) {
                        cands = self.world.lookup_methods(&own, name);
                    }
                }
                // A function has no `self`: an implicit call in it finds
                // functions only (docs/01 §2).
                let self_methods = if call.recv.is_none()
                    && implicit_self
                    && self.in_outer_self != Some(expr.id)
                    && self.function_self()
                {
                    std::mem::take(&mut cands)
                } else {
                    Vec::new()
                };
                // Top-level functions of the cog, then `Kernel`'s built-in
                // functions, after the methods of `self` (docs/01 §1): one
                // set of overloads, the first of each signature kept.
                if call.recv.is_none() {
                    let found = self.function_candidates(name);
                    if !found.is_empty() {
                        for f in found {
                            let fm = self.world.method(f.0);
                            if !cands.iter().any(|(id, _)| {
                                *id == f.0 || self.world.same_signature(self.world.method(*id), fm)
                            }) {
                                cands.push(f);
                            }
                        }
                    }
                }
                if cands.is_empty() && !implicit_self {
                    if let Some(t) = self.check_bang_assign(expr, call, recv_ty, expected) {
                        return t;
                    }
                }
                // (An `Object` method the call would have meant, which the
                // functions of the name do not take: `inspect` beside a
                // `def inspect(x: Int)`; `respond_to?(:x)`, which `self`
                // answers only written.)
                let meant_method = !self_methods.is_empty()
                    && (cands.is_empty()
                        || self_methods.iter().any(|(m, _)| self.shape_fits(*m, call)))
                    || self.function_self()
                        && call.recv.is_none()
                        && self_methods.is_empty()
                        && self.in_outer_self != Some(expr.id)
                        && (name == "respond_to?"
                            || !self
                                .world
                                .lookup_methods(&self.world.object(), name)
                                .is_empty());
                if meant_method && !cands.iter().any(|(m, _)| self.shape_fits(*m, call)) {
                    let args = if call.args.is_empty() { "" } else { "(...)" };
                    let others = if cands.is_empty() {
                        String::new()
                    } else {
                        let sigs: Vec<String> = cands
                            .iter()
                            .map(|(m, _)| self.signature(self.world.method(*m)))
                            .collect();
                        format!(
                            "; the functions `{name}` take other arguments: {}",
                            sigs.join(", ")
                        )
                    };
                    self.error(
                        format!("a function has no `self`: `{name}` is a method of an object, not a function; call it on one (`x.{name}{args}`){others}"),
                        expr.span,
                    );
                    self.check_args_blindly(call);
                    return Type::Nothing;
                }
                if cands.is_empty() {
                    let msg = if call.recv.is_none() && call.args.is_empty() && !call.has_parens {
                        format!(
                            "undefined local variable or method `{name}` for {}",
                            self.name(recv_ty)
                        )
                    } else if let Some(it) =
                        self.world.it_hints.get(&(expr.span.start, expr.span.end))
                    {
                        // `it -1` in a block declaring no parameters.
                        format!("undefined method `it` for {}: {it}", self.name(recv_ty))
                    } else {
                        let mut hint = self.immutable_hint(recv_ty, name, call.recv.as_ref());
                        if let Some(plain) = name.strip_suffix('!') {
                            if call.recv.is_some()
                                && !plain.is_empty()
                                && !self.world.lookup_methods(recv_ty, plain).is_empty()
                            {
                                let var = match call.recv.as_ref().map(|r| &r.kind) {
                                    Some(ExprKind::Local(v)) => v.clone(),
                                    Some(ExprKind::IVar(v)) => format!("@{v}"),
                                    _ => "x".to_string(),
                                };
                                let args = if call.args.is_empty() { "" } else { "(...)" };
                                hint = format!(
                                    "; `.{name}` rebinds its receiver only when the receiver's type is immutable: write `{var} = {var}.{plain}{args}`, or define `{name}`"
                                );
                            }
                        }
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

    /// Whether a call of the shape of `call` (its number of positional
    /// arguments, and whether it passes keywords) may go to `m`, its
    /// argument types aside.
    fn shape_fits(&self, m: MethodId, call: &Call) -> bool {
        let m = self.world.method(m);
        let mut positional = 0;
        let mut keywords = false;
        for a in &call.args {
            match a {
                Arg::Positional(_) => positional += 1,
                Arg::Keyword { .. } => keywords = true,
                Arg::BlockPass(_) => {}
                // (A splat's length is not known.)
                _ => return true,
            }
        }
        let mut required = 0;
        let mut max = Some(0);
        let mut named = false;
        for p in &m.params {
            match p.kind {
                ParamKind::Positional => {
                    named = true;
                    if p.default.is_none() {
                        required += 1;
                    }
                    max = max.map(|n| n + 1);
                }
                ParamKind::Rest => max = None,
                ParamKind::KeywordOnly | ParamKind::KeywordRest => named = true,
                ParamKind::Block => {}
            }
        }
        // (Keywords may bind positional parameters by name.)
        (!keywords || named)
            && (keywords || positional >= required)
            && max.is_none_or(|n| positional <= n)
    }

    /// The top-level `def`s named `name` of the library cog whose root
    /// module is `root`: its public ones, and whether it has others
    /// (docs/10 §6).
    fn cog_functions(&self, root: ClassId, name: &str) -> (Vec<MethodId>, bool) {
        let Some(cog) = self.world.cogs.iter().position(|c| c.root == Some(root)) else {
            return (Vec::new(), false);
        };
        let mut files: Vec<u32> = self
            .world
            .file_groups
            .iter()
            .filter(|(_, g)| matches!(g, UnitGroup::Cog(c) if *c as usize == cog))
            .map(|(f, _)| *f)
            .collect();
        files.sort();
        let (mut public, mut private) = (Vec::new(), false);
        for f in files {
            let Some(main) = self.file_main(f) else {
                continue;
            };
            for id in self
                .world
                .class(main)
                .methods
                .get(name)
                .into_iter()
                .flatten()
            {
                if self.world.method(*id).visibility == Visibility::Public {
                    public.push(*id);
                } else {
                    private = true;
                }
            }
        }
        (public, private)
    }

    /// The names of the public top-level `def`s of the library cog whose
    /// root module is `root`, sorted.
    fn cog_public_names(&self, root: ClassId) -> Vec<String> {
        let Some(cog) = self.world.cogs.iter().position(|c| c.root == Some(root)) else {
            return Vec::new();
        };
        let mut names: Vec<String> = self
            .world
            .file_groups
            .iter()
            .filter(|(_, g)| matches!(g, UnitGroup::Cog(c) if *c as usize == cog))
            .filter_map(|(f, _)| self.file_main(*f))
            .flat_map(|main| self.world.class(main).methods.iter())
            .filter(|(_, ids)| {
                ids.iter()
                    .any(|id| self.world.method(*id).visibility == Visibility::Public)
            })
            .map(|(n, _)| n.clone())
            .collect();
        names.sort();
        names.dedup();
        names
    }

    /// The functions of a name the current file sees (docs/01 §1): the
    /// top-level `def`s (its own, then its cog's or those of the files it
    /// requires, `World::function_scopes`), then `Kernel`'s built-ins.
    fn function_candidates(&self, name: &str) -> Vec<(MethodId, HashMap<TypeParamId, Type>)> {
        let file = self.env.file;
        let mut mains: Vec<ClassId> = self.file_main(file).into_iter().collect();
        if let Some(scope) = self.world.function_scopes.get(&file) {
            mains.extend(
                scope
                    .iter()
                    .filter(|f| **f != file)
                    .filter_map(|f| self.file_main(*f)),
            );
        }
        let mut cands: Vec<(MethodId, HashMap<TypeParamId, Type>)> = Vec::new();
        for m in mains {
            if let Some(ids) = self.world.class(m).methods.get(name) {
                cands.extend(ids.iter().map(|id| (*id, HashMap::default())));
            }
        }
        // Then `Kernel`'s built-ins, but those a `def` of their signature
        // hides (in the prelude, which has no `main`, only they).
        let ndefs = cands.len();
        let kernel = self.world.builtin.kernel;
        if let Some(ids) = self.world.class(kernel).methods.get(name) {
            for id in ids {
                let m = self.world.method(*id);
                if m.is_native
                    && !cands[..ndefs]
                        .iter()
                        .any(|(d, _)| self.world.same_signature(self.world.method(*d), m))
                {
                    cands.push((*id, HashMap::default()));
                }
            }
        }
        cands
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
        // Only on immutable receivers; a mutable member without `foo!`
        // reports the undefined method in its own check.
        if !members.iter().all(|m| self.world.bang_immutable(m)) {
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
        // Only on an immutable receiver: on a mutable one, `foo!` would
        // read as a change of the object (docs/01, assignment).
        if self.world.lookup_methods(recv_ty, plain_name).is_empty()
            || !self.world.bang_immutable(recv_ty)
        {
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
                let Some((field, subst)) = self.find_field_here(cid, name) else {
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
            function: false,
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
                self.note_not_builtin(expr.id);
                return None;
            }
            if !without.is_empty() {
                self.note_not_builtin(expr.id);
                let call = Call {
                    recv: Some(operand.clone()),
                    name: "!".to_string(),
                    args: vec![],
                    block: None,
                    safe_nav: false,
                    function: false,
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
                self.implicit_test_check(&targets, "`!` on a union", expr.span);
                self.note_not_dispatch(expr.id, targets);
                return Some(result);
            }
        } else if !has_not(self, &t) {
            self.note_not_builtin(expr.id);
            return None;
        }
        let call = Call {
            recv: Some(operand.clone()),
            name: "!".to_string(),
            args: vec![],
            block: None,
            safe_nav: false,
            function: false,
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
            self.implicit_test_check(&targets, "`!` on a union", expr.span);
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
    /// Mark `!` node `id` as taking the built-in negation in some check
    /// (`Output::not_builtin`), undone with a discarded check.
    fn note_not_builtin(&mut self, id: NodeId) {
        if self.out.not_builtin.insert(id) {
            self.table_journal.push(TableUndo::NotBuiltin(id));
        }
    }

    /// A per-type table the run time chooses from by class tests (a union
    /// call, `!` on a union): each module member a conditional extension
    /// brings must be answered exactly for every class the receiver may
    /// hold (#515), as a written test must.
    fn implicit_test_check(&mut self, table: &[(Type, MethodId)], what: &str, span: Span) {
        let types: Vec<Type> = table.iter().map(|(t, _)| t.clone()).collect();
        self.implicit_types_check(&types, what, span);
    }

    /// `implicit_test_check` for the types a run-time choice tests.
    fn implicit_types_check(&mut self, types: &[Type], what: &str, span: Span) {
        let recv = Type::union_of(types.to_vec());
        for t in types {
            if let Some((m, c, cargs)) = self.runtime_untestable(&recv, t) {
                self.report_untestable(what, &m, c, &cargs, span, None);
                return;
            }
        }
        for t in types {
            self.record_runtime_test(&recv, t, what);
        }
    }

    /// The refusal of a run-time test the membership table does not answer
    /// exactly (#515): at the test; or, for a test in a dependency (a
    /// library cog, a std module, the prelude) made unanswerable by a class
    /// or extension of the program using it, at that declaration, naming
    /// the test (decided on #515, (A)); `place`: an earlier REPL input's
    /// test, whose declaration is this input's.
    fn report_untestable(
        &mut self,
        what: &str,
        m: &Type,
        c: ClassId,
        cargs: &[Type],
        span: Span,
        place: Option<(&str, (u32, u32))>,
    ) {
        let cname = self.world.class(c).name.clone();
        let ty = self.name(&Type::Class(c, cargs.to_vec()));
        let mname = self.name(m);
        let reason = format!(
            "{what} cannot check at run time that a value of type {ty} is a {mname}: the run time sees only the class `{cname}`, and whether a `{cname}` is a `{mname}` depends on its type arguments (an `extension` with bounds brings `{mname}`)"
        );
        let Type::Class(mid, _) = m else {
            self.error(reason, span);
            return;
        };
        // (The test's place, and where the breaking declaration must be: a
        // dependency's test, the program using it; an earlier REPL input's,
        // this input.)
        let (test_place, there) = match place {
            Some((p, (classes, exts))) => (p.to_string(), DeclaredIn::ReplInput(classes, exts)),
            None => {
                let tg = self.world.file_groups.get(&self.env.file).copied();
                if matches!(tg, Some(UnitGroup::App)) {
                    self.error(reason, span);
                    return;
                }
                (self.test_place(), DeclaredIn::OtherGroup(tg))
            }
        };
        let decl_from = |c: &Self, f: u32, i: usize, is_class: bool| match there {
            DeclaredIn::ReplInput(classes, exts) => {
                i >= if is_class { classes } else { exts } as usize
            }
            DeclaredIn::OtherGroup(tg) => {
                let g = c.world.file_groups.get(&f).copied();
                g.is_some() && g != tg
            }
        };
        let mid = *mid;
        // The class, when declared there; else the extension with bounds
        // that brings the module to its chain, declared there.
        let class = self.world.class(c);
        let culprit = if decl_from(self, class.file, c as usize, true) {
            Some((class.file, class.span, format!("class `{cname}`")))
        } else {
            let chain: Vec<ClassId> = self
                .world
                .resolution(c, &[], View::Declared)
                .into_iter()
                .map(|(k, _)| k)
                .collect();
            self.world
                .extensions
                .iter()
                .find(|e| {
                    chain.contains(&e.target)
                        && e.includes.iter().any(|inc| match inc {
                            Type::Class(k, ka) => {
                                *k == mid
                                    || self
                                        .world
                                        .resolution(*k, ka, View::Override)
                                        .iter()
                                        .any(|(a, _)| *a == mid)
                            }
                            _ => false,
                        })
                        && decl_from(self, e.file, e.id as usize, false)
                })
                .map(|e| (e.file, e.span, self.world.extension_label(e.id)))
        };
        match culprit {
            Some((file, dspan, what_decl)) => {
                self.diagnostics.push((
                    file,
                    Diagnostic::error(
                        format!("{what_decl} makes a run-time test of {test_place} unanswerable: {reason}"),
                        dspan,
                    ),
                ));
            }
            None if place.is_none() => self.error(reason, span),
            // (An earlier input's test, with no declaration of this input to
            // name: refused here all the same.)
            None => self.error(
                format!("this input makes a run-time test of {test_place} unanswerable: {reason}"),
                span,
            ),
        }
    }

    /// Where the test being checked is, for a report at another
    /// declaration: its method, or its file's top level.
    fn test_place(&self) -> String {
        match self.env.method {
            Some(mid) => {
                let m = self.world.method(mid);
                let owner = self.world.class(m.owner);
                // (A file's top-level `def` is a function: named with the
                // cog it is in.)
                if owner.kind == ClassKind::Main {
                    let cog = match self.world.file_groups.get(&self.env.file) {
                        Some(UnitGroup::Cog(i)) => self
                            .world
                            .cogs
                            .get(*i as usize)
                            .map(|c| format!(" of the cog `{}`", c.name))
                            .unwrap_or_default(),
                        _ => String::new(),
                    };
                    format!("the function `{}`{cog}", m.name)
                } else {
                    let sep = if m.singleton { "." } else { "#" };
                    format!("`{}{sep}{}`", owner.name, m.name)
                }
            }
            None => "code outside a method (a top-level statement, a field default)".to_string(),
        }
    }

    /// Remember an accepted test against a module (#515), for the REPL.
    fn record_runtime_test(&mut self, rt: &Type, target: &Type, op: &str) {
        if self.repl_env.is_none() && self.repl_unit.is_none() {
            return;
        }
        if !target.members().iter().any(
            |t| matches!(t, Type::Class(k, _) if self.world.class(*k).kind == ClassKind::Module),
        ) {
            return;
        }
        let place = self.test_place();
        self.runtime_tests.push(RuntimeTest {
            rt: rt.clone(),
            target: target.clone(),
            op: op.to_string(),
            place,
        });
    }

    /// In the REPL, after an input: the earlier inputs' accepted tests that
    /// its classes or extensions make unanswerable are refused at those
    /// declarations (#515, (A)).
    fn recheck_runtime_tests(&mut self) {
        let (tests, classes, exts) = self.repl_test_marks;
        let earlier: Vec<RuntimeTest> =
            self.runtime_tests[..tests.min(self.runtime_tests.len())].to_vec();
        for t in &earlier {
            if let Some((m, c, cargs)) = self.runtime_untestable(&t.rt, &t.target) {
                self.report_untestable(
                    &t.op,
                    &m,
                    c,
                    &cargs,
                    Span::empty(0),
                    Some((&t.place, (classes as u32, exts as u32))),
                );
            }
        }
        self.repl_test_marks = (
            self.runtime_tests.len(),
            self.world.classes.len(),
            self.world.extensions.len(),
        );
    }

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
        // (A union is marked when its members all are.)
        let marked = |world: &World, t: &Type| -> bool {
            let one = |t: &Type| matches!(t, Type::Class(c, _) if dsl.is_some_and(|d| world.class_is_a(*c, d)));
            match t {
                Type::Union(ms) => ms.iter().all(one),
                t => one(t),
            }
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
            // A union `self` (a block on `PQ.()` with `PQ = P | Q`) answers
            // when every member does (#429): the call then dispatches per
            // member, as on any union receiver; a member that does not
            // answer is named by the call's own error.
            if let Type::Union(members) = &outer {
                if members
                    .iter()
                    .any(|m| !self.world.lookup_methods(m, name).is_empty())
                {
                    return Some((outer, k));
                }
            }
            // A module's macro's `self`: the module's class methods too.
            if let Some(own) = self.module_static_self(&outer) {
                if !self.world.lookup_methods(&own, name).is_empty() {
                    return Some((own, k));
                }
            }
        }
        None
    }

    /// In a module's macro, `self` (`t`) is the class that includes the
    /// module (docs/14 §2), whose class object has the module's class
    /// methods: the module's class object, for an implicit call to find
    /// them.
    fn module_static_self(&self, t: &Type) -> Option<Type> {
        let (Type::Class(c, _), Some(m)) = (t, self.env.method) else {
            return None;
        };
        let owner = self.world.method(m).owner;
        (*c == self.world.builtin.meta_classdef
            && self.world.class(owner).kind == ClassKind::Module)
            .then(|| {
                Type::ClassObject(
                    owner,
                    self.world
                        .class(owner)
                        .type_params
                        .iter()
                        .map(|p| Type::Param(p.id))
                        .collect(),
                )
            })
    }

    /// Route an implicit-self call to the `self` of receiver level `k`:
    /// that function keeps its `self` in a hidden frame slot the block
    /// reads like a captured variable.
    fn bind_outer_self(&mut self, expr: &Expr, k: usize) {
        let owner_frame = self.env.receivers[k].outer_frame;
        if k == 0 && self.in_function() {
            let name = match &expr.kind {
                ExprKind::Call(c) => c.name.clone(),
                _ => String::new(),
            };
            self.error(
                format!("a function has no `self`: `{name}` is not a method of the block's receiver, and a function has none of its own to call it on"),
                expr.span,
            );
        }
        // (A block with a receiver inside `static(...)` reaching a `self`
        // set outside it, the lexical one or an outer block's receiver:
        // captured as a variable would be.)
        // (The static block's own receiver, entered just before its frame,
        // is the `static def`'s to give.)
        let outside = |sf: usize| k == 0 || self.env.receivers[k - 1].outer_frame + 1 < sf;
        if self.env.static_frame.is_some_and(outside) {
            let name = match &expr.kind {
                ExprKind::Call(c) => c.name.clone(),
                _ => String::new(),
            };
            self.error(
                format!(
                    "a block in `static(...)` captures nothing: calling `{name}` uses `self`, which is not a constant (docs/14 §8)"
                ),
                expr.span,
            );
        }
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
        // An enclosing `self` from outside a task or shareable block is
        // captured by it, as a variable would be: it must be Shareable.
        // (That `self` is the one of the frame the `k`-th receiver block
        // was entered from: the lexical one for the outermost, else the
        // receiver of the block around it, which belongs to that block's
        // frame.)
        let self_frame = if k == 0 {
            0
        } else {
            self.env.receivers[k - 1].outer_frame + 1
        };
        if self.env.task_frame.is_some_and(|tf| self_frame < tf) && !self.in_static_block() {
            let name = match &expr.kind {
                ExprKind::Call(c) => c.name.clone(),
                _ => String::new(),
            };
            let outer = self.resolve(&self.env.receivers[k].outer_self.clone());
            if !outer.has_vars() && !self.world.is_shareable(&outer) {
                self.error(
                    format!(
                        "calling `{name}` uses the enclosing `self`, which has the non-shareable type {} and cannot be captured by {}",
                        self.world.type_name(&outer),
                        self.task_capture_name()
                    ),
                    expr.span,
                );
            }
        }
        self.bind_outer_self_slot(expr, k);
    }

    /// Record that `expr` reads the `self` outside the `k`-th block with
    /// a receiver around it, from the hidden slot of the frame that `self`
    /// belongs to (`Output::outer_self_calls`, `self_slots`).
    fn bind_outer_self_slot(&mut self, expr: &Expr, k: usize) {
        let owner_frame = self.env.receivers[k].outer_frame;
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
        // (Journaled: a check discarded, an overload tried with its
        // block's receiver type not yet inferred, leaves no fall-through
        // behind for the candidate chosen.)
        self.table_journal.push(TableUndo::OuterSelf(
            expr.id,
            expr.span,
            self.out.outer_self_calls.contains(&expr.id),
            self.out.outer_self_depths.get(&expr.id).copied(),
            self.out.var_refs.get(&expr.span).copied(),
        ));
        self.out.var_refs.insert(expr.span, VarRef { depth, slot });
        self.out.self_slots.insert(owner, slot);
        self.out.outer_self_calls.insert(expr.id);
        self.out
            .outer_self_depths
            .insert(expr.id, (self.env.receivers.len() - k) as u32);
    }

    /// Note which `self` an implicit call went to, while a
    /// block given to a union receiver is checked once per member.
    fn note_self_use(
        &mut self,
        id: NodeId,
        span: Span,
        name: &str,
        frame: usize,
        self_ty: Type,
        fell: bool,
    ) {
        if self.union_block_calls == 0 {
            return;
        }
        self.table_journal
            .push(TableUndo::SelfUse(self.self_uses.len()));
        self.self_uses.push(SelfUse {
            id,
            span,
            name: name.to_string(),
            frame,
            self_ty,
            fell,
            method: None,
        });
    }

    /// Whether the implicit call `expr`, just checked, fell through to an
    /// enclosing `self`, and to which hidden slot.
    fn fell_through(&self, expr: &Expr) -> Option<VarRef> {
        if self.out.outer_self_calls.contains(&expr.id) {
            self.out.var_refs.get(&expr.span).copied()
        } else {
            None
        }
    }

    /// A block given to a union receiver is compiled once: an implicit
    /// call in it that one member's check sends to the block's own `self`
    /// and another's to an enclosing one (read from its hidden slot), or a
    /// function for one and a method for another, or one `self`'s
    /// overloads chosen per member, would run the wrong method or on the
    /// wrong object (`self_uses_differ`). `uses` holds each
    /// member's range of `self_uses`.
    fn compare_self_uses(
        &mut self,
        call: &Call,
        members: &[Type],
        uses: &[(usize, usize)],
        block_frame: usize,
    ) {
        // Each node's first use in each member's check, compared pairwise.
        let mut by_node: Vec<(NodeId, Vec<(usize, usize)>)> = Vec::new();
        for (k, &(start, end)) in uses.iter().enumerate() {
            for (i, u) in self.self_uses.iter().enumerate().take(end).skip(start) {
                // (A call no method answered: an error of its own.)
                if u.method.is_none() {
                    continue;
                }
                match by_node.iter_mut().find(|(id, _)| *id == u.id) {
                    Some((_, seen)) if !seen.iter().any(|(j, _)| *j == k) => seen.push((k, i)),
                    Some(_) => {}
                    None => by_node.push((u.id, vec![(k, i)])),
                }
            }
        }
        for (_, seen) in by_node {
            let pair = seen.iter().enumerate().find_map(|(n, &a)| {
                seen[n + 1..]
                    .iter()
                    .find(|&&b| self.self_uses_differ(a.1, b.1))
                    .map(|&b| (a, b))
            });
            let Some((a, b)) = pair else { continue };
            let msg = self.self_use_conflict(call, members, a, b, block_frame);
            let span = self.self_uses[b.1].span;
            let file = self.env.file;
            // (Once, for the innermost call: an enclosing one's members
            // see it differ too; and not beside another error there, such
            // as overloads a test cannot choose between.)
            let known = self
                .diagnostics
                .iter()
                .any(|(f, d)| *f == file && d.span == span && d.severity == Severity::Error);
            if !known {
                self.error(msg, span);
            }
        }
    }

    /// Whether two checks' uses cannot be compiled as one. A call falling
    /// through reads an enclosing frame's hidden slot (`bind_outer_self`),
    /// and the compiled block reads it for every member: another member's
    /// must fall through to that frame too, or read its own `self` with no
    /// receiver block between that frame and the call (that `self` is the
    /// slot's), with the same method (tested by the receivers' classes,
    /// not the `self`'s). Calls on the block's own `self` (its receiver,
    /// or the enclosing `self` where its block has none, its `self` at run
    /// time) are chosen by a test of its class: overrides, or overloads on
    /// types no value is of both. A function (`Kernel`'s, a top-level
    /// `def`, which uses no `self`) agrees only with the same function.
    /// Built-in overloads are called by name (`union_conflicts`).
    fn self_uses_differ(&self, a: usize, b: usize) -> bool {
        let (ua, ub) = (&self.self_uses[a], &self.self_uses[b]);
        let function = |u: &SelfUse| u.method.is_some_and(|m| self.world.takes_no_self(m));
        let native = |u: &SelfUse| u.method.is_some_and(|m| self.world.method(m).is_native);
        let other_method = ua.method != ub.method && !(native(ua) && native(ub));
        match (function(ua), function(ub)) {
            (true, true) => return other_method,
            (false, false) => {}
            _ => return true,
        }
        match (ua.fell, ub.fell) {
            (true, true) => ua.frame != ub.frame || other_method,
            (true, false) => ub.frame > ua.frame || other_method,
            (false, true) => ua.frame > ub.frame || other_method,
            (false, false) => {
                let (Some(ma), Some(mb)) = (ua.method, ub.method) else {
                    return false;
                };
                if !other_method || self.overrides_one(ma, mb) {
                    return false;
                }
                let (ta, tb) = (self.resolve(&ua.self_ty), self.resolve(&ub.self_ty));
                // (A value may be of both: a subclass, a module a subclass
                // of the other includes, a type parameter's.)
                let open = |t: &Type| match t {
                    Type::Class(c, _) => self.world.class(*c).kind == ClassKind::Module,
                    Type::Param(_) => true,
                    _ => false,
                };
                // (On one type, `note_union_table` refuses them.)
                ta != tb
                    && (self.world.is_subtype(&ta, &tb)
                        || self.world.is_subtype(&tb, &ta)
                        || open(&ta)
                        || open(&tb))
            }
        }
    }

    /// Whether `a` and `b` are one method and its override (or both
    /// override one), as the runtime dispatches: a call of either runs
    /// the receiver's own.
    fn overrides_one(&self, a: MethodId, b: MethodId) -> bool {
        // (The override table, `World::overrides`.)
        let set = |r: MethodId| {
            let mut set = vec![r];
            set.extend(self.world.overrides(r));
            set
        };
        let (sa, sb) = (set(a), set(b));
        sa.iter().any(|m| sb.contains(m))
    }

    fn self_use_conflict(
        &self,
        call: &Call,
        members: &[Type],
        (j, a): (usize, usize),
        (k, b): (usize, usize),
        block_frame: usize,
    ) -> String {
        let (ua, ub) = (&self.self_uses[a], &self.self_uses[b]);
        let (ma, mb) = (self.name(&members[j]), self.name(&members[k]));
        let recv = match call.recv.as_ref().map(|r| &r.kind) {
            Some(ExprKind::Local(n)) => format!("`{n}`"),
            _ => "the receiver".to_string(),
        };
        let what = |u: &SelfUse| {
            let m = match u.method {
                // (With its parameters where overloaded: `f(Int)`.)
                Some(m) if self.world.takes_no_self(m) => {
                    let label = self.method_label(m);
                    let f = label.rsplit_once('#').map_or(label.as_str(), |(_, f)| f);
                    format!("the function `{f}`")
                }
                Some(m) => format!("`{}`", self.method_label(m)),
                None => format!("a method of {}", self.name(&u.self_ty)),
            };
            match (u.fell, ua.method == ub.method) {
                // (The block's own `self`, read by a receiver block in it.)
                (true, _) if u.frame >= block_frame => format!("{m} of the block's `self`"),
                (true, _) => format!("{m} of the enclosing `self`"),
                // (One method, on two `self`s.)
                (false, true) => format!("{m} on {}", self.name(&u.self_ty)),
                (false, false) => m,
            }
        };
        let name = &ua.name;
        // (A function has no receiver to write.)
        let function = [ua, ub]
            .iter()
            .any(|u| u.method.is_some_and(|m| self.world.takes_no_self(m)));
        let fix = match function {
            true => format!("narrow {recv} with `case`"),
            false => format!("write the receiver (`self.{name}`, or {recv} narrowed with `case`)"),
        };
        format!(
            "`{name}` in the block of `{}` resolves to {} for {ma} and to {} for {mb}: {UNION_SELF_RULE} resolve its calls the same way for every member; {fix}",
            call.name,
            what(ua),
            what(ub),
        )
    }

    /// `Self.new(args)` in an instance method, or a block or lambda in it
    /// (docs/01 §9): an instance of `self`'s run-time class, built with its
    /// `initialize`, as `new` in a class method builds the receiver's. A
    /// subclass inheriting the method keeps a compatible `initialize` or
    /// overrides the method (`check_inherited_constructors`). Typed `Self`
    /// where `self` is the opaque `Self`, else the class.
    fn check_self_new(&mut self, expr: &Expr, call: &Call, expected: Option<&Type>) -> Type {
        let refuse = |this: &mut Self, why: &str| {
            this.error(format!("`Self.new` {why}"), expr.span);
            this.check_args_blindly(call);
            Type::Nothing
        };
        let lifted = self.env.lifted_frame.is_some();
        // The class: the method's, or the one a lifted block's method is
        // generated into (bounded by the block's receiver type).
        let instance = match self.env.method {
            Some(_) if lifted => match (&self.env.self_type, &self.world.self_bound) {
                (Type::Param(SELF_PARAM), Some(Type::Class(c, args))) => Some((*c, args.clone())),
                _ => None,
            },
            Some(m) if !self.world.method(m).singleton && !self.in_function() => {
                let owner = self.world.method(m).owner;
                let args = self
                    .world
                    .class(owner)
                    .type_params
                    .iter()
                    .map(|p| Type::Param(p.id))
                    .collect();
                Some((owner, args))
            }
            _ => None,
        };
        let Some((cid, args)) = instance else {
            let why = if self.in_function() {
                "in a function: a function has no `self` whose class `Self` would be"
            } else {
                "is written in an instance method (in a class method, `new` builds the receiver's class)"
            };
            return refuse(self, why);
        };
        if !self.own_self() {
            return refuse(
                self,
                "builds the class of the method's `self`, which a block with another receiver hides: build it outside the block",
            );
        }
        if self.world.class(cid).kind == ClassKind::Module {
            return refuse(
                self,
                "in a module's method: the classes that include it may each take other arguments in `initialize`",
            );
        }
        let m = self.env.method.expect("in a method");
        // (It reads `self`, which a task's block or `static(...)` cannot
        // capture unless it is Shareable.)
        self.check_task_self("`self`, whose class `Self.new` builds,", expr.span);
        let saved = std::mem::replace(&mut self.constructing_self, true);
        let t = self.check_constructor(expr, call, cid, &args, expected);
        self.constructing_self = saved;
        // Built by the receiver's class at run time (a subclass, perhaps):
        // not where no class can inherit from it.
        if !self.world.has_no_subclass(cid) {
            if let Some(CallTarget::Constructor { init, .. }) =
                self.out.calls.get(&expr.id).cloned()
            {
                self.out.self_new.insert(expr.id);
                // (A lifted block's: recorded when its method is generated,
                // `StaticHost::generated_new`.)
                if !lifted {
                    self.self_news
                        .push((cid, init, m, expr.span, self.env.file));
                }
            }
        }
        if t.is_nothing() {
            return t;
        }
        if self.env.self_opaque {
            Type::Param(SELF_PARAM)
        } else {
            t
        }
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
        // (`Self.new` builds the receiver's class, which is concrete; taken
        // first, so that a construction among its arguments is checked as
        // any.)
        let constructing_self = std::mem::take(&mut self.constructing_self);
        if ((class.is_abstract || class.kind == ClassKind::Module) && !constructing_self)
            || class.kind == ClassKind::Enum
        {
            self.error(format!("cannot instantiate `{}`", class.name), expr.span);
            self.check_args_blindly(call);
            return Type::Nothing;
        }
        // A built-in value is the runtime's own: one without a `self.new`
        // of its own is made by its literal (or a builder), not with `new`
        // (which built an object of its class, no value of it).
        // (`World::built_by_runtime`, the rule the runtime's guard reads.)
        let b = &self.world.builtin;
        let class_object = self.world.class_is_a(cid, b.class_);
        if self.world.built_by_runtime(cid) {
            let hint = if cid == b.string {
                ": write `\"\"`, or `String::Builder.new` to build one".to_string()
            } else if cid == b.int {
                ": write `0`".to_string()
            } else if cid == b.float {
                ": write `0.0`".to_string()
            } else if cid == b.bool_ {
                ": write `true` or `false`".to_string()
            } else if cid == b.nil {
                ": write `nil`".to_string()
            } else if cid == b.symbol {
                ": write `:name`".to_string()
            } else if cid == b.range {
                ": write `a..b`".to_string()
            } else if class_object {
                ": a class is a value by its name".to_string()
            } else if cid == b.proc_ {
                ": write a lambda, `->(x: Int) { ... }`".to_string()
            } else if cid == b.integer {
                ": write a number where an `Integer` is expected, or `to_integer`".to_string()
            } else {
                String::new()
            };
            self.error(
                format!("`{}` is not built with `new`{hint}", class.name),
                expr.span,
            );
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
        // A handle names a field it reads in place: only `def_field` and
        // `field_ref` make one, for the field they name (docs/14 §5).
        if cid == self.world.builtin.meta_field_ref || cid == self.world.builtin.meta_method {
            self.error(
                if cid == self.world.builtin.meta_field_ref {
                    "a `Meta::FieldRef` is made by `def_field` or `field_ref` (docs/14 §5), not with `new`"
                } else {
                    "a `Meta::Method` is made by `def_method`, `def_class_method`, `method_ref` or `class_method_ref` (docs/14 §5), not with `new`"
                },
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
        // The class's own `initialize` hides its ancestors' (docs/01 §9):
        // the nearest that has one (in lookup order), so a class that
        // inherits them takes its superclass's alone, not those the
        // superclass's hide in turn.
        if let Some(nearest) = cands.first().map(|(m, _)| self.world.method(*m).owner) {
            cands.retain(|(m, _)| self.world.method(*m).owner == nearest);
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
    /// `Range[T <: Comparable[T]]`'s bound where a range is made (`a..b`)
    /// or a range pattern compares (`in a..b`), as for a written type
    /// (#559): the bounds' type with `nil` taken out (a missing bound, which
    /// nothing compares with), and none for built-in numbers, which compare
    /// with each other inline (`1..Float::INFINITY`). A type parameter
    /// without the bound is refused, as in a written `Range[T]`; so is a
    /// type not yet inferred, which could become anything.
    pub(crate) fn check_range_bound(&mut self, elem: &Type, span: Span) {
        let e = self.resolve(elem).without_nil(self.world.builtin.nil);
        if e.is_nothing() {
            return;
        }
        // (Not yet known: the comparison would run on whatever it becomes,
        // so it is refused rather than left unchecked.)
        if e.has_vars() {
            self.error(
                "the type of the range's bounds is not yet known here, but a range compares them, so it must be Comparable: give the bounds a type",
                span,
            );
            return;
        }
        // (Numbers of the built-in classes compare with each other, inline.)
        let b = &self.world.builtin;
        let numbers = [b.int, b.integer, b.float];
        if e.members()
            .iter()
            .all(|m| matches!(m, Type::Class(id, _) if numbers.contains(id)))
        {
            return;
        }
        let range = Type::Class(self.world.builtin.range, vec![e]);
        self.check_class_bounds(&range, span);
    }

    fn check_class_bounds(&mut self, instance: &Type, span: Span) {
        let Type::Class(cid, args) = self.resolve(instance) else {
            return;
        };
        let params = self.world.class(cid).type_params.clone();
        for (p, a) in params.iter().zip(args.iter()) {
            if a.has_vars() {
                let shareable = self.world.builtin.shareable;
                if p.bounds
                    .iter()
                    .any(|b| matches!(b, Type::Class(bid, _) if *bid == shareable))
                    && self.world.refuse_undecided()
                {
                    let class = self.world.class(cid).name.clone();
                    let param = self.world.type_param_name(p.id);
                    self.error(
                        format!("the type argument for `{param}` of `{class}` is not yet known here, but it must be Shareable: write it (as `{class}[Int].new`)"),
                        span,
                    );
                }
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
    /// type are typed (`pre`). A candidate refused only because a type is
    /// not yet known where a Shareable is required must not let the call
    /// silently take another (`a = []; f(a)` with `f(x: Shareable)` and
    /// `f(x: Object)`): when a check refused one so, the choice is made
    /// again as if the types were known, and a different winner is an
    /// error asking for an annotation.
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
        if cands.len() < 2 || self.world.undecided_passes.get() {
            return self.resolve_pretyped_once(
                expr,
                call,
                recv_ty,
                cands,
                implicit_self,
                expected,
                is_init,
                pre,
            );
        }
        let (infer, diags, tables) = (self.infer.save(), self.diagnostics.len(), self.table_mark());
        let refusals = self.world.undecided_refusals.get();
        self.last_winner = None;
        let t = self.resolve_pretyped_once(
            expr,
            call,
            recv_ty,
            cands.clone(),
            implicit_self,
            expected,
            is_init,
            pre,
        );
        if self.world.undecided_refusals.get() == refusals {
            return t;
        }
        // (What this call refused, it deals with here: the count goes
        // back, so the calls around it do not choose again.)
        let winner = self.last_winner.filter(|w| w.0 == expr.id).map(|w| w.1);
        // As if known: what it chooses is all that is kept.
        self.infer.restore(infer.clone());
        self.truncate_diagnostics(diags);
        self.discard_tables(tables);
        self.world.undecided_passes.set(true);
        self.last_winner = None;
        self.resolve_pretyped_once(
            expr,
            call,
            recv_ty,
            cands.clone(),
            implicit_self,
            expected,
            is_init,
            pre,
        );
        self.world.undecided_passes.set(false);
        let known = self.last_winner.filter(|w| w.0 == expr.id).map(|w| w.1);
        self.infer.restore(infer);
        self.truncate_diagnostics(diags);
        self.discard_tables(tables);
        let t = self.resolve_pretyped_once(
            expr,
            call,
            recv_ty,
            cands,
            implicit_self,
            expected,
            is_init,
            pre,
        );
        self.world.undecided_refusals.set(refusals);
        if let (Some(w), Some(k)) = (winner, known) {
            if w == k {
                return t;
            }
            let sig = self.signature(self.world.method(k));
            self.error(
                format!(
                    "which overload this call takes depends on a type not yet known here, which must be Shareable for {sig}: annotate it (as `a: Array[Int] = []`)"
                ),
                expr.span,
            );
        }
        t
    }

    /// `resolve_pretyped` for one choice.
    #[allow(clippy::too_many_arguments)]
    fn resolve_pretyped_once(
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
        // (Which active extension brought each module of the receiver's
        // order: two of them on the same target give no order, #577.)
        let ext_src = if single {
            Vec::new()
        } else {
            self.extension_sources(recv_ty)
        };
        let inferring = pre.values().any(|t| self.infer.resolve(t).has_vars());
        let mut fits: Vec<(usize, MethodId, bool)> = Vec::new();
        let mut kept: Option<KeptFirst> = None;
        // The candidates whose arguments passed and whose block failed.
        let mut block_failed: Vec<(MethodId, HashMap<TypeParamId, Type>)> = Vec::new();
        // Which candidate each failure is of (filled at the next one), to
        // leave out of the list a method another candidate overrides
        // (#624).
        let mut failure_of: Vec<MethodId> = Vec::new();
        let mut last_tried: Option<MethodId> = None;
        for (index, (mid, class_subst)) in cands.iter().enumerate().rev() {
            if let Some(prev) = last_tried {
                failure_of.resize(failures.len(), prev);
            }
            last_tried = Some(*mid);
            if !single
                && !inferring
                && fits.iter().any(|f| {
                    !f.2 && self.beats((f.0, f.1), (index, *mid), &cands, block_arity, &ext_src)
                })
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
            // `deinitialize` is run by the runtime when the object is
            // released (and by `super` in a `deinitialize`): called
            // otherwise, it would run again at the release.
            if m.name == "deinitialize" && !m.singleton && !is_init {
                failures.push(DEINITIALIZE_CALLED.to_string());
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
            let bound_self = if implicit_self && self.self_is_opaque_for(recv_ty, &m) {
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
                            block_failed.push((*mid, class_subst.clone()));
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
                            // (A bound is no holder: the call's result may
                            // be, so a literal is not decided here.)
                            self.checking_bound = true;
                            let fits = self.coerce(&rt, &b);
                            self.checking_bound = false;
                            if !fits {
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
            let (mut winner, mut rivals) = self.pick_overload(&fits, &cands, block_arity, &ext_src);
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
                    self.resolve_pretyped_once(
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
            self.last_winner = Some((expr.id, winner));
            self.note_lexical_class_call(expr, call, recv_ty, winner);
            // (The pair named: among the tied methods, those no other of
            // them overrides.)
            let tied: Vec<MethodId> = std::iter::once(winner)
                .chain(rivals.iter().copied())
                .collect();
            let open: Vec<MethodId> = tied
                .iter()
                .copied()
                .filter(|t| {
                    !tied
                        .iter()
                        .any(|u| u != t && self.overridden_by(*u).contains(t))
                })
                .collect();
            let ext_pair = open.iter().enumerate().find_map(|(i, x)| {
                open[i + 1..]
                    .iter()
                    .find_map(|y| self.extension_rivals(*x, *y, &ext_src).map(|p| (*x, *y, p)))
            });
            // (Two extensions' own methods with the same parameters, #585;
            // others tie by fitting equally, listed below.)
            let subst_of = |m: MethodId| {
                cands
                    .iter()
                    .find(|(k, _)| *k == m)
                    .map(|(_, s)| s.clone())
                    .unwrap_or_default()
            };
            let own_pair = open.iter().enumerate().find_map(|(i, x)| {
                let ex = self.world.method(*x).extension?;
                open[i + 1..].iter().find_map(|y| {
                    let ey = self.world.method(*y).extension?;
                    let (a, b) = (self.world.method(*x), self.world.method(*y));
                    let (sa, sb) = (subst_of(*x), subst_of(*y));
                    (ex != ey
                        && self.as_specific(a, &sa, b, &sb)
                        && self.as_specific(b, &sb, a, &sa))
                    .then_some((ex, ey))
                })
            });
            if let Some((x, y, (ea, eb))) = ext_pair {
                self.extension_ambiguity(&call.name, x, y, ea, eb, expr.span);
            } else if let Some((ea, eb)) = own_pair {
                let (na, nb) = (self.extension_name(ea), self.extension_name(eb));
                // (Two in one place have the same name; the `using` hint
                // only where both are scoped.)
                let who = if na == nb {
                    format!(
                        "two {}",
                        na.replacen("the extension", "extensions", 1).replacen(
                            "the top-level extension",
                            "top-level extensions",
                            1
                        )
                    )
                } else {
                    format!("{na} and {nb}")
                };
                let scoped = |e: ExtensionId| self.world.extensions[e as usize].module.is_some();
                let hint = if scoped(ea) && scoped(eb) {
                    "; leave out one `using`"
                } else {
                    ""
                };
                self.error(
                    format!(
                        "the call of `{}` is ambiguous: {who}, both active here, each define it with the same parameters{hint}",
                        call.name
                    ),
                    expr.span,
                );
            } else if !rivals.is_empty() {
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
        if let Some(prev) = last_tried {
            failure_of.resize(failures.len(), prev);
        }
        // A candidate another candidate overrides, by the override table
        // (`overridden_by`), whatever their result types: listed once, as
        // the overriding one (#624).
        if failure_of.len() == failures.len() {
            let hidden = |m: MethodId| {
                cands
                    .iter()
                    .any(|(o, _)| *o != m && self.overridden_by(*o).contains(&m))
            };
            let keep: Vec<bool> = failure_of.iter().map(|m| !hidden(*m)).collect();
            if keep.iter().any(|k| *k) {
                let mut i = 0;
                failures.retain(|_| {
                    let k = keep[i];
                    i += 1;
                    k
                });
            }
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
        // Still type the block for its own diagnostics: as the one
        // overload whose arguments passed and whose block, a block with a
        // receiver, failed, if there is one (`def_method`'s body, docs/14
        // §5: its `self` is the receiver, not the caller's; a `Quoted`
        // block type is not one of these), else as a plain block.
        if call.block.is_some() && !single {
            let receiver_block = |m: MethodId| {
                self.world
                    .method(m)
                    .block
                    .as_ref()
                    .is_some_and(|(_, t)| matches!(t, Type::Proc(Some(_), ..)))
            };
            if let [only] = block_failed.as_slice() {
                if receiver_block(only.0) {
                    self.resolve_pretyped_once(
                        expr,
                        call,
                        recv_ty,
                        vec![only.clone()],
                        implicit_self,
                        expected,
                        is_init,
                        pre,
                    );
                    return Type::Nothing;
                }
            }
        }
        if let Some(b) = &call.block {
            // (With the receiver every candidate's block has, if they
            // agree: its calls are on it, not on the caller's `self`.)
            let receivers: Vec<Option<Type>> = cands
                .iter()
                .map(|(m, subst)| match &self.world.method(*m).block {
                    Some((_, Type::Proc(Some(r), ..))) => Some(r.subst(subst)),
                    _ => None,
                })
                .collect();
            // (Not one still naming a type parameter, `Self` or the
            // method's: unbound here, it would mislead the block's calls.)
            let receiver = match receivers.first() {
                Some(Some(r))
                    if !r.has_params() && receivers.iter().all(|x| x.as_ref() == Some(r)) =>
                {
                    Some(Box::new(r.clone()))
                }
                _ => None,
            };
            let fresh = self.infer.fresh();
            let params: Vec<Type> = b
                .params
                .list
                .iter()
                .filter(|p| p.kind != ParamKind::KeywordOnly)
                .map(|_| self.infer.fresh())
                .collect();
            // (Its keywords as it declares them: no more errors about them.)
            let kws: Vec<ProcKw> = b
                .params
                .list
                .iter()
                .filter(|p| p.kind == ParamKind::KeywordOnly)
                .map(|p| ProcKw {
                    name: p.name.clone(),
                    ty: self.infer.fresh(),
                    required: p.default.is_none(),
                })
                .collect();
            self.check_block(
                expr.id,
                b,
                &Type::Proc(
                    receiver,
                    params,
                    Box::new(fresh),
                    false,
                    ProcKw::sorted(kws),
                ),
            );
        }
        Type::Nothing
    }

    /// `JSON.decode[T]`'s `T`: written at the call, and a type JSON
    /// decodes into (`json_decode::descriptor`), else an error naming the
    /// type at fault.
    fn check_json_decode_type(
        &mut self,
        expr: &Expr,
        call: &Call,
        m: &MethodInfo,
        args: &[(TypeParamId, Type)],
    ) {
        if call.type_args.is_empty() {
            self.error(
                format!(
                    "`JSON.{}` takes the type to decode into explicitly (`JSON.{}[Args](text)`)",
                    m.name, m.name
                ),
                expr.span,
            );
            return;
        }
        let t_param = m.type_params.first().map(|p| p.id);
        let Some((_, t)) = args.iter().find(|(p, _)| Some(*p) == t_param) else {
            return;
        };
        let t = self.resolve(t);
        // In a block given to `def_method` and its kin, the enclosing
        // method's type parameters may be carried into the generated
        // method (docs/14 §5): `T` is decided there, at the statement.
        let carried: Vec<TypeParamId> = match (self.env.lifted_frame, self.env.method) {
            (Some(_), Some(mid)) => self
                .world
                .method(mid)
                .type_params
                .iter()
                .map(|p| p.id)
                .collect(),
            _ => Vec::new(),
        };
        if let Err(why) = crate::json_decode::check_with(&self.world, &t, &|p| carried.contains(&p))
        {
            self.error(
                format!(
                    "`JSON.{}` cannot decode into {}: {why}",
                    m.name,
                    self.world.type_name(&t)
                ),
                expr.span,
            );
        }
    }

    /// `statement_values[U]`'s `U` (docs/14 §5): written, concrete (no
    /// type parameter, which would let one key hold the values of
    /// different instantiations of a generic `static def`), and bakeable
    /// (the values are what later statements and the class-end hooks read,
    /// and what they generate from).
    fn check_statement_values_type(
        &mut self,
        expr: &Expr,
        call: &Call,
        m: &MethodInfo,
        args: &[(TypeParamId, Type)],
    ) {
        if call.type_args.is_empty() {
            self.error(
                "`statement_values` takes the values' type explicitly (`statement_values[Plug](:plugs)`): a key has one type, written where it is named",
                expr.span,
            );
            return;
        }
        let u_param = m.type_params.first().map(|p| p.id);
        let Some((_, u)) = args.iter().find(|(p, _)| Some(*p) == u_param) else {
            return;
        };
        let u = self.resolve(u);
        if u.has_vars() || u.mentions_any_param() {
            self.error(
                format!(
                    "statement values of type {} cannot be kept: their type must be a concrete one, not a type parameter (a generic `static def`'s calls would put values of different types under one key)",
                    self.world.type_name(&u)
                ),
                expr.span,
            );
            return;
        }
        if let Some(why) = self.bake_refusal(&u) {
            let why = if why.is_empty() {
                String::new()
            } else {
                format!(" ({why})")
            };
            self.error(
                format!(
                    "statement values of type {} cannot be kept: their values must be bakeable{why} (literals, classes, `data` of Shareable fields, arrays and hashes of them)",
                    self.world.type_name(&u)
                ),
                expr.span,
            );
        }
    }

    /// What a call that a method was chosen for gives.
    fn finish_call(&mut self, expr: &Expr, call: &Call, m: &MethodInfo, ret: Type) -> Type {
        self.out
            .calls
            .insert(expr.id, CallTarget::Method { method: m.id });
        // A handle's `get`/`set`/`bind` is lowered in place where the
        // handle is baked (docs/14 §5): its receiver is a variable of the
        // `static def` that a block given to `def_method` captures.
        let b = &self.world.builtin;
        let handle = if m.owner == b.meta_field_ref && matches!(m.name.as_str(), "get" | "set") {
            Some("Meta::FieldRef")
        } else if m.owner == b.meta_method && m.name == "bind" {
            Some("Meta::Method")
        } else {
            None
        };
        if let Some(class) = handle {
            let baked = match (&call.recv, self.env.lifted_frame) {
                (Some(r), Some(lf)) => match &r.kind {
                    ExprKind::Local(name) => self
                        .lookup_var(name)
                        .is_some_and(|(depth, _)| self.env.frames.len() - 1 - depth < lf),
                    _ => false,
                },
                _ => false,
            };
            if !baked {
                let what = match m.name.as_str() {
                    "get" => "read",
                    "set" => "written",
                    _ => "bound",
                };
                self.error(
                    format!(
                        "a `{class}` is {what} only in a block given to `def_method` (or `def_class_method`) that captures it from the `static def`, where it is baked"
                    ),
                    expr.span,
                );
            } else if call.args.iter().any(|a| !matches!(a, Arg::Positional(_))) {
                // (Lowered in place: its arguments by position.)
                self.error(
                    format!(
                        "`{}` on a `{class}` takes its arguments by position",
                        m.name
                    ),
                    expr.span,
                );
            } else {
                // Its object is the generated method's `self`, for now: the
                // handle's `T` is the `static def`'s view of the class, and
                // the member belongs to the class generated into, which
                // only `self` is sure to be (docs/14 §5).
                let own_self = self
                    .env
                    .lifted_frame
                    .is_some_and(|lf| !self.env.receivers.iter().any(|r| r.outer_frame + 1 > lf));
                let is_self = matches!(
                    call.args.first(),
                    Some(Arg::Positional(e)) if matches!(e.kind, ExprKind::SelfRef)
                );
                if !(is_self && own_self) {
                    self.error(
                        format!(
                            "`{}` on a `{class}` takes the generated method's `self` (`ref.{}(self{})`): the handle's class is the `static def`'s view, the member the class generated into's",
                            m.name,
                            m.name,
                            if m.name == "set" { ", value" } else { "" }
                        ),
                        expr.span,
                    );
                }
            }
        }
        self.note_static_call(expr, m.id);
        // The chosen candidate's type arguments: a `static def`'s, and a
        // generic method's (`call_type_args`). The trials of this call go;
        // those of the calls around it, still being checked, stay.
        if m.is_static || !m.type_params.is_empty() {
            if let Some((_, _, args)) = self
                .type_args_trials
                .iter()
                .rev()
                .find(|(id, mid, _)| *id == expr.id && *mid == m.id)
                .cloned()
            {
                if m.is_static {
                    // `statement_values[U]`'s values are what later
                    // statements and the class-end hooks read, and what
                    // they generate from: `U` is a type whose values can be
                    // baked (docs/14 §5).
                    if m.owner == self.world.builtin.meta_classdef && m.name == "statement_values" {
                        self.check_statement_values_type(expr, call, m, &args);
                    }
                    self.out.type_args.insert(expr.id, args);
                } else {
                    // `JSON.decode[T]`: `T` written, and decodable.
                    if crate::json_decode::is_decode(&self.world, m) {
                        self.check_json_decode_type(expr, call, m, &args);
                    }
                    self.out.call_type_args.insert(expr.id, args);
                }
            }
        }
        self.type_args_trials.retain(|(id, _, _)| *id != expr.id);
        // A `Quoted[shareable P]`'s captures passed the shareable-capture
        // check: an `Array[Shareable]` (docs/14 §6).
        let ret = if m.owner == self.world.builtin.quoted && m.name == "captures" {
            let recv = call
                .recv
                .as_ref()
                .and_then(|r| self.out.node_types.get(&r.id).cloned())
                .map(|t| self.resolve(&t))
                // (`q&.captures` calls it on the `Quoted` only.)
                .map(|t| {
                    if call.safe_nav {
                        t.without_nil(self.world.builtin.nil)
                    } else {
                        t
                    }
                });
            match recv {
                Some(t) if self.quoted_shareable(&t) => Type::Class(
                    self.world.builtin.array,
                    vec![Type::Class(self.world.builtin.shareable, Vec::new())],
                ),
                _ => ret,
            }
        } else {
            ret
        };
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

    /// Whether `t` is a `Quoted` of a `shareable` procedure type (each
    /// member of a union one): its block captured Shareable values only.
    fn quoted_shareable(&mut self, t: &Type) -> bool {
        match self.resolve(t) {
            Type::Class(c, args) if c == self.world.builtin.quoted && args.len() == 1 => {
                matches!(self.resolve(&args[0]), Type::Proc(_, _, _, true, _))
            }
            Type::Union(ms) => !ms.is_empty() && ms.iter().all(|m| self.quoted_shareable(m)),
            _ => false,
        }
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
        ext_src: &[(ClassId, ExtensionId)],
    ) -> (MethodId, Vec<MethodId>) {
        let best_level = fits.iter().any(|f| !f.2);
        let level: Vec<&(usize, MethodId, bool)> =
            fits.iter().filter(|f| f.2 != best_level).collect();
        let top: Vec<MethodId> = level
            .iter()
            .filter(|x| {
                !level
                    .iter()
                    .any(|y| self.beats((y.0, y.1), (x.0, x.1), cands, block_arity, ext_src))
            })
            .map(|x| x.1)
            .collect();
        // A tie whose methods one of them overrides all the others goes to
        // that one, as dispatch would run it (docs/01 §9, #436).
        if top.len() > 1 {
            if let Some(&x) = top.iter().find(|&&x| {
                let o = self.overridden_by(x);
                top.iter().all(|y| *y == x || o.contains(y))
            }) {
                return (x, Vec::new());
            }
        }
        let winner = top.first().copied().unwrap_or(level[0].1);
        (winner, top.into_iter().skip(1).collect())
    }

    /// Whether candidate `x` (its index and method) is chosen over `y`
    /// at the same literal level: it is more specific; or, as specific,
    /// its block takes as many parameters as the call's (`block_arity`),
    /// or else the fewest more than it,
    /// or it is an extension's method in scope beside the class's own, or
    /// it comes first from another owner (an override, a subclass's) —
    /// except between the modules of two active extensions of the same
    /// target (`ext_src`, `World::resolution_sources`), which tie: the
    /// override table decides, else the call is ambiguous (#577).
    fn beats(
        &self,
        x: (usize, MethodId),
        y: (usize, MethodId),
        cands: &[(MethodId, HashMap<TypeParamId, Type>)],
        block_arity: Option<usize>,
        ext_src: &[(ClassId, ExtensionId)],
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
            (Some((_, Type::Proc(_, ps, _, _, _))), Some(n)) if ps.len() == n => Some(0),
            (Some((_, Type::Proc(_, ps, _, _, _))), Some(n)) if ps.len() > n => Some(ps.len()),
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
        // (Two files' top-level `def`s are one set: neither comes first.)
        let main = |c: ClassId| self.world.class(c).kind == ClassKind::Main;
        // (Two active extensions' modules: no order; a body over an
        // abstract declaration, a requirement and not an implementation,
        // #522; two declarations, the first, either being no body.)
        if self.extension_rivals(x.1, y.1, ext_src).is_some() {
            return match (a.is_abstract, b.is_abstract) {
                (false, true) => true,
                (true, true) => x.0 < y.0,
                _ => false,
            };
        }
        a.owner != b.owner && !(main(a.owner) && main(b.owner)) && x.0 < y.0
    }

    /// The modules of `recv`'s static order that an active scoped or
    /// conditional extension brought, with that extension
    /// (`World::resolution_sources`), on both sides.
    fn extension_sources(&self, recv: &Type) -> Vec<(ClassId, ExtensionId)> {
        match recv {
            Type::Class(id, args) | Type::ClassObject(id, args) => self
                .world
                .resolution_sources(*id, args)
                .into_iter()
                .filter_map(|(k, _, e)| e.map(|e| (k, e)))
                .collect(),
            // (A class object of a type parameter, `Type[T]`: its bounds'.)
            Type::TypeOf(t) => self.extension_sources(t),
            // (A type parameter's: its bounds', as its lookup is.)
            Type::Param(p) => self
                .world
                .param_bounds(*p)
                .iter()
                .flat_map(|b| self.extension_sources(b))
                .collect(),
            _ => Vec::new(),
        }
    }

    /// Whether methods `a` and `b` belong to modules two different active
    /// extensions of the same target brought (`ext_src`): those
    /// extensions, which no order separates (#577).
    fn extension_rivals(
        &self,
        a: MethodId,
        b: MethodId,
        ext_src: &[(ClassId, ExtensionId)],
    ) -> Option<(ExtensionId, ExtensionId)> {
        let of = |m: MethodId| {
            let owner = self.world.method(m).owner;
            ext_src.iter().find(|(k, _)| *k == owner).map(|(_, e)| *e)
        };
        let (ea, eb) = (of(a)?, of(b)?);
        let target = |e: ExtensionId| self.world.extensions[e as usize].target;
        (ea != eb && target(ea) == target(eb)).then_some((ea, eb))
    }

    /// The error for a call that two active extensions' modules both answer
    /// (#577), naming the extensions and the modules: "includes" a module
    /// one of its includes is, "brings" one that comes through them.
    fn extension_ambiguity(
        &mut self,
        name: &str,
        a: MethodId,
        b: MethodId,
        ea: ExtensionId,
        eb: ExtensionId,
        span: Span,
    ) {
        let msg = self.extension_ambiguity_message(name, a, b, ea, eb);
        self.extension_ambiguities += 1;
        self.table_journal.push(TableUndo::ExtensionAmbiguity);
        self.error(msg, span);
    }

    /// `extension_ambiguity`'s message.
    fn extension_ambiguity_message(
        &self,
        name: &str,
        a: MethodId,
        b: MethodId,
        ea: ExtensionId,
        eb: ExtensionId,
    ) -> String {
        let part = |c: &Self, m: MethodId, e: ExtensionId| {
            let owner = c.world.method(m).owner;
            let direct = c.world.extensions[e as usize]
                .includes
                .iter()
                .any(|t| matches!(t, Type::Class(k, _) if *k == owner));
            let verb = if direct { "includes" } else { "brings" };
            (verb, c.world.class(owner).name.clone())
        };
        let ((va, ma), (vb, mb)) = (part(self, a, ea), part(self, b, eb));
        let (na, nb) = (self.extension_name(ea), self.extension_name(eb));
        // (Two extensions in one module have the same name.)
        let who = if na == nb {
            format!(
                "two {}: one {va} `{ma}`, the other {vb} `{mb}`",
                na.replacen("the extension", "extensions", 1).replacen(
                    "the top-level extension",
                    "top-level extensions",
                    1
                )
            )
        } else {
            format!("{na} {va} `{ma}` and {nb} {vb} `{mb}`")
        };
        format!(
            "the call of `{name}` is ambiguous: {who}, both active here, and each gives `{name}` (neither overrides the other); pass the value where one module's type is expected (a parameter typed `{ma}`), or leave out one `using`"
        )
    }

    /// Of `cands`, those `&:name` can call (`symbol_callable`), each
    /// tried and undone.
    fn symbol_callable_cands(
        &mut self,
        cands: &[(MethodId, HashMap<TypeParamId, Type>)],
        name: &str,
    ) -> Vec<(MethodId, HashMap<TypeParamId, Type>)> {
        cands
            .iter()
            .filter(|(k, ks)| {
                let saved = self.infer.save();
                let ok = self.symbol_callable(*k, ks, name).is_ok();
                self.infer.restore(saved);
                ok
            })
            .cloned()
            .collect()
    }

    /// For a call found by name (`chosen`, among `cands`, the candidates
    /// that form can call), the method it resolves to when active
    /// extensions' modules give more than one (#577): such a form has no
    /// arguments to choose with, so every candidate a rival active
    /// extension of the same target brought counts; of their bodies (an
    /// abstract declaration gives none, #522), the one overriding all the
    /// others, or else the ambiguous pair and their extensions for
    /// `extension_ambiguity`. `chosen` when no rival gives one.
    fn by_name_choice(
        &self,
        recv: &Type,
        chosen: MethodId,
        cands: &[(MethodId, HashMap<TypeParamId, Type>)],
    ) -> Result<MethodId, (MethodId, MethodId, ExtensionId, ExtensionId)> {
        let src = self.extension_sources(recv);
        if src.is_empty() {
            return Ok(chosen);
        }
        let mut group = vec![chosen];
        for (r, _) in cands {
            if *r != chosen && self.extension_rivals(chosen, *r, &src).is_some() {
                group.push(*r);
            }
        }
        if group.len() == 1 {
            return Ok(chosen);
        }
        let bodies: Vec<MethodId> = group
            .iter()
            .copied()
            .filter(|m| !self.world.method(*m).is_abstract)
            .collect();
        let open: Vec<MethodId> = bodies
            .iter()
            .copied()
            .filter(|t| {
                !bodies
                    .iter()
                    .any(|u| u != t && self.overridden_by(*u).contains(t))
            })
            .collect();
        match open[..] {
            [] => Ok(chosen),
            [only] => Ok(only),
            _ => {
                for (i, x) in open.iter().enumerate() {
                    for y in &open[i + 1..] {
                        if let Some((ea, eb)) = self.extension_rivals(*x, *y, &src) {
                            return Err((*x, *y, ea, eb));
                        }
                    }
                }
                Ok(open[0])
            }
        }
    }

    /// An extension as the user wrote it: "the extension of `C` in `Sc`"
    /// (or "the top-level extension of `C`").
    fn extension_name(&self, e: ExtensionId) -> String {
        let ext = &self.world.extensions[e as usize];
        let target = &self.world.class(ext.target).name;
        match ext.module {
            Some(m) => format!(
                "the extension of `{target}` in `{}`",
                self.world.class(m).name
            ),
            None => format!("the top-level extension of `{target}`"),
        }
    }

    /// The methods `m` overrides: its entry in the override table
    /// (`World::overrides`, what dispatch reads, #536): none for a
    /// top-level function, nor for an extension's method, which the
    /// runtime does not put in place of the class's.
    fn overridden_by(&self, m: MethodId) -> Vec<MethodId> {
        let mm = self.world.method(m);
        if mm.extension.is_some() || self.world.class(mm.owner).kind == ClassKind::Main {
            return Vec::new();
        }
        self.world.overrides(m)
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
    /// Whether the splats of `call` may fill positional parameter `pi`: a
    /// splatted tuple has a known length (`h(*t, b: 2)` with `t: [Int]`
    /// fills `a` only), anything else may fill any position.
    fn splats_may_reach(
        &self,
        call: &Call,
        pre: &HashMap<NodeId, Type>,
        positional: &[usize],
        pi: usize,
    ) -> bool {
        let mut filled = 0usize;
        for a in &call.args {
            match a {
                Arg::Positional(_) => filled += 1,
                Arg::Splat(e) => match pre.get(&e.id).map(|t| self.infer.resolve(t)) {
                    Some(Type::Tuple(ts)) => filled += ts.len(),
                    _ => return true,
                },
                _ => {}
            }
        }
        positional
            .iter()
            .position(|p| *p == pi)
            .is_some_and(|at| at < filled)
    }

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
        } else if !m.type_params.is_empty() {
            let args = m
                .type_params
                .iter()
                .filter_map(|tp| subst.get(&tp.id).map(|t| (tp.id, t.clone())))
                .collect();
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
        // A splat anywhere in the call: what it holds is bound first, by
        // position, whatever its place (docs/01 §9).
        let splat = call.args.iter().find_map(|a| match a {
            Arg::Splat(e) => Some(e),
            _ => None,
        });
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
                    // (Where the method has a `*rest`: without one, a splat
                    // is refused by itself; one given twice is reported so.)
                    if let (Some(pi), Some(s), Some(_)) = (found, splat, rest) {
                        if m.params[pi].kind == ParamKind::Positional
                            && !bound.contains_key(&pi)
                            && self.splats_may_reach(call, pre, &positional, pi)
                        {
                            let shown = match &s.kind {
                                ExprKind::Local(n) => format!("`*{n}`"),
                                _ => "the splat".to_string(),
                            };
                            return Err(
                                if matches!(&expr.kind, ExprKind::Super { args: None, .. }) {
                                    format!(
                                        "this `super` passes `{name}:` by keyword beside {shown}, which may fill that position: pass the arguments explicitly, `{name}` by position"
                                    )
                                } else {
                                    format!(
                                        "`{name}:` names a positional parameter, but {shown} in the call may fill that position; pass it positionally"
                                    )
                                },
                            );
                        }
                    }
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
                let active_len = self.world.active_extensions.get_mut().len();
                for e in m.block_usings.clone() {
                    if !self.world.active_extensions.get_mut().contains(&e) {
                        self.world.active_extensions.get_mut().push(e);
                    }
                }
                // A named `&block` may be kept (an anonymous one is only
                // yielded to; a native that keeps its block names it).
                self.env.next_block_escapes = m.block.as_ref().is_some_and(|(n, _)| n != "&");
                self.env.next_block_elsewhere = (Self::runs_block_in_task(&self.world, m)
                    || (m.name == "timeout" && m.owner == self.world.builtin.task))
                    .then(|| {
                        if m.owner == self.world.builtin.task {
                            format!("Task.{}", m.name)
                        } else {
                            format!("{}#{}", self.world.classes[m.owner as usize].name, m.name)
                        }
                    });
                // A block given to `Meta::ClassDef`'s generating natives
                // becomes a method's body (docs/14 §5).
                // (A class-end hook's block is compile-time code, run
                // with the class, not a generated method's body.)
                self.env.next_block_lifted = m.is_native
                    && m.owner == self.world.builtin.meta_classdef
                    && m.name != "at_class_end";
                self.env.next_block_init = self.env.next_block_lifted && m.name == "def_initialize";
                // (Own only on the `static def`'s own `self`, outside any
                // block run with another receiver: `instance_exec` on
                // another class's `Meta::ClassDef` makes its `self` that.)
                self.env.next_block_foreign = self.env.next_block_lifted
                    && (!self.env.receivers.is_empty()
                        || call
                            .recv
                            .as_ref()
                            .is_some_and(|r| !matches!(r.kind, ExprKind::SelfRef)));
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
                let was = self.out.receiver_blocks.contains(&expr.id);
                self.table_journal
                    .push(TableUndo::ReceiverBlock(expr.id, was));
                if matches!(self.infer.resolve(&resolved), Type::Proc(Some(_), ..)) {
                    self.out.receiver_blocks.insert(expr.id);
                } else {
                    self.out.receiver_blocks.remove(&expr.id);
                }
                self.block_callee = Some(call.name.clone());
                self.check_block_as(expr.id, b, &resolved, is_task);
                if quoted {
                    self.check_quotable_block(b);
                }
                self.env.next_block_lifted = false;
                self.env.next_block_init = false;
                self.world.active_extensions.get_mut().truncate(active_len);
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
                        let Type::Proc(_, params, ret, _, kws) = resolved else {
                            return Err("invalid block type".to_string());
                        };
                        if !kws.is_empty() {
                            let msg = format!(
                                "`&:{name}` passes no keywords, and the block takes `{}`: write the block",
                                kws[0].name
                            );
                            if report {
                                self.error(msg.clone(), e.span);
                            }
                            return Err(msg);
                        }
                        if params.len() != 1 {
                            return Err(format!("`&:{name}` needs a block with one parameter"));
                        }
                        let recv = self.infer.resolve(&params[0]);
                        // (A member two active extensions' modules both give
                        // the method, #577: the ambiguity, by its name.)
                        if matches!(recv, Type::Union(_)) {
                            for m in recv.members() {
                                let all = self.world.lookup_methods(&m, name);
                                // (The callable ones, as `union_symbol`.)
                                let all = self.symbol_callable_cands(&all, name);
                                let Some((first, _)) = all.first().cloned() else {
                                    continue;
                                };
                                if let Err((a, b, ea, eb)) = self.by_name_choice(&m, first, &all) {
                                    let msg = format!(
                                        "{} (in `&:{name}`)",
                                        self.extension_ambiguity_message(name, a, b, ea, eb)
                                    );
                                    if report {
                                        self.extension_ambiguities += 1;
                                        self.table_journal.push(TableUndo::ExtensionAmbiguity);
                                        self.error(msg.clone(), e.span);
                                    }
                                    return Err(msg);
                                }
                            }
                        }
                        let union = self.union_symbol(&recv, name);
                        // (As a call: a `Meta::ClassDef` member and a class
                        // object holding the same value, #491.)
                        if let Some((_, each, _)) = &union {
                            let members: Vec<Type> = each.iter().map(|(t, ..)| t.clone()).collect();
                            let targets: Vec<Option<MethodId>> =
                                each.iter().map(|(_, k, _)| Some(*k)).collect();
                            if let Some((a, b)) = self.classdef_ambiguity(&members, &targets) {
                                let msg = self.classdef_ambiguity_msg(
                                    &format!("&:{name}"),
                                    name,
                                    &recv,
                                    &members[a],
                                    &members[b],
                                );
                                if report {
                                    self.error(msg.clone(), e.span);
                                }
                                return Err(msg);
                            }
                        }
                        let cands = match &union {
                            Some((_, each, _)) => vec![(each[0].1, each[0].2.clone())],
                            None => self.world.lookup_methods(&recv, name),
                        };
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
                        let callable = self.symbol_callable_cands(&cands, name);
                        let (mid, msubst) = match self.by_name_choice(&recv, mid, &callable) {
                            Ok(m) => cands
                                .iter()
                                .find(|(k, _)| *k == m)
                                .cloned()
                                .unwrap_or((mid, msubst)),
                            Err((a, b, ea, eb)) => {
                                let msg = format!(
                                    "{} (in `&:{name}`)",
                                    self.extension_ambiguity_message(name, a, b, ea, eb)
                                );
                                if report {
                                    self.extension_ambiguities += 1;
                                    self.table_journal.push(TableUndo::ExtensionAmbiguity);
                                    self.error(msg.clone(), e.span);
                                }
                                return Err(msg);
                            }
                        };
                        // `deinitialize` runs only at the release (docs/03
                        // §4), `initialize` only from `new` and `super`
                        // (docs/01 §3).
                        if name == "deinitialize" && !self.world.method(mid).singleton {
                            let msg = format!("{DEINITIALIZE_CALLED} (in `&:{name}`)");
                            if report {
                                self.error(msg.clone(), e.span);
                            }
                            return Err(msg);
                        }
                        if name == "initialize" && !self.world.method(mid).singleton {
                            let msg = format!(
                                "`initialize` is called only by `new` and by `super` in `initialize` (in `&:{name}`)"
                            );
                            if report {
                                self.error(msg.clone(), e.span);
                            }
                            return Err(msg);
                        }
                        // As Ruby's `Symbol#to_proc`, only a public method
                        // (each member's own, for class objects of a union).
                        let each = match &union {
                            Some((_, each, _)) => each.clone(),
                            None => vec![(recv.clone(), mid, msubst.clone())],
                        };
                        let visibility = each
                            .iter()
                            .map(|(_, k, _)| self.world.method(*k).visibility)
                            .find(|v| *v != Visibility::Public)
                            .unwrap_or(Visibility::Public);
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
                        // The result: each member's method's (joined, as
                        // the block's), `Self` as a call binds it.
                        let mut r = Type::Nothing;
                        for (member, k, mut ksubst) in each {
                            let this =
                                Self::self_binding(&self.world, self.world.method(k), &member);
                            ksubst.insert(SELF_PARAM, this);
                            let kr = self.world.unvoid(&self.method_ret(k)).subst(&ksubst);
                            r = self.join(&r, &kr);
                        }
                        let mid = union.as_ref().map_or(mid, |(base, ..)| *base);
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
                        let on_class_objects = recv
                            .members()
                            .iter()
                            .all(|m| matches!(m, Type::ClassObject(..) | Type::TypeOf(_)));
                        if on_class_objects {
                            self.symbol_on_class_object.insert(e.id);
                        }
                        // Values of a union: each member with its method, in
                        // the table choosing by the argument's class where
                        // they differ, and in a block (another check of it
                        // may find others), as the block's call notes them.
                        let union_table: Option<Vec<(Type, MethodId)>> = match &union {
                            Some((_, each, differ))
                                if !on_class_objects
                                    && (differ.is_some() || !self.env.blocks.is_empty()) =>
                            {
                                Some(each.iter().map(|(m, k, _)| (m.clone(), *k)).collect())
                            }
                            _ => None,
                        };
                        let union_varied = matches!(union, Some((_, _, Some(_))));
                        // (A compile-time-only method is any member's.)
                        let union_methods: Vec<MethodId> = match &union {
                            Some((_, each, _)) => each.iter().map(|(_, k, _)| *k).collect(),
                            None => Vec::new(),
                        };
                        // Checked again with another class method on a class
                        // object, both overriding one: the procedure calls
                        // that one, which runs the receiver's own
                        // (`World::overridden_class_method`).
                        let base = match self.out.block_pass.get(&e.id) {
                            Some(BlockPass::Symbol(_, before, _)) if *before != mid => {
                                self.world.overridden_class_method(&[*before, mid])
                            }
                            _ => None,
                        };
                        let mid = base.unwrap_or(mid);
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
                            if before != mid
                                && base.is_none()
                                && !self.out.varied_symbols.contains(&e.id)
                            {
                                self.out.varied_symbols.insert(e.id);
                                self.table_journal.push(TableUndo::VariedSymbol(e.id));
                            }
                            // (On every check that finds another method, not
                            // only the first: the class object, or the
                            // extension's method, may come later.)
                            if before != mid
                                && base.is_none()
                                && self.out.varied_symbols.contains(&e.id)
                            {
                                let ext = |m: MethodId| self.world.method(m).extension.is_some();
                                // Both checks in the table (`union_calls`), the
                                // procedure chooses by its argument's class,
                                // which reaches an extension's method too;
                                // otherwise it goes by name, which does not.
                                let tabled = (!self.env.blocks.is_empty()
                                    && self.union_testable(&recv)
                                    && self.out.union_calls.contains_key(&e.id))
                                    || union_table.is_some();
                                // A class object's methods (its class's, or an
                                // included module's) are never found by name
                                // on it (no class test tells class objects
                                // apart either): as the block `{ |c| c.name }`
                                // on them is.
                                let class_methods = self.symbol_on_class_object.contains(&e.id);
                                if (ext(before) || ext(mid) || class_methods) && !tabled {
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
                        // Checked once per type (a block's), the procedure
                        // chooses by its argument's class at run time.
                        // The members' methods differ (not class objects):
                        // chosen by the argument's class, as the block's
                        // call on the union is.
                        // (Not one method, so not called, nor lowered in
                        // place, as one: `varied_symbols`.)
                        if let Some(table) = union_table {
                            self.note_union_table(e.id, table, e.span);
                            if union_varied && self.out.varied_symbols.insert(e.id) {
                                self.table_journal.push(TableUndo::VariedSymbol(e.id));
                            }
                        } else if !self.env.blocks.is_empty() && self.union_testable(&recv) {
                            self.note_union_table(e.id, vec![(recv.clone(), mid)], e.span);
                        }
                        // (Class objects: what each member found, which no
                        // table records.)
                        if on_class_objects && union_methods.len() > 1 {
                            self.note_union_methods(e.id, union_methods.clone());
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
                        for k in union_methods {
                            if k != mid {
                                self.note_static_call(e, k);
                            }
                        }
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
                        // A procedure that would fit if it were `shareable`,
                        // for a method running its block in a task: why,
                        // and what to pass (the call is typed as it is).
                        if let Type::Proc(precv, pparams, pret, false, pkws) = self.resolve(&t) {
                            let as_shareable = Type::Proc(precv, pparams, pret, true, pkws);
                            if Self::runs_block_in_task(&self.world, m)
                                && matches!(self.resolve(&block_ty), Type::Proc(_, _, _, true, _))
                                && self.coerce(&as_shareable, &block_ty)
                            {
                                if report {
                                    let wanted = self.name(&self.resolve(&as_shareable));
                                    let callee = if m.owner == self.world.builtin.task {
                                        format!("Task.{}", m.name)
                                    } else {
                                        format!("{}#{}", self.world.class(m.owner).name, m.name)
                                    };
                                    self.error(
                                        format!(
                                            "`{callee}` runs the block in a task: pass a `{wanted}`, whose captures are Shareable (declare it: `f: {wanted} = -> {{ ... }}`)"
                                        ),
                                        e.span,
                                    );
                                }
                                self.out.block_pass.insert(expr.id, BlockPass::Proc);
                                return Ok(ret);
                            }
                        }
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
                        // Its result passes to the task that awaits it, as
                        // a task block's does: Shareable.
                        if Self::runs_block_in_task(&self.world, m) && report {
                            if let Type::Proc(_, _, pret, _, _) = self.resolve(&t) {
                                let pret = self.resolve(&pret);
                                if !pret.has_vars()
                                    && pret != Type::Void
                                    && !self.world.is_shareable(&pret)
                                {
                                    self.error(
                                        format!(
                                            "a procedure run in a task returns the non-shareable type {}, but its value passes to the task that awaits it",
                                            self.world.type_name(&pret)
                                        ),
                                        e.span,
                                    );
                                }
                            }
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
        if let Err(why) = self.static_stage(&m) {
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
            // (A function, docs/01 §2: no receiver.)
            None if m.singleton || self.world.class(m.owner).kind == ClassKind::Main => {}
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
        if let Some(why) = self.bake_refusal(&rt) {
            let why = if why.is_empty() {
                String::new()
            } else {
                format!(" ({why})")
            };
            self.error(
                format!("`static(...)` gives a {}, which cannot be baked into the program{why}: its value must be a literal, a class or `data` of Shareable fields (docs/14 §5)", self.world.type_name(&rt)),
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

    /// The staging rule of `static` statements (docs/14 §2): whether the
    /// code being checked may run `m` at compile time, compiled before it
    /// (a method of the cogs or required files it depends on), or else
    /// whose `m` is ("this file", "this cog", "this input", ...).
    fn static_stage(&self, m: &MethodInfo) -> Result<(), String> {
        match self.repl_unit {
            Some((file, base)) => {
                if m.file == file && m.span.start >= base {
                    Err("this input".to_string())
                } else {
                    Ok(())
                }
            }
            None => self.world.static_callee_allowed(self.env.file, m.file),
        }
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

    /// `&:name` on a union (`A | B`, `Type[A] | Type[B]`), as the block
    /// `{ |x| x.name }` calls it: each member's own method (the first
    /// callable one, as for one type), whose results and visibility the
    /// block's go by. One method for every member is called; class objects
    /// call the class method (or extended module method) each member's own
    /// overrides (`World::class_object_base`); other members' methods are
    /// chosen by the argument's class, as the block's call is
    /// (`note_union_table`). `None` for any other receiver, or a member
    /// without the method.
    fn union_symbol(&mut self, recv: &Type, name: &str) -> Option<UnionSymbol> {
        let members = recv.members();
        if members.len() < 2 || members.iter().any(|m| matches!(m, Type::Var(_))) {
            return None;
        }
        let mut table = Vec::new();
        let mut substs = Vec::new();
        for m in &members {
            // (The first callable one, as for one class object; between two
            // active extensions' modules, the one overriding the other, #577.)
            let all = self.world.lookup_methods(m, name);
            let all = self.symbol_callable_cands(&all, name);
            let first = all.first().cloned()?;
            let found = match self.by_name_choice(m, first.0, &all) {
                Ok(k) => all.iter().find(|(x, _)| *x == k).cloned().unwrap_or(first),
                Err(_) => return None,
            };
            table.push((m.clone(), found.0));
            substs.push(found);
        }
        // (One method for every member: that one.)
        let class_objects = members.iter().all(|m| matches!(m, Type::ClassObject(..)));
        let (base, table) = if table.iter().all(|(_, k)| *k == table[0].1) {
            (table[0].1, None)
        } else if class_objects {
            (self.world.class_object_base(&table)?, None)
        } else {
            (table[0].1, Some(table))
        };
        let each = members
            .into_iter()
            .zip(substs)
            .map(|(m, (k, ks))| (m, k, ks))
            .collect();
        Some((base, each, table))
    }

    /// What a block or a lambda runs, for the scans of what it assigns:
    /// its keyword parameters' defaults, then its body.
    fn closure_code(block: &Block) -> std::borrow::Cow<'_, [Expr]> {
        let defaults: Vec<&Expr> = block
            .params
            .list
            .iter()
            .filter_map(|p| p.default.as_ref())
            .collect();
        if defaults.is_empty() {
            std::borrow::Cow::Borrowed(&block.body)
        } else {
            std::borrow::Cow::Owned(
                defaults
                    .into_iter()
                    .chain(block.body.iter())
                    .cloned()
                    .collect(),
            )
        }
    }

    /// Check a block against the procedure type it is passed as.
    fn check_block(&mut self, call_id: NodeId, block: &Block, proc_ty: &Type) {
        self.check_block_as(call_id, block, proc_ty, false)
    }

    fn check_block_as(&mut self, call_id: NodeId, block: &Block, proc_ty: &Type, is_task: bool) {
        let callee = self.block_callee.take();
        let Type::Proc(recv, params, ret, shareable0, kws) = proc_ty else {
            self.error("internal: block type is not a procedure", block.span);
            return;
        };
        let shareable = *shareable0 && !is_task;
        if shareable {
            self.out.shareable_procs.insert(call_id);
        }
        let lifted = std::mem::take(&mut self.env.next_block_lifted);
        let init = std::mem::take(&mut self.env.next_block_init) && lifted;
        let foreign = std::mem::take(&mut self.env.next_block_foreign);
        let lifted_before = lifted.then(|| self.out.lifted_blocks.get(&call_id).cloned());
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
        // A block lifted to a generated method (docs/14 §5): its `self` is
        // the method's, of the class generated into or a subclass, so it
        // is the opaque `Self` (bounded by the block's receiver type), and
        // a `Self` written in it (its declared types included) means that
        // class, which the generated signature substitutes. On the class
        // side, as in a class method, `self` is the class, whose `new`
        // gives a `Self`.
        let mut saved_lifted_self = None;
        let mut lifted_instance_side = false;
        if let (true, Some(r)) = (lifted, recv.as_ref()) {
            let r = self.resolve(r);
            let (class_side, instance) = match &r {
                Type::ClassObject(c, args) => (true, Type::Class(*c, args.clone())),
                Type::TypeOf(t) => (true, (**t).clone()),
                t => (false, t.clone()),
            };
            lifted_instance_side = !class_side;
            // (`Self` itself, a module macro's: bounded as it is.)
            let instance = match instance {
                Type::Param(SELF_PARAM) => self
                    .world
                    .self_bound
                    .clone()
                    .unwrap_or(Type::Param(SELF_PARAM)),
                t => t,
            };
            saved_lifted_self = Some((
                self.world.self_bound.replace(instance),
                self.env.scope.self_type.take(),
                std::mem::replace(&mut self.env.self_opaque, true),
                std::mem::replace(&mut self.env.self_is_self, !class_side),
            ));
        }
        let params = params.clone();
        // `do |x| -> T ... end`: the block's result is `T`, as a `def`'s
        // return type is (checked and used; `-> Void` discards the body's
        // value), and it must fit the callee's (an expected `Void` takes
        // any).
        let expected_ret = (**ret).clone();
        let ret = match &block.ret {
            Some(te) => {
                let scope = self.env.scope.clone();
                let declared = self
                    .resolve_result_type_expr(te, &scope)
                    .unwrap_or(Type::Nothing);
                let expected_void = self.infer.resolve(&expected_ret) == Type::Void;
                if !expected_void && !self.coerce(&declared, &expected_ret) {
                    let expected_proc = Type::Proc(
                        recv.clone(),
                        params.clone(),
                        Box::new(expected_ret.clone()),
                        shareable,
                        kws.clone(),
                    );
                    self.error(
                        format!(
                            "the block is declared `-> {}` but {} expects {}",
                            self.name(&declared),
                            callee
                                .as_deref()
                                .map_or("the method".to_string(), |c| format!("`{c}`")),
                            self.name(&expected_proc)
                        ),
                        te.span,
                    );
                }
                // (A block checked more than once: what any check saw.)
                let seen = match self.out.block_results.get(&call_id).cloned() {
                    Some(old) if old != declared => self.join(&old, &declared),
                    _ => declared.clone(),
                };
                self.out.block_results.insert(call_id, seen);
                if lifted {
                    self.out.lifted_blocks.insert(
                        call_id,
                        Type::Proc(
                            recv.clone(),
                            params.clone(),
                            Box::new(declared.clone()),
                            *shareable0,
                            kws.clone(),
                        ),
                    );
                }
                declared
            }
            None => expected_ret,
        };
        let code = Self::closure_code(block);
        self.widen_assigned(&code);
        self.prescan_repeated(code.iter(), true);
        // A block the method may keep may run later, as a lambda may.
        let escapes = std::mem::take(&mut self.env.next_block_escapes);
        let elsewhere = std::mem::take(&mut self.env.next_block_elsewhere);
        let late = (escapes && !shareable && !is_task).then(|| self.enter_late_closure(&code));
        // A task's block copies the locals it captures, but reads `self`'s
        // fields live, as their declared types (as a late closure does).
        let saved_ivars =
            (late.is_none() && (is_task || shareable) && !self.fields_fixed_at_construction())
                .then(|| std::mem::take(&mut self.env.ivar_narrow));
        // A block with a receiver runs with `self` = the receiver: the
        // enclosing `self` stays reachable for calls it alone answers.
        let receiver = recv.as_ref().map(|t| self.resolve(t));
        let receiver = if lifted_instance_side {
            Some(Type::Param(SELF_PARAM))
        } else {
            receiver
        };
        let saved_self = self.enter_receiver(receiver.as_ref());
        // A block given to `def_initialize` (docs/14 §5) is an
        // `initialize`'s body: it assigns the fields of the class it is
        // bounded by (those it can name), under `initialize`'s rules.
        let init_bound = if init {
            // (A type parameter's class bound: `T` of `module Gen[T <:
            // Model]`'s `static def`.)
            let mut bound = self.world.self_bound.clone();
            let mut seen = 0;
            while let Some(Type::Param(p)) = &bound {
                seen += 1;
                bound = if seen > 16 {
                    None
                } else {
                    self.world
                        .param_bounds(*p)
                        .into_iter()
                        .find(|b| matches!(b, Type::Class(..) | Type::Param(_)))
                };
            }
            match &bound {
                Some(Type::Class(id, _)) => Some(*id),
                _ => {
                    self.error(
                        "`def_initialize` generates into a class: its `Meta::ClassDef`'s type must be one",
                        block.span,
                    );
                    None
                }
            }
        } else {
            None
        };
        let saved_assigned = init_bound.map(|_| {
            self.env.in_initialize = true;
            std::mem::take(&mut self.env.assigned_fields)
        });
        if let Some(bound) = init_bound {
            self.out.init_blocks.insert(call_id, bound);
        }
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
        let saved_lifted = (
            self.env.lifted_frame,
            self.env.is_static,
            self.env.lifted_foreign,
        );
        if lifted {
            self.env.lifted_frame = Some(self.env.frames.len() - 1);
            self.env.is_static = false;
            self.env.lifted_foreign = foreign;
        }
        self.env.blocks.push(BlockCtx {
            ret: ret.clone(),
            breaks: Vec::new(),
            is_lambda: false,
            // A task's block runs elsewhere, later: the method's block may
            // not be live there either.
            escapes: escapes || is_task || shareable || lifted,
            lifted,
            init,
            static_call: in_static,
            task: elsewhere.or_else(|| is_task.then(|| "the task's method".to_string())),
            shareable,
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
            .filter(|p| !matches!(p.kind, ParamKind::Block | ParamKind::KeywordOnly))
            .collect();
        let mut param_types: Vec<Type> = params.clone();
        // (Destructuring an array: the binder pads a shorter element with
        // `nil`, so each parameter's type must admit it, #531.)
        let mut padded: Option<Type> = None;
        if declared.len() > 1 && params.len() == 1 {
            match self.infer.resolve(&params[0]) {
                Type::Tuple(ts) => {
                    // (A tuple only into its arity: a parameter past it
                    // would get `nil`; a `*rest` takes what is left.)
                    let rest = declared.iter().any(|p| p.kind == ParamKind::Rest);
                    let fixed = declared.len() - usize::from(rest);
                    if !rest && fixed < ts.len() {
                        self.error(
                            format!(
                                "block destructures a {}-element tuple into {} parameters: name each element (`|{}|`), or take the tuple as one parameter",
                                ts.len(),
                                fixed,
                                (0..ts.len())
                                    .map(|i| ((b'a' + (i % 26) as u8) as char).to_string())
                                    .collect::<Vec<_>>()
                                    .join(", ")
                            ),
                            block.span,
                        );
                    }
                    // (A `*rest` takes the elements past the parameters
                    // before it, as an array of them: `tuple_element`, the
                    // one rule for a tuple's elements as an array's.)
                    if let Some(at) = declared.iter().position(|p| p.kind == ParamKind::Rest) {
                        if at < ts.len() {
                            let left = self.world.tuple_element(&ts[at..]);
                            let mut ts = ts;
                            ts.truncate(at);
                            ts.push(left);
                            param_types = ts;
                        } else {
                            param_types = ts;
                        }
                    } else {
                        param_types = ts;
                    }
                    self.out.block_destructure.insert(call_id, declared.len());
                }
                // An array is spread over the parameters, as in Ruby: each
                // may get `nil` where the element is shorter.
                Type::Class(id, args) if id == self.world.builtin.array && args.len() == 1 => {
                    let t = self.world.nilable(args[0].clone());
                    padded = Some(args[0].clone());
                    param_types = vec![t; declared.len()];
                    self.out.block_destructure.insert(call_id, declared.len());
                }
                _ => {}
            }
        }
        // `it` (docs/01 §9): the argument of a one-parameter block.
        let implicit = declared.first().filter(|p| p.implicit).map(|p| p.span);
        if let Some(span) = implicit.filter(|_| params.len() != 1) {
            let takes = match params.len() {
                0 => "none".to_string(),
                n => format!(
                    "{n}: write `|{}|`",
                    (0..n)
                        .map(|i| ((b'a' + (i % 26) as u8) as char).to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
            };
            self.error(
                format!("`it` is the single argument of a one-parameter block; this block takes {takes}"),
                span,
            );
        } else if declared.len() > param_types.len() {
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
            // (A `*rest` takes the elements there are: no `nil` padding.)
            if let Some(elem) = padded.as_ref().filter(|_| p.kind == ParamKind::Rest) {
                t = elem.clone();
            }
            if let Some(te) = &p.ty {
                let scope = self.env.scope.clone();
                if let Some(annotated) = self.resolve_type_expr(te, &scope) {
                    // (An array element destructured: the parameter may get
                    // `nil`, #531; the error names the fix.)
                    if let Some(elem) = padded.as_ref().filter(|_| p.kind != ParamKind::Rest) {
                        if !self.world.is_subtype(&self.world.nil(), &annotated) {
                            let elem = self.name(elem);
                            self.error(
                                format!(
                                    "block destructures an Array[{elem}] element into {} parameters: an element may be shorter, so each gets `nil` where it has no value; type them to admit it (`|{}: {}?, ...|`), or take the element as one parameter",
                                    declared.len(),
                                    p.name,
                                    self.name(&annotated)
                                ),
                                te.span,
                            );
                            self.declare_var(&p.name, annotated, p.span);
                            continue;
                        }
                    }
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
        let kws = kws.clone();
        self.check_block_keywords(block, &kws, callee.as_deref());
        let void = self.infer.resolve(&ret) == Type::Void;
        self.next_body_void = void;
        let bt = self.check_body(&block.body, if void { None } else { Some(&ret) });
        self.mark_discarded(block.body.last(), void);
        if let Some(bound) = init_bound {
            self.check_init_block(call_id, block, bound);
        }
        if let Some(saved) = saved_assigned {
            self.env.assigned_fields = saved;
        }
        // A task's result reaches the task that awaits it: the declared
        // result, when there is one (a `next` may give any of it).
        // Without one, what the body ends with and what a `next` gave (the
        // result variable it was coerced to): when the body ends in
        // `raise`, a `next` value is all that passes.
        let joined;
        let result = if block.ret.is_some() {
            &ret
        } else {
            let r = self.resolve(&ret);
            if matches!(r, Type::Var(_)) {
                &bt
            } else {
                joined = self.join(&bt, &r);
                &joined
            }
        };
        if is_task && !void && !result.is_nothing() {
            let rt = self.resolve(result);
            // A literal the block ends with is held by no variable: its
            // undecided element types are decided as `Nothing` (nothing can
            // add to it later).
            let rt = if rt.has_vars() && {
                let mut vs = Vec::new();
                Self::vars_in(&rt, &mut vs);
                vs.iter().all(|v| self.literal_vars.contains(v))
            } {
                self.decide_as_nothing(&rt);
                self.resolve(&rt)
            } else {
                rt
            };
            if rt.has_vars() {
                if self.world.refuse_undecided() {
                    let span = block.body.last().map(|e| e.span).unwrap_or(block.span);
                    self.error(
                        "the type of a task block's result is not yet known here, but it passes to the task that awaits it and must be Shareable: annotate what the block returns",
                        span,
                    );
                }
            } else if !self.world.is_shareable(&rt) {
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
            let message = if block.ret.is_some() {
                format!(
                    "block returns {} but is declared `-> {}`",
                    self.name(&bt),
                    self.name(&ret)
                )
            } else {
                format!(
                    "block returns {} but {} was expected",
                    self.name(&bt),
                    self.name(&ret)
                )
            };
            self.error(message, span);
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
        (
            self.env.lifted_frame,
            self.env.is_static,
            self.env.lifted_foreign,
        ) = saved_lifted;
        self.leave_receiver(saved_self);
        if let Some((bound, scope_self, opaque, is_self)) = saved_lifted_self {
            self.world.self_bound = bound;
            self.env.scope.self_type = scope_self;
            self.env.self_opaque = opaque;
            self.env.self_is_self = is_self;
        }
        self.out
            .frame_sizes
            .insert(call_id, frame.vars.len() as u32);
        if let Some(ivars) = saved_ivars {
            self.env.ivar_narrow = ivars;
        }
        match late {
            Some(snap) => self.leave_late_closure(&snap, &code),
            None => self.widen_assigned(&code),
        }
        if let (Some(before), Some(now)) = (lifted_before, self.out.lifted_blocks.get(&call_id)) {
            let now = now.clone();
            let seen = self.lifted_seen.entry(call_id).or_insert_with(|| {
                let callee = callee
                    .as_deref()
                    .map_or("the method".to_string(), |c| format!("`{c}`"));
                (Vec::new(), block.span, callee)
            });
            seen.0.push(now);
            self.table_journal.push(TableUndo::Lifted(call_id, before));
        }
    }

    /// A block's keyword-only parameters, against the keywords of the
    /// procedure type it is given for (docs/02 §9): it declares each
    /// (optional where the type's is), and any other has a default.
    /// Declares them, typed by their annotation, else the type's, else
    /// their default's.
    fn check_block_keywords(&mut self, block: &Block, kws: &[ProcKw], callee: Option<&str>) {
        let callee = callee.map_or("the method".to_string(), |c| format!("`{c}`"));
        let own: Vec<&Param> = block
            .params
            .list
            .iter()
            .filter(|p| p.kind == ParamKind::KeywordOnly)
            .collect();
        for k in kws {
            match own.iter().find(|p| p.name == k.name) {
                None => self.error(
                    format!(
                        "{callee} passes the block the keyword `{}`: declare it (`|..., *, {}: {}|`)",
                        k.name,
                        k.name,
                        self.name(&k.ty)
                    ),
                    block.span,
                ),
                Some(p) if p.default.is_none() && !k.required => self.error(
                    format!(
                        "the keyword `{}` is optional for {callee}: give it a default",
                        k.name
                    ),
                    p.span,
                ),
                Some(_) => {}
            }
        }
        for p in own {
            let expected = kws.iter().find(|k| k.name == p.name).map(|k| k.ty.clone());
            if expected.is_none() && p.default.is_none() {
                self.error(
                    format!(
                        "the block requires the keyword `{}`, which {callee} does not pass: give it a default, or leave it out",
                        p.name
                    ),
                    p.span,
                );
            }
            self.declare_keyword_param(p, expected.as_ref(), "block");
        }
    }

    /// Declare a block's or a lambda's keyword-only parameter `p`, typed
    /// by its annotation (which must take `expected`, the type a caller
    /// passes), else `expected`, else its default's type; its default is
    /// checked against that type.
    fn declare_keyword_param(&mut self, p: &Param, expected: Option<&Type>, what: &str) -> Type {
        let annotated = p.ty.as_ref().and_then(|te| {
            let scope = self.env.scope.clone();
            self.resolve_type_expr(te, &scope)
        });
        if let (Some(a), Some(e), Some(te)) = (&annotated, expected, &p.ty) {
            if !self.coerce(e, a) {
                self.error(
                    format!(
                        "{what} keyword `{}` is annotated {} but receives {}",
                        p.name,
                        self.name(a),
                        self.name(e)
                    ),
                    te.span,
                );
            }
        }
        let mut t = annotated.or_else(|| expected.cloned());
        if let Some(d) = &p.default {
            let dt = self.check_expr(d, t.as_ref());
            match &t {
                Some(t) => {
                    if !self.coerce(&dt, t) {
                        self.error(
                            format!(
                                "the default of keyword `{}` is {}, not {}",
                                p.name,
                                self.name(&dt),
                                self.name(t)
                            ),
                            d.span,
                        );
                    }
                }
                None => t = Some(self.resolve(&dt)),
            }
        }
        let t = t.unwrap_or_else(|| {
            self.error(format!("{what} keyword `{}` needs a type", p.name), p.span);
            Type::Nothing
        });
        self.declare_var(&p.name, t.clone(), p.span);
        t
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
            // (A lifted block's `self`, docs/14 §5: the class it is
            // bounded by, whose fields and protected methods it reaches as
            // a method does.)
            Type::Param(SELF_PARAM) => match &self.world.self_bound {
                Some(Type::Class(id, _)) => Some(*id),
                _ => None,
            },
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

    /// Whether the code being checked is in the block of a `static(...)`
    /// call, which captures nothing (docs/14 §8).
    /// Inside the block of `static(...)`, with its `self` the code around
    /// it's (no block with a receiver inside it gives another), whatever
    /// task or shareable block inside it the code sits in.
    fn in_static_block(&self) -> bool {
        self.env
            .static_frame
            .is_some_and(|sf| !self.env.receivers.iter().any(|r| r.outer_frame + 1 >= sf))
    }

    /// Whether the code being checked is in a function (a top-level `def`,
    /// docs/01 §2), its parameters' defaults and its blocks and lambdas
    /// included.
    fn in_function(&self) -> bool {
        self.env
            .method
            .is_some_and(|m| self.world.class(self.world.method(m).owner).kind == ClassKind::Main)
    }

    /// Whether `self` here would be a function's, which it has none of:
    /// in a function, outside any block with a receiver.
    fn function_self(&self) -> bool {
        self.env.receivers.is_empty() && self.in_function()
    }

    /// Fields are reachable only from their class's own body: inside a
    /// block with another receiver, `@x` is an error.
    /// Whether `self` here is the `self` of the code around the innermost
    /// `spawn` (or `Task.blocking`) block, captured by it (and not the
    /// receiver of a block run with `instance_exec` inside the task).
    fn self_crosses_task(&self) -> bool {
        match self.env.task_frame {
            // A block with a receiver, at the task block or inside it:
            // its `self` is the receiver given at each call (a shareable
            // `T.() -> R` block's, a block given to `def_method`, the
            // block of `static(...)`'s call when its parameter takes
            // one), not captured. A call that falls through to the
            // enclosing `self` is checked where it binds it
            // (`bind_outer_self`).
            Some(tf) => !self.env.receivers.iter().any(|r| r.outer_frame + 1 >= tf),
            None => false,
        }
    }

    /// A task block captures `self` like a variable: it must be Shareable.
    fn check_task_self(&mut self, what: &str, span: Span) {
        if !self.self_crosses_task() {
            return;
        }
        if self.in_static_block() {
            self.error(
                format!("a block in `static(...)` captures nothing: {what} is not a constant (docs/14 §8)"),
                span,
            );
            return;
        }
        let t = self.resolve(&self.env.self_type.clone());
        if t.has_vars() {
            if !self.world.refuse_undecided() {
                return;
            }
            self.error(
                format!("the type of {what} is not yet known here, but {} must have a Shareable one: annotate it", self.task_capture_name()),
                span,
            );
            return;
        }
        if self.world.is_shareable(&t) {
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
        if self.function_self() {
            self.error(
                "a function has no `self`, so no fields: keep state in an object of a class (a field in its methods), or pass it as an argument",
                span,
            );
            return false;
        }
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
        let (expected_recv, expected_proc, shareable, expected_kws) = match expected_proc_type {
            Some(Type::Proc(rc, ps, r, sh, kws)) => (rc.map(|t| *t), Some((ps, *r)), sh, kws),
            _ => (None, None, false, Box::default()),
        };
        let code = Self::closure_code(block);
        self.widen_assigned(&code);
        self.prescan_repeated(code.iter(), true);
        // A lambda may run later, after what it captures has changed (a
        // shareable one copies what it captures, and assigns none of it).
        let late = (!shareable).then(|| self.enter_late_closure(&code));
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
            init: false,
            static_call: false,
            task: None,
            shareable: false,
        });
        // `break` and `next` here do not leave a loop around the lambda.
        let saved_loop = (
            std::mem::take(&mut self.env.loop_depth),
            std::mem::take(&mut self.env.loop_exits),
        );
        let mut keywords = Vec::new();
        let mut i = 0;
        for p in &block.params.list {
            if p.kind == ParamKind::KeywordOnly {
                let expected = expected_kws
                    .iter()
                    .find(|k| k.name == p.name)
                    .map(|k| k.ty.clone());
                let ty = self.declare_keyword_param(p, expected.as_ref(), "lambda");
                keywords.push(ProcKw {
                    name: p.name.clone(),
                    ty,
                    required: p.default.is_none(),
                });
                continue;
            }
            i += 1;
            let i = i - 1;
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
            self.leave_late_closure(&snap, &code);
        }
        self.out.frame_sizes.insert(id, frame.vars.len() as u32);
        let ret = self.infer.resolve(&ret_var);
        Type::Proc(
            expected_recv.map(Box::new),
            param_types,
            Box::new(ret),
            shareable,
            ProcKw::sorted(keywords),
        )
    }

    fn check_yield(&mut self, expr: &Expr, args: &[Arg]) -> Type {
        // (The method's block, outside the block of `static(...)`.)
        if self.env.static_frame.is_some() {
            self.error(
                "a block in `static(...)` captures nothing: `yield` uses the method's block (docs/14 §8)",
                expr.span,
            );
        }
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
                function: false,
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
                function: false,
                has_parens: true,
                type_args: vec![],
            });
            return Type::Nothing;
        };
        let Type::Proc(recv, params, ret, _, kws) = bt else {
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
                function: false,
                has_parens: true,
                type_args: vec![],
            });
            return Type::Nothing;
        }
        self.check_proc_args(args, &params, &kws, expr.span, true);
        self.world.unvoid(&ret)
    }

    /// `recv.instance_exec(args, k: v, &b)`, with keyword arguments: a
    /// call of the block, with `self` = `recv` (docs/01 §9). A block
    /// passed with `&` takes the arguments as a procedure call does, its
    /// receiver type taking `recv`; a literal block is checked as the
    /// procedure type the arguments make (`Recv.(A, *, k: B) -> R`).
    /// (Without keywords, `instance_exec` is the native.)
    fn check_instance_exec_kw(
        &mut self,
        expr: &Expr,
        call: &Call,
        recv_ty: &Type,
        expected: Option<&Type>,
    ) -> Type {
        let recv_ty = self.resolve(recv_ty);
        let passed = call.args.iter().find_map(|a| match a {
            Arg::BlockPass(e) => Some(e),
            _ => None,
        });
        let args: Vec<Arg> = call
            .args
            .iter()
            .filter(|a| !matches!(a, Arg::BlockPass(_)))
            .cloned()
            .collect();
        let ret = match (&call.block, passed) {
            (None, Some(e)) => {
                let bt = self.check_expr(e, None);
                match self.resolve(&bt) {
                    Type::Proc(Some(r), ps, ret, _, kws) => {
                        if !self.coerce(&recv_ty, &r) {
                            self.error(
                                format!(
                                    "the block runs with a receiver of type {}, not {}",
                                    self.name(&r),
                                    self.name(&recv_ty)
                                ),
                                e.span,
                            );
                        }
                        self.check_proc_args(&args, &ps, &kws, expr.span, false);
                        self.world.unvoid(&ret)
                    }
                    t => {
                        self.error(
                            format!(
                                "`instance_exec` with keywords runs a block with a receiver (`Recv.(*, k: T) -> R`), not {}",
                                self.name(&t)
                            ),
                            e.span,
                        );
                        self.check_args_blindly(call);
                        Type::Nothing
                    }
                }
            }
            (Some(b), None) => {
                let mut params = Vec::new();
                let mut kws: Vec<ProcKw> = Vec::new();
                for a in &args {
                    match a {
                        Arg::Positional(e) => {
                            let t = self.check_expr(e, None);
                            params.push(self.resolve(&t));
                        }
                        Arg::Keyword { name, value, span } => {
                            let t = self.check_expr(value, None);
                            if kws.iter().any(|k| k.name == *name) {
                                self.error(format!("keyword `{name}` is given twice"), *span);
                                continue;
                            }
                            kws.push(ProcKw {
                                name: name.clone(),
                                ty: self.resolve(&t),
                                required: true,
                            });
                        }
                        Arg::Splat(e) | Arg::DoubleSplat(e) | Arg::BlockPass(e) => {
                            self.error(
                                "`instance_exec` with keywords takes plain arguments (no `*` or `**`)",
                                e.span,
                            );
                            self.check_expr(e, None);
                        }
                    }
                }
                // (The expected type, where there is one, as for a
                // method's result `R`.)
                let fresh = match expected {
                    Some(e) if !self.resolve(e).has_vars() => self.resolve(e),
                    _ => self.infer.fresh(),
                };
                let proc_ty = Type::Proc(
                    Some(Box::new(recv_ty.clone())),
                    params,
                    Box::new(fresh.clone()),
                    false,
                    ProcKw::sorted(kws),
                );
                self.block_callee = Some("instance_exec".to_string());
                self.check_block(expr.id, b, &proc_ty);
                // What a `break` gives is the call's value too; a body
                // that only leaves (`return`, `raise`) gives `Nothing`.
                let broken = self.breaking_blocks.get(&expr.id).cloned();
                let r = match (self.resolve(&fresh), broken) {
                    (Type::Var(_), b) => {
                        let t = b.unwrap_or(Type::Nothing);
                        self.coerce(&fresh, &t);
                        t
                    }
                    (r, Some(b)) => self.join(&r, &b),
                    (r, None) => r,
                };
                self.world.unvoid(&r)
            }
            _ => {
                self.error("`instance_exec` runs one block", expr.span);
                self.check_args_blindly(call);
                Type::Nothing
            }
        };
        self.out.calls.insert(expr.id, CallTarget::InstanceExec);
        ret
    }

    /// The arguments of a call of a procedure (`p.call(...)`, `p.(...)`,
    /// `p[...]`) or of `yield` (`yielding`): positional ones by place,
    /// keyword ones by name, each required keyword once, no other
    /// (docs/02 §9).
    fn check_proc_args(
        &mut self,
        args: &[Arg],
        params: &[Type],
        kws: &[ProcKw],
        span: Span,
        yielding: bool,
    ) {
        let positional: Vec<&Expr> = args
            .iter()
            .filter_map(|a| match a {
                Arg::Positional(e) => Some(e),
                _ => None,
            })
            .collect();
        let other = args
            .iter()
            .any(|a| !matches!(a, Arg::Positional(_) | Arg::Keyword { .. }));
        let blindly = |this: &mut Self| {
            for a in args {
                match a {
                    Arg::Positional(e)
                    | Arg::Splat(e)
                    | Arg::DoubleSplat(e)
                    | Arg::BlockPass(e)
                    | Arg::Keyword { value: e, .. } => {
                        this.check_expr(e, None);
                    }
                }
            }
        };
        if positional.len() != params.len() || other {
            if let Some(a) = args.iter().find(|a| matches!(a, Arg::DoubleSplat(_))) {
                self.error(
                    "a procedure takes no `**hash`: its type names each keyword, passed by name",
                    a.span(),
                );
                blindly(self);
                return;
            }
            let given = args
                .iter()
                .filter(|a| !matches!(a, Arg::Keyword { .. }))
                .count();
            let message = if yielding {
                format!(
                    "the block takes {} argument(s), `yield` passes {given}",
                    params.len()
                )
            } else {
                format!(
                    "procedure takes {} argument(s), {given} given",
                    params.len()
                )
            };
            self.error(message, span);
            blindly(self);
            return;
        }
        for (e, p) in positional.iter().zip(params.iter()) {
            let t = self.check_expr(e, Some(p));
            if !self.coerce(&t, p) {
                let message = if yielding {
                    format!(
                        "`yield` passes {} where the block expects {}",
                        self.name(&t),
                        self.name(p)
                    )
                } else {
                    format!("expected {} but found {}", self.name(p), self.name(&t))
                };
                self.error(message, e.span);
            }
        }
        let mut given: Vec<&str> = Vec::new();
        for a in args {
            let Arg::Keyword {
                name,
                value,
                span: kspan,
            } = a
            else {
                continue;
            };
            let Some(k) = kws.iter().find(|k| k.name == *name) else {
                let takes = if kws.is_empty() {
                    "it takes none".to_string()
                } else {
                    format!(
                        "it takes {}",
                        kws.iter()
                            .map(|k| format!("`{}`", k.name))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                };
                let whose = if yielding {
                    "the block"
                } else {
                    "the procedure"
                };
                self.error(
                    format!("unknown keyword `{name}` for {whose}: {takes}"),
                    *kspan,
                );
                self.check_expr(value, None);
                continue;
            };
            if given.contains(&name.as_str()) {
                self.error(format!("keyword `{name}` is given twice"), *kspan);
            }
            given.push(name);
            let t = self.check_expr(value, Some(&k.ty));
            if !self.coerce(&t, &k.ty) {
                self.error(
                    format!(
                        "keyword `{name}` takes {} but found {}",
                        self.name(&k.ty),
                        self.name(&t)
                    ),
                    value.span,
                );
            }
        }
        for k in kws {
            if k.required && !given.contains(&k.name.as_str()) {
                let whose = if yielding {
                    "the block"
                } else {
                    "the procedure"
                };
                self.error(
                    format!("missing keyword `{}`: {whose} requires it", k.name),
                    span,
                );
            }
        }
    }

    fn check_super(&mut self, expr: &Expr, args: Option<&[Arg]>, block: Option<&Block>) -> Type {
        if self.in_function() && self.env.lifted_frame.is_none() {
            self.error(
                "a function has no `self`, so no `super`: `super` calls the overridden method from a method of a class; call another function by its name",
                expr.span,
            );
            return Type::Nothing;
        }
        // (The method's `self`, outside the block of `static(...)`.)
        if self.env.static_frame.is_some() {
            self.error(
                "a block in `static(...)` captures nothing: `super` uses the method's `self` (docs/14 §8)",
                expr.span,
            );
        } else if self
            .env
            .task_frame
            .is_some_and(|tf| self.env.lifted_frame.is_none_or(|lf| tf > lf))
        {
            // The method's `self` (not a receiver's: `super` is the
            // method's), captured by a task or shareable block around
            // (a block given to `def_method` is the generated method's
            // body: it captures no `self`).
            let lexical = match self.env.receivers.first() {
                Some(r) => r.outer_self.clone(),
                None => self.env.self_type.clone(),
            };
            let t = self.resolve(&lexical);
            if !t.has_vars() && !self.world.is_shareable(&t) {
                self.error(
                    format!(
                        "`super` uses `self`, which has the non-shareable type {} and cannot be captured by {}",
                        self.world.type_name(&t),
                        self.task_capture_name()
                    ),
                    expr.span,
                );
            }
        }
        // In a block given to `def_initialize` (docs/14 §5): the generated
        // `initialize`'s `super`.
        if let Some(pos) = self.env.blocks.iter().rposition(|b| b.lifted) {
            if self.env.blocks[pos].init {
                return self.check_init_super(expr, args, block, pos);
            }
        }
        let Some(mid) = self.env.method else {
            self.error("`super` outside of a method", expr.span);
            return Type::Nothing;
        };
        let m = self.world.method(mid).clone();
        // A `using` inside an extension's method of a module that extends
        // the same class adds candidates to its `super` that #585's order
        // (from the declarations) does not see, and two such methods can
        // reach each other in a loop (#593, decided 2026-11-13): refused,
        // with the `using` to be written at the declaration level, where
        // the extensions are ordered.
        if let Some(e) = m.extension {
            let target = self.world.extensions[e as usize].target;
            if let Some(&x) = self
                .local_usings
                .iter()
                .find(|&&x| x != e && self.world.extensions[x as usize].target == target)
            {
                let label = self.world.extension_label(x);
                let tname = self.world.class(target).name.clone();
                self.error(
                    format!(
                        "`super` in an extension's method under a `using` of another extension of `{tname}` ({label}): such a `using` adds candidates that no order sees, which can call each other in a loop; write the `using` at the declaration level (around the extension), where the extensions are ordered (#585)"
                    ),
                    expr.span,
                );
            }
        }
        // An operator's or a setter's takes no keyword argument, in `super`
        // as in a call (docs/01 §9).
        if quarz_syntax::positional_only_name(&m.name) {
            if let Some(Arg::Keyword { value, .. }) = args
                .unwrap_or(&[])
                .iter()
                .find(|a| matches!(a, Arg::Keyword { .. }))
            {
                self.error(
                    format!(
                        "`{}` takes no keyword arguments: an operator's or a setter's are positional",
                        m.name
                    ),
                    value.span,
                );
            }
        }
        // (`deinitialize` likewise: a block or lambda may run its `super`
        // again, or after the release, docs/03 §4.)
        if matches!(m.name.as_str(), "initialize" | "deinitialize")
            && !m.singleton
            && !self.env.blocks.is_empty()
        {
            // A block or lambda may run after `initialize` (its callee or
            // a field may keep it) and would then assign the immutable
            // inherited fields again (as Swift's `super.init`; docs/01 §3).
            self.error(
                format!(
                    "`super` in `{}` must be called directly, not from a block or lambda",
                    m.name
                ),
                expr.span,
            );
            self.check_args_blindly(&Call {
                recv: None,
                name: m.name.clone(),
                args: args.map(|a| a.to_vec()).unwrap_or_default(),
                block: block.cloned(),
                safe_nav: false,
                function: false,
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
        // Inside a block with a receiver, the method's `self`, which the
        // `super` runs on (as Ruby's `instance_exec`; #384): the `self`
        // outside the outermost such block, or, in a block given to
        // `def_method`, outside the outermost one inside it (the lifted
        // block's own is the generated method's).
        let method_self = self
            .env
            .receivers
            .iter()
            .position(|r| self.env.lifted_frame.is_none_or(|lf| r.outer_frame >= lf));
        let self_ty = match method_self {
            Some(k) => self.env.receivers[k].outer_self.clone(),
            None => self.env.self_type.clone(),
        };
        // An extension is not active in its own body unless `using`-ed
        // there: its method is listed (as the group to pass) only while it
        // is, last among the extensions in scope.
        let own_ext = m
            .extension
            .filter(|e| !self.world.active_extensions.borrow().contains(e));
        if let Some(e) = own_ext {
            self.world.active_extensions.get_mut().push(e);
        }
        let found = self.world.lookup_methods(&self_ty, &m.name);
        if own_ext.is_some() {
            self.world.active_extensions.get_mut().pop();
        }
        // (An abstract declaration is a requirement, not an
        // implementation: `super` passes over it to the next method with a
        // body, on both sides, #522. Per signature: an owner with an
        // abstract method of the name and no method with a body this one
        // replaces (`World::replaces_seen`, an extension's body on it too)
        // is passed over whole, even with concrete overloads of other
        // signatures; one with a body this method replaces stops the walk
        // there, its overloads chosen among as a call's.)
        // (From each owner's own table: an extension's method of the
        // signature hides the target's own abstract in the lookup.)
        let has_abstract: Vec<ClassId> = found
            .iter()
            .map(|(c, _)| self.world.method(*c).owner)
            .filter(|o| {
                let k = self.world.class(*o);
                let table = if m.singleton {
                    &k.singleton_methods
                } else {
                    &k.methods
                };
                table.get(&m.name).is_some_and(|ids| {
                    ids.iter().any(|i| {
                        let im = self.world.method(*i);
                        im.owner == *o && im.is_abstract
                    })
                })
            })
            .collect();
        // (The method's own group, as the walk below takes it, is not a
        // body above it.)
        let in_own_group = |cm: &MethodInfo| match m.extension {
            Some(e) => cm.extension == Some(e),
            None => cm.owner == owner && cm.extension.is_none(),
        };
        // (Only what the walk reaches: the methods after the own group's
        // first, an earlier extension's never a body above it.)
        let own_at = found
            .iter()
            .position(|(c, _)| in_own_group(self.world.method(*c)))
            .unwrap_or(found.len());
        let replaced_body: Vec<ClassId> = found[own_at..]
            .iter()
            .filter(|(c, subst)| {
                let cm = self.world.method(*c);
                !cm.is_abstract
                    && !in_own_group(cm)
                    && cm.singleton == m.singleton
                    && has_abstract.contains(&cm.owner)
                    && self
                        .world
                        .replaces_seen(mid, &HashMap::default(), *c, subst)
            })
            .map(|(c, _)| self.world.method(*c).owner)
            .collect();
        let passed: Vec<ClassId> = has_abstract
            .into_iter()
            .filter(|o| !replaced_body.contains(o))
            .collect();
        let mut after_own = false;
        let mut next_owner = None;
        let mut cands = Vec::new();
        // (Every method after the own group on its side: two active
        // extensions' modules there give `super` no order, #577.)
        let mut after = Vec::new();
        let found_all = found.clone();
        for (c, subst) in found {
            let cm = self.world.method(c);
            if in_own_group(cm) {
                after_own = true;
                continue;
            }
            if !after_own
                || cm.singleton != m.singleton
                || cm.is_abstract
                || passed.contains(&cm.owner)
            {
                continue;
            }
            after.push((c, subst.clone()));
            if next_owner.is_some_and(|o| o != cm.owner) {
                continue;
            }
            next_owner = Some(cm.owner);
            cands.push((c, subst));
        }
        // (The next owner a module an active extension brought: the
        // methods of the other active extensions' modules on the same
        // target join it, the overload choice deciding among them as a
        // call's does, the overriding one or else an ambiguity, #577;
        // their `using` order gives none.)
        let src = self.extension_sources(&self_ty);
        let target_of = |c: MethodId| {
            let owner = self.world.method(c).owner;
            src.iter()
                .find(|(k, _)| *k == owner)
                .map(|(_, e)| self.world.extensions[*e as usize].target)
        };
        if let Some(target) = cands.first().and_then(|(c, _)| target_of(*c)) {
            for (c, cs) in &after {
                if !cands.iter().any(|(k, _)| k == c) && target_of(*c) == Some(target) {
                    cands.push((*c, cs.clone()));
                }
            }
        }
        let mut cycle_exts: Vec<ExtensionId> = Vec::new();
        // (In an extension's method: the methods of the other extensions of
        // its target active where it is declared, in front, chosen among
        // with the rest as a call's overloads are; two of the same
        // signature, neither overriding the other, are ambiguous, #585,
        // docs/01 §7.)
        if let Some(e) = m.extension {
            let target = self.world.extensions[e as usize].target;
            let others: Vec<_> = found_all
                .iter()
                .filter(|(c, _)| {
                    let cm = self.world.method(*c);
                    cm.singleton == m.singleton
                        && !cm.is_abstract
                        && cm.extension.is_some_and(|x| {
                            x != e && self.world.extensions[x as usize].target == target
                        })
                        && !cands.iter().any(|(k, _)| k == c)
                })
                .cloned()
                .collect();
            // (An extension that reaches this one back, directly or
            // through others, is in its cycle: no order between them; the
            // `super` taking one of its methods is an error, #585, below.)
            // (Only when another extension's method is a candidate: the
            // relation, once for this `super`.)
            let other_ext = |c: &MethodId| {
                self.world
                    .method(*c)
                    .extension
                    .is_some_and(|x| x != e && self.world.extensions[x as usize].target == target)
            };
            let graph = if others.iter().chain(cands.iter()).any(|(c, _)| other_ext(c)) {
                self.world.reach_graph(target)
            } else {
                Vec::new()
            };
            // (Every extension's cycle, once.)
            let comps = World::reach_components(&graph);
            let same_cycle = |a: ExtensionId, b: ExtensionId| {
                comps.get(&a).is_some_and(|c| comps.get(&b) == Some(c))
            };
            if !graph.is_empty() {
                cycle_exts = graph
                    .iter()
                    .map(|(k, _)| *k)
                    .filter(|x| *x != e && same_cycle(e, *x))
                    .collect();
            }
            let reaches = |a: ExtensionId, b: ExtensionId| {
                graph.iter().any(|(k, next)| *k == a && next.contains(&b))
            };
            // (One extension reaching another orders them: the reached
            // one's method of the same parameters is hidden, X -> Y -> W.)
            let ext_of = |c: &MethodId| self.world.method(*c).extension.unwrap();
            let hidden: Vec<MethodId> = others
                .iter()
                .filter(|(w, ws)| {
                    others.iter().any(|(y, ys)| {
                        let (ey, ew) = (ext_of(y), ext_of(w));
                        // (Not within one cycle: no order there.)
                        ey != ew
                            && reaches(ey, ew)
                            && !same_cycle(ey, ew)
                            && self.as_specific(
                                self.world.method(*y),
                                ys,
                                self.world.method(*w),
                                ws,
                            )
                            && self.as_specific(
                                self.world.method(*w),
                                ws,
                                self.world.method(*y),
                                ys,
                            )
                    })
                })
                .map(|(w, _)| *w)
                .collect();
            let others: Vec<_> = others
                .into_iter()
                .filter(|(c, _)| !hidden.contains(c))
                .collect();
            if !others.is_empty() {
                cands.splice(0..0, others);
            }
        }
        if cands.is_empty() {
            // A built-in function is no method to override (docs/01 §1).
            let kernel = self.world.builtin.kernel;
            let builtin = !m.singleton
                && self
                    .world
                    .class(kernel)
                    .methods
                    .get(&m.name)
                    .is_some_and(|ms| ms.iter().any(|id| self.world.method(*id).is_native));
            let hint = if builtin {
                format!(
                    ": `{0}` is a built-in function, called as `Kernel.{0}`",
                    m.name
                )
            } else {
                String::new()
            };
            self.error(
                format!("no superclass method `{}`{hint}", m.name),
                expr.span,
            );
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
            function: false,
            has_parens: true,
            type_args: vec![],
        };
        let zsuper = args
            .is_none()
            .then(|| m.params.len() + usize::from(m.block.is_some()));
        let saved = std::mem::replace(&mut self.zsuper_forwards, zsuper);
        // (A candidate of an extension in this one's cycle: tried, undone;
        // the `super` taking it is an error, else it is left out, #585.)
        let in_cycle = |c: &Self, k: MethodId| {
            c.world
                .method(k)
                .extension
                .is_some_and(|x| cycle_exts.contains(&x))
        };
        let cands = if cands.iter().any(|(k, _)| in_cycle(self, *k)) {
            let infer = self.infer.save();
            let env = self.env.clone();
            let reported = self.diagnostics.len();
            let tables = self.table_mark();
            let last = self.last_winner;
            let initish = m.name == "initialize" || (m.name == "deinitialize" && !m.singleton);
            self.resolve_overloads_as(expr, &call, &self_ty, cands.clone(), true, None, initish);
            // (One candidate is the winner when the call fits it.)
            let fits = !self.diagnostics[reported..]
                .iter()
                .any(|(_, d)| d.is_error());
            let trial_errors: Vec<String> = self.diagnostics[reported..]
                .iter()
                .filter(|(_, d)| d.is_error())
                .map(|(_, d)| d.message.clone())
                .collect();
            let winner = self
                .last_winner
                .filter(|(id, _)| *id == expr.id)
                .map(|(_, w)| w)
                .or_else(|| (cands.len() == 1 && fits).then(|| cands[0].0));
            self.truncate_diagnostics(reported);
            self.discard_tables(tables);
            self.infer.restore(infer);
            self.env = env;
            self.last_winner = last;
            // (An ambiguity among them, a cycle's candidate in it: no
            // order, the cycle's error too.)
            let ambiguous = trial_errors.iter().any(|m| m.contains("is ambiguous"));
            let winner =
                if ambiguous && winner.is_some() && !winner.is_some_and(|w| in_cycle(self, w)) {
                    cands.iter().map(|(k, _)| *k).find(|k| in_cycle(self, *k))
                } else {
                    winner
                };
            if let Some(w) = winner.filter(|w| in_cycle(self, *w)) {
                let x = self.world.method(w).extension.unwrap();
                let e = m.extension.unwrap();
                let (na, mut nb) = (self.extension_name(e), self.extension_name(x));
                if na == nb {
                    nb = nb.replacen("the ", "another ", 1);
                }
                self.zsuper_forwards = saved;
                self.error(
                    format!(
                        "`super` in {na} would reach `{}` of {nb}, which reaches this one back: there is no order between them; put one in a module and `using` it from the other's",
                        m.name
                    ),
                    expr.span,
                );
                return Type::Nothing;
            }
            cands
                .into_iter()
                .filter(|(k, _)| !in_cycle(self, *k))
                .collect()
        } else {
            cands
        };
        let t = self.resolve_overloads_as(
            expr,
            &call,
            &self_ty,
            cands,
            true,
            None,
            // (`super` in `deinitialize` chains the parent's, the one
            // other call of it, docs/03 §4.)
            m.name == "initialize" || (m.name == "deinitialize" && !m.singleton),
        );
        self.zsuper_forwards = saved;
        if let Some(CallTarget::Method { method }) = self.out.calls.get(&expr.id).cloned() {
            self.out.calls.insert(expr.id, CallTarget::Super { method });
            if let Some(args) = args {
                self.note_abstract_type_args(method, args);
            }
        }
        // (The lowering passes that `self` as the receiver, read from the
        // hidden slot, as an implicit call falling through to it.)
        if let Some(k) = method_self {
            self.bind_outer_self_slot(expr, k);
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

    /// `super(args)` in a block given to `def_initialize` (docs/14 §5),
    /// whose block is `self.env.blocks[pos]`: the `initialize` a class
    /// directly below the block's bound would reach (the bound's own
    /// overloads, or the nearest ancestor's), chosen among as a call's
    /// overloads are and called as that method. The statement checks
    /// that the class generated into reaches the same ones.
    fn check_init_super(
        &mut self,
        expr: &Expr,
        args: Option<&[Arg]>,
        block: Option<&Block>,
        pos: usize,
    ) -> Type {
        let call = Call {
            recv: None,
            name: "initialize".to_string(),
            args: args.map(|a| a.to_vec()).unwrap_or_default(),
            block: block.cloned(),
            safe_nav: false,
            function: false,
            has_parens: true,
            type_args: vec![],
        };
        if pos + 1 != self.env.blocks.len() {
            self.error(
                "`super` in `initialize` must be called directly, not from a block or lambda",
                expr.span,
            );
            self.check_args_blindly(&call);
            return Type::Nothing;
        }
        if args.is_none() {
            self.error(
                "a bare `super` forwards a method's parameters: in a block given to `def_initialize`, write the arguments (`super(x)`)",
                expr.span,
            );
            return Type::Nothing;
        }
        let self_ty = self.env.self_type.clone();
        let mut owner = None;
        let mut cands = Vec::new();
        for (c, subst) in self.world.lookup_methods(&self_ty, "initialize") {
            let cm = self.world.method(c);
            if cm.singleton {
                continue;
            }
            if *owner.get_or_insert(cm.owner) != cm.owner {
                break;
            }
            cands.push((c, subst));
        }
        if cands.is_empty() {
            self.error("no superclass method `initialize`", expr.span);
            self.check_args_blindly(&call);
            return Type::Nothing;
        }
        let t = self.resolve_overloads_as(expr, &call, &self_ty, cands, true, None, true);
        if let Some(CallTarget::Method { method }) = self.out.calls.get(&expr.id).cloned() {
            self.out.calls.insert(expr.id, CallTarget::Super { method });
            if let Some(args) = args {
                self.note_abstract_type_args(method, args);
            }
            // It assigned its class's fields, perhaps other values than
            // the ones narrowed before.
            let owner = self.world.method(method).owner;
            for (f, _) in self.world.all_fields(owner) {
                self.env.ivar_narrow.remove(&f.name);
                self.env.assigned_fields.insert(f.name);
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
        // A module a conditional extension brings: whether a value is one
        // may depend on its type arguments, which the run time does not
        // see; refused wherever the value may be of a class whose answer
        // the table does not give exactly (#515).
        if let Some((m, c, cargs)) = self.runtime_untestable(&rt, target) {
            self.report_untestable(&format!("`{op}`"), &m, c, &cargs, span, None);
            return;
        }
        self.record_runtime_test(&rt, target, &format!("`{op}`"));
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

    /// For a run-time test of a value of type `rt` against `target`: a
    /// module of `target` an extension with bounds brings and a class (with
    /// the arguments `rt` fixes) a value of `rt` may be of, for which the
    /// membership table does not answer exactly
    /// (`World::runtime_test_exact`), #515. The elements of the
    /// collections and tuples the test checks too, and a class value's
    /// test (`Type[M]`).
    /// A run-time test against a type parameter's class value (`x.is_a?(k)`,
    /// `when k`, with `k: Type[T]`): refused where `T` may be a module the
    /// class alone cannot answer for (#598, decided 2026-11-13), decided as
    /// for a written module (`runtime_untestable`, #596) over every module
    /// `T`'s bounds admit. It errs toward refusing: an unbounded `T` admits
    /// every module, among them those the prelude's conditional extensions
    /// bring (`Comparable`), so it is always refused; a class bound admits
    /// no module.
    fn check_testable_param(&mut self, rt: &Type, at: &Type, op: &str, span: Span) {
        // (Each member of a union of class values, `Type[T] | Type[Q]`.)
        for m in at.members() {
            if self.check_testable_param_one(rt, &m, op, span) {
                return;
            }
        }
    }

    /// `check_testable_param` for one class value; whether it refused.
    fn check_testable_param_one(&mut self, rt: &Type, at: &Type, op: &str, span: Span) -> bool {
        let Type::TypeOf(inner) = at else {
            return false;
        };
        let Type::Param(p) = inner.as_ref() else {
            return false;
        };
        let bounds = self.world.param_bounds(*p);
        let n = self.world.classes.len() as ClassId;
        for x in 0..n {
            if self.world.class(x).kind != ClassKind::Module {
                continue;
            }
            let cand = Type::Class(x, self.world.own_args(x));
            if !bounds.iter().all(|b| self.world.is_subtype(&cand, b)) {
                continue;
            }
            if let Some((_, c, _)) = self.runtime_untestable(rt, &cand) {
                let pname = self.world.type_name(inner);
                let (mname, cname) = (
                    self.world.class(x).name.clone(),
                    self.world.class(c).name.clone(),
                );
                self.error(
                    format!(
                        "`{op}` against `Type[{pname}]` cannot be checked at run time: `{pname}` may be the module `{mname}`, and whether a value of class `{cname}` is one depends on its type arguments, which the run time does not see; bound `{pname}` by a class, or test against a type written out"
                    ),
                    span,
                );
                return true;
            }
        }
        false
    }

    fn runtime_untestable(&self, rt: &Type, target: &Type) -> Option<(Type, ClassId, Vec<Type>)> {
        let b = self.world.builtin.clone();
        for tm in target.members() {
            match &tm {
                // (The elements a test checks: of the static type's when every
                // member of it is that collection, else of anything, #596.)
                Type::Class(k, targs) if [b.array, b.set, b.hash, b.range].contains(k) => {
                    let members = rt.members();
                    let all_same = members
                        .iter()
                        .all(|m| matches!(m, Type::Class(mk, _) if mk == k));
                    for (i, ta) in targs.iter().enumerate() {
                        let elems: Vec<Type> = members
                            .iter()
                            .filter_map(|m| match m {
                                Type::Class(_, ma) => ma.get(i).cloned(),
                                _ => None,
                            })
                            .collect();
                        let elem = if !all_same || elems.is_empty() {
                            self.world.object()
                        } else {
                            Type::union_of(elems)
                        };
                        if let Some(found) = self.runtime_untestable(&elem, ta) {
                            return Some(found);
                        }
                    }
                }
                Type::Tuple(ts) => {
                    let members = rt.members();
                    let all_same = members
                        .iter()
                        .all(|m| matches!(m, Type::Tuple(ms) if ms.len() == ts.len()));
                    for (i, ta) in ts.iter().enumerate() {
                        let elems: Vec<Type> = members
                            .iter()
                            .filter_map(|m| match m {
                                Type::Tuple(ms) => ms.get(i).cloned(),
                                _ => None,
                            })
                            .collect();
                        let elem = if !all_same || elems.is_empty() {
                            self.world.object()
                        } else {
                            Type::union_of(elems)
                        };
                        if let Some(found) = self.runtime_untestable(&elem, ta) {
                            return Some(found);
                        }
                    }
                }
                Type::Class(mid, _) => {
                    if let Some(found) = self.untestable_against(rt, *mid, false) {
                        return Some((tm.clone(), found.0, found.1));
                    }
                }
                Type::ClassObject(mid, _) => {
                    if let Some(found) = self.untestable_against(rt, *mid, true) {
                        return Some((Type::Class(*mid, vec![]), found.0, found.1));
                    }
                }
                _ => {}
            }
        }
        None
    }

    /// `runtime_untestable` for module `mid`: a class a value of `rt` may
    /// be of (`class_values`: a class value of `rt`, `Type[M]`'s test),
    /// whose membership the table does not answer exactly. Remembered per
    /// static type and module.
    fn untestable_against(
        &self,
        rt: &Type,
        mid: ClassId,
        class_values: bool,
    ) -> Option<(ClassId, Vec<Type>)> {
        if self.world.class(mid).kind != ClassKind::Module
            || !self.world.conditionally_included(mid)
        {
            return None;
        }
        // (With the declarations' count: the REPL adds classes and
        // extensions, which change the answer.)
        let key = (
            format!(
                "{rt:?}/{}/{}",
                self.world.classes.len(),
                self.world.extensions.len()
            ),
            mid,
            class_values,
        );
        if let Some(found) = self.untestable_memo.borrow().get(&key) {
            return found.clone();
        }
        let mut found = None;
        'members: for m in rt.members() {
            let held = if class_values {
                match &m {
                    Type::ClassObject(k, _) => {
                        let own: Vec<Type> = self
                            .world
                            .class(*k)
                            .type_params
                            .iter()
                            .map(|tp| Type::Param(tp.id))
                            .collect();
                        self.classes_a_value_may_hold(&Type::Class(*k, own))
                    }
                    Type::TypeOf(t) => self.classes_a_value_may_hold(t),
                    Type::Class(k, _) if *k == self.world.builtin.object => {
                        self.classes_a_value_may_hold(&m)
                    }
                    Type::Param(_) | Type::Var(_) => self.classes_a_value_may_hold(&m),
                    _ => Vec::new(),
                }
            } else {
                self.classes_a_value_may_hold(&m)
            };
            // (Where the static member is the target module itself, every
            // value is one: the test is exact where the table says yes too.
            // No other shortcut, #596.)
            let always = !class_values && matches!(&m, Type::Class(k, _) if *k == mid);
            for (c, cargs) in held {
                if always {
                    let run = self
                        .world
                        .resolution(c, &[], View::Runtime)
                        .iter()
                        .any(|(a, _)| *a == mid);
                    if !run {
                        found = Some((c, cargs));
                        break 'members;
                    }
                    continue;
                }
                // (A class value carries no arguments: its own parameters.)
                let cargs = if class_values {
                    self.world
                        .class(c)
                        .type_params
                        .iter()
                        .map(|tp| Type::Param(tp.id))
                        .collect()
                } else {
                    cargs
                };
                if !self.world.runtime_test_exact(c, &cargs, mid) {
                    found = Some((c, cargs));
                    break 'members;
                }
            }
        }
        self.untestable_memo.borrow_mut().insert(key, found.clone());
        found
    }

    /// The classes a value of type `t` may be of, each with the type
    /// arguments `t` fixes (the others as the class's own parameters): the
    /// class itself, its subclasses, the classes including a module type
    /// (any extension's include, one with bounds included, their bounds
    /// assumed); every class for `Object`, a type parameter or an
    /// inference variable (#515). Not an abstract class, of which no value
    /// is. Complete for the program checked: its classes, every cog's, are
    /// declared before any body is checked. An approximation that
    /// over-refuses: a class counts whatever its arguments (`AS <
    /// AB[String]` for an `AB[Int]`), and an argument is fixed only for an
    /// invariant parameter given a plain type (not through variance or a
    /// union), #597 makes it exact; it never accepts more (#596).
    fn classes_a_value_may_hold(&self, t: &Type) -> Vec<(ClassId, Vec<Type>)> {
        let concrete = |c: &ClassInfo| {
            !matches!(c.kind, ClassKind::Module | ClassKind::Main) && !c.is_abstract
        };
        let params = |c: &ClassInfo| -> Vec<Type> {
            c.type_params.iter().map(|tp| Type::Param(tp.id)).collect()
        };
        let all = || {
            self.world
                .classes
                .iter()
                .filter(|c| concrete(c))
                .map(|c| (c.id, params(c)))
                .collect::<Vec<_>>()
        };
        match t {
            Type::Union(ms) => ms
                .iter()
                .flat_map(|m| self.classes_a_value_may_hold(m))
                .collect(),
            Type::Param(_) | Type::Var(_) => all(),
            Type::Class(k, _) if *k == self.world.builtin.object => all(),
            Type::Class(k, ka) => {
                let (k, ka) = (*k, ka.clone());
                self.world
                    .classes
                    .iter()
                    .filter(|c| concrete(c))
                    .filter_map(|c| {
                        let own = params(c);
                        // (With bounds assumed: a class a module type comes
                        // to only through an extension with bounds holds
                        // values of that type too.)
                        let anc = self.world.resolution(c.id, &own, View::Override);
                        let (_, kargs) = anc.iter().find(|(a, _)| *a == k)?;
                        // (The arguments `t` fixes: a parameter of `c`
                        // standing where `t` has a type.)
                        // (An argument fixed from the static type only for an
                        // invariant parameter of `k` given a plain type there,
                        // a parameter of `c` standing in it: then every value
                        // of `c` that is of `t` has it. Else left as `c`'s own
                        // parameter, which can only refuse more.)
                        let kinfo = self.world.class(k);
                        let mut fixed: HashMap<TypeParamId, Type> = HashMap::default();
                        for (i, (x, y)) in kargs.iter().zip(&ka).enumerate() {
                            let invariant = kinfo.type_params.get(i).is_some_and(|tp| {
                                tp.variance == quarz_syntax::ast::Variance::Invariant
                            });
                            let plain = !matches!(y, Type::Union(_))
                                && !y.mentions_any_param()
                                && !y.has_vars();
                            if let Type::Param(p) = x {
                                if invariant && plain && c.type_params.iter().any(|tp| tp.id == *p)
                                {
                                    fixed.insert(*p, y.clone());
                                }
                            }
                        }
                        Some((c.id, own.iter().map(|a| a.subst(&fixed)).collect()))
                    })
                    .collect()
            }
            _ => Vec::new(),
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
            // A class value is tested for its class (`Type[Model]`: a class
            // `<= Model`), not for type arguments, which it does not carry:
            // a generic class (`Type[Box[Int]]`) is refused.
            Type::ClassObject(id, _) => !self.world.class(*id).type_params.is_empty(),
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
                // (A `Cog` is a `Type`: a class value too.)
                *id == self.world.builtin.object
                    || self.world.class_is_a(*id, self.world.builtin.class_)
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
    /// Out of any alternative pattern (for an expression in one, a pin's),
    /// giving back what to restore.
    pub(crate) fn leave_alternatives(&mut self) -> u32 {
        std::mem::take(&mut self.env.in_alternative)
    }

    pub(crate) fn restore_alternatives(&mut self, saved: u32) {
        self.env.in_alternative = saved;
    }

    /// Entering (`true`) or leaving an alternative pattern (`a | b`).
    pub(crate) fn enter_alternative(&mut self, enter: bool) {
        if enter {
            self.env.in_alternative += 1;
        } else {
            self.env.in_alternative -= 1;
        }
    }

    pub(crate) fn declare_pattern_var(&mut self, name: &str, ty: Type, span: Span) {
        // An alternative binds no name (as Ruby's "illegal variable in
        // alternative pattern"): which alternative matched, and so what was
        // bound, is not known after it (docs/01 §11). `_` there is a
        // wildcard, binding nothing.
        if self.env.in_alternative > 0 {
            if name == "_" {
                return;
            }
            // (Declared all the same, so that its reads add no error.)
            self.error(
                format!("`{name}` is bound in an alternative pattern: an alternative binds no names (match the alternatives apart, or bind outside the `|`)"),
                span,
            );
        }
        // (A `case/in` arm's names are its own: always fresh.)
        let existing = self.lookup_var(name).filter(|(depth, slot)| {
            !self.env.arm_local
                && !(*depth == 0 && self.env.pattern_base.is_some_and(|base| *slot >= base))
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
        let members = remaining.len();
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
        // Whether an earlier arm's guard may have assigned the subject
        // variable: it no longer holds the value matched, so is not
        // narrowed by the later patterns.
        let mut subject_rebound = false;
        for arm in arms {
            self.restore(&before);
            self.widen_rebound(&rebound);
            self.widen_ivars(&ivars_assigned);
            let at_arm = self.snapshot();
            // The subject is evaluated once: an arm sees its value as what
            // the earlier unguarded arms left (`in nil` then `in v` binds
            // `v` without `nil`), whatever the subject expression.
            let left = (remaining.len() < members && !remaining.is_empty())
                .then(|| Type::union_of(remaining.clone()));
            let on = match &left {
                Some(t) if names_class(&arm.pattern) || st_class == st => t,
                _ if names_class(&arm.pattern) => &st_class,
                _ => &st,
            };
            // The names the pattern binds are the arm's own, as a block's
            // parameters (docs/01 §11): fresh, shadowing outer locals of
            // the names, which a failed arm so never changes.
            let own_from = self.env.frames.last().unwrap().vars.len();
            let saved_arm_local = std::mem::replace(&mut self.env.arm_local, true);
            let narrowed = self.check_pattern(&arm.pattern, on);
            self.env.arm_local = saved_arm_local;
            let own_to = self.env.frames.last().unwrap().vars.len();
            // (A pinned expression in the pattern may assign it too.)
            for (_, _, name, _, _) in self.rebound_since(&at_arm) {
                subject_rebound |= key == Some(VarKey::Local(name));
            }
            // (Where the pattern binds the subject's name, `in
            // L::Cons(_, l)` on `l`, that name is the binding in the arm.)
            match &key {
                Some(VarKey::Local(n)) if arm.pattern.binds(n) => {}
                _ if subject_rebound => {}
                Some(k) => self.narrow_subject(k, Some(narrowed)),
                None => {}
            }
            // (The arm, its pattern's names included, is a scope of its
            // own for what it declares, `y := e`, in its guard or body.)
            let saved_scope = self.enter_decl_scope(own_from);
            if let Some(g) = &arm.guard {
                let (_, ft, ff) = self.check_cond(&g.cond);
                // (Where it fails, as a later arm sees it: what it bound
                // or assigned too.)
                let at_guard = self.snapshot();
                self.apply_facts(if g.negate { &ft } else { &ff });
                for (fi, slot, name, _, now) in self.rebound_since(&at_arm) {
                    subject_rebound |= key == Some(VarKey::Local(name));
                    rebound.push((fi, slot, now));
                }
                for n in self.ivars_changed_since(&at_arm) {
                    let t = self.env.ivar_narrow.get(&n).cloned();
                    subject_rebound |= key.as_ref() == Some(&VarKey::IVar(n.clone()));
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
            self.leave_decl_scope(saved_scope);
            snaps.push((self.snapshot(), bt.is_nothing()));
            result = self.join(&result, &bt);
            // The arm's names are out of scope after it (their slots stay,
            // for the code that refers to them).
            let frame = self.env.frames.last_mut().unwrap();
            for slot in own_from..own_to.min(frame.vars.len()) {
                let hidden = format!("{} (case arm)", frame.vars.list[slot].name);
                frame.vars.rename(slot, hidden);
            }
        }
        self.env.pattern_base = saved_base;
        self.restore(&before);
        self.widen_rebound(&rebound);
        self.widen_ivars(&ivars_assigned);
        let et = match els {
            Some(els) => {
                if let (Some(k), false) = (&key, subject_rebound) {
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
    fn errors_after(&self, n: usize) -> Vec<(u32, Diagnostic)> {
        self.diagnostics
            .iter()
            .filter(|(_, d)| d.is_error())
            .skip(n)
            .cloned()
            .collect()
    }
    fn pending_classes(&self) -> Vec<ClassId> {
        self.pending_statement_classes()
    }
    fn pending_statements(&self) -> Vec<usize> {
        (0..self.world.static_stmts.len())
            .filter(|i| !self.static_done.get(*i).copied().unwrap_or(false))
            .collect()
    }
    fn generated_new(
        &mut self,
        class: ClassId,
        from: ClassId,
        method: MethodId,
        init: Option<MethodId>,
        at: (u32, Span),
    ) -> Result<(), String> {
        self.check_generated_new(class, from, method, init)?;
        self.generated_news.push((class, from, method, init));
        // Its subclasses inherit `method`: checked as a written one's `new`.
        self.self_news.push((class, init, method, at.1, at.0));
        Ok(())
    }
    fn set_generated_captures(&mut self, method: MethodId, captures: Vec<(u32, u32, Baked)>) {
        if let Some(g) = &mut self.world.method_mut(method).generated {
            g.captures = captures;
        }
    }
    fn add_generated(&mut self, info: MethodInfo) -> Result<MethodId, String> {
        // `def_initialize` (docs/14 §5): one more overload of
        // `initialize`, written or generated, of another signature.
        if info.generated.as_ref().is_some_and(|g| g.initialize) {
            let class = self.world.class(info.owner);
            if let Some(existing) = class
                .methods
                .get("initialize")
                .into_iter()
                .flatten()
                .map(|id| self.world.method(*id))
                .find(|m| self.world.same_signature(m, &info))
            {
                return Err(format!(
                    "`{}` already has an `initialize` with the same parameters{}",
                    class.name,
                    if existing.generated.is_some() {
                        " (generated by an earlier `def_initialize`)"
                    } else {
                        ""
                    }
                ));
            }
            let owner = info.owner;
            let id = self.world.add_method(info);
            // The generated methods building a class that finds its
            // `initialize` through `owner` (on the way from it up to the
            // class `new` was checked for) now find this overload, which
            // hides the inherited ones.
            let sites: Vec<_> = self
                .generated_news
                .iter()
                .filter(|s| self.world.class_is_a(s.0, owner) && !self.world.class_is_a(s.1, owner))
                .copied()
                .collect();
            for (class, from, method, init) in sites {
                self.check_generated_new(class, from, method, init)?;
            }
            return Ok(id);
        }
        self.add_generated_other(info)
    }
    fn add_generated_field(&mut self, class: ClassId, field: FieldInfo) -> Result<(), String> {
        if let Some(why) = crate::declare::reserved_field_name(&field.name) {
            return Err(why);
        }
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

    fn report_errors(&mut self, errors: Vec<crate::FileDiagnostic>) {
        self.diagnostics.extend(errors);
    }
}

impl Checker {
    /// `StaticHost::generated_new`'s check of the class generated into.
    fn check_generated_new(
        &mut self,
        class: ClassId,
        from: ClassId,
        method: MethodId,
        init: Option<MethodId>,
    ) -> Result<(), String> {
        // The class generated into builds itself with the first
        // `initialize` from it up to (not including) `from`, the class
        // `new` was checked for, given what `new` passes for `init`.
        let mut own: Option<Vec<MethodId>> = None;
        let mut cur = Some(class);
        while let Some(c) = cur {
            if c == from {
                break;
            }
            let k = self.world.class(c);
            if let Some(ids) = k.methods.get("initialize").filter(|ids| !ids.is_empty()) {
                own = Some(ids.clone());
                break;
            }
            cur = k.superclass.as_ref().and_then(|t| match t {
                Type::Class(id, _) => Some(*id),
                _ => None,
            });
        }
        if let Some(own) = own.filter(|o| !init.is_some_and(|i| o.contains(&i))) {
            let s = self.world.method(own[0]).clone();
            // The first of its overloads that takes the arguments (recorded
            // for the runtime), else an error.
            let chosen = own
                .iter()
                .copied()
                .find(|&o| self.inherited_init_fits(class, init, o));
            if let Some(chosen) = chosen {
                self.record_inherited_init(class, init, chosen);
            } else {
                let cname = self.world.class(class).name.clone();
                let mname = self.world.method(method).name.clone();
                let oname = self.world.class(s.owner).name.clone();
                let which = if oname == cname {
                    format!("`{cname}#initialize`")
                } else {
                    format!("`{oname}#initialize`, which `{cname}` builds with,")
                };
                let (new_in, sep) = if self.world.method(method).singleton {
                    ("`new`", ".")
                } else {
                    ("`Self.new`", "#")
                };
                return Err(format!(
                    "{which} does not take the arguments of {new_in} in the generated `{cname}{sep}{mname}`"
                ));
            }
        }
        Ok(())
    }

    /// `StaticHost::add_generated` for a method other than `initialize`.
    fn add_generated_other(&mut self, info: MethodInfo) -> Result<MethodId, String> {
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
}
