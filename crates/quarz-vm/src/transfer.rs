//! Running a block on another operating-system thread (`Task.blocking`).
//!
//! Values are reference counted and belong to one thread, so a block
//! cannot simply be called elsewhere. Instead the block (its function,
//! captured frames and `self`) is exported to a thread-safe
//! representation, [`Transfer`], and imported into a second interpreter
//! that lives on a helper thread and runs the same program image. The
//! result (or the exception) comes back the same way. Only immutable
//! values travel; mutable ones and the concurrency primitives are
//! rejected, since they would have to be shared, not copied.

use crate::rc::{Rc, SendRc};
use std::cell::RefCell;
use std::sync::{Arc, Mutex};

use num_bigint::BigInt;
use quarz_ir::{ClassId, FuncId, FuncInfo, MethodId, RtWorld, Unit};

use crate::interp::{CompiledFn, Flow, Interp, SharedState};
use crate::sched::{TaskExit, TaskResult};
use crate::value::*;

/// Everything a second interpreter needs to run the loaded program.
pub struct ProgramImage {
    pub world: RtWorld,
    /// A compiled program's methods (shared: decoded once for all).
    pub lazy: Option<Arc<crate::methods::Lazy>>,
    pub functions: Vec<FuncInfo>,
    /// The functions' bodies, for the interpreter (none in a compiled
    /// program).
    pub bodies: Option<crate::vm::Bodies>,
    pub units: Vec<Unit>,
    pub compiled: Vec<Option<CompiledFn>>,
}

impl ProgramImage {
    /// An interpreter of the program over `state`, on this thread.
    pub fn load(&self, argv: Vec<String>, state: SharedState) -> std::rc::Rc<Interp> {
        if let (Some(bodies), Some(i)) = (&self.bodies, crate::vm::INTERPRETER.get()) {
            (i.import)(&state, bodies);
        }
        Interp::with_state_lazy(
            self.world.clone(),
            0,
            self.functions.clone(),
            self.units.clone(),
            argv,
            state,
            self.lazy.clone(),
        )
    }
}

// SAFETY: the image holds plain data and `extern "C"` function pointers.
unsafe impl Send for ProgramImage {}
unsafe impl Sync for ProgramImage {}

/// A value in transit between threads: its nodes, the root first. A
/// node refers to its parts by their indices, always after its own, so
/// that a value nested however deeply is exported, imported and dropped
/// without recursion (#466: a list 100,000 cells deep overflowed a
/// thread's stack).
#[derive(Debug)]
pub struct Transfer {
    nodes: Vec<Node>,
}

/// A node's index in its `Transfer`.
type Ix = u32;

#[derive(Debug)]
enum Node {
    Nil,
    Bool(bool),
    Int(i64),
    Float(f64),
    Symbol(String),
    Class(ClassId),
    Duration(i64),
    BigInt(Box<BigInt>),
    Str(String),
    /// A string or byte sequence nothing else refers to, moved rather
    /// than copied (#468): its allocation itself, marked shared (as a
    /// value a task hands to another is, `crate::rc`), so that the other
    /// thread may own it; the import makes it local again on its first
    /// update in place (`Rc::get_mut`).
    MovedStr(Moved<str>),
    MovedBytes(Moved<[u8]>),
    /// A value nothing else refers to, with nothing in it bound to its
    /// thread's interpreter (`movable_whole`): marked shared, as a value
    /// one task hands to another is, and handed over whole (#479).
    Whole(SharedValue),
    Array(Vec<Ix>),
    /// An `Array[Int]`/`Array[Float]` stored as words, its vector moved
    /// out when nothing else refers to the array, copied otherwise: no
    /// node per element.
    Ints(Vec<i64>),
    Floats(Vec<f64>),
    Hash(Vec<(Ix, Ix)>),
    Set(Vec<Ix>),
    Range {
        lo: Ix,
        hi: Ix,
        exclusive: bool,
    },
    /// (The rarer kinds boxed: a node stays small.)
    Regexp(Box<(String, String)>),
    Bytes(Vec<u8>),
    Time(TimeVal),
    Object {
        class: ClassId,
        fields: Vec<Ix>,
        exc: Option<Box<ExcNode>>,
    },
    Proc(Box<ProcNode>),
    /// A captured frame: its slots (`None`: one the block does not use,
    /// left out) and its parent.
    Frame {
        slots: Vec<Option<Ix>>,
        parent: Option<Ix>,
    },
    /// Not filled in yet (while exporting).
    Pending,
}

/// A shared allocation in transit (see `Node::MovedStr`).
struct Moved<T: ?Sized + crate::rc::Target>(SendRc<T>);

impl<T: ?Sized + crate::rc::Target> std::fmt::Debug for Moved<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Moved")
    }
}

impl<T: ?Sized + crate::rc::Target> Moved<T> {
    /// `rc` moved, when it is its allocation's only reference: marked
    /// shared, and with it what it refers to (nothing, for a string or
    /// bytes). Otherwise `rc` back.
    fn of(rc: Rc<T>) -> Result<Moved<T>, Rc<T>> {
        if Rc::strong_count(&rc) != 1 {
            return Err(rc);
        }
        Rc::mark_shared(&rc);
        count_move();
        Ok(Moved(SendRc::new(rc)))
    }
}

/// How many values crossed `Task.blocking` moved rather than copied
/// (`QUARZ_COUNT_COPIES` prints it at exit, after the copies).
static MOVED: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

fn count_move() {
    MOVED.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
}

pub fn moved() -> u64 {
    MOVED.load(std::sync::atomic::Ordering::Relaxed)
}

/// An exception's: its identity (`ExcInfo::id`), backtrace and cause.
#[derive(Debug)]
struct ExcNode {
    id: Option<u64>,
    backtrace: Option<Vec<String>>,
    cause: Option<Ix>,
}

#[derive(Debug)]
struct ProcNode {
    body: ProcBody,
    frame: Option<Ix>,
    self_val: Ix,
    destructure: Option<usize>,
    is_lambda: bool,
    tag: u64,
    method_block: Option<Ix>,
    method_tag: u64,
    file: u32,
}

#[derive(Debug)]
enum ProcBody {
    Func(FuncId),
    MethodName(
        String,
        Option<MethodId>,
        bool,
        Vec<(quarz_ir::RtType, MethodId)>,
    ),
    BoundMethod {
        recv: Ix,
        name: String,
        method: Option<MethodId>,
    },
}

impl Transfer {
    /// `nil` in transit.
    fn nil() -> Transfer {
        Transfer {
            nodes: vec![Node::Nil],
        }
    }
}

/// How the block ended on the helper thread.
pub enum WorkerExit {
    Value(Transfer),
    Raise(Transfer),
    Exit(i32),
    /// The thread could not run the block (out of descriptors for its
    /// poller): a `SystemCallError` with this message.
    Failed(String),
}

pub struct WorkerOutcome {
    pub exit: WorkerExit,
    /// What the block printed, written out by the caller afterwards.
    pub output: Vec<u8>,
}

// ----- export --------------------------------------------------------------------

/// What a node is exported from.
enum Job {
    /// A value, and how many levels down from it a part nothing else
    /// refers to may still be handed over whole (`whole`).
    Value(Value, u8),
    /// Frame `depth` of a closure's chain, keeping only the slots in
    /// `needed` (all of them when `None`).
    Frame(
        Rc<Frame>,
        Option<std::rc::Rc<std::collections::HashSet<(i64, u32)>>>,
        i64,
    ),
}

/// A node for `job`, filled in later: its index.
fn later(nodes: &mut Vec<Node>, jobs: &mut Vec<(Ix, Job)>, job: Job) -> Ix {
    let ix = nodes.len() as Ix;
    nodes.push(Node::Pending);
    jobs.push((ix, job));
    ix
}

/// The node of a value with no parts, if `v` is one.
#[inline(always)]
fn leaf(interp: &Interp, v: &Value) -> Option<Node> {
    Some(match v {
        Value::Nil => Node::Nil,
        Value::Bool(b) => Node::Bool(*b),
        Value::Int(i) => Node::Int(*i),
        Value::Float(f) => Node::Float(*f),
        Value::Symbol(s) => Node::Symbol(interp.symbol_name(*s).to_string()),
        Value::Class(c) => Node::Class(*c),
        Value::Duration(d) => Node::Duration(*d),
        Value::BigInt(b) => Node::BigInt(Box::new((**b).clone())),
        Value::Str(s) => Node::Str(s.to_string()),
        Value::Short(s) => Node::Str(s.as_str().to_string()),
        Value::Bytes(b) => Node::Bytes(b.to_vec()),
        Value::Time(t) => Node::Time(**t),
        _ => return None,
    })
}

/// The node of `v` when it has no parts, moving what it owns alone (a
/// string's or bytes' allocation); else `v` back.
fn owned_leaf(interp: &Interp, v: Value) -> Result<Node, Value> {
    let v = match v {
        Value::Str(s) => match Moved::of(s) {
            Ok(m) => return Ok(Node::MovedStr(m)),
            Err(s) => Value::Str(s),
        },
        Value::Bytes(b) => match Moved::of(b) {
            Ok(m) => return Ok(Node::MovedBytes(m)),
            Err(b) => Value::Bytes(b),
        },
        v => v,
    };
    leaf(interp, &v).ok_or(v)
}

/// A node for `v`: a leaf's at once, another's filled in later. (`v` is
/// given up: what only it refers to is moved, not copied.)
fn part(
    interp: &Interp,
    nodes: &mut Vec<Node>,
    jobs: &mut Vec<(Ix, Job)>,
    v: Value,
    whole: u8,
) -> Ix {
    match owned_leaf(interp, v) {
        Ok(node) => {
            nodes.push(node);
            (nodes.len() - 1) as Ix
        }
        Err(v) => later(nodes, jobs, Job::Value(v, whole)),
    }
}

/// `v` for another thread, exported from a work list (no recursion,
/// however deeply it is nested). `v` is given up: a part nothing else
/// refers to may be moved rather than copied (`Node::MovedStr`,
/// `Node::Ints`), so a caller that keeps using the value passes a clone,
/// which leaves every part referred to twice.
pub fn export(interp: &Interp, v: Value) -> Result<Transfer, Flow> {
    export_taking(interp, v, None)
}

/// A `Task.blocking` block for the helper thread, with the values taken
/// out of slots of its closure's frame (`frame`, now `nil` there: the
/// caller reads them no more, #478) exported in their place, given up.
pub fn export_block(
    interp: &Interp,
    block: Value,
    frame: Rc<Frame>,
    taken: Vec<(u32, Value)>,
) -> Result<Transfer, Flow> {
    export_taking(interp, block, Some((frame, taken)))
}

/// A block's frame, with the values taken out of its slots (#478).
pub type Taken = (Rc<Frame>, Vec<(u32, Value)>);

fn export_taking(interp: &Interp, v: Value, mut taken: Option<Taken>) -> Result<Transfer, Flow> {
    let mut nodes: Vec<Node> = Vec::new();
    let mut jobs: Vec<(Ix, Job)> = Vec::new();
    later(&mut nodes, &mut jobs, Job::Value(v, WHOLE_LEVELS));
    while let Some((ix, job)) = jobs.pop() {
        // (A node's parts are pushed in order and reversed below, so that
        // they are exported first to last, as the recursion did: of two
        // parts that cannot cross, the first is the one reported.)
        let start = jobs.len();
        let node = match job {
            Job::Value(v, whole) => export_value(interp, v, whole, &mut nodes, &mut jobs)?,
            Job::Frame(frame, needed, depth) => {
                // The block's own frame, with the values taken out of it.
                let mut given = match &taken {
                    Some((f, _)) if depth == 0 && Rc::ptr_eq(f, &frame) => {
                        taken.take().map(|(_, t)| t).unwrap_or_default()
                    }
                    _ => Vec::new(),
                };
                let mut slots = Vec::new();
                for (j, v) in frame.slots().iter().enumerate() {
                    let wanted = needed
                        .as_ref()
                        .is_none_or(|n| n.contains(&(depth, j as u32)));
                    let v = match given.iter().position(|(s, _)| *s == j as u32) {
                        Some(k) => given.swap_remove(k).1,
                        None => v.clone(),
                    };
                    slots
                        .push(wanted.then(|| part(interp, &mut nodes, &mut jobs, v, WHOLE_LEVELS)));
                }
                let parent = frame.parent.as_ref().map(|p| {
                    later(
                        &mut nodes,
                        &mut jobs,
                        Job::Frame(p.clone(), needed.clone(), depth + 1),
                    )
                });
                Node::Frame { slots, parent }
            }
        };
        nodes[ix as usize] = node;
        jobs[start..].reverse();
    }
    Ok(Transfer { nodes })
}

/// The node of `v`, its parts left for later.
fn export_value(
    interp: &Interp,
    v: Value,
    whole: u8,
    nodes: &mut Vec<Node>,
    jobs: &mut Vec<(Ix, Job)>,
) -> Result<Node, Flow> {
    let v = match owned_leaf(interp, v) {
        Ok(node) => return Ok(node),
        Err(v) => v,
    };
    if whole > 0 && movable_whole(interp, &v) {
        count_move();
        return Ok(Node::Whole(SharedValue::new(v)));
    }
    let v = match v {
        Value::Array(items) => {
            return Ok(export_array(
                interp,
                items,
                whole.saturating_sub(1),
                nodes,
                jobs,
            ))
        }
        v => v,
    };
    let mut p = |v: &Value| part(interp, nodes, jobs, v.clone(), 0);
    Ok(match &v {
        Value::Hash(h) => Node::Hash(h.as_map().iter().map(|(k, v)| (p(k), p(v))).collect()),
        Value::Set(s) => Node::Set(s.iter().map(&mut p).collect()),
        Value::Range(r) => Node::Range {
            lo: p(&r.lo),
            hi: p(&r.hi),
            exclusive: r.exclusive,
        },
        Value::Regexp(r) => Node::Regexp(Box::new((r.source.clone(), r.flags.clone()))),
        Value::Object(o) if crate::deinit::has(o.class) => {
            // Copied to the helper thread, it would be released twice.
            return Err(interp.raise(
                interp.program.exc.argument_error,
                &format!(
                    "an instance of {} cannot cross Task.blocking: its class defines \
                     `deinitialize`, and the other thread would get a copy",
                    interp.class_name(&v)
                ),
            ));
        }
        Value::Object(o) => {
            // An exception keeps its identity across: one never raised
            // gets it recorded now (`natives::raised` does so too).
            if o.exc_info().is_none() && interp.program.world.class(o.class).is_exception {
                o.init_exc(crate::value::ExcInfo::new(None, None));
            }
            let fields = o.fields().iter().map(&mut p).collect();
            let id = o.exc_info().map(|i| i.id);
            let backtrace = o.backtrace().map(|b| b.to_vec());
            let cause = o.cause().map(|c| p(&c));
            Node::Object {
                class: o.class,
                fields,
                exc: (id.is_some() || backtrace.is_some() || cause.is_some()).then(|| {
                    Box::new(ExcNode {
                        id,
                        backtrace,
                        cause,
                    })
                }),
            }
        }
        Value::Proc(c) => {
            // Only the captured variables the block (and the blocks inside
            // it) actually use travel; the rest of the frame chain is
            // left out, so an unrelated channel in scope is no obstacle.
            let needed = match &c.body {
                ClosureBody::Func(id) => Some(std::rc::Rc::new(needed_slots(interp, *id))),
                _ => None,
            };
            let body = match &c.body {
                ClosureBody::Func(id) => ProcBody::Func(*id),
                ClosureBody::MethodName(n, _, m, d, among) => ProcBody::MethodName(
                    n.to_string(),
                    *m,
                    *d,
                    among.as_deref().cloned().unwrap_or_default(),
                ),
                ClosureBody::BoundMethod { recv, name, method } => ProcBody::BoundMethod {
                    recv: p(recv),
                    name: name.to_string(),
                    method: *method,
                },
                ClosureBody::Native(_) => return Err(not_transferable(interp, &v)),
            };
            // (In the recursion's order: the receiver, the frame, `self`,
            // the method's block.)
            let frame = c
                .frame
                .as_ref()
                .map(|f| later(nodes, jobs, Job::Frame(f.clone(), needed, 0)));
            let self_val = part(interp, nodes, jobs, c.self_val.clone(), 0);
            let method_block = c
                .method_block
                .as_ref()
                .map(|b| part(interp, nodes, jobs, b.clone(), 0));
            Node::Proc(Box::new(ProcNode {
                body,
                frame,
                self_val,
                destructure: c.destructure,
                is_lambda: c.is_lambda,
                tag: c.tag,
                method_block,
                method_tag: c.method_tag,
                file: c.file,
            }))
        }
        _ => return Err(not_transferable(interp, &v)),
    })
}

/// How many levels down from a value exported (a block's result, a
/// capture) a part may still be handed over whole: the check walks the
/// part, so a bound keeps the export linear in the value's size however
/// deep it is (#465).
const WHOLE_LEVELS: u8 = 3;

/// Whether `v` can be handed to the other thread whole (`Node::Whole`):
/// every allocation in it referred to once (by `v`, given up, or by its
/// container), and nothing in it bound to this thread's interpreter or
/// to its copy semantics: no symbol (interned per interpreter), no
/// procedure, regular expression or exception, no object but a `data`
/// value or an enum variant with data (the runtime does not know which
/// classes are immutable; a variant without data is its interpreter's
/// singleton), no object whose class defines `deinitialize` or a `hash`
/// or `==` of its own (`object_movable`). A flat walk.
fn movable_whole(interp: &Interp, v: &Value) -> bool {
    // (The walk holds a clone of each value it looks at: one referred to
    // once otherwise is referred to twice while looked at.)
    let unique = |n: usize| n == 2;
    let mut work: Vec<Value> = vec![v.clone()];
    while let Some(v) = work.pop() {
        match &v {
            Value::Nil
            | Value::Bool(_)
            | Value::Int(_)
            | Value::Float(_)
            | Value::Class(_)
            | Value::Duration(_)
            | Value::Short(_) => {}
            Value::Str(s) if unique(Rc::strong_count(s)) => {}
            Value::Bytes(b) if unique(Rc::strong_count(b)) => {}
            Value::BigInt(b) if unique(Rc::strong_count(b)) => {}
            Value::Time(t) if unique(Rc::strong_count(t)) => {}
            Value::Array(a) if unique(Rc::strong_count(a)) => match &**a {
                ArrayData::Ints(_) | ArrayData::Floats(_) => {}
                data => work.extend(data.iter()),
            },
            Value::Hash(h) if unique(Rc::strong_count(h)) => {
                if let HashData::Values(map) = &**h {
                    for (k, x) in map.iter() {
                        work.push(k.clone());
                        work.push(x.clone());
                    }
                }
            }
            Value::Set(s) if unique(Rc::strong_count(s)) => work.extend(s.iter().cloned()),
            Value::Range(r) if unique(Rc::strong_count(r)) => {
                work.push(r.lo.clone());
                work.push(r.hi.clone());
            }
            Value::Object(o) if unique(Rc::strong_count(o)) && object_movable(interp, o) => {
                work.extend(o.fields())
            }
            _ => return false,
        }
    }
    true
}

/// An object `movable_whole` may hand over: a `data` value or a variant
/// with data, no `deinitialize`, and no `hash` or `==` of its own (a
/// hash or set holding it, at any depth of a key, is rebuilt by the copy,
/// which calls them on the receiving side).
fn object_movable(interp: &Interp, o: &Rc<Object>) -> bool {
    use quarz_ir::RtClassKind;
    let class = interp.program.world.class(o.class);
    matches!(class.kind, RtClassKind::Data | RtClassKind::Variant)
        && !class.is_exception
        && !crate::deinit::has(o.class)
        && crate::keys::of(o.class).is_none()
        && o.field_count() > 0
}

/// Whether `v` can cross to the helper thread whole: nothing in it that
/// `export` refuses (an object whose class defines `deinitialize`, a
/// mutable value, a procedure, a native), walked without recursion. A
/// capture is taken out of its frame to be moved only then: taken and
/// refused, it would be released at once, a `deinitialize` running early
/// (#478).
pub fn crosses(interp: &Interp, v: &Value) -> bool {
    let mut work: Vec<Value> = vec![v.clone()];
    while let Some(v) = work.pop() {
        if leaf(interp, &v).is_some() {
            continue;
        }
        match &v {
            Value::Array(items) => {
                if let ArrayData::Values(_) | ArrayData::Objects(_) = &**items {
                    work.extend(items.iter());
                }
            }
            Value::Hash(h) => {
                for (k, x) in h.as_map().iter() {
                    work.push(k.clone());
                    work.push(x.clone());
                }
            }
            Value::Set(s) => work.extend(s.iter().cloned()),
            Value::Range(r) => {
                work.push(r.lo.clone());
                work.push(r.hi.clone());
            }
            Value::Regexp(_) => {}
            Value::Object(o) => {
                if crate::deinit::has(o.class) {
                    return false;
                }
                work.extend(o.fields());
                work.extend(o.cause());
            }
            _ => return false,
        }
    }
    true
}

/// The node of an array: its storage moved out when nothing else refers
/// to it (the words of an `Array[Int]`/`Array[Float]` as they are; the
/// elements of another, each given up in turn), copied otherwise.
fn export_array(
    interp: &Interp,
    mut items: Rc<ArrayData>,
    whole: u8,
    nodes: &mut Vec<Node>,
    jobs: &mut Vec<(Ix, Job)>,
) -> Node {
    if let Some(data) = Rc::get_mut(&mut items) {
        return match std::mem::replace(data, ArrayData::Values(Vec::new())) {
            ArrayData::Ints(words) => {
                count_move();
                Node::Ints(words)
            }
            ArrayData::Floats(words) => {
                count_move();
                Node::Floats(words)
            }
            ArrayData::Values(vs) => Node::Array(
                vs.into_iter()
                    .map(|v| part(interp, nodes, jobs, v, whole))
                    .collect(),
            ),
            ArrayData::Objects(os) => Node::Array(
                os.into_iter()
                    .map(|o| part(interp, nodes, jobs, Value::Object(o), whole))
                    .collect(),
            ),
        };
    }
    match &*items {
        ArrayData::Ints(words) => Node::Ints(words.clone()),
        ArrayData::Floats(words) => Node::Floats(words.clone()),
        data => Node::Array(
            data.iter()
                .map(|v| part(interp, nodes, jobs, v, 0))
                .collect(),
        ),
    }
}

/// The `(depth, slot)` pairs of the closure's frame chain that the
/// function `fid` and the blocks created inside it read or write. Depth 0
/// is the closure's own captured frame.
fn needed_slots(interp: &Interp, fid: FuncId) -> std::collections::HashSet<(i64, u32)> {
    let mut needed = std::collections::HashSet::new();
    let mut visited = std::collections::HashSet::new();
    // (function, offset): a frame depth seen from the function's own
    // frame, minus the frames the function and its enclosing blocks own
    // themselves, gives the index in the exported chain.
    let mut work: Vec<(FuncId, i64)> = vec![(fid, 0)];
    let funcs = interp.funcs.borrow();
    while let Some((id, base)) = work.pop() {
        if !visited.insert((id, base)) {
            continue;
        }
        let Some(f) = funcs.get(id as usize) else {
            continue;
        };
        let own = if f.frame_size > 0 { 1 } else { 0 };
        for &(depth, slot) in &f.facts.uses {
            let index = depth as i64 - own + base;
            if index >= 0 {
                needed.insert((index, slot));
            }
        }
        for &func in &f.facts.blocks {
            work.push((func, base - own));
        }
    }
    needed
}

/// An exception raised on the helper thread, for the caller: when it
/// holds what cannot cross, the exception that says so instead.
fn export_raised(interp: &Interp, e: Value) -> Transfer {
    match export(interp, e) {
        Ok(t) => t,
        Err(Flow::Raise(why)) => export(interp, why).unwrap_or_else(|_| Transfer::nil()),
        Err(_) => Transfer::nil(),
    }
}

fn not_transferable(interp: &Interp, v: &Value) -> Flow {
    interp.raise(
        interp.program.exc.argument_error,
        &format!(
            "a {} cannot be used in Task.blocking: it belongs to the calling thread \
             (only immutable values are copied to the helper thread)",
            interp.class_name(v)
        ),
    )
}

// ----- import --------------------------------------------------------------------

/// What a node was imported as.
enum Built {
    Value(Value),
    Frame(Rc<Frame>),
}

/// Push the parts of a node on `work` to be built first to last, in the
/// order the recursion imported them; whether it has any.
fn push_parts(node: &Node, work: &mut Vec<(Ix, bool)>) -> bool {
    let start = work.len();
    let mut push = |ix: Ix| work.push((ix, false));
    match node {
        Node::Array(items) | Node::Set(items) => items.iter().copied().for_each(&mut push),
        Node::Hash(pairs) => pairs.iter().for_each(|(k, v)| {
            push(*k);
            push(*v);
        }),
        Node::Range { lo, hi, .. } => {
            push(*lo);
            push(*hi);
        }
        Node::Object { fields, exc, .. } => {
            fields.iter().copied().for_each(&mut push);
            exc.iter().flat_map(|e| e.cause).for_each(&mut push);
        }
        Node::Proc(c) => {
            if let ProcBody::BoundMethod { recv, .. } = &c.body {
                push(*recv);
            }
            c.frame.iter().copied().for_each(&mut push);
            push(c.self_val);
            c.method_block.iter().copied().for_each(&mut push);
        }
        Node::Frame { slots, parent } => {
            parent.iter().copied().for_each(&mut push);
            slots.iter().flatten().copied().for_each(&mut push);
        }
        _ => {}
    }
    // (Popped last first: reversed, built first to last.)
    work[start..].reverse();
    work.len() > start
}

/// The value of a transfer, without recursion. When it holds an instance
/// of a class with its own `hash` or `==` (called as a hash or set holding
/// it is rebuilt), the nodes are imported depth first, each after its
/// parts, first to last, so that those run in nearly the recursion's
/// order (one difference: a hash's pairs are all built before they are
/// inserted, where the recursion inserted each pair before building the
/// next); otherwise from the last node back.
pub fn import(interp: &Interp, t: Transfer) -> Value {
    let mut nodes = t.nodes;
    let mut built: Vec<Option<Built>> = (0..nodes.len()).map(|_| None).collect();
    let custom = crate::keys::any()
        && nodes
            .iter()
            .any(|n| matches!(n, Node::Object { class, .. } if crate::keys::of(*class).is_some()));
    if !custom {
        // No value here has a `hash` or `==` of its own: nothing the
        // import runs can tell the order, and from the last node back each
        // node's parts (after it) are built before it.
        for ix in (0..nodes.len()).rev() {
            build(interp, &mut nodes, &mut built, ix);
        }
        return value(&mut built, 0);
    }
    // (node, whether its parts are built)
    let mut work: Vec<(Ix, bool)> = vec![(0, false)];
    while let Some((ix, ready)) = work.pop() {
        if !ready {
            // (A node with no parts is built at once.)
            work.push((ix, true));
            let at = work.len() - 1;
            if push_parts(&nodes[ix as usize], &mut work) {
                continue;
            }
            work.truncate(at);
        }
        build(interp, &mut nodes, &mut built, ix as usize);
    }
    value(&mut built, 0)
}

/// Build node `ix`, its parts built.
fn build(interp: &Interp, nodes: &mut [Node], built: &mut [Option<Built>], ix: usize) {
    let node = std::mem::replace(&mut nodes[ix], Node::Pending);
    let b = match node {
        Node::Frame { slots, parent } => {
            let slots: Vec<Value> = slots
                .into_iter()
                .map(|s| s.map(|s| value(built, s)).unwrap_or(Value::Nil))
                .collect();
            let parent = parent.and_then(|p| frame(built, p));
            Built::Frame(Frame::from_slots(slots.into_iter().collect(), parent))
        }
        node => Built::Value(import_node(interp, node, built)),
    };
    built[ix] = Some(b);
}

/// The value built for node `ix`. (Each part belongs to one node: taken
/// once.)
fn value(built: &mut [Option<Built>], ix: Ix) -> Value {
    match built[ix as usize].take() {
        Some(Built::Value(v)) => v,
        _ => Value::Nil,
    }
}

/// The frame built for node `ix`.
fn frame(built: &mut [Option<Built>], ix: Ix) -> Option<Rc<Frame>> {
    match built[ix as usize].take() {
        Some(Built::Frame(f)) => Some(f),
        _ => None,
    }
}

/// A node's value, its parts already built.
fn import_node(interp: &Interp, node: Node, built: &mut [Option<Built>]) -> Value {
    match node {
        Node::Nil | Node::Pending | Node::Frame { .. } => Value::Nil,
        Node::Bool(b) => Value::Bool(b),
        Node::Int(i) => Value::Int(i),
        Node::Float(f) => Value::Float(f),
        Node::Symbol(s) => Value::Symbol(interp.intern(&s)),
        Node::Class(c) => Value::Class(c),
        Node::Duration(d) => Value::Duration(d),
        Node::BigInt(b) => integer(*b),
        Node::Str(s) => Value::string(s),
        Node::MovedStr(m) => Value::Str(m.0.into_inner()),
        Node::Whole(v) => v.into_inner(),
        Node::MovedBytes(m) => Value::Bytes(m.0.into_inner()),
        Node::Ints(words) if words.is_empty() => Value::empty_array(),
        Node::Ints(words) => Value::ints(words),
        Node::Floats(words) if words.is_empty() => Value::empty_array(),
        Node::Floats(words) => Value::floats(words),
        Node::Array(items) => Value::array(items.into_iter().map(|i| value(built, i)).collect()),
        Node::Hash(pairs) => Value::Hash(Rc::new(crate::value::HashData::from(
            pairs
                .into_iter()
                .map(|(k, v)| (value(built, k), value(built, v)))
                .collect::<crate::value::ValueMap>(),
        ))),
        Node::Set(items) => Value::Set(Rc::new(
            items.into_iter().map(|i| value(built, i)).collect(),
        )),
        Node::Range { lo, hi, exclusive } => Value::Range(Rc::new(RangeVal {
            lo: value(built, lo),
            hi: value(built, hi),
            exclusive,
        })),
        Node::Regexp(r) => interp.make_regexp(&r.0, &r.1).unwrap_or(Value::Nil),
        Node::Bytes(b) => Value::bytes(b),
        Node::Time(t) => Value::Time(Rc::new(t)),
        Node::Object { class, fields, exc } => {
            let (id, backtrace, cause) = match exc {
                Some(e) => (e.id, e.backtrace, e.cause),
                None => (None, None, None),
            };
            let fields: Fields = fields.into_iter().map(|i| value(built, i)).collect();
            // Variants without data are singletons.
            if fields.is_empty() {
                let info = interp.program.world.class(class);
                if info.kind == quarz_ir::RtClassKind::Variant {
                    return interp.variant_singleton(class);
                }
            }
            let cause = cause.map(|c| value(built, c));
            Value::Object({
                let o = Object::new(class, fields);
                // A raised exception stays the same one (its id).
                if let Some(id) = id {
                    let info = crate::value::ExcInfo::with_id(id, backtrace.map(Rc::new), cause);
                    o.init_exc(info);
                }
                o
            })
        }
        Node::Proc(c) => {
            let ProcNode {
                body,
                frame: f,
                self_val,
                destructure,
                is_lambda,
                tag,
                method_block,
                method_tag,
                file,
            } = *c;
            Value::Proc(Rc::new(Closure {
                body: match body {
                    ProcBody::Func(id) => ClosureBody::Func(id),
                    ProcBody::MethodName(n, m, d, among) => ClosureBody::MethodName(
                        Rc::from(n),
                        std::cell::Cell::new(None),
                        m,
                        d,
                        (!among.is_empty()).then(|| Rc::new(among)),
                    ),
                    ProcBody::BoundMethod { recv, name, method } => ClosureBody::BoundMethod {
                        recv: value(built, recv),
                        name: Rc::from(name),
                        method,
                    },
                },
                frame: f.and_then(|f| frame(built, f)),
                self_val: value(built, self_val),
                destructure,
                is_lambda,
                tag,
                method_block: method_block.map(|b| value(built, b)),
                method_tag,
                file,
            }))
        }
    }
}

// ----- the helper thread's interpreter ------------------------------------------

/// Output of the helper interpreter, handed back with the result.
struct SyncBuffer(Arc<Mutex<Vec<u8>>>);

impl std::io::Write for SyncBuffer {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.0.lock().unwrap().extend_from_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

/// A helper thread's interpreter: the image it was built from (kept, so
/// that another image cannot come at its address and be taken for it),
/// the interpreter, and its output buffer.
type Worker = (Arc<ProgramImage>, std::rc::Rc<Interp>, Arc<Mutex<Vec<u8>>>);

thread_local! {
    /// The interpreter a helper thread keeps between jobs.
    static WORKER: RefCell<Option<Worker>> = const { RefCell::new(None) };
}

/// For `exit!` on a helper thread: write what the block printed so far to
/// the process's standard output, which the caller would have written on
/// its return. Nothing on another thread.
pub fn write_worker_output() {
    WORKER.with(|w| {
        if let Some((_, interp, out)) = &*w.borrow() {
            interp.flush();
            let bytes = std::mem::take(&mut *out.lock().unwrap_or_else(|e| e.into_inner()));
            use std::io::Write;
            let mut stdout = std::io::stdout();
            let _ = stdout.write_all(&bytes);
            let _ = stdout.flush();
        }
    });
}

/// Run an exported block to completion on the current (helper) thread.
pub fn run_on_thread(
    image: Arc<ProgramImage>,
    argv: Vec<String>,
    closure: Transfer,
) -> WorkerOutcome {
    // Another image's interpreter goes first (out of the borrow): what it
    // releases is queued under its own classes, not the next program's
    // (`deinit::set_classes`).
    let old = WORKER.with(|w| {
        let mut w = w.borrow_mut();
        match &*w {
            Some((k, _, _)) if !Arc::ptr_eq(k, &image) => w.take(),
            _ => None,
        }
    });
    drop(old);
    let made: std::io::Result<_> = WORKER.with(|w| {
        let mut w = w.borrow_mut();
        match &*w {
            Some((k, i, out)) if Arc::ptr_eq(k, &image) => Ok((i.clone(), out.clone())),
            _ => {
                let out = Arc::new(Mutex::new(Vec::new()));
                let state = SharedState::try_new(Box::new(SyncBuffer(out.clone())))?;
                let interp = image.load(argv, state);
                {
                    let mut compiled = interp.compiled.borrow_mut();
                    for (i, f) in image.compiled.iter().enumerate() {
                        if i < compiled.len() {
                            compiled[i] = *f;
                        }
                    }
                }
                *w = Some((image.clone(), interp.clone(), out.clone()));
                Ok((interp, out))
            }
        }
    });
    let (interp, output) = match made {
        Ok(made) => made,
        Err(e) => {
            return WorkerOutcome {
                exit: WorkerExit::Failed(format!("cannot create the IO poller: {e}")),
                output: Vec::new(),
            }
        }
    };
    let exit = interp.run_closure(closure);
    let exit = match exit {
        // The block's result and exception are given up: what only they
        // refer to moves to the caller's thread (#468).
        Ok(v) => match export(&interp, v) {
            Ok(t) => WorkerExit::Value(t),
            Err(Flow::Raise(e)) => WorkerExit::Raise(export_raised(&interp, e)),
            Err(_) => WorkerExit::Exit(1),
        },
        Err(Flow::Raise(e)) => WorkerExit::Raise(export_raised(&interp, e)),
        Err(Flow::Exit(code)) => WorkerExit::Exit(code),
        Err(_) => WorkerExit::Exit(1),
    };
    // What did not cross (an object with a `deinitialize`, refused) was
    // released here: its `deinitialize` runs now, with this job's output.
    if crate::deinit::pending() {
        interp.run_deinitializers();
    }
    interp.flush();
    let output = std::mem::take(&mut *output.lock().unwrap());
    WorkerOutcome { exit, output }
}

impl Interp {
    /// A snapshot of the loaded program for helper threads (cached until
    /// more functions are loaded).
    pub fn image(&self) -> Arc<ProgramImage> {
        let n = self.funcs.borrow().len();
        if let Some((k, image)) = &*self.image_cache.borrow() {
            if *k == n {
                return image.clone();
            }
        }
        let image = Arc::new(ProgramImage {
            world: self.program.world.clone(),
            lazy: self.program.lazy.clone(),
            functions: self.funcs.borrow().iter().map(|f| (**f).clone()).collect(),
            bodies: crate::vm::INTERPRETER.get().and_then(|i| (i.export)(self)),
            units: self.program.units.clone(),
            compiled: self.compiled.borrow().clone(),
        });
        *self.image_cache.borrow_mut() = Some((n, image.clone()));
        image
    }

    /// Import a block and call it as the root task of this interpreter,
    /// and run the scheduler until it finishes. The import is the task's:
    /// rebuilding a captured hash or set calls its keys' own `hash` and
    /// `==` (`crate::keys`), which may need a task (and what they raise is
    /// the block's to raise).
    pub fn run_closure(self: &std::rc::Rc<Interp>, closure: Transfer) -> Result<Value, Flow> {
        let me = self.clone();
        let body: Box<dyn FnOnce() -> TaskExit> = Box::new(move || {
            let closure = import(&me, closure);
            match me.call_block(&closure, smallvec::smallvec![]) {
                // A `SystemExit` goes back to the caller of `Task.blocking`,
                // to be raised there (its `ensure`s, its `rescue`).
                Err(Flow::Raise(e)) => TaskExit::Result(TaskResult::Error(e)),
                r => crate::interp::task_exit(&me, r),
            }
        });
        let root =
            self.sched
                .borrow_mut()
                .spawn(body, None, "blocking".to_string(), 256 * 1024 * 1024);
        self.set_root(&root);
        let code = self.run_loop_with(&root, false);
        // The tasks the block spawned and left: cancelled and run to their
        // end now, as a scope's would be (the interpreter is kept for later
        // blocks, which would run them otherwise).
        if root.is_done() {
            if let Some(code) = self.cancel_leftovers() {
                return Err(Flow::Exit(code));
            }
        }
        // An `exit` in a task the block spawned and nobody awaited, which
        // the block ended before raising: the caller raises it.
        if let Some(status) = root.take_exit().or_else(|| self.take_exit_request()) {
            if root.is_done() {
                return Err(Flow::Raise(crate::natives::system_exit(
                    self, status, "exit",
                )));
            }
        }
        if !root.is_done() {
            return Err(Flow::Exit(code));
        }
        let result = root.result();
        match result {
            Some(TaskResult::Value(v)) => Ok(v),
            Some(TaskResult::Error(e)) => Err(Flow::Raise(e)),
            None => Err(Flow::Exit(code)),
        }
    }
}
