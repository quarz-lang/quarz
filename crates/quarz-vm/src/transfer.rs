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

use crate::rc::Rc;
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

/// A value in transit between threads.
#[derive(Clone, Debug)]
pub enum Transfer {
    Nil,
    Bool(bool),
    Int(i64),
    Float(f64),
    Symbol(String),
    Class(ClassId),
    Duration(i64),
    BigInt(BigInt),
    Str(String),
    Array(Vec<Transfer>),
    Hash(Vec<(Transfer, Transfer)>),
    Set(Vec<Transfer>),
    Range {
        lo: Box<Transfer>,
        hi: Box<Transfer>,
        exclusive: bool,
    },
    Regexp {
        source: String,
        flags: String,
    },
    Bytes(Vec<u8>),
    Time(TimeVal),
    Object {
        class: ClassId,
        fields: Vec<Transfer>,
        /// A raised exception's identity (`ExcInfo::id`).
        id: Option<u64>,
        backtrace: Option<Vec<String>>,
        cause: Option<Box<Transfer>>,
    },
    Proc {
        body: ProcBody,
        frame: Option<Box<TFrame>>,
        self_val: Box<Transfer>,
        destructure: Option<usize>,
        is_lambda: bool,
        tag: u64,
        method_block: Option<Box<Transfer>>,
        method_tag: u64,
        file: u32,
    },
}

#[derive(Clone, Debug)]
pub enum ProcBody {
    Func(FuncId),
    MethodName(String, Option<MethodId>),
    BoundMethod { recv: Box<Transfer>, name: String },
}

#[derive(Clone, Debug)]
pub struct TFrame {
    pub slots: Vec<Transfer>,
    pub parent: Option<Box<TFrame>>,
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

pub fn export(interp: &Interp, v: &Value) -> Result<Transfer, Flow> {
    Ok(match v {
        Value::Nil => Transfer::Nil,
        Value::Bool(b) => Transfer::Bool(*b),
        Value::Int(i) => Transfer::Int(*i),
        Value::Float(f) => Transfer::Float(*f),
        Value::Symbol(s) => Transfer::Symbol(interp.symbol_name(*s).to_string()),
        Value::Class(c) => Transfer::Class(*c),
        Value::Duration(d) => Transfer::Duration(*d),
        Value::BigInt(b) => Transfer::BigInt((**b).clone()),
        Value::Str(s) => Transfer::Str(s.to_string()),
        Value::Short(s) => Transfer::Str(s.as_str().to_string()),
        Value::Array(items) => Transfer::Array(export_all(interp, items.values().iter())?),
        Value::Hash(h) => {
            let mut out = Vec::with_capacity(h.len());
            for (k, v) in h.as_map().iter() {
                out.push((export(interp, k)?, export(interp, v)?));
            }
            Transfer::Hash(out)
        }
        Value::Set(s) => Transfer::Set(export_all(interp, s.iter())?),
        Value::Range(r) => Transfer::Range {
            lo: Box::new(export(interp, &r.lo)?),
            hi: Box::new(export(interp, &r.hi)?),
            exclusive: r.exclusive,
        },
        Value::Regexp(r) => Transfer::Regexp {
            source: r.source.clone(),
            flags: r.flags.clone(),
        },
        Value::Bytes(b) => Transfer::Bytes(b.to_vec()),
        Value::Time(t) => Transfer::Time(**t),
        Value::Object(o) if crate::deinit::has(o.class) => {
            // Copied to the helper thread, it would be released twice.
            return Err(interp.raise(
                interp.program.exc.argument_error,
                &format!(
                    "an instance of {} cannot cross Task.blocking: its class defines \
                     `deinitialize`, and the other thread would get a copy",
                    interp.class_name(v)
                ),
            ));
        }
        Value::Object(o) => Transfer::Object {
            class: o.class,
            fields: export_all(interp, o.fields().iter())?,
            id: {
                // An exception keeps its identity across: one never raised
                // gets it recorded now (`natives::raised` does so too).
                if o.exc_info().is_none() && interp.program.world.class(o.class).is_exception {
                    o.init_exc(crate::value::ExcInfo::new(None, None));
                }
                o.exc_info().map(|i| i.id)
            },
            backtrace: o.backtrace().map(|b| b.to_vec()),
            cause: match o.cause() {
                Some(c) => Some(Box::new(export(interp, &c)?)),
                None => None,
            },
        },
        Value::Proc(c) => {
            // Only the captured variables the block (and the blocks inside
            // it) actually use travel; the rest of the frame chain is
            // left out, so an unrelated channel in scope is no obstacle.
            let needed = match &c.body {
                ClosureBody::Func(id) => Some(needed_slots(interp, *id)),
                _ => None,
            };
            let body = match &c.body {
                ClosureBody::Func(id) => ProcBody::Func(*id),
                ClosureBody::MethodName(n, _, m) => ProcBody::MethodName(n.to_string(), *m),
                ClosureBody::BoundMethod { recv, name } => ProcBody::BoundMethod {
                    recv: Box::new(export(interp, recv)?),
                    name: name.to_string(),
                },
                ClosureBody::Native(_) => return Err(not_transferable(interp, v)),
            };
            Transfer::Proc {
                body,
                frame: match &c.frame {
                    Some(f) => Some(Box::new(export_frame(interp, f, needed.as_ref(), 0)?)),
                    None => None,
                },
                self_val: Box::new(export(interp, &c.self_val)?),
                destructure: c.destructure,
                is_lambda: c.is_lambda,
                tag: c.tag,
                method_block: match &c.method_block {
                    Some(b) => Some(Box::new(export(interp, b)?)),
                    None => None,
                },
                method_tag: c.method_tag,
                file: c.file,
            }
        }
        _ => return Err(not_transferable(interp, v)),
    })
}

fn export_all<'a>(
    interp: &Interp,
    items: impl Iterator<Item = &'a Value>,
) -> Result<Vec<Transfer>, Flow> {
    items.map(|v| export(interp, v)).collect()
}

/// Export frame `depth` of a chain, keeping only the slots in `needed`
/// (all of them when `None`).
fn export_frame(
    interp: &Interp,
    frame: &Frame,
    needed: Option<&std::collections::HashSet<(i64, u32)>>,
    depth: i64,
) -> Result<TFrame, Flow> {
    let mut slots = Vec::new();
    for (j, v) in frame.slots().iter().enumerate() {
        let wanted = needed.is_none_or(|n| n.contains(&(depth, j as u32)));
        slots.push(if wanted {
            export(interp, v)?
        } else {
            Transfer::Nil
        });
    }
    Ok(TFrame {
        slots,
        parent: match &frame.parent {
            Some(p) => Some(Box::new(export_frame(interp, p, needed, depth + 1)?)),
            None => None,
        },
    })
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
fn export_raised(interp: &Interp, e: &Value) -> Transfer {
    match export(interp, e) {
        Ok(t) => t,
        Err(Flow::Raise(why)) => export(interp, &why).unwrap_or(Transfer::Nil),
        Err(_) => Transfer::Nil,
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

pub fn import(interp: &Interp, t: Transfer) -> Value {
    match t {
        Transfer::Nil => Value::Nil,
        Transfer::Bool(b) => Value::Bool(b),
        Transfer::Int(i) => Value::Int(i),
        Transfer::Float(f) => Value::Float(f),
        Transfer::Symbol(s) => Value::Symbol(interp.intern(&s)),
        Transfer::Class(c) => Value::Class(c),
        Transfer::Duration(d) => Value::Duration(d),
        Transfer::BigInt(b) => integer(b),
        Transfer::Str(s) => Value::string(s),
        Transfer::Array(items) => Value::array(import_all(interp, items)),
        Transfer::Hash(pairs) => Value::Hash(Rc::new(crate::value::HashData::from(
            pairs
                .into_iter()
                .map(|(k, v)| (import(interp, k), import(interp, v)))
                .collect::<crate::value::ValueMap>(),
        ))),
        Transfer::Set(items) => {
            Value::Set(Rc::new(import_all(interp, items).into_iter().collect()))
        }
        Transfer::Range { lo, hi, exclusive } => Value::Range(Rc::new(RangeVal {
            lo: import(interp, *lo),
            hi: import(interp, *hi),
            exclusive,
        })),
        Transfer::Regexp { source, flags } => {
            interp.make_regexp(&source, &flags).unwrap_or(Value::Nil)
        }
        Transfer::Bytes(b) => Value::bytes(b),
        Transfer::Time(t) => Value::Time(Rc::new(t)),
        Transfer::Object {
            class,
            fields,
            id,
            backtrace,
            cause,
        } => {
            let fields: Fields = import_all(interp, fields).into_iter().collect();
            // Variants without data are singletons.
            if fields.is_empty() {
                let info = interp.program.world.class(class);
                if info.kind == quarz_ir::RtClassKind::Variant {
                    return interp.variant_singleton(class);
                }
            }
            Value::Object({
                let o = Object::new(class, fields);
                // A raised exception stays the same one (its id).
                if let Some(id) = id {
                    let info = crate::value::ExcInfo::with_id(
                        id,
                        backtrace.map(Rc::new),
                        cause.map(|c| import(interp, *c)),
                    );
                    o.init_exc(info);
                }
                o
            })
        }
        Transfer::Proc {
            body,
            frame,
            self_val,
            destructure,
            is_lambda,
            tag,
            method_block,
            method_tag,
            file,
        } => Value::Proc(Rc::new(Closure {
            body: match body {
                ProcBody::Func(id) => ClosureBody::Func(id),
                ProcBody::MethodName(n, m) => {
                    ClosureBody::MethodName(Rc::from(n), std::cell::Cell::new(None), m)
                }
                ProcBody::BoundMethod { recv, name } => ClosureBody::BoundMethod {
                    recv: import(interp, *recv),
                    name: Rc::from(name),
                },
            },
            frame: frame.map(|f| import_frame(interp, *f)),
            self_val: import(interp, *self_val),
            destructure,
            is_lambda,
            tag,
            method_block: method_block.map(|b| import(interp, *b)),
            method_tag,
            file,
        })),
    }
}

fn import_all(interp: &Interp, items: Vec<Transfer>) -> Vec<Value> {
    items.into_iter().map(|t| import(interp, t)).collect()
}

fn import_frame(interp: &Interp, f: TFrame) -> Rc<Frame> {
    let parent = f.parent.map(|p| import_frame(interp, *p));
    Frame::from_slots(import_all(interp, f.slots).into_iter().collect(), parent)
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
        Ok(v) => match export(&interp, &v) {
            Ok(t) => WorkerExit::Value(t),
            Err(Flow::Raise(e)) => WorkerExit::Raise(export_raised(&interp, &e)),
            Err(_) => WorkerExit::Exit(1),
        },
        Err(Flow::Raise(e)) => WorkerExit::Raise(export_raised(&interp, &e)),
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
