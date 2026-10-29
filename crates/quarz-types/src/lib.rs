//! Name resolution and type checking for Quarz.
//!
//! [`check_units`] takes the parsed prelude and the user's compilation
//! units (files, dependencies first) and produces a [`Checked`] program:
//! the world of classes and methods, plus side tables keyed by AST node
//! that the evaluator uses (types, call targets, variable slots).

use std::path::{Path, PathBuf};

pub mod cache;
pub mod check;
pub mod declare;
pub mod init;
pub mod load;
pub mod patterns;
mod reloc;
pub mod types;
mod unit;
pub mod world;

use quarz_syntax::ast::{Expr, ExprKind, Program};
use quarz_syntax::{parse_with_bases, Diagnostic, SourceFile};

pub use check::{BlockPass, CallTarget, ConstTarget, Output, SelfOwner, VarRef};
pub use declare::CogDecl;
pub use load::{load, load_movement, load_movement_tests, CogSpec, LoadedUnit, STD_MODULES};
pub use types::*;
pub use world::*;

/// The source of the standard prelude, embedded at build time.
pub const PRELUDE_SOURCE: &str = include_str!("../../../std/prelude.qz");

/// A compilation unit to check: a parsed file and the name used for
/// `__FILE__`.
pub struct Unit {
    pub name: String,
    pub program: Program,
    /// The cog the file belongs to (an index into the cogs given to
    /// `check_movement`); `None` for a script or the standard library.
    pub cog: Option<u32>,
    /// Whether the file may hold statements (only the application's main
    /// file, in a movement).
    pub statements: bool,
    /// Whether its statements are left out, unchecked and not run (an
    /// application's main file under `quarz test`).
    pub declarations_only: bool,
}

impl Unit {
    /// A file outside any cog: a script, or a file it requires.
    pub fn script(name: String, program: Program) -> Unit {
        Unit {
            name,
            program,
            cog: None,
            statements: true,
            declarations_only: false,
        }
    }
}

impl From<LoadedUnit> for Unit {
    fn from(u: LoadedUnit) -> Unit {
        Unit {
            name: u.name,
            program: u.program,
            cog: u.cog,
            statements: u.statements,
            declarations_only: u.declarations_only,
        }
    }
}

/// A checked compilation unit: its top-level statements and the
/// pseudo-class holding its top-level methods.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct CheckedUnit {
    pub file: u32,
    pub name: String,
    pub main_class: ClassId,
    pub body: Vec<Expr>,
}

/// A fully checked program.
pub struct Checked {
    pub world: World,
    pub output: Output,
    /// Units in execution order (dependencies first, the main file last).
    pub units: Vec<CheckedUnit>,
}

/// Diagnostics tagged with the index of the file they refer to (0 = prelude,
/// 1.. = units in order).
pub type FileDiagnostic = (u32, Diagnostic);

/// A session's state to roll back to (`Session::checkpoint`).
pub struct Checkpoint {
    checker: check::ReplSnapshot,
    loaded: Vec<(u32, String, ClassId)>,
    loaded_keys: rustc_hash::FxHashSet<String>,
    sources: Vec<(u32, SourceFile)>,
    next_file: u32,
    /// The world's sizes then.
    pub classes: usize,
    pub methods: usize,
    pub consts: usize,
}

/// An interactive session: declarations and variables accumulate across
/// inputs, which are all part of unit 1. Libraries and files loaded with
/// `require` become units 2, 3, ...
pub struct Session {
    checker: check::Checker,
    main: ClassId,
    inputs: u32,
    /// Units loaded by `require`: file index, name and pseudo-class.
    loaded: Vec<(u32, String, ClassId)>,
    loaded_keys: rustc_hash::FxHashSet<String>,
    /// The file index the next required file takes (a file's own
    /// requires are loaded after it took one: `loaded` is pushed to only
    /// once they are).
    next_file: u32,
    sources: Vec<(u32, SourceFile)>,
}

impl Session {
    pub fn new(prelude: &Program) -> Result<Session, Vec<FileDiagnostic>> {
        let empty = Program {
            body: Vec::new(),
            span: quarz_syntax::Span::empty(0),
            docs: Vec::new(),
        };
        let cached = PRELUDE_CACHE.get().map(|bytes| PreludeState::decode(bytes));
        let mut prelude_output = None;
        let mut declarer = match cached {
            Some(state) => {
                prelude_output = Some((state.output, state.self_news));
                declare::Declarer::with_world(state.world)
            }
            None => {
                let mut d = declare::Declarer::new();
                d.collect_prelude(prelude);
                d
            }
        };
        declarer.collect_unit(&empty, 1);
        declarer.resolve_headers();
        let diagnostics = std::mem::take(&mut declarer.diagnostics);
        if diagnostics.iter().any(|(_, d)| d.is_error()) {
            return Err(diagnostics);
        }
        let main = declarer.units[0].main;
        let mut checker = check::Checker::new(declarer.world, vec![None, Some(main)]);
        if let Some((out, sites)) = prelude_output {
            checker.set_output(out);
            checker.set_self_news(sites);
        }
        checker.check_all(&[(1, Vec::new())]);
        let diagnostics = checker.take_diagnostics();
        if diagnostics.iter().any(|(_, d)| d.is_error()) {
            return Err(diagnostics);
        }
        Ok(Session {
            checker,
            main,
            inputs: 0,
            loaded: Vec::new(),
            loaded_keys: rustc_hash::FxHashSet::default(),
            next_file: 2,
            sources: Vec::new(),
        })
    }

    /// Whether standard library module `module` is loaded, or one of its
    /// names is taken (so that loading it implicitly would clash).
    pub fn std_loaded(&self, module: &str) -> bool {
        self.loaded_keys.contains(&format!("<std:{module}>"))
            || load::std_exports()
                .iter()
                .filter(|(m, _)| *m == module)
                .any(|(_, names)| names.iter().any(|n| self.checker.world.top.contains_key(n)))
    }

    /// The source of a unit loaded by `require`, for rendering diagnostics.
    pub fn source(&self, file: u32) -> Option<&SourceFile> {
        self.sources
            .iter()
            .find(|(f, _)| *f == file)
            .map(|(_, s)| s)
    }

    /// Load a library (`require "name"`) or a file (`require_relative`,
    /// resolved against `dir`) requested at `span` in unit `from`. Returns
    /// the newly loaded units in execution order (dependencies first),
    /// The session as it is, to go back to if what comes next fails
    /// (docs/05 §7: a failed input is discarded): the checker's state and
    /// the files loaded, and how many classes, methods and constants
    /// there are (what the lowering and the interpreter keep by those ids
    /// is cut back to them, `Lowerer::forget`, `SharedState::forget`).
    pub fn checkpoint(&self) -> Checkpoint {
        Checkpoint {
            checker: self.checker.repl_snapshot(),
            loaded: self.loaded.clone(),
            loaded_keys: self.loaded_keys.clone(),
            sources: self.sources.clone(),
            next_file: self.next_file,
            classes: self.checker.world.classes.len(),
            methods: self.checker.world.methods.len(),
            consts: self.checker.world.consts.len(),
        }
    }

    /// Back to `c`.
    pub fn rollback(&mut self, c: Checkpoint) {
        self.checker.repl_restore(c.checker);
        self.loaded = c.loaded;
        self.loaded_keys = c.loaded_keys;
        self.sources = c.sources;
        self.next_file = c.next_file;
    }

    /// Load a library (`require "name"`) or a file (`require_relative`,
    /// resolved against `dir`) requested at `span` in unit `from`. Returns
    /// the newly loaded units in execution order (dependencies first),
    /// whose top-level statements the caller runs once; an empty list when
    /// everything was already loaded. If it fails, the caller rolls back
    /// (`checkpoint`), so that it can be required again.
    pub fn require(
        &mut self,
        path: &str,
        relative: bool,
        dir: &Path,
        from: u32,
        span: quarz_syntax::Span,
        mut runner: Option<&mut (dyn StaticRunner + '_)>,
    ) -> Result<Vec<CheckedUnit>, Vec<FileDiagnostic>> {
        let (key, name, text, module_dir) = if relative {
            let mut target = dir.join(path);
            if target.extension().is_none() {
                target.set_extension("qz");
            }
            let text = std::fs::read_to_string(&target).map_err(|e| {
                let message = format!("cannot read `{}`: {e}", target.display());
                vec![(from, Diagnostic::error(message, span))]
            })?;
            let module_dir = target
                .parent()
                .map(Path::to_path_buf)
                .unwrap_or_else(|| PathBuf::from("."));
            (
                load::canonical(&target),
                target.display().to_string(),
                text,
                module_dir,
            )
        } else {
            let key = format!("<std:{path}>");
            let Some((_, text)) = STD_MODULES.iter().find(|(n, _)| *n == path) else {
                let message = format!("unknown library `{path}`");
                return Err(vec![(from, Diagnostic::error(message, span))]);
            };
            (key.clone(), key, text.to_string(), PathBuf::from("."))
        };
        if !self.loaded_keys.insert(key) {
            return Ok(Vec::new());
        }
        let file = self.next_file;
        self.next_file += 1;
        let base = self.next_base();
        self.inputs += 1;
        let source = SourceFile::with_base(name.clone(), text, base);
        let parsed = parse_with_bases(&source.text, base, base);
        if let Some(r) = runner.as_deref_mut() {
            r.add_file(file, source.clone());
        }
        self.sources.push((file, source));
        let mut diagnostics: Vec<FileDiagnostic> = parsed
            .diagnostics
            .iter()
            .map(|d| (file, d.clone()))
            .collect();
        if diagnostics.iter().any(|(_, d)| d.is_error()) {
            return Err(diagnostics);
        }
        // Dependencies first.
        let mut units = Vec::new();
        for expr in &parsed.program.body {
            if let ExprKind::Require { path, relative } = &expr.kind {
                units.extend(self.require(
                    path,
                    *relative,
                    &module_dir,
                    file,
                    expr.span,
                    runner.as_deref_mut(),
                )?);
            }
        }
        let world = std::mem::take(&mut self.checker.world);
        let mut declarer = declare::Declarer::with_world(world);
        if name.starts_with("<std:") {
            declarer.world.std_files.insert(file);
        }
        declarer.collect_unit(&parsed.program, file);
        declarer.resolve_headers();
        diagnostics.append(&mut declarer.diagnostics);
        let main = declarer.units[0].main;
        let body: Vec<Expr> = declarer.units[0]
            .body
            .iter()
            .map(|e| (*e).clone())
            .collect();
        self.checker.world = std::mem::take(&mut declarer.world);
        self.checker.world.freeze_ancestors(true);
        self.checker.add_file_main(file, main);
        self.loaded.push((file, name.clone(), main));
        if diagnostics.iter().any(|(_, d)| d.is_error()) {
            self.checker.drop_static_stmts(file, base);
            diagnostics.append(&mut self.checker.take_diagnostics());
            return Err(diagnostics);
        }
        self.run_static_stmts(file, base, runner.as_deref_mut());
        diagnostics.append(&mut self.checker.take_diagnostics());
        if diagnostics.iter().any(|(_, d)| d.is_error()) {
            return Err(diagnostics);
        }
        let refs: Vec<&Expr> = body.iter().collect();
        // Its `static(...)` expressions under its unit's staging rule
        // (docs/14 §8), evaluated with it.
        self.checker.repl_unit = Some((file, base));
        self.checker.check_all(&[(file, refs)]);
        if self.checker.error_count() == 0 {
            self.checker.eval_static_exprs(runner, &|f| f == file);
        }
        self.checker.repl_unit = None;
        diagnostics.append(&mut self.checker.take_diagnostics());
        if diagnostics.iter().any(|(_, d)| d.is_error()) {
            return Err(diagnostics);
        }
        units.push(CheckedUnit {
            file,
            name,
            main_class: main,
            body,
        });
        Ok(units)
    }

    pub fn world(&self) -> &World {
        &self.checker.world
    }

    pub fn output(&self) -> &check::Output {
        &self.checker.out
    }

    /// The span/node-id base to parse the next input with.
    pub fn next_base(&self) -> u32 {
        load::unit_base(self.inputs + 1)
    }

    /// Take the base `next_base` gave for an input that parsed, before
    /// what it requires is loaded: each unit has its own spans and node
    /// ids (a compile-time run reuses a statement's function by node id).
    pub fn reserve_input(&mut self) {
        self.inputs += 1;
    }

    pub fn main_class(&self) -> ClassId {
        self.main
    }

    /// Variables declared so far (the parser needs them to tell variables
    /// from method calls).
    pub fn locals(&self) -> Vec<String> {
        self.checker.repl_locals()
    }

    /// The REPL's local variables with their types.
    pub fn local_types(&self) -> Vec<(String, Type)> {
        self.checker.repl_local_types()
    }

    /// Declare and check one input, parsed at `base`; its class bodies'
    /// `static` statements run with `runner` (docs/14 §2). On success,
    /// returns the statements to run; the world and output are available
    /// through `snapshot`.
    pub fn feed(
        &mut self,
        program: &Program,
        base: u32,
        mut runner: Option<&mut (dyn StaticRunner + '_)>,
    ) -> Result<Vec<Expr>, Vec<FileDiagnostic>> {
        let world = std::mem::take(&mut self.checker.world);
        let mut declarer = declare::Declarer::with_world(world);
        declarer.collect_into_unit(program, 1, self.main);
        declarer.resolve_headers();
        let mut diagnostics = std::mem::take(&mut declarer.diagnostics);
        let body: Vec<Expr> = declarer.units[0]
            .body
            .iter()
            .map(|e| (*e).clone())
            .collect();
        self.checker.world = std::mem::take(&mut declarer.world);
        self.checker.world.freeze_ancestors(true);
        if diagnostics.iter().any(|(_, d)| d.is_error()) {
            // Its statements do not run, now or with a later input.
            self.checker.drop_static_stmts(1, base);
            diagnostics.append(&mut self.checker.take_diagnostics());
            return Err(diagnostics);
        }
        self.run_static_stmts(1, base, runner.as_deref_mut());
        diagnostics.append(&mut self.checker.take_diagnostics());
        if diagnostics.iter().any(|(_, d)| d.is_error()) {
            return Err(diagnostics);
        }
        let refs: Vec<&Expr> = body.iter().collect();
        // The staging rule of the input's unit, for its `static(...)`
        // expressions too (docs/14 §8).
        self.checker.repl_unit = Some((1, base));
        self.checker.check_repl(1, &refs);
        if self.checker.error_count() == 0 {
            self.checker.eval_static_exprs(runner, &|f| f == 1);
        }
        self.checker.repl_unit = None;
        diagnostics.append(&mut self.checker.take_diagnostics());
        if diagnostics.iter().any(|(_, d)| d.is_error()) {
            return Err(diagnostics);
        }
        for (_, d) in &diagnostics {
            let _ = d;
        }
        Ok(body)
    }

    /// The `static` statements of the unit just declared (`file`, its
    /// spans from `base`), run with `runner`, before its bodies are
    /// checked, as a program's run before its files' (docs/14 §2).
    /// Without a runner they are an error.
    fn run_static_stmts(
        &mut self,
        file: u32,
        base: u32,
        runner: Option<&mut (dyn StaticRunner + '_)>,
    ) {
        if runner.is_none() {
            let new: Vec<(u32, quarz_syntax::Span)> = self
                .checker
                .world
                .static_stmts
                .iter()
                .filter(|s| s.file == file && s.span.start >= base)
                .map(|s| (s.file, s.span))
                .collect();
            for (f, span) in new {
                self.checker.error_in(
                    f,
                    "`static` statements do not run here: there is no compile-time runner"
                        .to_string(),
                    span,
                );
            }
        }
        self.checker.repl_unit = Some((file, base));
        self.checker.check_static_stmts_of(runner, &|f| f == file);
        self.checker.repl_unit = None;
    }

    /// Warnings of the last input are returned by `feed` only on error; the
    /// checker's current world and output, cloned for an interpreter.
    pub fn snapshot(&self, body: Vec<Expr>, name: &str) -> Checked {
        let mut units: Vec<CheckedUnit> = self
            .loaded
            .iter()
            .map(|(file, name, main)| CheckedUnit {
                file: *file,
                name: name.clone(),
                main_class: *main,
                body: Vec::new(),
            })
            .collect();
        units.push(CheckedUnit {
            file: 1,
            name: name.to_string(),
            main_class: self.main,
            body,
        });
        Checked {
            world: self.checker.world.clone(),
            output: self.checker.out.clone(),
            units,
        }
    }
}

/// Check a single-file program.
/// Check a single program against the prelude. The program must have been
/// parsed with `parse_with_bases(src, load::unit_base(0), load::unit_base(0))`
/// so that its spans and node ids do not collide with the prelude's.
pub fn check(prelude: &Program, program: &Program) -> (Option<Checked>, Vec<FileDiagnostic>) {
    let unit = Unit::script("main".to_string(), program.clone());
    check_units(prelude, &[unit])
}

pub fn check_units(prelude: &Program, units: &[Unit]) -> (Option<Checked>, Vec<FileDiagnostic>) {
    check_movement(prelude, units, &[])
}

/// Check the files of a movement: `cogs` are its cogs (the application
/// first), and each unit names the cog it belongs to.
pub fn check_movement(
    prelude: &Program,
    units: &[Unit],
    cogs: &[CogDecl],
) -> (Option<Checked>, Vec<FileDiagnostic>) {
    check_with_extra(prelude, units, cogs, None, None)
}

/// `check_movement` with a runner for the class bodies' `static`
/// statements (docs/14): without one, they are checked but not run.
pub fn check_movement_with(
    prelude: &Program,
    units: &[Unit],
    cogs: &[CogDecl],
    runner: &mut (dyn StaticRunner + '_),
) -> (Option<Checked>, Vec<FileDiagnostic>) {
    check_with_extra(prelude, units, cogs, None, Some(runner))
}

/// What a `StaticRunner` may ask of the checker while it runs a
/// `static` statement: the world and the results so far, and the check
/// of a method the statement's callee reaches.
pub trait StaticHost {
    fn world(&self) -> &World;
    fn output(&self) -> &Output;
    fn ensure_method_checked(&mut self, mid: MethodId);
    fn ensure_const_checked(&mut self, cid: ConstId);
    /// Before the first run: what every run may need checked (the field
    /// defaults, for constructions at compile time).
    fn prepare(&mut self);
    /// The errors reported so far: a run is skipped when the checks it
    /// asked for added some.
    fn error_count(&self) -> usize;
    /// The classes whose statements have not all run yet (the one
    /// running included): the lowering reaches their methods, and their
    /// descendants', only through a call that resolves to one.
    fn pending_classes(&self) -> Vec<ClassId>;
    /// A member a statement generated (docs/14 §5): declared, or refused
    /// with the reason (a name the class has already).
    fn add_generated(&mut self, info: MethodInfo) -> Result<MethodId, String>;
    /// A field a statement generated (`def_field`), likewise.
    fn add_generated_field(&mut self, class: ClassId, field: FieldInfo) -> Result<(), String>;
    /// After a statement's generations: the declaration-time checks of
    /// the classes they went into, again.
    fn recheck_classes(&mut self, classes: &[ClassId]);
}

/// Why a `static` statement could not run: reported at its position.
pub struct StaticFailure {
    pub message: String,
    pub notes: Vec<String>,
}

/// Runs a class body's `static` statement at compile time (the
/// interpreter lives above this crate: `quarz-cli` provides one).
pub trait StaticRunner {
    fn run(
        &mut self,
        host: &mut dyn StaticHost,
        stmt: &StaticStmt,
        callee: MethodId,
    ) -> Result<(), StaticFailure>;
    /// Run a `static(...)`'s call (`stmt.expr`, of `callee`) and give its
    /// value, baked (docs/14 §8).
    fn eval(
        &mut self,
        _host: &mut dyn StaticHost,
        _stmt: &world::StaticStmt,
        _callee: MethodId,
    ) -> Result<world::Baked, StaticFailure> {
        Err(StaticFailure {
            message: "`static(...)` cannot be evaluated here: there is no compile-time runner"
                .to_string(),
            notes: Vec::new(),
        })
    }
    /// Forget everything lowered and run so far: the check starts over
    /// (`check_uncached` after a cache mismatch).
    fn reset(&mut self);
    /// A source file loaded while checking (a file the REPL requires),
    /// for the line numbers of what is lowered from it.
    fn add_file(&mut self, _index: u32, _file: SourceFile) {}
}

/// The prelude declared and checked (every method body, so that a
/// program's checking only adds to it): what `check_with_extra` starts
/// from instead of the prelude's source when a command was built with it
/// (`set_prelude_cache`).
#[derive(serde::Serialize, serde::Deserialize)]
pub struct PreludeState {
    pub world: World,
    pub output: Output,
    pub self_news: Vec<check::SelfNew>,
    /// The standard library's modules checked with it (`std_state`): the
    /// first units of a program that loads exactly these.
    pub units: Vec<CheckedUnit>,
}

impl PreludeState {
    /// The state, then the world's documentation comments: more than half
    /// of it, which only the commands that show or run them read
    /// (`want_docs`). The state's length comes first.
    pub fn encode(&self) -> Vec<u8> {
        let config = bincode::config::standard();
        let state = bincode::serde::encode_to_vec(self, config).expect("encode the prelude");
        let docs = bincode::serde::encode_to_vec(&self.world.docs, config).expect("encode docs");
        let mut bytes = (state.len() as u64).to_le_bytes().to_vec();
        bytes.extend(state);
        bytes.extend(docs);
        bytes
    }

    /// The state, with the documentation comments when `want_docs` asked
    /// for them.
    pub fn decode(bytes: &[u8]) -> PreludeState {
        let config = bincode::config::standard();
        let (len, rest) = bytes.split_at(8);
        let len = u64::from_le_bytes(len.try_into().unwrap()) as usize;
        let (state, docs) = rest.split_at(len);
        let mut state: PreludeState = bincode::serde::decode_from_slice(state, config)
            .expect("decode the prelude")
            .0;
        if WANT_DOCS.load(std::sync::atomic::Ordering::Relaxed) {
            state.world.docs = bincode::serde::decode_from_slice(docs, config)
                .expect("decode the prelude's docs")
                .0;
        }
        state
    }
}

static WANT_DOCS: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// Keep the documentation comments of the prelude and the standard
/// library when checking starts from their cached states (for the
/// commands that show or run them).
pub fn want_docs() {
    WANT_DOCS.store(true, std::sync::atomic::Ordering::Relaxed);
}

/// Declare and check the prelude alone (for `PreludeState::encode`).
pub fn prelude_state(prelude: &Program) -> (PreludeState, Vec<FileDiagnostic>) {
    let mut declarer = declare::Declarer::new();
    declarer.collect_prelude(prelude);
    declarer.resolve_headers();
    let mut diagnostics = std::mem::take(&mut declarer.diagnostics);
    let mut checker = check::Checker::new(declarer.world, vec![None]);
    checker.check_all(&[]);
    let self_news = checker.self_news().to_vec();
    let (world, output, mut diags) = checker.into_output();
    diagnostics.append(&mut diags);
    (
        PreludeState {
            world,
            output,
            self_news,
            units: Vec::new(),
        },
        diagnostics,
    )
}

/// Declare and check the prelude with the standard library's `modules`
/// (each after those it requires, in `STD_MODULES` order), as a program
/// that loads exactly these has them first (`load::std_first`).
pub fn std_state(prelude: &Program, modules: &[&str]) -> (PreludeState, Vec<FileDiagnostic>) {
    let parsed: Vec<(String, Program)> = modules
        .iter()
        .map(|m| {
            let text = load::STD_MODULES.iter().find(|(n, _)| n == m).unwrap().1;
            let base = load::unit_base(load::std_unit(m));
            (
                format!("<std:{m}>"),
                parse_with_bases(text, base, base).program,
            )
        })
        .collect();
    let mut declarer = declare::Declarer::new();
    declarer.collect_prelude(prelude);
    for (i, (_, program)) in parsed.iter().enumerate() {
        let file = i as u32 + 1;
        declarer.world.std_files.insert(file);
        declarer.collect_unit(program, file);
    }
    declarer.resolve_headers();
    let mut diagnostics = std::mem::take(&mut declarer.diagnostics);
    let mut file_mains: Vec<Option<ClassId>> = vec![None; parsed.len() + 1];
    let mut bodies: Vec<(u32, ClassId, Vec<&Expr>)> = Vec::new();
    for u in &declarer.units {
        file_mains[u.file as usize] = Some(u.main);
        bodies.push((u.file, u.main, u.body.clone()));
    }
    let mut checker = check::Checker::new(declarer.world, file_mains);
    let refs: Vec<(u32, Vec<&Expr>)> = bodies.iter().map(|(f, _, b)| (*f, b.clone())).collect();
    checker.check_all(&refs);
    let units = bodies
        .into_iter()
        .map(|(file, main, body)| CheckedUnit {
            file,
            name: parsed[file as usize - 1].0.clone(),
            main_class: main,
            body: body.into_iter().cloned().collect(),
        })
        .collect();
    let self_news = checker.self_news().to_vec();
    let (world, output, mut diags) = checker.into_output();
    diagnostics.append(&mut diags);
    (
        PreludeState {
            world,
            output,
            self_news,
            units,
        },
        diagnostics,
    )
}

static STD_CACHE: std::sync::OnceLock<Vec<(String, &'static [u8])>> = std::sync::OnceLock::new();

/// Start checking a program whose first units are exactly the standard
/// library modules named (comma-separated) from these encoded states.
pub fn set_std_cache(states: Vec<(String, &'static [u8])>) {
    let _ = STD_CACHE.set(states);
}

static PRELUDE_CACHE: std::sync::OnceLock<&'static [u8]> = std::sync::OnceLock::new();

/// The prelude's syntax tree, for checking: an empty one when checking
/// starts from a cached `PreludeState`, which has it.
pub fn parse_prelude() -> quarz_syntax::Parsed {
    if PRELUDE_CACHE.get().is_some() {
        quarz_syntax::parse("")
    } else {
        quarz_syntax::parse(PRELUDE_SOURCE)
    }
}

/// Start checking from this encoded `PreludeState` rather than the
/// prelude's source, in this process.
pub fn set_prelude_cache(bytes: &'static [u8]) {
    let _ = PRELUDE_CACHE.set(bytes);
}

/// What makes a unit from the checked world: its source (named), or the
/// errors that prevent it.
/// A unit `extra` writes: its source (named) and the cog it belongs to,
/// if any (an example of a library sees the library as its users do).
pub struct ExtraSource {
    pub source: SourceFile,
    pub cog: Option<u32>,
}

/// What makes units from the checked world (the test runner, a cog's
/// examples), or the errors that prevent them.
pub type ExtraUnit<'a> = &'a mut dyn FnMut(&World) -> Result<Vec<ExtraSource>, Vec<FileDiagnostic>>;

thread_local! {
    static NO_CACHE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// `check_with_extra` reading nothing back.
fn check_uncached(
    prelude: &Program,
    units: &[Unit],
    cogs: &[CogDecl],
    extra: Option<ExtraUnit>,
    runner: Option<&mut (dyn StaticRunner + '_)>,
) -> (Option<Checked>, Vec<FileDiagnostic>) {
    NO_CACHE.set(true);
    let mut runner = runner;
    if let Some(r) = runner.as_deref_mut() {
        r.reset();
    }
    let r = check_with_extra(prelude, units, cogs, extra, runner);
    NO_CACHE.set(false);
    r
}

/// Check `units`, then the unit `extra` writes from what they declare (the
/// test runner, `quarz test`), checked after them as one more unit, the
/// way `Session::require` adds one. Its file index is `units.len() + 1`,
/// and it must be parsed at `load::unit_base(units.len())`, as `extra`'s
/// `SourceFile` says.
pub fn check_with_extra(
    prelude: &Program,
    units: &[Unit],
    cogs: &[CogDecl],
    extra: Option<ExtraUnit>,
    mut runner: Option<&mut (dyn StaticRunner + '_)>,
) -> (Option<Checked>, Vec<FileDiagnostic>) {
    // The prelude declared and checked ahead of time (`prelude_state`),
    // when the command was built with it.
    // And with the standard library modules the program loads first
    // (`std_state`), when exactly those were.
    let leading = units
        .iter()
        .take_while(|u| u.name.starts_with("<std:"))
        .count();
    let key: Vec<&str> = units[..leading]
        .iter()
        .map(|u| u.name.trim_start_matches("<std:").trim_end_matches('>'))
        .collect();
    let std_cached = (leading > 0)
        .then(|| STD_CACHE.get())
        .flatten()
        .and_then(|states| states.iter().find(|(k, _)| *k == key.join(",")))
        .map(|(_, bytes)| PreludeState::decode(bytes));
    let cached =
        std_cached.or_else(|| PRELUDE_CACHE.get().map(|bytes| PreludeState::decode(bytes)));
    let mut prelude_output = None;
    let mut std_units: Vec<CheckedUnit> = Vec::new();
    let mut declarer = match cached {
        Some(state) => {
            prelude_output = Some((state.output, state.self_news));
            std_units = state.units;
            declare::Declarer::with_world(state.world)
        }
        None => {
            let mut d = declare::Declarer::new();
            d.collect_prelude(prelude);
            d
        }
    };
    declarer.declare_cogs(cogs, units.len() as u32);
    for (i, unit) in units.iter().enumerate().skip(std_units.len()) {
        let file = i as u32 + 1;
        if unit.name.starts_with("<std:") {
            declarer.world.std_files.insert(file);
        }
        match unit.cog {
            Some(cog) if !cogs.is_empty() => {
                declarer.collect_cog_unit(&unit.program, file, cog, unit.statements)
            }
            _ => declarer.collect_unit(&unit.program, file),
        }
    }
    declarer.resolve_headers();
    let mut diagnostics = std::mem::take(&mut declarer.diagnostics);
    let mut file_mains: Vec<Option<ClassId>> = vec![None; units.len() + 1];
    for u in &std_units {
        file_mains[u.file as usize] = Some(u.main_class);
    }
    let mut bodies: Vec<(u32, Vec<&Expr>)> = Vec::new();
    for u in &declarer.units {
        file_mains[u.file as usize] = Some(u.main);
        if units[u.file as usize - 1].declarations_only {
            bodies.push((u.file, Vec::new()));
        } else {
            bodies.push((u.file, u.body.clone()));
        }
    }
    if diagnostics.iter().any(|(_, d)| d.is_error()) {
        return (None, diagnostics);
    }
    let (out, sites) = prelude_output.unwrap_or_default();
    // The files whose checks were kept (`cache`): their bodies are not
    // checked again.
    let key_of = |f: u32| -> String {
        if f == 0 {
            "<prelude>".to_string()
        } else {
            units
                .get(f as usize - 1)
                .map(|u| u.name.clone())
                .unwrap_or_default()
        }
    };
    let file_of = |k: &str| -> Option<u32> {
        if k == "<prelude>" {
            return Some(0);
        }
        units.iter().position(|u| u.name == k).map(|i| i as u32 + 1)
    };
    let mut keys: Vec<Option<u64>> = vec![None; units.len() + 1];
    let mut reused: Vec<bool> = vec![false; units.len() + 1];
    let mut consts_seen: Vec<u64> = Vec::new();
    // The warnings of the files read back.
    let mut kept: Vec<FileDiagnostic> = Vec::new();
    let mut checker = check::Checker::new(declarer.world, file_mains.clone());
    checker.set_output(out);
    checker.set_self_news(sites);
    // Cog by cog, in dependency order (a script file by file, in load
    // order): the class bodies' `static` statements run first, before any
    // body is checked (docs/14; what they call is checked on demand) and
    // generate members; then the cog's files are keyed and read back from
    // the cache. Read back after, so that the generated members, which
    // the kept checks refer to and which are part of the files'
    // interfaces, exist (docs/05 §2).
    let use_cache = cache::build().is_some() && cache::dir().is_some() && !NO_CACHE.get();
    let mut groups: Vec<Vec<u32>> = Vec::new();
    let mut last_cog: Option<u32> = None;
    for (i, u) in units.iter().enumerate() {
        let file = i as u32 + 1;
        match (u.cog, groups.last_mut()) {
            (Some(c), Some(last)) if last_cog == Some(c) => last.push(file),
            _ => groups.push(vec![file]),
        }
        last_cog = u.cog;
    }
    let mut interfaces: Vec<(String, u64)> =
        (1..=units.len() as u32).map(|f| (key_of(f), 0)).collect();
    let cogs_hash = cache::cogs(&checker.world);
    for group in groups {
        let in_group = |f: u32| group.contains(&f);
        checker.check_static_stmts_of(runner.as_deref_mut(), &in_group);
        // The constants of these files: a type inferred from what the
        // statements generated is possible, so after them.
        checker.check_consts_of(&in_group);
        if !use_cache {
            continue;
        }
        // The movement's cogs too: their root modules belong to no file.
        // The interfaces of the groups to come are those before their
        // own statements run, the same on every check.
        for f in 1..=units.len() as u32 {
            if interfaces[f as usize - 1].1 == 0 || in_group(f) {
                interfaces[f as usize - 1].1 = cache::interface(&checker.world, f);
            }
        }
        let all = cache::hash(&(&interfaces, cogs_hash));
        for &file in &group {
            let u = &units[file as usize - 1];
            if (file as usize) <= std_units.len() || u.declarations_only {
                continue;
            }
            let Some(key) = cache::key(&u.program, cache::hash(&(all, u.cog, u.statements))) else {
                continue;
            };
            keys[file as usize] = Some(key);
            let Some(checks) = cache::load(key) else {
                continue;
            };
            let seen = checks.consts_seen;
            if let Some(warnings) = checker.apply_cached(checks, file, &file_of) {
                kept.extend(warnings.into_iter().map(|d| (file, d)));
                reused[file as usize] = true;
                consts_seen.push(seen);
                checker.mark_reused(file);
            }
        }
    }
    // A constant's type is inferred: when one differs from what a file
    // read back was checked with, check everything again.
    checker.check_consts();
    let consts_now = cache::const_types(&checker.world, &key_of);
    if consts_seen.iter().any(|s| *s != consts_now) {
        return check_uncached(prelude, units, cogs, extra, runner);
    }
    let to_check: Vec<(u32, Vec<&Expr>)> = bodies
        .iter()
        .filter(|(f, _)| !reused[*f as usize])
        .cloned()
        .collect();
    checker.check_all(&to_check);
    // The `static(...)` expressions, of every file, read back or not
    // (docs/14 §8: their values are not kept by the cache).
    if checker.error_count() == 0 {
        // Recomputed: a file read back brings the values of its last check.
        checker.out.static_values.clear();
        checker.eval_static_exprs(runner.as_deref_mut(), &|_| true);
    }
    let mut checked_units: Vec<CheckedUnit> = std::mem::take(&mut std_units);
    checked_units.extend(bodies.into_iter().map(|(file, body)| CheckedUnit {
        file,
        name: units[file as usize - 1].name.clone(),
        main_class: file_mains[file as usize].unwrap(),
        body: body.into_iter().cloned().collect(),
    }));
    let checked_diagnostics = checker.take_diagnostics();
    // In the order of the files and of positions in them, which is the
    // same whether a file's warnings were found now or read back (each
    // file's in the order they were found).
    let mut all = kept;
    all.extend(checked_diagnostics.iter().cloned());
    all.sort_by_key(|(f, d)| (*f, d.span.start));
    // A method of a file read back that a `static` statement reached
    // before was checked then too: its warnings once.
    all.dedup_by(|a, b| a.0 == b.0 && a.1.span == b.1.span && a.1.message == b.1.message);
    diagnostics.extend(all);
    // Keep what was checked, when it is free of errors (with its warnings,
    // reported again when it is read back).
    if !diagnostics.iter().any(|(_, d)| d.is_error()) {
        for (file, key) in keys.iter().enumerate() {
            let (Some(key), false) = (key, reused[file]) else {
                continue;
            };
            let file = file as u32;
            let base = units[file as usize - 1].program.span.start & !((1 << load::UNIT_BITS) - 1);
            let warnings = checked_diagnostics
                .iter()
                .filter(|(f, _)| *f == file)
                .map(|(_, d)| d.clone())
                .collect();
            let checks = cache::extract(
                &checker.world,
                checker.output(),
                checker.self_news(),
                file,
                base,
                warnings,
                consts_now,
                &key_of,
            );
            cache::store(*key, &checks);
        }
    }
    if let Some(extra) = extra {
        if !diagnostics.iter().any(|(_, d)| d.is_error()) {
            match extra(&checker.world) {
                Err(mut errors) => diagnostics.append(&mut errors),
                Ok(sources) => {
                    let first = units.len() as u32 + 1;
                    let parsed: Vec<_> = sources
                        .iter()
                        .enumerate()
                        .map(|(k, s)| {
                            let base = load::unit_base(units.len() as u32 + k as u32);
                            parse_with_bases(&s.source.text, base, base)
                        })
                        .collect();
                    for (k, p) in parsed.iter().enumerate() {
                        let file = first + k as u32;
                        diagnostics.extend(p.diagnostics.iter().map(|d| (file, d.clone())));
                    }
                    if !diagnostics.iter().any(|(_, d)| d.is_error()) {
                        // Declared together, so that one (the runner) may
                        // name another's classes (an example's).
                        let world = std::mem::take(&mut checker.world);
                        let mut declarer = declare::Declarer::with_world(world);
                        for (k, (s, p)) in sources.iter().zip(&parsed).enumerate() {
                            let file = first + k as u32;
                            match s.cog {
                                Some(cog) if !cogs.is_empty() => {
                                    declarer.collect_cog_unit(&p.program, file, cog, true)
                                }
                                _ => declarer.collect_unit(&p.program, file),
                            }
                        }
                        declarer.resolve_headers();
                        diagnostics.append(&mut declarer.diagnostics);
                        let mut bodies: Vec<(u32, ClassId, Vec<Expr>)> = Vec::new();
                        for u in &declarer.units {
                            let body = u.body.iter().map(|e| (*e).clone()).collect();
                            bodies.push((u.file, u.main, body));
                        }
                        checker.world = std::mem::take(&mut declarer.world);
                        checker.world.freeze_ancestors(true);
                        for (file, main, _) in &bodies {
                            checker.add_file_main(*file, *main);
                        }
                        if !diagnostics.iter().any(|(_, d)| d.is_error()) {
                            let refs: Vec<(u32, Vec<&Expr>)> = bodies
                                .iter()
                                .map(|(file, _, body)| (*file, body.iter().collect()))
                                .collect();
                            // The extra units' own `static` statements (a test file's,
                            // a doc example's).
                            checker.check_static_stmts(runner.as_deref_mut());
                            checker.check_all(&refs);
                            if checker.error_count() == 0 {
                                checker.eval_static_exprs(runner, &|_| true);
                            }
                            diagnostics.append(&mut checker.take_diagnostics());
                        }
                        for (file, main, body) in bodies {
                            checked_units.push(CheckedUnit {
                                file,
                                name: sources[(file - first) as usize].source.name.clone(),
                                main_class: main,
                                body,
                            });
                        }
                    }
                }
            }
        }
    }
    let (world, output, mut diags) = checker.into_output();
    diagnostics.append(&mut diags);
    let failed = diagnostics.iter().any(|(_, d)| d.is_error());
    let checked = Checked {
        world,
        output,
        units: checked_units,
    };
    if failed {
        (None, diagnostics)
    } else {
        (Some(checked), diagnostics)
    }
}
