//! The interactive session: parsing, checking, lowering and running one
//! input at a time while declarations, variables and tasks persist.

use std::io::Write;
use std::path::Path;
use std::rc::Rc;

use quarz_ir::Unit;
use quarz_lower::{Lowerer, UnitInput};
use quarz_syntax::ast::ExprKind;
use quarz_syntax::{parse, parse_repl, Diagnostic, SourceFile};
use quarz_types::{CheckedUnit, FileDiagnostic, Session, PRELUDE_SOURCE};
use quarz_vm::value::Frame;
use quarz_vm::{Interp, SharedState};

pub struct Repl {
    session: Session,
    lowerer: Lowerer,
    state: SharedState,
    prelude_file: SourceFile,
    buffer: String,
    /// Every unit lowered so far (required files first, the REPL unit
    /// last), re-registered with each interpreter.
    units: Vec<Unit>,
    /// Source files by index: the prelude, the current input, required
    /// files.
    files: Vec<SourceFile>,
}

/// What happened to one line of input.
pub enum Outcome {
    /// The input is not complete yet; more lines are needed.
    Incomplete,
    /// Rendered diagnostics; the input was discarded.
    Errors(Vec<String>),
    /// The input ran; the rendered value of its last statement, if any.
    Value(Option<String>),
    /// `exit` was called.
    Exit(i32),
}

/// Whether the parse errors mean the input is not finished yet.
fn incomplete(diagnostics: &[Diagnostic]) -> bool {
    diagnostics
        .iter()
        .filter(|d| d.is_error())
        .all(|d| d.message.contains("end of file") || d.message.contains("unterminated"))
}

impl Repl {
    pub fn new(out: Box<dyn Write>) -> Result<Repl, Vec<String>> {
        let prelude_file = SourceFile::new("<prelude>", PRELUDE_SOURCE);
        let prelude = parse(&prelude_file.text);
        let session = Session::new(&prelude.program).map_err(|diags| {
            diags
                .iter()
                .map(|(_, d)| d.render(&prelude_file))
                .collect::<Vec<_>>()
        })?;
        let mut state = SharedState::new(out);
        state.repl_frame = Some(Frame::new(16, None));
        let files = vec![prelude_file.clone(), SourceFile::new("<repl>", "")];
        Ok(Repl {
            session,
            lowerer: Lowerer::new(),
            state,
            prelude_file,
            buffer: String::new(),
            units: Vec::new(),
            files,
        })
    }

    /// Whether a multi-line input is being accumulated.
    pub fn continuing(&self) -> bool {
        !self.buffer.is_empty()
    }

    /// Feed one line (with or without its newline).
    pub fn feed_line(&mut self, line: &str) -> Outcome {
        self.buffer.push_str(line);
        if !line.ends_with('\n') {
            self.buffer.push('\n');
        }
        if self.buffer.trim().is_empty() {
            self.buffer.clear();
            return Outcome::Value(None);
        }
        let base = self.session.next_base();
        let file = SourceFile::with_base("<repl>", self.buffer.clone(), base);
        self.files[1] = file.clone();
        let parsed = parse_repl(&file.text, base, base, &self.session.locals());
        if parsed.diagnostics.iter().any(|d| d.is_error()) {
            if incomplete(&parsed.diagnostics) {
                return Outcome::Incomplete;
            }
            self.buffer.clear();
            return Outcome::Errors(parsed.diagnostics.iter().map(|d| d.render(&file)).collect());
        }
        self.buffer.clear();
        // Load what the input requires, running each library's top level
        // the first time it is loaded.
        for expr in &parsed.program.body {
            if let ExprKind::Require { path, relative } = &expr.kind {
                let loaded = self
                    .session
                    .require(path, *relative, Path::new("."), 1, expr.span);
                match loaded {
                    Ok(units) => {
                        for unit in units {
                            if let Some(outcome) = self.run_unit(unit) {
                                return outcome;
                            }
                        }
                    }
                    Err(diags) => return Outcome::Errors(self.render(&diags, &file)),
                }
            }
        }
        let body = match self.session.feed(&parsed.program) {
            Ok(body) => body,
            Err(diags) => return Outcome::Errors(self.render(&diags, &file)),
        };
        // Declarations, `require`s and `using`s have no value to show.
        if body
            .iter()
            .all(|e| matches!(e.kind, ExprKind::Require { .. } | ExprKind::Using(_)))
        {
            return Outcome::Value(None);
        }
        let input = UnitInput {
            file: 1,
            name: "<repl>".to_string(),
            main_class: self.session.main_class(),
            body: &body,
            repl: true,
        };
        let (interp, fid) = self.load(input);
        let outcome = match interp.run_repl(1, fid) {
            Ok(Some(value)) => Outcome::Value(Some(
                interp.inspect(&value).unwrap_or_else(|_| "?".to_string()),
            )),
            Ok(None) => Outcome::Value(None),
            Err(code) => Outcome::Exit(code),
        };
        self.state = interp.shared_state();
        outcome
    }

    /// Lower a unit body (with everything else new in the world) and
    /// create an interpreter over the shared state that has it loaded.
    fn load(&mut self, input: UnitInput) -> (Rc<Interp>, quarz_ir::FuncId) {
        let delta = self.lowerer.lower(
            self.session.world(),
            self.session.output(),
            &[input],
            self.files.clone(),
        );
        let unit = delta.units.into_iter().next().expect("one unit lowered");
        let fid = unit.body;
        // The REPL unit (file 1) is replaced each time; required files
        // stay.
        self.units.retain(|u| u.file != unit.file);
        self.units.push(unit);
        let interp = Interp::with_state(
            delta.world,
            delta.base,
            delta.functions,
            self.units.clone(),
            Vec::new(),
            self.state.clone(),
        );
        (interp, fid)
    }

    /// Run the top level of a unit loaded by `require`.
    fn run_unit(&mut self, unit: CheckedUnit) -> Option<Outcome> {
        if self.files.len() <= unit.file as usize {
            self.files
                .resize(unit.file as usize + 1, SourceFile::new("", ""));
        }
        self.files[unit.file as usize] = self
            .session
            .source(unit.file)
            .cloned()
            .unwrap_or_else(|| SourceFile::new(unit.name.clone(), ""));
        let input = UnitInput {
            file: unit.file,
            name: unit.name.clone(),
            main_class: unit.main_class,
            body: &unit.body,
            repl: false,
        };
        let (interp, fid) = self.load(input);
        let result = interp.run_repl(unit.file, fid);
        self.state = interp.shared_state();
        match result {
            Err(code) => Some(Outcome::Exit(code)),
            Ok(_) => None,
        }
    }

    fn render(&self, diags: &[FileDiagnostic], input: &SourceFile) -> Vec<String> {
        diags
            .iter()
            .map(|(index, d)| match *index {
                0 => d.render(&self.prelude_file),
                1 => d.render(input),
                other => d.render(self.session.source(other).unwrap_or(input)),
            })
            .collect()
    }
}
