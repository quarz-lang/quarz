//! The interactive session: parsing, checking and running one input at a
//! time while declarations, variables and tasks persist.

use std::io::Write;
use std::rc::Rc;

use quarz_syntax::{parse, parse_repl, Diagnostic, SourceFile};
use quarz_types::{Session, PRELUDE_SOURCE};

use crate::interp::{Interp, SharedState};
use crate::value::Frame;

pub struct Repl {
    session: Session,
    state: SharedState,
    prelude_file: SourceFile,
    buffer: String,
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
        Ok(Repl {
            session,
            state,
            prelude_file,
            buffer: String::new(),
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
        let parsed = parse_repl(&file.text, base, base, &self.session.locals());
        if parsed.diagnostics.iter().any(|d| d.is_error()) {
            if incomplete(&parsed.diagnostics) {
                return Outcome::Incomplete;
            }
            self.buffer.clear();
            return Outcome::Errors(parsed.diagnostics.iter().map(|d| d.render(&file)).collect());
        }
        self.buffer.clear();
        let body = match self.session.feed(&parsed.program) {
            Ok(body) => body,
            Err(diags) => {
                return Outcome::Errors(
                    diags
                        .iter()
                        .map(|(index, d)| {
                            if *index == 0 {
                                d.render(&self.prelude_file)
                            } else {
                                d.render(&file)
                            }
                        })
                        .collect(),
                );
            }
        };
        if body.is_empty() {
            return Outcome::Value(None);
        }
        let checked = self.session.snapshot(Vec::new(), "<repl>");
        let interp: Rc<Interp> = Interp::with_state(checked, Vec::new(), self.state.clone());
        let outcome = match interp.run_repl(1, body) {
            Ok(Some(value)) => Outcome::Value(Some(
                interp.inspect(&value).unwrap_or_else(|_| "?".to_string()),
            )),
            Ok(None) => Outcome::Value(None),
            Err(code) => Outcome::Exit(code),
        };
        self.state = interp.shared_state();
        outcome
    }
}
