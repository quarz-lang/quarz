//! The interactive session (`quarz repl`): line editing, history and
//! display; the evaluation lives in `quarz_cli::session`.
//!
//! Lines are edited with rustyline (Emacs or vi keys, history search,
//! and so on). An input that lacks its end (an open block, bracket or
//! string) goes on in the same entry on the next line, so a whole
//! definition is edited, and recalled from the history, at once; the
//! next line starts with as many spaces as the prompt is wide (part of
//! the entry: rustyline shows no prompt there), so the code lines up,
//! except inside a string, which they would change. The history is kept
//! in `~/.quarz_history`. The entry is highlighted as it
//! is typed (not with `NO_COLOR` set), and Tab completes names.

use std::path::PathBuf;
use std::process::ExitCode;

use std::borrow::Cow;
use std::sync::{Arc, Mutex};

use quarz_cli::complete::Completions;
use quarz_cli::session::{needs_more, unfinished, Outcome, Repl, Unfinished};
use rustyline::completion::{Completer, Pair};
use rustyline::error::ReadlineError;
use rustyline::highlight::{CmdKind, Highlighter};
use rustyline::history::FileHistory;
use rustyline::validate::{ValidationContext, ValidationResult, Validator};
use rustyline::{
    Cmd, CompletionType, ConditionalEventHandler, Config, Context, Editor, Event, EventContext,
    EventHandler, KeyCode, KeyEvent, Modifiers, RepeatCount,
};

/// How many entries the history keeps.
const HISTORY_SIZE: usize = 1000;

const PROMPT: &str = "quarz> ";
/// For an input the session still finds incomplete (the editor judged
/// otherwise): as wide as `PROMPT`.
const CONTINUATION_PROMPT: &str = "     > ";

/// The session's local variables, which decide how some lines parse:
/// shared by the helper and the Enter binding, taken again after each
/// input.
type Locals = Arc<Mutex<Vec<String>>>;

/// Enter: in an entry that lacks its end, a new line indented as wide as
/// the prompt (a plain new line inside a string); otherwise the usual
/// (the entry is accepted).
struct Enter {
    locals: Locals,
}

impl ConditionalEventHandler for Enter {
    fn handle(&self, _: &Event, _: RepeatCount, _: bool, ctx: &EventContext) -> Option<Cmd> {
        let locals = self.locals.lock().unwrap_or_else(|e| e.into_inner());
        match unfinished(ctx.line(), &locals) {
            Unfinished::No => None,
            Unfinished::Code => Some(Cmd::Insert(1, format!("\n{}", " ".repeat(PROMPT.len())))),
            Unfinished::String => Some(Cmd::Insert(1, "\n".to_string())),
        }
    }
}

/// What the line editor asks the session: whether an entry is complete,
/// what completes a name, and how to color the entry. What it knows of
/// the session is taken again after each input.
#[derive(rustyline::Helper, rustyline::Hinter)]
struct Helper {
    locals: Locals,
    completions: Completions,
    color: bool,
}

impl Helper {
    fn new(repl: &Repl, locals: Locals) -> Helper {
        *locals.lock().unwrap_or_else(|e| e.into_inner()) = repl.locals();
        Helper {
            locals,
            completions: repl.completions(),
            color: std::env::var_os("NO_COLOR").is_none_or(|v| v.is_empty()),
        }
    }
}

impl Completer for Helper {
    type Candidate = Pair;

    fn complete(
        &self,
        line: &str,
        pos: usize,
        _: &Context<'_>,
    ) -> rustyline::Result<(usize, Vec<Pair>)> {
        let (start, names) = self.completions.complete(line, pos);
        let pairs = names
            .into_iter()
            .map(|n| Pair {
                display: n.clone(),
                replacement: n,
            })
            .collect();
        Ok((start, pairs))
    }
}

impl Highlighter for Helper {
    fn highlight<'l>(&self, line: &'l str, _: usize) -> Cow<'l, str> {
        if self.color {
            Cow::Owned(quarz_cli::highlight::highlight(line))
        } else {
            Cow::Borrowed(line)
        }
    }

    fn highlight_char(&self, _: &str, _: usize, _: CmdKind) -> bool {
        // Any change may change the colors (a quote opens a string).
        self.color
    }
}

impl Validator for Helper {
    fn validate(&self, ctx: &mut ValidationContext) -> rustyline::Result<ValidationResult> {
        let locals = self.locals.lock().unwrap_or_else(|e| e.into_inner());
        Ok(if needs_more(ctx.input(), &locals) {
            ValidationResult::Incomplete
        } else {
            ValidationResult::Valid(None)
        })
    }
}

fn editor() -> rustyline::Result<Editor<Helper, FileHistory>> {
    let config = Config::builder()
        .max_history_size(HISTORY_SIZE)?
        .history_ignore_dups(true)?
        .completion_type(CompletionType::List)
        .build();
    Editor::with_config(config)
}

fn history_path() -> Option<PathBuf> {
    let home = std::env::var_os("HOME")?;
    Some(PathBuf::from(home).join(".quarz_history"))
}

pub fn repl() -> ExitCode {
    let out = Box::new(std::io::LineWriter::new(std::io::stdout()));
    let mut repl = match Repl::new(out) {
        Ok(r) => r,
        Err(errors) => {
            for e in errors {
                eprint!("{e}");
            }
            return ExitCode::FAILURE;
        }
    };
    let mut editor = match editor() {
        Ok(e) => e,
        Err(e) => {
            eprintln!("quarz: cannot start the line editor: {e}");
            return ExitCode::FAILURE;
        }
    };
    let locals: Locals = Arc::new(Mutex::new(Vec::new()));
    editor.set_helper(Some(Helper::new(&repl, locals.clone())));
    editor.bind_sequence(
        KeyEvent(KeyCode::Enter, Modifiers::NONE),
        EventHandler::Conditional(Box::new(Enter {
            locals: locals.clone(),
        })),
    );
    let history = history_path();
    if let Some(path) = &history {
        // No history yet is fine.
        let _ = editor.load_history(path);
    }
    let save = |editor: &mut Editor<Helper, FileHistory>| {
        if let Some(path) = &history {
            if let Err(e) = editor.save_history(path) {
                eprintln!("quarz: cannot save the history to {}: {e}", path.display());
            }
        }
    };
    println!(
        "Quarz {} (type an expression; Ctrl-D exits)",
        env!("CARGO_PKG_VERSION")
    );
    loop {
        // An input the session still finds incomplete (the editor judged
        // otherwise) goes on with a continuation prompt.
        let prompt = if repl.continuing() {
            CONTINUATION_PROMPT
        } else {
            PROMPT
        };
        let entry = match editor.readline(prompt) {
            Ok(entry) => entry,
            // Ctrl-C drops what is being typed.
            Err(ReadlineError::Interrupted) => {
                repl.discard();
                continue;
            }
            Err(ReadlineError::Eof) => {
                println!();
                break;
            }
            Err(e) => {
                eprintln!("quarz: {e}");
                break;
            }
        };
        if !entry.trim().is_empty() {
            let _ = editor.add_history_entry(entry.as_str());
        }
        let outcome = repl.feed_line(&entry);
        if let Some(helper) = editor.helper_mut() {
            *helper = Helper::new(&repl, locals.clone());
        }
        match outcome {
            Outcome::Incomplete => {}
            Outcome::Errors(errors) => {
                for e in errors {
                    eprint!("{e}");
                }
            }
            Outcome::Value(Some(v)) => println!("=> {v}"),
            Outcome::Value(None) => {}
            Outcome::Exit(code) => {
                save(&mut editor);
                let code = repl.finish(code);
                return ExitCode::from(code.clamp(0, 255) as u8);
            }
        }
    }
    save(&mut editor);
    let code = repl.finish(0);
    ExitCode::from(code.clamp(0, 255) as u8)
}
