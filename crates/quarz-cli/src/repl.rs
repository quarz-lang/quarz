//! The interactive session (`quarz repl`): line editing and display; the
//! evaluation lives in `quarz_vm::repl`.

use std::io::{BufRead, Write};
use std::process::ExitCode;

use quarz_vm::repl::{Outcome, Repl};

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
    println!(
        "Quarz {} (type an expression; Ctrl-D exits)",
        env!("CARGO_PKG_VERSION")
    );
    let stdin = std::io::stdin();
    loop {
        let prompt = if repl.continuing() {
            "     > "
        } else {
            "quarz> "
        };
        print!("{prompt}");
        let _ = std::io::stdout().flush();
        let mut line = String::new();
        match stdin.lock().read_line(&mut line) {
            Ok(0) => {
                println!();
                break;
            }
            Ok(_) => {}
            Err(_) => break,
        }
        match repl.feed_line(&line) {
            Outcome::Incomplete => {}
            Outcome::Errors(errors) => {
                for e in errors {
                    eprint!("{e}");
                }
            }
            Outcome::Value(Some(v)) => println!("=> {v}"),
            Outcome::Value(None) => {}
            Outcome::Exit(code) => return ExitCode::from(code.clamp(0, 255) as u8),
        }
    }
    ExitCode::SUCCESS
}
