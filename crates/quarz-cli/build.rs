//! Declare and check the prelude once, when `quarz` is built: the
//! command starts checking a program from this state (encoded into the
//! executable) instead of parsing, declaring and checking the prelude
//! each time, which was most of a short program's start-up.

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    let prelude = quarz_syntax::parse(quarz_types::PRELUDE_SOURCE);
    assert!(
        prelude.diagnostics.iter().all(|d| !d.is_error()),
        "the prelude does not parse"
    );
    let (state, diagnostics) = quarz_types::prelude_state(&prelude.program);
    assert!(
        diagnostics.iter().all(|(_, d)| !d.is_error()),
        "the prelude does not check"
    );
    let out = std::path::PathBuf::from(std::env::var("OUT_DIR").unwrap()).join("prelude.bin");
    std::fs::write(out, state.encode()).unwrap();
}
