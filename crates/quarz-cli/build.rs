//! Declare and check the prelude once, when `quarz` is built: the
//! command starts checking a program from this state (encoded into the
//! executable) instead of parsing, declaring and checking the prelude
//! each time, which was most of a short program's start-up.

/// The standard library modules cached together: each module with what it
/// requires, in `STD_MODULES` order (a program loading another mix checks
/// them from their source).
const STD_SETS: &[&[&str]] = &[
    &["json"],
    &["time"],
    &["socket"],
    &["json", "socket", "http"],
    &["test"],
];

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    let prelude = quarz_syntax::parse(quarz_types::PRELUDE_SOURCE);
    assert!(
        prelude.diagnostics.iter().all(|d| !d.is_error()),
        "the prelude does not parse"
    );
    let (state, diagnostics) = quarz_types::prelude_state(&prelude.program);
    let errors: Vec<&str> = diagnostics
        .iter()
        .filter(|(_, d)| d.is_error())
        .map(|(_, d)| d.message.as_str())
        .collect();
    assert!(errors.is_empty(), "the prelude does not check: {errors:#?}");
    let dir = std::path::PathBuf::from(std::env::var("OUT_DIR").unwrap());
    std::fs::write(dir.join("prelude.bin"), state.encode()).unwrap();
    // The standard library's modules as programs load them (with what each
    // requires): `std_<a>,<b>.bin` for each set in `STD_SETS`.
    let mut list = String::new();
    for set in STD_SETS {
        let (state, diagnostics) = quarz_types::std_state(&prelude.program, set);
        let errors: Vec<&str> = diagnostics
            .iter()
            .filter(|(_, d)| d.is_error())
            .map(|(_, d)| d.message.as_str())
            .collect();
        assert!(errors.is_empty(), "std {set:?} does not check: {errors:#?}");
        let key = set.join(",");
        let file = format!("std_{}.bin", set.join("_"));
        std::fs::write(dir.join(&file), state.encode()).unwrap();
        list.push_str(&format!(
            "(\"{key}\", include_bytes!(concat!(env!(\"OUT_DIR\"), \"/{file}\")) as &[u8]),\n"
        ));
    }
    std::fs::write(dir.join("std_states.rs"), format!("&[\n{list}]")).unwrap();
}
