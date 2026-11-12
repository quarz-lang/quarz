//! The witness table (`World::witnesses`, #536 step 3) over the prelude
//! and the standard library: its rows by kind, so that what the table
//! holds there is countable, and none stands for a method nothing
//! implements (a row whose `by` is abstract raises when called; the
//! checker accepts some in programs today, #600 and #555, never here).

use quarz_syntax::parse;
use quarz_types::witness::WitnessSource;
use quarz_types::{std_state, PRELUDE_SOURCE, STD_MODULES};

#[test]
fn the_rows_of_the_prelude_and_the_standard_library() {
    let prelude = parse(PRELUDE_SOURCE);
    let names: Vec<&str> = STD_MODULES.iter().map(|(n, _)| *n).collect();
    let (state, diags) = std_state(&prelude.program, &names);
    assert!(diags.iter().all(|(_, d)| !d.is_error()), "{diags:?}");
    let world = &state.world;
    let table = world.witnesses();
    let name = |m: u32| {
        let i = world.method(m);
        let sep = if i.singleton { "." } else { "#" };
        format!("{}{sep}{}", world.class(i.owner).name, i.name)
    };
    let row = |w: &quarz_types::witness::Witness| {
        format!(
            "{}: {} -> {}",
            world.class(w.class).name,
            name(w.method),
            name(w.by)
        )
    };
    let unimplemented: Vec<String> = table
        .rows
        .iter()
        .filter(|w| world.method(w.by).is_abstract)
        .map(row)
        .collect();
    assert!(unimplemented.is_empty(), "{unimplemented:#?}");
    // A conformance through an extension: `extension Array[T <:
    // Comparable[T]]; include Comparable[Array[T]]`, a row for each method
    // of `Comparable`; the one another method stands for:
    let includes: Vec<&quarz_types::witness::Witness> = table
        .rows
        .iter()
        .filter(|w| matches!(w.source, WitnessSource::Include { .. }))
        .collect();
    assert!(
        includes
            .iter()
            .all(|w| world.class(w.class).name == "Array"
                && world.class(w.module).name == "Comparable"),
        "{:#?}",
        includes.iter().map(|w| row(w)).collect::<Vec<_>>()
    );
    let replaced: Vec<String> = includes
        .iter()
        .filter(|w| w.by != w.method)
        .map(|w| row(w))
        .collect();
    assert_eq!(replaced, ["Array: Comparable#<=> -> Array#<=>"]);
    let comparable = world
        .classes
        .iter()
        .find(|c| c.name == "Comparable")
        .unwrap();
    let own = comparable
        .methods
        .values()
        .flatten()
        .filter(|m| world.method(**m).owner == comparable.id)
        .count();
    assert_eq!(includes.len(), own);
    // An extension's own method for an abstract method of the class's own
    // ancestors: none.
    let methods: Vec<String> = table
        .rows
        .iter()
        .filter(|w| matches!(w.source, WitnessSource::Method { .. }))
        .map(row)
        .collect();
    assert!(methods.is_empty(), "{methods:#?}");
    // An implementation the override table's walk does not reach: the
    // `<=>` of the signature past `Integer`'s other overload.
    let inherited: Vec<String> = table
        .rows
        .iter()
        .filter(|w| w.source == WitnessSource::Inherited)
        .map(row)
        .collect();
    assert_eq!(inherited, ["Integer: Comparable#<=> -> Integer#<=>"]);
}
