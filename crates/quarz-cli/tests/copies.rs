//! Collections updated in place stay in place: the programs in `copies/`
//! are run with `QUARZ_COUNT_COPIES`, on the VM and compiled, and the
//! number of updates that had to copy a shared
//! collection is checked. A regression here (a reference left behind in
//! a register, an argument copied instead of moved) makes a loop of
//! updates quadratic while its output stays the same, so the other
//! tests cannot see it.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn program(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/copies")
        .join(name)
}

/// The count `QUARZ_COUNT_COPIES` reported on standard error (the line
/// ending in `suffix`).
fn counted(out: &Output, what: &str, suffix: &str) -> u64 {
    assert!(
        out.status.success(),
        "{what} failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let err = String::from_utf8_lossy(&out.stderr);
    err.lines()
        .find_map(|l| {
            l.strip_prefix("quarz: ")?
                .strip_suffix(suffix)?
                .parse()
                .ok()
        })
        .unwrap_or_else(|| panic!("{what}: no count in {err:?}"))
}

const COPIES: &str = " copies of shared collections";
const MOVED: &str = " values moved across Task.blocking";

fn on_vm(path: &Path, suffix: &str) -> u64 {
    let out = Command::new(env!("CARGO_BIN_EXE_quarz"))
        .arg("run")
        .arg(path)
        .env("QUARZ_COUNT_COPIES", "1")
        .output()
        .expect("run quarz");
    counted(&out, &format!("quarz run {}", path.display()), suffix)
}

fn compiled(path: &Path, suffix: &str) -> u64 {
    // One directory per program: the tests run in parallel.
    let dir = std::env::temp_dir().join(format!(
        "quarz-copies-test-{}-{}",
        std::process::id(),
        path.file_stem().unwrap().to_string_lossy()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    let exe = dir.join(path.file_stem().unwrap());
    let built = Command::new(env!("CARGO_BIN_EXE_quarz"))
        .arg("build")
        .arg(path)
        .arg("-o")
        .arg(&exe)
        .output()
        .expect("run quarz build");
    assert!(
        built.status.success(),
        "quarz build {}: {}",
        path.display(),
        String::from_utf8_lossy(&built.stderr)
    );
    let out = Command::new(&exe)
        .env("QUARZ_COUNT_COPIES", "1")
        .output()
        .expect("run the executable");
    let _ = std::fs::remove_dir_all(&dir);
    counted(&out, &format!("{} (compiled)", path.display()), suffix)
}

fn check(name: &str, want: u64) {
    let path = program(name);
    assert_eq!(on_vm(&path, COPIES), want, "{name} on the VM");
    assert_eq!(compiled(&path, COPIES), want, "{name} compiled");
}

#[test]
fn updates_of_unshared_collections_copy_nothing() {
    check("in_place.qz", 0);
}

/// The count itself: each update of a collection still referred to
/// elsewhere copies it once.
#[test]
fn updates_of_shared_collections_copy_once_each() {
    check("shared.qz", 3);
}

/// #927: a field or a captured local is updated in place only by a
/// native that runs no code of the program; a plain local always is.
#[test]
fn fields_updated_by_natives_running_no_program_code_copy_nothing() {
    check("owned_in_place.qz", 0);
}

/// #927: the forms whose native may run code of the program (an
/// element's, a key's or the argument's own `==` or `hash`, a `data`
/// type's own, an instance of a class in a `data` value) copy once each,
/// the place keeping its value meanwhile.
#[test]
fn fields_updated_by_natives_running_program_code_copy_once_each() {
    check("owned_copies.qz", 8);
}

/// #987: a native calling its block through a kept activation, which
/// borrows the arguments, copies no more than the general path did: an
/// element the collection still holds copies once when the block updates
/// it, a fresh value made per call (a line, a match) none, and
/// `Hash#each`'s `[k, v]` once when a `|pair|` block updates it.
#[test]
fn a_kept_block_caller_copies_no_more_than_before() {
    check("kept_block_args.qz", 1100);
}

/// #1123: `HTTP.parse_query` and `URI.decode_www_form` gather the values
/// of one name without copying those before (main: 796 on the VM, one
/// per value but each name's first).
#[test]
fn query_values_of_one_name_copy_nothing() {
    check("query_values.qz", 0);
}

/// #993: `Hash#each` and `Hash::Builder#each` hand a destructuring block the
/// key and the value apart: a value the hash holds still copies once when
/// the block updates it, and a `|pair|` block's fresh pair once, as on
/// main.
#[test]
fn hash_each_destructuring_copies_as_before() {
    check("hash_each_pairs.qz", 500);
}

/// #988: a native called with its arguments borrowed copies no more
/// than with an argument list, for the natives that keep the list itself
/// and those that keep an argument.
#[test]
fn a_native_with_borrowed_arguments_copies_no_more_than_before() {
    check("borrowed_args.qz", 201);
}

/// #939: a construction compiled inline copies what the runtime's did: an
/// argument kept in a field once when the caller's variable is updated
/// after, and a fresh last value of `initialize` none.
#[test]
fn an_inline_construction_copies_no_more_than_before() {
    check("construct_inline.qz", 200);
}

/// #1000: an inline construction's collection defaults, run by a direct
/// call of their functions, are a new value per object, as the runtime's
/// loop made them: updating one in place copies nothing (main: 0 on
/// both).
#[test]
fn inline_field_defaults_are_each_objects_own() {
    check("field_defaults.qz", 0);
}

/// #704: a `data` value's collection field updated with the old value
/// given up each time is taken from its only holder, not copied (main:
/// 399 on both).
#[test]
fn a_data_values_field_is_taken_from_its_only_holder() {
    check("field_take.qz", 0);
}

/// #938: a call left to its defaults, inlined, copies no more than the
/// call did (main: 0 on both): a fresh collection default updated in
/// place by the body.
#[test]
fn an_inlined_default_copies_no_more_than_the_call() {
    check("inline_defaults.qz", 0);
}

/// #941: a direct call binding keywords in compiled code copies no more
/// than the runtime's binding (main: 400 on both): the same on the VM,
/// which binds them as before, and fewer compiled, where an argument
/// passed by keyword and not read again is moved into the call.
#[test]
fn keyword_calls_copy_no_more_than_before() {
    let path = program("keyword_calls.qz");
    assert_eq!(on_vm(&path, COPIES), 400, "on the VM");
    let n = compiled(&path, COPIES);
    assert!(n <= 400, "compiled: {n} copies, main's 400");
    assert_eq!(n, 200, "compiled");
}

#[test]
fn an_early_exit_from_any_or_all_leaves_no_reference_behind() {
    check("early_exit.qz", 0);
}

#[test]
fn a_break_out_of_a_loop_leaves_no_reference_behind() {
    check("break_exit.qz", 0);
}

#[test]
fn a_quoted_block_leaves_no_reference_behind() {
    // The `Quoted` given for a block (docs/14 §6), with its captures and
    // its closure's copies, is released after its call.
    check("quoted.qz", 0);
}

#[test]
fn a_collection_owned_by_a_task_is_updated_in_place() {
    // docs/04 §4's count table: updated through a channel by the task
    // that owns it, never shared.
    check("task_owned.qz", 0);
}

#[test]
fn a_field_read_through_a_handle_copies_nothing() {
    // docs/14 §5: `ref.get(self)` is the field read `@items` is.
    check("handles.qz", 0);
}

#[test]
fn task_blocking_moves_the_captures_its_caller_reads_no_more() {
    // #478: of the fixture's captures, those read again, shared with
    // another closure, read by a handler or by the next turn of a loop
    // are copied; the five others (one per call that is their last use)
    // move, on the VM and compiled.
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/blocking_captures.qz");
    assert_eq!(on_vm(&path, MOVED), 5, "on the VM");
    assert_eq!(compiled(&path, MOVED), 5, "compiled");
}

#[test]
fn task_blocking_hands_unique_boxed_values_over_whole() {
    // #479: of the fixture's results, the rows, a fresh row beside a kept
    // one, the hash, the string among symbols and the two circles move;
    // the rest is copied, on the VM and compiled.
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/blocking_boxed.qz");
    assert_eq!(on_vm(&path, MOVED), 6, "on the VM");
    assert_eq!(compiled(&path, MOVED), 6, "compiled");
}
