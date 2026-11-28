//! `QUARZ_VERIFY`: the interpreter checks the facts compiled code trusts.
//! A program the checker accepts never violates one, so each test lowers
//! one and changes its QIR to lie, runs it in a child process (a violation
//! stops the process) and expects the report.

mod common;

use std::process::Command;

use quarz_ir::{Inst, Module};

/// Run `module` in a child of this test binary, which re-enters the test
/// named `name` with `QUARZ_VERIFY_CHILD` set and runs it there: the
/// child's exit code and standard error.
fn in_child(name: &str, module: impl FnOnce() -> Module) -> (Option<i32>, String) {
    in_child_with(name, "1", module)
}

/// `in_child`, with `QUARZ_VERIFY` set to `verify`.
fn in_child_with(
    name: &str,
    verify: &str,
    module: impl FnOnce() -> Module,
) -> (Option<i32>, String) {
    in_child_env(name, Some(verify), module)
}

/// `in_child`, with `QUARZ_VERIFY` set to `verify`, or removed from the
/// child's environment for `None` (`cargo test` sets it for this binary).
fn in_child_env(
    name: &str,
    verify: Option<&str>,
    module: impl FnOnce() -> Module,
) -> (Option<i32>, String) {
    if std::env::var("QUARZ_VERIFY_CHILD").as_deref() == Ok(name) {
        let code = quarz_cli::run_module(module(), Vec::new());
        std::process::exit(code);
    }
    let mut cmd = Command::new(std::env::current_exe().unwrap());
    cmd.args([name, "--exact", "--nocapture", "--test-threads=1"])
        .env("QUARZ_VERIFY_CHILD", name);
    match verify {
        Some(v) => cmd.env("QUARZ_VERIFY", v),
        None => cmd.env_remove("QUARZ_VERIFY"),
    };
    let out = cmd.output().expect("run the test binary");
    (
        out.status.code(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    )
}

fn class_id(module: &Module, name: &str) -> u32 {
    module
        .world
        .classes
        .iter()
        .position(|c| c.name == name)
        .unwrap_or_else(|| panic!("no class {name}")) as u32
}

/// Every instruction of every function, to change.
fn insts(module: &mut Module) -> impl Iterator<Item = &mut Inst> {
    module
        .functions
        .iter_mut()
        .flat_map(|f| f.blocks.iter_mut())
        .flat_map(|b| b.insts.iter_mut())
}

#[test]
fn an_array_word_read_out_of_range_stops_the_program() {
    let (code, err) = in_child("an_array_word_read_out_of_range_stops_the_program", || {
        let mut module = common::lower("xs = [1, 2, 3]\ns = 0\nxs.each { |x| s += x }\np s\n");
        // The loop reads the element at the array's length instead.
        let main = module.units.last().unwrap().body as usize;
        let f = &mut module.functions[main];
        let len = f
            .blocks
            .iter()
            .flat_map(|b| &b.insts)
            .find_map(|i| match i {
                Inst::Len { dst, .. } => Some(*dst),
                _ => None,
            })
            .expect("the loop's length");
        let mut changed = false;
        for inst in f.blocks.iter_mut().flat_map(|b| b.insts.iter_mut()) {
            if let Inst::ArrayGetWord { index, .. } = inst {
                *index = len;
                changed = true;
            }
        }
        assert!(changed, "no ArrayGetWord");
        module
    });
    assert_eq!(code, Some(101), "{err}");
    assert!(
        err.contains("QIR fact violated: ArrayGetWord index 3 out of range (len 3)"),
        "{err}"
    );
}

#[test]
fn a_counted_value_in_a_register_heap_possible_leaves_out_stops_the_program() {
    // #536 step 9: compiled code never releases a register outside
    // `live::heap_possible`. A comparison's result is a `Bool` by the
    // checker's types, so `heap_possible` leaves its register out; here
    // a comparison is added of objects whose `<` returns an array (a
    // broken promise), so a counted value lands there. (A rewrite storing a
    // counted value through an instruction `heap_possible` marks, a call
    // or a constant that is not a number, marks the register itself, so
    // only such a broken type fact reaches the check.)
    let (code, err) = in_child(
        "a_counted_value_in_a_register_heap_possible_leaves_out_stops_the_program",
        || {
            let mut module = common::lower(
                "class X\n  def <(o: X) -> Array[Int] = [1, 2]\nend\np(X.new < X.new)\n",
            );
            // After the first `X.new`, a comparison of that object with
            // itself, into a register of its own that nothing else writes
            // (`X#<` itself is inlined at the program's call, and
            // register sharing may give a register to an object too).
            let x = class_id(&module, "X");
            let main = module.units.last().unwrap().body as usize;
            let f = &mut module.functions[main];
            let fresh = f.nregs;
            let mut changed = false;
            'blocks: for b in &mut f.blocks {
                for i in 0..b.insts.len() {
                    if let Inst::Call {
                        dst,
                        kind: quarz_ir::CallKind::Construct { class, .. },
                        ..
                    } = &b.insts[i]
                    {
                        if *class == x {
                            let obj = *dst;
                            b.insts.insert(
                                i + 1,
                                Inst::BinOp {
                                    dst: fresh,
                                    op: quarz_ir::FastOp::Lt,
                                    lhs: obj,
                                    rhs: obj,
                                    method: None,
                                },
                            );
                            let line = b.lines[i];
                            b.lines.insert(i + 1, line);
                            changed = true;
                            break 'blocks;
                        }
                    }
                }
            }
            f.nregs += 1;
            assert!(changed, "no construction of X");
            module
        },
    );
    assert_eq!(code, Some(101), "{err}");
    assert!(
        err.contains("QIR fact violated: BinOp in ")
            && err.contains("wrote an Array to r")
            && err.contains("which `live::heap_possible` says holds no counted value"),
        "{err}"
    );
}

/// `module` with native `key`'s declared result changed to `ty`, shown
/// as `shown`: the native, honest, now returns what its declaration (as
/// shipped) does not admit (#1187).
fn with_native_result(mut module: Module, key: &str, ty: quarz_ir::RtType, shown: &str) -> Module {
    let m = module
        .world
        .methods
        .iter_mut()
        .find(|m| m.native_key.as_deref() == Some(key))
        .unwrap_or_else(|| panic!("no native {key}"));
    m.result_test = Some(ty);
    m.result_union = None;
    m.ret = Some(shown.to_string());
    module
}

/// The program of the native result tests: `String#size` (an `Int`) and
/// `Hash#[]?` (nil for a missing key).
const NATIVES: &str = "h = {\"a\" => 1}\np \"ab\".size, h[\"b\"]?\n";

/// #1187: what a native returns is checked against its declared result
/// (`RtMethod::result_test`) under `QUARZ_VERIFY`: a value of another
/// class stops the program, naming the native.
#[test]
fn a_native_returning_another_class_stops_the_program() {
    let name = "a_native_returning_another_class_stops_the_program";
    let (code, err) = in_child(name, || {
        let module = common::lower(NATIVES);
        let s = class_id(&module, "String");
        with_native_result(module, "String#size", quarz_ir::RtType::Class(s), "String")
    });
    assert_eq!(code, Some(101), "{err}");
    assert!(
        err.contains("QIR fact violated: native `String#size` returned a value of class Int, but its declared result is String"),
        "{err}"
    );
}

/// #1187: nil from a native whose declared result does not admit it.
#[test]
fn a_native_returning_nil_for_a_class_stops_the_program() {
    let name = "a_native_returning_nil_for_a_class_stops_the_program";
    let (code, err) = in_child(name, || {
        let module = common::lower(NATIVES);
        let s = class_id(&module, "String");
        with_native_result(module, "Hash#[]?", quarz_ir::RtType::Class(s), "String")
    });
    assert_eq!(code, Some(101), "{err}");
    assert!(
        err.contains("QIR fact violated: native `Hash#[]?` returned a value of class Nil, but its declared result is String"),
        "{err}"
    );
}

/// #1187: a value outside a declared union stops the program; one inside
/// it does not.
#[test]
fn a_native_result_outside_its_union_stops_the_program() {
    let name = "a_native_result_outside_its_union_stops_the_program";
    let (code, err) = in_child(name, || {
        let module = common::lower(NATIVES);
        let (s, f) = (class_id(&module, "String"), class_id(&module, "Float"));
        use quarz_ir::RtType::{Class, Union};
        with_native_result(
            module,
            "String#size",
            Union(vec![Class(s), Class(f)]),
            "String | Float",
        )
    });
    assert_eq!(code, Some(101), "{err}");
    assert!(
        err.contains("QIR fact violated: native `String#size` returned a value of class Int, but its declared result is String | Float"),
        "{err}"
    );
}

/// #1187: a value inside the declared union passes.
#[test]
fn a_native_result_inside_its_union_runs() {
    let name = "a_native_result_inside_its_union_runs";
    let (code, err) = in_child(name, || {
        let module = common::lower(NATIVES);
        let (s, i) = (class_id(&module, "String"), class_id(&module, "Int"));
        use quarz_ir::RtType::{Class, Union};
        with_native_result(
            module,
            "String#size",
            Union(vec![Class(s), Class(i)]),
            "String | Int",
        )
    });
    assert_eq!(code, Some(0), "{err}");
    assert!(!err.contains("QIR fact violated"), "{err}");
}

/// #1190: a native declared `-> Self` is checked against the receiver's
/// class, not its owner: `String#size` shipped as returning `Self` (its
/// owner-based test admitting anything) stops the program on its `Int`.
#[test]
fn a_native_result_of_self_is_tested_as_the_receivers_class() {
    let name = "a_native_result_of_self_is_tested_as_the_receivers_class";
    let (code, err) = in_child(name, || {
        let module = common::lower(NATIVES);
        let mut module = with_native_result(module, "String#size", quarz_ir::RtType::Any, "Self");
        let m = module
            .world
            .methods
            .iter_mut()
            .find(|m| m.native_key.as_deref() == Some("String#size"))
            .unwrap();
        m.result_self = Some(quarz_ir::RtType::Nothing);
        module
    });
    assert_eq!(code, Some(101), "{err}");
    assert!(
        err.contains("QIR fact violated: native `String#size` returned a value of class Int, but its declared result is Self, with `Self` the receiver's class String"),
        "{err}"
    );
}

/// #1190: `Object#dup` (`-> Self`) on an object of a subclass returns
/// one of the receiver's class, which the check, exact now, admits.
#[test]
fn a_native_result_of_self_of_the_receivers_class_runs() {
    let name = "a_native_result_of_self_of_the_receivers_class_runs";
    let (code, err) = in_child(name, || {
        let module = common::lower("class A\nend\nclass B < A\nend\np B.new.dup.class\n");
        let m = module
            .world
            .methods
            .iter()
            .find(|m| m.native_key.as_deref() == Some("Object#dup"))
            .expect("Object#dup");
        assert_eq!(m.result_self, Some(quarz_ir::RtType::Nothing));
        module
    });
    assert_eq!(code, Some(0), "{err}");
    assert!(!err.contains("QIR fact violated"), "{err}");
}

#[test]
fn a_field_read_on_another_class_stops_the_program() {
    let (code, err) = in_child("a_field_read_on_another_class_stops_the_program", || {
        let mut module = common::lower(
            "class A\n  var @x: Int\n  def initialize(@x: Int) end\n  def x -> Int = @x\nend\n\
             class B\n  var @y: Int\n  def initialize(@y: Int) end\nend\n\
             p A.new(1).x\np B.new(2)\n",
        );
        // Reads of A's field claim it is B's.
        let (a, b) = (class_id(&module, "A"), class_id(&module, "B"));
        let mut changed = false;
        for inst in insts(&mut module) {
            if let Inst::FieldGet { class, .. } = inst {
                if *class == a {
                    *class = b;
                    changed = true;
                }
            }
        }
        assert!(changed, "no FieldGet of A");
        module
    });
    assert_eq!(code, Some(101), "{err}");
    assert!(
        err.contains("QIR fact violated: FieldGet of B on a A"),
        "{err}"
    );
}

/// The program of `a_field_read_on_another_class_stops_the_program`: reads
/// of `A`'s field claiming it is `B`'s.
fn field_read_on_another_class() -> Module {
    let mut module = common::lower(
        "class A\n  var @x: Int\n  def initialize(@x: Int) end\n  def x -> Int = @x\nend\n\
         class B\n  var @y: Int\n  def initialize(@y: Int) end\nend\n\
         p A.new(1).x\np B.new(2)\n",
    );
    let (a, b) = (class_id(&module, "A"), class_id(&module, "B"));
    for inst in insts(&mut module) {
        if let Inst::FieldGet { class, .. } = inst {
            if *class == a {
                *class = b;
            }
        }
    }
    module
}

/// With `QUARZ_VERIFY` unset, a debug build checks the facts as with `1`
/// (#536 step 10), a release build does not; `0` turns the checks off.
#[test]
fn a_debug_build_checks_the_facts_by_default() {
    let (code, err) = in_child_env(
        "a_debug_build_checks_the_facts_by_default",
        None,
        field_read_on_another_class,
    );
    if cfg!(debug_assertions) {
        assert_eq!(code, Some(101), "{err}");
        assert!(
            err.contains("QIR fact violated: FieldGet of B on a A"),
            "{err}"
        );
    } else {
        assert_eq!(code, Some(0), "{err}");
        assert!(!err.contains("QIR fact violated"), "{err}");
    }
}

#[test]
fn verify_zero_turns_the_checks_off() {
    let (code, err) = in_child_env(
        "verify_zero_turns_the_checks_off",
        Some("0"),
        field_read_on_another_class,
    );
    assert_eq!(code, Some(0), "{err}");
    assert!(!err.contains("QIR fact violated"), "{err}");
}

#[test]
fn an_int_operator_on_a_float_stops_the_program() {
    let (code, err) = in_child("an_int_operator_on_a_float_stops_the_program", || {
        let mut module =
            common::lower("def f(a: Float, b: Float) -> Float = a + b\np f(1.5, 2.0)\n");
        // `Float#+` claimed to be `Int#+`.
        let int_plus = module
            .world
            .methods
            .iter()
            .position(|m| m.owner == module.world.builtin.int && m.name == "+")
            .expect("Int#+") as u32;
        let float = module.world.builtin.float;
        let methods = module.world.methods.clone();
        let mut changed = false;
        for inst in insts(&mut module) {
            if let Inst::BinOp {
                method: Some(m), ..
            } = inst
            {
                if methods[*m as usize].owner == float {
                    *m = int_plus;
                    changed = true;
                }
            }
        }
        assert!(changed, "no Float BinOp");
        module
    });
    assert_eq!(code, Some(101), "{err}");
    assert!(
        err.contains("QIR fact violated: BinOp Int#+ on a Float"),
        "{err}"
    );
}

// ----- The checker of the QIR the passes leave (quarz_lower::verify) -----

use quarz_lower::verify::{verify, Stage};

/// A program with a word loop, a handler, a call and constants: it
/// passes the checks, and each test breaks one thing in its `<main>`.
const SAMPLE: &str =
    "def f(n: Int) -> Int\n  begin\n    10 / n\n  rescue ZeroDivisionError\n    0\n  end\nend\n\
    def g(n: Int) -> Int\n  begin\n    n + 1\n  ensure\n    p n\n  end\nend\n\
    xs = [1, 2, 3]\ns = 0\nxs.each { |x| s += x }\nys = xs.map { |x| x * 2 }\n\
    p f(s), f(0), g(1), ys\n";

/// The violations of `<main>` after `stage` once `change` broke it.
fn broken(stage: Stage, change: impl FnOnce(&mut quarz_ir::Function)) -> Vec<String> {
    let mut module = common::lower(SAMPLE);
    let main = module.units.last().unwrap().body as usize;
    let n = module.functions.len();
    assert!(verify(&module.functions[main], &module.world, n, Stage::Moves).is_empty());
    change(&mut module.functions[main]);
    verify(&module.functions[main], &module.world, n, stage)
        .into_iter()
        .map(|v| v.what)
        .collect()
}

/// The functions of the lowered sample pass, after the last pass.
#[test]
fn lowered_functions_pass_the_checks() {
    let module = common::lower(SAMPLE);
    let n = module.functions.len();
    for f in &module.functions {
        let found = verify(f, &module.world, n, Stage::Moves);
        assert!(found.is_empty(), "{}: {found:?}", f.name);
    }
}

/// The copy of a shareable procedure that uses neither its creator's
/// `self` nor its method block drops them (`Function::unused`, #706): a
/// read of either there is found.
#[test]
fn a_read_of_what_a_blocks_copy_drops_is_found() {
    const SRC: &str = "class C\n  var @n: Int = 0\n  def make(&blk: shareable (Int) -> Int) -> shareable () -> Int = -> { [1].map { |x| x + 1 }.sum }\nend\np C.new.make { |x| x }.call\n";
    let found = |inst: fn(u32) -> Inst| -> String {
        let mut module = common::lower(SRC);
        let by_name = |name: &str| {
            (module.functions.iter())
                .position(|f| f.name == name)
                .unwrap_or_else(|| panic!("no {name}"))
        };
        let lambda = by_name("lambda in C#make");
        let unused = module.functions[lambda].unused;
        assert!(unused.self_val && unused.method_block, "{unused:?}");
        // As lowered, it passes.
        quarz_lower::verify::check(&module.functions, &module.world, Stage::Moves);
        // A read into a register of its own.
        let f = &mut module.functions[lambda];
        let dst = f.nregs;
        f.nregs += 1;
        f.blocks[0].insts.insert(0, inst(dst));
        let line = f.blocks[0].lines.first().copied().unwrap_or(0);
        f.blocks[0].lines.insert(0, line);
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            quarz_lower::verify::check(&module.functions, &module.world, Stage::Moves)
        }));
        let err = r.expect_err("the read is found");
        (err.downcast_ref::<String>().cloned()).unwrap_or_default()
    };
    let err = found(|dst| Inst::SelfRef { dst });
    assert!(
        err.contains("reads `self`, which the copy of this block drops"),
        "{err}"
    );
    let err = found(|dst| Inst::BlockParam { dst });
    assert!(err.contains("reads the method's block"), "{err}");
}

/// #939: a construction's result is never a register its handler reads
/// (compiled code builds the object there before `initialize` runs): a
/// lowered program passes, and one whose construction writes the
/// variable the handler path reads is found.
#[test]
fn a_construction_into_a_register_its_handler_reads_is_found() {
    const SRC: &str = "class Pt\n  @x: Int\n  def initialize(x: Int)\n    raise ArgumentError, \"neg\" if x < 0\n    @x = x\n  end\n  def x -> Int = @x\nend\ndef f(n: Int) -> Int\n  p = Pt.new(1)\n  begin\n    p = Pt.new(n)\n  rescue ArgumentError\n  end\n  p.x\nend\np f(-1)\n";
    let mut module = common::lower(SRC);
    let n = module.functions.len();
    let fi = (module.functions.iter())
        .position(|f| f.name == "main#f")
        .expect("f");
    assert!(verify(&module.functions[fi], &module.world, n, Stage::Moves).is_empty());
    // The construction in the `begin` writes the variable itself.
    let f = &mut module.functions[fi];
    let (bi, ii) = (f.blocks.iter().enumerate())
        .filter(|(_, b)| b.handler.is_some())
        .find_map(|(bi, b)| {
            b.insts
                .iter()
                .position(|i| {
                    matches!(
                        i,
                        Inst::Call {
                            kind: quarz_ir::CallKind::Construct { .. },
                            ..
                        }
                    )
                })
                .map(|ii| (bi, ii))
        })
        .expect("a construction under a handler");
    let var = f.blocks[bi].insts[ii + 1..]
        .iter()
        .find_map(|i| match i {
            Inst::Take { dst, .. } | Inst::Move { dst, .. } => Some(*dst),
            _ => None,
        })
        .expect("the move into the variable");
    let Inst::Call { dst, .. } = &mut f.blocks[bi].insts[ii] else {
        unreachable!()
    };
    *dst = var;
    let found: Vec<String> = verify(&module.functions[fi], &module.world, n, Stage::Lowered)
        .into_iter()
        .map(|v| v.what)
        .collect();
    assert!(
        found
            .iter()
            .any(|w| w.contains("a construction's result") && w.contains("is read by its handler")),
        "{found:?}"
    );
}

fn first_inst(f: &mut quarz_ir::Function, pick: impl Fn(&Inst) -> bool) -> &mut Inst {
    f.blocks
        .iter_mut()
        .flat_map(|b| b.insts.iter_mut())
        .find(|i| pick(i))
        .expect("the instruction")
}

#[test]
fn a_word_read_of_another_register_is_found() {
    let found = broken(Stage::Moves, |f| {
        let Inst::ArrayGetWord { arr, index, .. } =
            first_inst(f, |i| matches!(i, Inst::ArrayGetWord { .. }))
        else {
            unreachable!()
        };
        // The index register instead of the words.
        *arr = *index;
    });
    assert!(
        found.iter().any(|w| w.starts_with("ArrayGetWord reads")),
        "{found:?}"
    );
}

#[test]
fn a_register_past_the_function_is_found() {
    let found = broken(Stage::Moves, |f| {
        let n = f.nregs;
        let Inst::LoadConst { dst, .. } = first_inst(f, |i| matches!(i, Inst::LoadConst { .. }))
        else {
            unreachable!()
        };
        *dst = n;
    });
    assert!(found.iter().any(|w| w.contains("past the")), "{found:?}");
}

#[test]
fn a_clear_past_the_registers_is_found() {
    let found = broken(Stage::Moves, |f| {
        let n = f.nregs;
        f.blocks[0]
            .insts
            .push(Inst::ClearRegs { from: 0, to: n + 1 });
        f.blocks[0].lines.push(0);
    });
    assert!(
        found.iter().any(|w| w.starts_with("ClearRegs")),
        "{found:?}"
    );
}

#[test]
fn a_jump_out_of_the_function_is_found() {
    let found = broken(Stage::Moves, |f| {
        let n = f.blocks.len() as u32;
        let b = f
            .blocks
            .iter_mut()
            .find(|b| matches!(b.term, quarz_ir::Term::Jump(_)))
            .unwrap();
        b.term = quarz_ir::Term::Jump(n);
    });
    assert!(
        found.iter().any(|w| w.starts_with("jump to block")),
        "{found:?}"
    );
}

#[test]
fn lines_out_of_step_with_instructions_are_found() {
    let found = broken(Stage::Moves, |f| f.blocks[0].lines.push(0));
    assert!(found.iter().any(|w| w.contains("lines for")), "{found:?}");
}

#[test]
fn a_constant_out_of_range_is_found() {
    let found = broken(Stage::Moves, |f| {
        let n = f.consts.len() as u32;
        let Inst::LoadConst { idx, .. } = first_inst(f, |i| matches!(i, Inst::LoadConst { .. }))
        else {
            unreachable!()
        };
        *idx = n;
    });
    assert!(found.iter().any(|w| w.starts_with("constant")), "{found:?}");
}

/// Moves exist only once `mark_moves` ran: the final QIR checked as if
/// after an earlier pass has them too early.
#[test]
fn moves_before_mark_moves_are_found() {
    let found = broken(Stage::Copyprop, |_| {});
    assert!(
        found
            .iter()
            .any(|w| w == "Take before mark_moves" || w.starts_with("moved operands")),
        "{found:?}"
    );
}

#[test]
fn a_catch_outside_its_handler_is_found() {
    let mut module = common::lower(SAMPLE);
    let n = module.functions.len();
    let f = module
        .functions
        .iter_mut()
        .find(|f| f.name == "main#f")
        .expect("f");
    let (bi, ii) = f
        .blocks
        .iter()
        .enumerate()
        .find_map(|(bi, b)| {
            b.insts
                .iter()
                .position(|i| matches!(i, Inst::CatchException { .. }))
                .map(|ii| (bi, ii))
        })
        .expect("a CatchException");
    let inst = f.blocks[bi].insts.remove(ii);
    let line = f.blocks[bi].lines.remove(ii);
    f.blocks[0].insts.insert(0, inst);
    f.blocks[0].lines.insert(0, line);
    let found: Vec<String> = verify(f, &module.world, n, Stage::Moves)
        .into_iter()
        .map(|v| v.what)
        .collect();
    assert!(
        found
            .iter()
            .any(|w| w == "CatchException outside a rescue handler"),
        "{found:?}"
    );
}

/// The violations of the function named `name` once `change` broke it.
fn broken_fn(name: &str, change: impl FnOnce(&mut quarz_ir::Function)) -> Vec<String> {
    let mut module = common::lower(SAMPLE);
    let n = module.functions.len();
    let f = module
        .functions
        .iter_mut()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("no {name}"));
    change(f);
    verify(f, &module.world, n, Stage::Moves)
        .into_iter()
        .map(|v| v.what)
        .collect()
}

#[test]
fn a_word_append_to_another_array_is_found() {
    let found = broken(Stage::Moves, |f| {
        let words = f
            .blocks
            .iter()
            .flat_map(|b| &b.insts)
            .find_map(|i| match i {
                Inst::ArrayWords { dst, .. } => Some(*dst),
                _ => None,
            })
            .expect("the read words");
        let Inst::ArrayPushWord { arr, .. } =
            first_inst(f, |i| matches!(i, Inst::ArrayPushWord { .. }))
        else {
            unreachable!()
        };
        // The array read as words, not the one being built.
        *arr = words;
    });
    assert!(
        found.iter().any(|w| w.starts_with("ArrayPushWord on")),
        "{found:?}"
    );
}

#[test]
fn an_update_of_a_borrowed_element_is_found() {
    let found = broken(Stage::Moves, |f| {
        let b = &mut f.blocks[0];
        b.insts.push(Inst::ArrayGetReg {
            dst: 0,
            arr: 1,
            index: 2,
            borrow: true,
            objects: false,
        });
        b.insts.push(Inst::ArrayPush { arr: 0, src: 2 });
        b.lines.extend([0, 0]);
    });
    assert!(
        found.iter().any(|w| w.contains("a borrowed element")),
        "{found:?}"
    );
}

#[test]
fn a_resume_of_something_not_caught_is_found() {
    let found = broken_fn("main#g", |f| {
        let b = f
            .blocks
            .iter()
            .position(|b| matches!(b.term, quarz_ir::Term::Resume(_)))
            .expect("a Resume");
        // Continues the parameter instead of the caught flow.
        f.blocks[b].term = quarz_ir::Term::Resume(0);
    });
    assert!(
        found.iter().any(|w| w.starts_with("Resume of")),
        "{found:?}"
    );
}

#[test]
fn a_block_that_is_its_own_handler_is_found() {
    let found = broken_fn("main#f", |f| {
        let b = f.blocks.iter().position(|b| b.handler.is_some()).unwrap();
        f.blocks[b].handler.as_mut().unwrap().block = b as u32;
    });
    assert!(
        found.iter().any(|w| w == "the block is its own handler"),
        "{found:?}"
    );
}

#[test]
fn a_parameter_past_the_method_is_found() {
    let found = broken_fn("main#f", |f| {
        let Inst::Arg { index, .. } = first_inst(f, |i| matches!(i, Inst::Arg { .. })) else {
            unreachable!()
        };
        *index = 5;
    });
    assert!(found.iter().any(|w| w == "parameter 5 of 1"), "{found:?}");
}

// ----- Moves (C) -----

/// Where `pick` first matches in `f`: (block, instruction).
fn find(f: &quarz_ir::Function, pick: impl Fn(&Inst) -> bool) -> (usize, usize) {
    f.blocks
        .iter()
        .enumerate()
        .find_map(|(bi, b)| b.insts.iter().position(&pick).map(|ii| (bi, ii)))
        .expect("the instruction")
}

#[test]
fn a_read_after_a_take_is_found() {
    let found = broken(Stage::Moves, |f| {
        let (bi, ii) = find(f, |i| matches!(i, Inst::Take { .. }));
        let Inst::Take { src, .. } = f.blocks[bi].insts[ii] else {
            unreachable!()
        };
        // Its source read again just after.
        f.blocks[bi]
            .insts
            .insert(ii + 1, Inst::IsNil { dst: src, src });
        f.blocks[bi].lines.insert(ii + 1, 0);
    });
    assert!(
        found.iter().any(|w| w.contains("moved out or released")),
        "{found:?}"
    );
}

#[test]
fn a_read_after_a_release_is_found() {
    // (A call after the last read keeps the end of `c`'s scope.)
    let mut module =
        common::lower("class C\nend\ndef h -> Void\n  c = C.new\n  p c\n  p 1\nend\nh\n");
    let n = module.functions.len();
    let f = module
        .functions
        .iter_mut()
        .find(|f| f.name == "main#h")
        .unwrap();
    let (bi, ii) = find(f, |i| matches!(i, Inst::Release { .. }));
    let Inst::Release { src } = f.blocks[bi].insts[ii] else {
        unreachable!()
    };
    f.blocks[bi]
        .insts
        .insert(ii + 1, Inst::IsNil { dst: src, src });
    f.blocks[bi].lines.insert(ii + 1, 0);
    let found: Vec<String> = verify(f, &module.world, n, Stage::Moves)
        .into_iter()
        .map(|v| v.what)
        .collect();
    assert!(
        found.iter().any(|w| w.contains("moved out or released")),
        "{found:?}"
    );
}

#[test]
fn an_operand_moved_and_read_again_is_found() {
    let found = broken(Stage::Moves, |f| {
        let (bi, ii) = find(
            f,
            |i| matches!(i, Inst::Call { args, .. } if !args.is_empty()),
        );
        let Inst::Call { args, moved, .. } = &mut f.blocks[bi].insts[ii] else {
            unreachable!()
        };
        // The first argument moved, and read once more after the call.
        *moved |= 1;
        let a = args[0];
        f.blocks[bi]
            .insts
            .insert(ii + 1, Inst::IsNil { dst: a, src: a });
        f.blocks[bi].lines.insert(ii + 1, 0);
    });
    assert!(
        found.iter().any(|w| w.contains("moved out or released")),
        "{found:?}"
    );
}

#[test]
fn a_take_into_itself_is_found() {
    let found = broken(Stage::Moves, |f| {
        let Inst::Take { dst, src } = first_inst(f, |i| matches!(i, Inst::Take { .. })) else {
            unreachable!()
        };
        *dst = *src;
    });
    assert!(found.iter().any(|w| w.contains("into itself")), "{found:?}");
}

// ----- Borrows (D) and register sharing (E) -----

#[test]
fn a_write_of_a_borrowed_element_register_is_found() {
    let mut module = common::lower(
        "class P\n  @v: Int\n  def initialize(@v: Int) end\n  def v -> Int = @v\nend\n\
         def s(ps: Array[P]) -> Int\n  t = 0\n  ps.each { |q| t += q.v }\n  t\nend\n\
         p s([P.new(1), P.new(2)])\n",
    );
    let n = module.functions.len();
    let f = module
        .functions
        .iter_mut()
        .find(|f| f.name == "main#s")
        .unwrap();
    let (bi, ii) = find(f, |i| matches!(i, Inst::ArrayGetReg { borrow: true, .. }));
    let Inst::ArrayGetReg { dst, .. } = f.blocks[bi].insts[ii] else {
        unreachable!()
    };
    // (Checked up to register sharing, see `verify::Checker::borrows`:
    // the final QIR's moves are too early there, and not the point.)
    let world = &module.world;
    let borrow_found = |f: &quarz_ir::Function| -> Vec<String> {
        verify(f, world, n, Stage::Regshare)
            .into_iter()
            .map(|v| v.what)
            .filter(|w| w.contains("borrow"))
            .collect()
    };
    assert!(borrow_found(f).is_empty());
    f.blocks[bi]
        .insts
        .insert(ii + 1, Inst::LoadConst { dst, idx: 0 });
    f.blocks[bi].lines.insert(ii + 1, 0);
    let found = borrow_found(f);
    assert!(
        found
            .iter()
            .any(|w| w.contains("a borrowed element's register")),
        "{found:?}"
    );
}

/// The lowered sample, its `<main>`'s index and the identity map of its
/// registers.
fn regshare_sample() -> (quarz_ir::Module, usize, Vec<u32>) {
    let module = common::lower(SAMPLE);
    let main = module.units.last().unwrap().body as usize;
    let map: Vec<u32> = (0..module.functions[main].nregs).collect();
    (module, main, map)
}

fn regshare_found(
    old: &quarz_ir::Function,
    new: &quarz_ir::Function,
    map: &[u32],
    world: &quarz_ir::RtWorld,
) -> Vec<String> {
    quarz_lower::verify::regshare(old, new, map, world)
        .into_iter()
        .map(|v| v.what)
        .collect()
}

#[test]
fn sharing_a_counted_and_a_number_register_is_found() {
    let (module, main, mut map) = regshare_sample();
    let f = &module.functions[main];
    let heap = quarz_ir::live::heap_possible(f, &module.world.methods);
    let mentioned = |r: u32| {
        f.blocks
            .iter()
            .flat_map(|b| &b.insts)
            .any(|i| i.defs().contains(&r) || i.uses().contains(&r))
    };
    let counted = (0..f.nregs)
        .find(|r| heap[*r as usize] && mentioned(*r))
        .unwrap();
    let number = (0..f.nregs)
        .find(|r| !heap[*r as usize] && mentioned(*r))
        .unwrap();
    map[number as usize] = counted;
    let new = quarz_lower::verify::renumber(f, &map);
    let found = regshare_found(f, &new, &map, &module.world);
    assert!(
        found
            .iter()
            .any(|w| w.contains("a counted and a non-counted")),
        "{found:?}"
    );
}

#[test]
fn a_result_sharing_an_operand_is_found() {
    let (module, main, mut map) = regshare_sample();
    let f = &module.functions[main];
    let (dst, lhs) = f
        .blocks
        .iter()
        .flat_map(|b| &b.insts)
        .find_map(|i| match i {
            Inst::BinOp { dst, lhs, .. } if dst != lhs => Some((*dst, *lhs)),
            _ => None,
        })
        .unwrap();
    map[dst as usize] = lhs;
    let new = quarz_lower::verify::renumber(f, &map);
    let found = regshare_found(f, &new, &map, &module.world);
    assert!(
        found.iter().any(|w| w.contains("shares with its operand")),
        "{found:?}"
    );
}

#[test]
fn a_clear_left_out_is_found() {
    let (module, main, map) = regshare_sample();
    let f = &module.functions[main];
    let heap = quarz_ir::live::heap_possible(f, &module.world.methods);
    let mut new = f.clone();
    let (bi, ii) = find(
        &new,
        |i| matches!(i, Inst::ClearRegs { from, to } if (*from..*to).any(|r| heap[r as usize])),
    );
    new.blocks[bi].insts.remove(ii);
    new.blocks[bi].lines.remove(ii);
    let found = regshare_found(f, &new, &map, &module.world);
    assert!(
        found.iter().any(|w| w.contains("no longer clears")),
        "{found:?}"
    );
}

#[test]
fn two_live_registers_sharing_are_found() {
    let (module, main, mut map) = regshare_sample();
    let f = &module.functions[main];
    let heap = quarz_ir::live::heap_possible(f, &module.world.methods);
    let live = quarz_ir::live::liveness(f);
    // Two registers of one kind live at once.
    let (a, b) = live
        .iter()
        .flatten()
        .find_map(|at| {
            let regs: Vec<u32> = (0..f.nregs).filter(|r| at[*r as usize]).collect();
            regs.iter().find_map(|a| {
                regs.iter()
                    .find(|b| a < *b && heap[*a as usize] == heap[**b as usize])
                    .map(|b| (*a, *b))
            })
        })
        .unwrap();
    map[b as usize] = a;
    let new = quarz_lower::verify::renumber(f, &map);
    let found = regshare_found(f, &new, &map, &module.world);
    assert!(
        found
            .iter()
            .any(|w| w.contains(&format!("r{a} and r{b}, both live"))),
        "{found:?}"
    );
}

#[test]
fn a_release_redirected_to_another_variable_is_found() {
    let (module, main, _) = regshare_sample();
    let f = &module.functions[main];
    let (bi, ii) = find(f, |i| matches!(i, Inst::Release { .. }));
    let Inst::Release { src } = f.blocks[bi].insts[ii] else {
        unreachable!()
    };
    let other = (0..f.nregs).find(|r| *r != src).unwrap();
    let mut new = f.clone();
    new.blocks[bi].insts[ii] = Inst::Release { src: other };
    let found: Vec<String> = quarz_lower::verify::copyprop(f, &new)
        .into_iter()
        .map(|v| v.what)
        .collect();
    assert!(
        found
            .iter()
            .any(|w| w.contains(&format!("releases r{other} instead of r{src}"))),
        "{found:?}"
    );
}

#[test]
fn a_release_removed_without_its_copy_is_found() {
    let (module, main, _) = regshare_sample();
    let f = &module.functions[main];
    assert!(quarz_lower::verify::copyprop(f, f).is_empty());
    let (bi, ii) = find(f, |i| matches!(i, Inst::Release { .. }));
    let mut new = f.clone();
    new.blocks[bi].insts.remove(ii);
    new.blocks[bi].lines.remove(ii);
    let found: Vec<String> = quarz_lower::verify::copyprop(f, &new)
        .into_iter()
        .map(|v| v.what)
        .collect();
    assert!(
        found.iter().any(|w| w.contains("is removed, with no copy")),
        "{found:?}"
    );
}

// ----- The moved shadow (QUARZ_VERIFY=moves) -----

#[test]
fn a_run_reading_a_moved_register_stops() {
    let name = "a_run_reading_a_moved_register_stops";
    let (code, err) = in_child_with(name, "moves", || {
        let mut module = common::lower("def f(s: String) -> String = s + \"!\"\np f(\"a\" * 2)\n");
        let main = module.units.last().unwrap().body as usize;
        let f = &mut module.functions[main];
        let (bi, ii) = find(
            f,
            |i| matches!(i, Inst::Call { moved, .. } if *moved & 0x7fff != 0),
        );
        let Inst::Call { args, moved, .. } = &f.blocks[bi].insts[ii] else {
            unreachable!()
        };
        // The operand the call moved, read again after it.
        let r = args[moved.trailing_zeros() as usize];
        f.blocks[bi]
            .insts
            .insert(ii + 1, Inst::IsNil { dst: r, src: r });
        f.blocks[bi].lines.insert(ii + 1, 0);
        module
    });
    assert_eq!(code, Some(101), "{err}");
    assert!(err.contains("QIR fact violated: IsNil reads r"), "{err}");
}

#[test]
fn a_read_of_a_capture_task_blocking_moved_stops() {
    // `live::blocking_takes` moves a capture only when the caller reads it
    // no more (#478): told to move one it reads after, the run stops.
    let name = "a_read_of_a_capture_task_blocking_moved_stops";
    let (code, err) = in_child_with(name, "moves", || {
        let mut module = common::lower(
            "def g -> Int\n  big = \"x\" * 100\n  n = Task.blocking { big.size }\n  n + big.size\nend\np g\n",
        );
        let block = module
            .functions
            .iter()
            .flat_map(|f| f.blocks.iter().flat_map(|b| &b.insts))
            .find_map(|i| match i {
                Inst::MakeBlock { func, .. } => Some(*func),
                _ => None,
            })
            .expect("the block");
        let f = &mut module.functions[block as usize];
        assert!(f.takes.is_empty(), "read after the call, yet moved");
        let (_, slot) = f.frame_facts().uses[0];
        f.takes = vec![slot];
        module
    });
    assert_eq!(code, Some(101), "{err}");
    assert!(
        err.contains("QIR fact violated: FrameGet reads frame slot"),
        "{err}"
    );
}

/// #630: an abstract method reached at run time is a check the checker
/// missed, a violation under `QUARZ_VERIFY`, otherwise a `TypeError` that
/// says so (not `NotImplementedError`). No program the checker accepts
/// reaches one (#644's net, R0's recorded witnesses, #632, #557), so the
/// arm is tested with #557's program, now accepted, its row for `K`
/// pointed at the requirement itself (`common::lower_with_no_witness`).
const ABSTRACT_REACHED: &str = "module Named\n  abstract def label -> String\nend\nmodule Gives\n  def label -> String = \"Gives\"\nend\nclass K\n  def initialize; end\nend\nmodule S2\n  extension K\n    include Gives\n    include Named\n  end\n  def self.n(k: K) -> Named = k\nend\ndef via(n: Named) -> String = n.label\nputs via(S2.n(K.new))\n";

#[test]
fn an_abstract_method_reached_is_a_violation() {
    let (code, err) = in_child_with("an_abstract_method_reached_is_a_violation", "moves", || {
        common::lower_with_no_witness(ABSTRACT_REACHED, "K", "Named", "label")
    });
    assert_eq!(code, Some(101), "{err}");
    assert!(
        err.contains("QIR fact violated: abstract method `label` called on K, which no check saw implemented"),
        "{err}"
    );
}

#[test]
fn an_abstract_method_reached_without_verify_is_a_type_error() {
    let (code, err) = in_child_with(
        "an_abstract_method_reached_without_verify_is_a_type_error",
        "0",
        || common::lower_with_no_witness(ABSTRACT_REACHED, "K", "Named", "label"),
    );
    assert_eq!(code, Some(1), "{err}");
    assert!(
        err.contains(
            "TypeError: abstract method `label` called on K, which no check saw implemented"
        ),
        "{err}"
    );
}

/// Whether function `name` of the program still makes a block: a call
/// with a literal block the inliner left a call (#1223).
fn makes_block(src: &str, name: &str) -> bool {
    let module = common::lower(src);
    let f = module
        .functions
        .iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("no function {name}"));
    f.blocks
        .iter()
        .flat_map(|b| b.insts.iter())
        .any(|i| matches!(i, Inst::MakeBlock { .. }))
}

/// #1223: a call giving a literal block to a method that yields is
/// inlined with the block where `inline`'s rules allow it (the module's
/// doc), and stays a call for each form they refuse.
#[test]
fn a_literal_block_is_inlined_only_where_the_rules_allow() {
    let helpers = "class W
  def with(&blk: () -> Int) -> Int
    yield
  end
  def two(&blk: (Int, Int) -> Int) -> Int
    yield 1, 2
  end
  def kept(&blk: () -> Int) -> Int
    blk.call
  end
  def guarded(&blk: () -> Int) -> Int
    begin
      yield
    rescue => e
      0
    end
  end
  def four(&blk: () -> Int) -> Int
    yield + yield + yield + yield
  end
  def thrice(&blk: () -> Int) -> Int
    yield + yield + yield
  end
  def pair(&blk: ([Int, Int]) -> Int) -> Int
    yield [1, 2]
  end
  def walk(n: Int, &blk: () -> Int) -> Int
    n == 0 ? yield : walk(n - 1) { yield }
  end
end
class A
  def with(&blk: () -> Int) -> Int
    yield
  end
end
class B < A
  def with(&blk: () -> Int) -> Int
    yield + 1
  end
end
";
    let big = (0..36)
        .map(|k| format!("x = x * 3 + {k}"))
        .collect::<Vec<_>>()
        .join("; ");
    let cases: Vec<(&str, String, bool)> = vec![
        ("inlined", "w.with { 1 }".into(), false),
        ("dynamic dispatch", "a.with { 1 }".into(), true),
        // (Nested uses are inlined level by level, `inline_calls`'s
        // passes bounding the depth.)
        ("nested", "w.with { w.with { 1 } }".into(), false),
        (
            "recursive through the block",
            "w.walk(2) { 1 }".into(),
            true,
        ),
        ("the block used as a value", "w.kept { 1 }".into(), true),
        ("a rescue in the callee", "w.guarded { 1 }".into(), true),
        ("more yields than allowed", "w.four { 1 }".into(), true),
        (
            "the block with a frame",
            "w.with { x = 1; f = -> { x }; f.call }".into(),
            true,
        ),
        (
            "two parameters, two arguments",
            "w.two { |a, b| a + b }".into(),
            false,
        ),
        (
            "a destructuring block",
            "w.pair { |a, b| a + b }".into(),
            true,
        ),
        ("an arity mismatch", "w.two { |a| a }".into(), true),
        (
            "over the size bound",
            format!("w.thrice {{ x = 1; {big}; x }}"),
            true,
        ),
    ];
    for (what, call, stays) in cases {
        let src = format!("{helpers}def site(w: W, a: A) -> Int = {call}\np site(W.new, B.new)\n");
        assert_eq!(makes_block(&src, "main#site"), stays, "{what}: {call}");
    }
}
