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
    if std::env::var("QUARZ_VERIFY_CHILD").as_deref() == Ok(name) {
        let code = quarz_cli::run_module(module(), Vec::new());
        std::process::exit(code);
    }
    let out = Command::new(std::env::current_exe().unwrap())
        .args([name, "--exact", "--nocapture", "--test-threads=1"])
        .env("QUARZ_VERIFY_CHILD", name)
        .env("QUARZ_VERIFY", "1")
        .output()
        .expect("run the test binary");
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
