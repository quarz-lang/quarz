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
