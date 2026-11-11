//! What a program does as a process: its exit status, its output when it
//! ends with an error or a deadlock, its arguments and standard output.
//! The language itself is tested in Quarz, `std/test` (tests/std.rs).

mod common;
use common::{expect, run};

#[test]
fn an_unhandled_exception_ends_the_program_with_1() {
    let (code, out) = run("puts \"before\"\nraise \"unhandled\"\nputs \"after\"", &[]);
    assert_eq!(code, 1);
    assert_eq!(out, "before\n");
}

#[test]
fn exit_gives_the_status() {
    let (code, _) = run("exit(3)", &[]);
    assert_eq!(code, 3);
}

/// `exit` raises `SystemExit`, as Ruby's: every `ensure` it leaves runs
/// (also in a `begin` with a `rescue` clause, which does not catch it),
/// then the `at_exit` blocks, and the status is the one given.
#[test]
fn exit_runs_ensure_clauses_and_at_exit_blocks() {
    let (code, out) = run(
        "at_exit { puts \"at_exit\" }\n\
         begin\n  begin\n    exit 3\n  rescue => e\n    puts \"rescued\"\n  ensure\n    puts \"inner\"\n  end\n\
         ensure\n  puts \"outer\"\nend\nputs \"after\"",
        &[],
    );
    assert_eq!((code, out.as_str()), (3, "inner\nouter\nat_exit\n"));
}

#[test]
fn rescuing_system_exit_goes_on() {
    let (code, out) = run(
        "begin\n  exit 4\nrescue SystemExit => e\n  p e.status, e.success?\nend\n\
         begin\n  abort \"bye\"\nrescue SystemExit => e\n  p e.status, e.message\nend\nputs \"on\"",
        &[],
    );
    assert_eq!((code, out.as_str()), (0, "4\nfalse\n1\n\"bye\"\non\n"));
}

/// In a process of its own: `exit!` ends the one it runs in.
#[test]
fn exit_bang_skips_ensure_and_at_exit() {
    let dir = std::env::temp_dir().join(format!("quarz-run-exit-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("exit.qz");
    std::fs::write(
        &path,
        "at_exit { puts \"at_exit\" }\nbegin\n  puts \"before\"\n  exit!(5)\nensure\n  puts \"ensure\"\nend\n",
    )
    .unwrap();
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_quarz"))
        .arg("run")
        .arg(&path)
        .output()
        .expect("quarz");
    std::fs::remove_dir_all(&dir).ok();
    assert_eq!(out.status.code(), Some(5));
    assert_eq!(String::from_utf8_lossy(&out.stdout), "before\n");
}

/// In another task, `SystemExit` goes where the task's exceptions go: to
/// `await`, the scope's owner, `Task.timeout`'s caller, `Task.blocking`'s.
#[test]
fn exit_in_an_awaited_task_is_raised_in_the_caller() {
    for body in [
        "Task.spawn { exit 3 }.await",
        "Task.scope { |s| s.spawn { exit 3 } }",
        "Task.timeout(10.seconds) { exit 3 }",
        "Task.blocking { exit 3 }",
    ] {
        let (code, out) = run(
            &format!(
                "begin\n  {body}\nrescue SystemExit => e\n  puts \"rescued #{{e.status}}\"\nensure\n  puts \"ensure\"\nend\nputs \"after\""
            ),
            &[],
        );
        assert_eq!(
            (code, out.as_str()),
            (0, "rescued 3\nensure\nafter\n"),
            "{body}"
        );
    }
}

/// One nobody waits for is raised in the root task (the main one, or the
/// block of `Task.blocking`), as Ruby raises a thread's in the main thread.
#[test]
fn exit_in_a_task_nobody_awaits_or_a_blocking_block() {
    let (code, out) = run(
        "begin\n  Task.spawn { exit 6 }\n  Task.sleep(50.ms)\n  puts \"main still running\"\nensure\n  puts \"main ensure\"\nend",
        &[],
    );
    assert_eq!((code, out.as_str()), (6, "main ensure\n"));
    let (code, out) = run(
        "begin\n  begin\n    Task.blocking { exit 7 }\n  rescue ArgumentError\n    puts \"no\"\n  ensure\n    puts \"ensure\"\n  end\n\
         rescue SystemExit => e\n  puts \"rescued #{e.status}\"\nend",
        &[],
    );
    assert_eq!((code, out.as_str()), (0, "ensure\nrescued 7\n"));
}

/// The exit of a task nobody awaits is not lost while `Task.timeout`
/// waits for its cancelled block; `await` raises it again, as Ruby's
/// `Thread#join` does.
#[test]
fn an_exit_request_is_kept() {
    let (code, out) = run(
        "Task.spawn { Task.sleep(30.ms); exit 4 }\nbegin\n  Task.timeout(10.ms) do\n    begin\n      Task.sleep(1.second)\n\
         ensure\n      Task.uncancellable { Task.sleep(50.ms) }\n    end\n  end\nrescue Task::Timeout\n  puts \"timed out\"\nend\nputs \"after\"",
        &[],
    );
    assert_eq!((code, out.as_str()), (4, ""));
    let (code, out) = run(
        "t = Task.spawn { exit 3 }\nbegin\n  Task.sleep(10.ms)\nrescue SystemExit => e\n  puts \"sleep raised #{e.status}\"\nend\n\
         begin\n  p t.await\nrescue SystemExit\n  puts \"await raised\"\nend\nputs \"after\"",
        &[],
    );
    assert_eq!(
        (code, out.as_str()),
        (0, "sleep raised 3\nawait raised\nafter\n")
    );
    // `Task.timeout`'s block exiting in its `ensure`: the exit wins.
    let (code, out) = run(
        "begin\n  Task.timeout(10.ms) do\n    begin\n      Task.sleep(1.second)\n    ensure\n      exit 4\n    end\n  end\n\
         rescue Task::Timeout\n  puts \"timed out\"\nend",
        &[],
    );
    assert_eq!((code, out.as_str()), (4, ""));
}

/// A scope child's `exit` ends the program even while the scope's owner
/// is blocked in its own block (an HTTP server waiting for `shutdown`).
#[test]
fn exit_in_a_scope_child_reaches_a_blocked_owner() {
    let (code, out) = run(
        "begin\n  Task.scope do |s|\n    s.spawn { exit 5 }\n    Channel[Int].new.receive\n  end\nensure\n  puts \"main ensure\"\nend",
        &[],
    );
    assert_eq!((code, out.as_str()), (5, "main ensure\n"));
}

/// `Task.timeout`'s block is the caller's code: a scope in it takes its
/// children's exits as one in the caller would.
#[test]
fn exit_in_a_scope_in_a_timeout_block() {
    let (code, out) = run(
        "begin\n  Task.timeout(10.seconds) do\n    begin\n      Task.scope { |s| s.spawn { exit 1 } }\n    rescue SystemExit\n\
         puts \"rescued in block\"\n    end\n    nil\n  end\n  puts \"after\"\nrescue SystemExit\n  puts \"rescued outside\"\nend",
        &[],
    );
    assert_eq!((code, out.as_str()), (0, "rescued in block\nafter\n"));
    // An exit the block took, then the timeout raised in its `ensure`: as in
    // Ruby, the exception raised in an `ensure` replaces the one passing.
    let (code, out) = run(
        "Task.spawn { Task.sleep(30.ms); exit 3 }\nbegin\n  Task.timeout(60.ms) do\n    begin\n      Task.sleep(1.second)\n\
         ensure\n      Task.sleep(100.ms)\n    end\n  end\nrescue Task::Timeout\n  puts \"timeout\"\nend\nputs \"after\"",
        &[],
    );
    assert_eq!((code, out.as_str()), (0, "timeout\nafter\n"));
}

/// A failing scope child is not mistaken for its owner's cancellation.
#[test]
fn a_scope_child_failure_survives_the_owner_being_cancelled() {
    let (code, out) = run(
        "outer = Task.spawn do\n  begin\n    r = Task.scope do |s|\n      s.spawn { raise \"boom\" }\n      Task.uncancellable do\n        Task.yield\n        Task.yield\n      end\n      :value\n    end\n\
         puts \"scope returned #{r}\"\n  rescue Exception => e\n    puts \"scope raised #{e.message}\"\n  end\n  nil\nend\n\
         Task.yield\nouter.cancel\nouter.await",
        &[],
    );
    // The yields uncancellable: the block returns, and the scope then
    // awaits the failed child while its owner is cancelled.
    assert_eq!((code, out.as_str()), (0, "scope raised boom\n"));
}

/// An exit reaches a main task that computes, at its `Task.yield`.
#[test]
fn exit_reaches_a_computing_loop_that_yields() {
    let (code, out) = run(
        "Task.spawn { Task.sleep(10.ms); exit 6 }\nbegin\n  x = 0\n  loop do\n    x += 1\n    Task.yield\n  end\nensure\n  puts \"main ensure\"\nend",
        &[],
    );
    assert_eq!((code, out.as_str()), (6, "main ensure\n"));
}

/// From another task, `exit` ends the whole program, as in Ruby.
#[test]
fn exit_in_a_task_ends_the_program() {
    let (code, out) = run(
        "t = Task.spawn do\n  begin\n    exit 6\n  ensure\n    puts \"task ensure\"\n  end\nend\nt.await\nputs \"not reached\"",
        &[],
    );
    assert_eq!((code, out.as_str()), (6, "task ensure\n"));
}

#[test]
fn a_deadlock_ends_the_program_with_1() {
    let (code, out) = run("ch = Channel[Int].new\nputs \"waiting\"\nch.receive", &[]);
    assert_eq!(code, 1);
    assert_eq!(out, "waiting\n");
}

#[test]
fn arguments() {
    expect("puts ARGV.inspect", "[]\n");
    let (code, out) = run("puts ARGV.inspect, ARGV.size", &["x", "y"]);
    assert_eq!((code, out.as_str()), (0, "[\"x\", \"y\"]\n2\n"));
}

#[test]
fn standard_output() {
    expect(
        "STDOUT.puts \"to stdout\"\nSTDOUT.print \"a\", \"b\\n\"\nprint 1, 2\nputs\np 1, \"s\"",
        "to stdout\nab\n12\n1\n\"s\"\n",
    );
}

/// The server's default report of a handler's error, on STDERR, names
/// the method and the path as sent, still encoded (a decoded `%0a` would
/// forge a line), but not the query, which may carry a token.
#[test]
fn http_errors_are_reported_without_the_query() {
    let dir = std::env::temp_dir().join(format!("quarz-run-http-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("report.qz");
    std::fs::write(
        &path,
        r#"require "http"
h = HTTP.handler { |req| raise "boom" }
s = HTTP::Server.new(h, host: "127.0.0.1", port: 0)
port = s.local_address.port
Task.scope do |scope|
  scope.spawn { s.serve }
  ["/a/b?token=secret", "/x%0d%0aforged%3Fa?b"].each do |target|
    Task.timeout(10.seconds) do
      Socket.tcp("127.0.0.1", port) do |c|
        c.write("GET #{target} HTTP/1.1\r\nConnection: close\r\n\r\n")
        puts c.read.lines[0].chomp
      end
    end
  end
  s.shutdown
end
"#,
    )
    .unwrap();
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_quarz"))
        .arg("run")
        .arg(&path)
        .output()
        .unwrap();
    let _ = std::fs::remove_dir_all(&dir);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "HTTP/1.1 500 Internal Server Error\n".repeat(2)
    );
    assert_eq!(
        stderr,
        "HTTP::Server (GET /a/b): RuntimeError: boom\n\
         HTTP::Server (GET /x%0d%0aforged%3Fa): RuntimeError: boom\n"
    );
}

/// A `return` from a kept block called after its method returned has no
/// method to leave: the program ends with an error that says so.
#[test]
fn a_return_from_a_block_whose_method_returned() {
    let dir = std::env::temp_dir().join(format!("quarz-run-late-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("late.qz");
    std::fs::write(
        &path,
        r#"class K
  var @b: ((Int) -> Int)? = nil
  def keep(&b: (Int) -> Int) -> Void
    @b = b
  end
  def fire -> Int
    if (b = @b)
      b.call(1)
    else
      0
    end
  end
end
def m(k: K) -> Int
  k.keep { |x| return x + 12 }
  0
end
k = K.new
p m(k)
p k.fire
"#,
    )
    .unwrap();
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_quarz"))
        .arg("run")
        .arg(&path)
        .output()
        .unwrap();
    let _ = std::fs::remove_dir_all(&dir);
    assert_eq!(out.status.code(), Some(1));
    assert_eq!(String::from_utf8_lossy(&out.stdout), "0\n");
    assert!(
        String::from_utf8_lossy(&out.stderr).contains(
            "RuntimeError: `return` from a block whose method or lambda has already returned"
        ),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
}

/// `quarz --version` prints Cargo's version of the workspace, which a
/// release tag (`v` and the version) names too, and the commit it was
/// built from when built from a checkout (#449).
#[test]
fn version_prints_the_cargo_version() {
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_quarz"))
        .arg("--version")
        .output()
        .expect("quarz");
    assert!(out.status.success());
    let text = String::from_utf8_lossy(&out.stdout);
    let rest = text
        .strip_prefix(&format!("quarz {}", env!("CARGO_PKG_VERSION")))
        .unwrap_or_else(|| panic!("{text}"));
    let commit = rest.strip_prefix(" (").and_then(|r| r.strip_suffix(")\n"));
    assert!(
        rest == "\n"
            || commit.is_some_and(|c| c.len() == 12 && c.chars().all(|c| c.is_ascii_hexdigit())),
        "{text}"
    );
}

/// What runs does not depend on the checker's cache (#554): the lowering
/// takes every extension's include, not the ones active where it ran, so a
/// warm cache lowers a program as a cold one does. Each program runs with
/// the cache off, cold, then warm.
#[test]
fn an_extensions_include_dispatches_alike_with_a_warm_cache() {
    let dir = std::env::temp_dir().join(format!("quarz-warm-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let fixtures = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures");
    let programs: Vec<(String, std::path::PathBuf)> = vec![
        // A non-generic class, an extension's module over its superclass.
        (
            "over_superclass".into(),
            "module EM\n  def m(x: Int) -> String = \"sub\"\nend\nclass EB\n  def initialize; end\n  def m(x: Int) -> String = \"base\"\nend\nclass EC < EB\n  def initialize; end\nend\nextension EC\n  include EM\nend\ndef e(x: EB) -> String = x.m(1)\nputs e(EC.new)\n".into(),
        ),
        // An abstract method only an extension's module implements.
        (
            "abstract".into(),
            "abstract class EB\n  def initialize; end\n  abstract def m(x: Int) -> String\nend\nmodule EM\n  def m(x: Int) -> String = \"em\"\nend\nclass EC < EB\n  def initialize; end\nend\nextension EC\n  include EM\nend\ndef e(x: EB) -> String = x.m(1)\nputs e(EC.new)\n".into(),
        ),
    ]
    .into_iter()
    .map(|(name, src): (String, String)| {
        let path = dir.join(format!("{name}.qz"));
        std::fs::write(&path, src).unwrap();
        (name, path)
    })
    .chain(
        [
            "override_matrix",
            "conditional_extension_own_override",
            "conditional_extension_include_dispatch",
            "scoped_extension_include_dispatch",
            "scoped_extension_by_name",
            "extension_witness_by_name",
            "extension_optional_hook",
            "resolution_matrix",
            "extension_include_order",
            "extension_conformance_is_a",
            "extension_witness_order",
            "module_class_side",
            "extension_witness_three",
            "superclass_scoped_extension_order",
            "superclass_scoped_extension_using",
            "scoped_extensions_not_ambiguous",
            "scoped_extensions_super_order",
            "scoped_extensions_symbol_union",
            "class_call_scoped_extension",
            "class_call_scoped_extension_file",
            "scoped_extension_after_own",
            "scoped_extension_after_own_file",
            "super_past_abstract",
        ]
        .iter()
        .map(|n| (n.to_string(), std::path::Path::new(fixtures).join(format!("{n}.qz")))),
    )
    .collect();
    let cache = dir.join("cache");
    for (name, path) in &programs {
        let run = |env: (&str, &str)| {
            let out = std::process::Command::new(env!("CARGO_BIN_EXE_quarz"))
                .arg("run")
                .arg(path)
                .env_remove("QUARZ_NO_CACHE")
                .env_remove("QUARZ_CACHE_DIR")
                .env(env.0, env.1)
                .output()
                .unwrap();
            assert!(
                out.status.success(),
                "{name}: {}",
                String::from_utf8_lossy(&out.stderr)
            );
            String::from_utf8_lossy(&out.stdout).into_owned()
        };
        let off = run(("QUARZ_NO_CACHE", "1"));
        let cold = run(("QUARZ_CACHE_DIR", cache.to_str().unwrap()));
        let warm = run(("QUARZ_CACHE_DIR", cache.to_str().unwrap()));
        assert_eq!(off, cold, "{name}: cold");
        assert_eq!(off, warm, "{name}: warm");
    }
    let _ = std::fs::remove_dir_all(&dir);
}
