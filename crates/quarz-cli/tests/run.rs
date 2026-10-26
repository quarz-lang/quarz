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
