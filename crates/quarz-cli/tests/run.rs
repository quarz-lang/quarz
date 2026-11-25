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

/// Run `src` with `quarz run` and `env`, in a directory of the test's
/// own (which `setup` may fill first): (status, stdout, stderr). A run
/// past 20 seconds is killed and reported as status -2: a hang fails the
/// test rather than holding up the run.
#[cfg(debug_assertions)]
fn run_with_env_in(
    name: &str,
    src: &str,
    env: &[(&str, &str)],
    setup: impl FnOnce(&std::path::Path),
) -> (i32, String, String) {
    use std::io::Read;
    let dir = std::env::temp_dir().join(format!("quarz-run-{name}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    setup(&dir);
    let file = dir.join("main.qz");
    std::fs::write(&file, src).unwrap();
    let mut child = std::process::Command::new(env!("CARGO_BIN_EXE_quarz"))
        .arg("run")
        .arg(&file)
        .current_dir(&dir)
        .envs(env.iter().copied())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .unwrap();
    let started = std::time::Instant::now();
    let code = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status.code().unwrap_or(-1);
        }
        if started.elapsed() > std::time::Duration::from_secs(20) {
            let _ = child.kill();
            let _ = child.wait();
            break -2;
        }
        std::thread::sleep(std::time::Duration::from_millis(20));
    };
    let (mut out, mut err) = (String::new(), String::new());
    child
        .stdout
        .take()
        .unwrap()
        .read_to_string(&mut out)
        .unwrap();
    child
        .stderr
        .take()
        .unwrap()
        .read_to_string(&mut err)
        .unwrap();
    let _ = std::fs::remove_dir_all(&dir);
    (code, out, err)
}

#[cfg(debug_assertions)]
fn run_with_env(name: &str, src: &str, env: &[(&str, &str)]) -> (i32, String, String) {
    run_with_env_in(name, src, env, |_| {})
}

/// Six lookups at once, each made to take 400 ms (a debug build's
/// `QUARZ_TEST_SLOW_LOOKUP`): with two lookup threads they run two at a
/// time, so they take three rounds; with six, one (#1128).
#[cfg(debug_assertions)]
#[test]
fn name_resolution_takes_at_most_its_threads() {
    let src = "require \"socket\"\nt0 = Time.monotonic\n\
               ts = (1..6).map { |_| Task.spawn { Socket.getaddrinfo(\"localhost\", 80).size } }\n\
               ts.each { |t| t.await }\nputs (Time.monotonic - t0).to_ms\n";
    let ms = |threads: &str| -> u64 {
        let (code, out, err) = run_with_env(
            &format!("lookup-slots-{threads}"),
            src,
            &[
                ("QUARZ_LOOKUP_THREADS", threads),
                ("QUARZ_TEST_SLOW_LOOKUP", "400"),
            ],
        );
        assert_eq!(code, 0, "{err}");
        out.trim().parse().unwrap()
    };
    let two = ms("2");
    assert!(two >= 1200, "two threads, six lookups of 400 ms: {two} ms");
    let six = ms("6");
    assert!(six < 1200, "six threads, six lookups of 400 ms: {six} ms");
}

/// A lookup waiting for the only lookup thread, whose task a timeout
/// cancels, is dropped unrun: the thread then has nothing to resolve
/// for it (#1128).
#[cfg(debug_assertions)]
#[test]
fn a_cancelled_lookup_waiting_for_a_thread_is_dropped() {
    let (code, out, err) = run_with_env(
        "lookup-dropped",
        "require \"socket\"\n\
         a = Task.spawn { Socket.getaddrinfo(\"localhost\", 80).size }\n\
         Task.sleep(50.ms)\n\
         begin\n  Task.timeout(100.ms) { Socket.getaddrinfo(\"localhost\", 80).size }\n\
         rescue Task::Timeout\n  puts \"timed out\"\nend\n\
         a.await\nTask.sleep(500.ms)\nputs \"done\"\n",
        &[
            ("QUARZ_LOOKUP_THREADS", "1"),
            ("QUARZ_TEST_SLOW_LOOKUP", "600"),
        ],
    );
    assert_eq!((code, out.as_str()), (0, "timed out\ndone\n"), "{err}");
    assert_eq!(
        err.matches("quarz: dropped a cancelled helper job").count(),
        1,
        "{err}"
    );
}

/// A helper thread that cannot be started (`QUARZ_TEST_HELPER_SPAWNS`
/// lets a debug build start only so many): while the pool has another,
/// the job waits for it; with none, the task gets a `SystemCallError`,
/// where the process used to panic (#1128).
#[cfg(debug_assertions)]
#[test]
fn a_helper_thread_that_cannot_start_is_an_error_not_a_panic() {
    let (code, out, err) = run_with_env(
        "helper-spawn",
        "require \"socket\"\nFile.write(\"a.txt\", \"abc\")\n\
         ts = (1..4).map { |_| Task.spawn { File.read(\"a.txt\") } }\n\
         puts ts.map { |t| t.await }.join(\" \")\n\
         begin\n  Socket.getaddrinfo(\"localhost\", 80)\n\
         rescue SystemCallError => e\n  puts \"#{e.class}: #{e.message}\"\nend\n",
        &[("QUARZ_TEST_HELPER_SPAWNS", "1")],
    );
    assert_eq!(
        (code, out.as_str()),
        (
            0,
            "abc abc abc abc\n\
             SystemCallError: start a helper thread: Resource temporarily unavailable (os error 11)\n"
        ),
        "{err}"
    );
}

/// A job that panics on its helper thread ends the program with status
/// 101, as a panic on a worker does: left alone, the thread ended and
/// the task waiting for the job's result stayed parked for good (#1156).
/// (What the program wrote to standard output is not flushed: the
/// process ends at once, as on a worker's panic.)
#[cfg(debug_assertions)]
#[test]
fn a_helper_job_that_panics_ends_the_program() {
    let (code, out, err) = run_with_env(
        "helper-panic",
        "puts \"before\"\nFile.write(\"a.txt\", \"x\")\nputs \"after\"\n",
        &[("QUARZ_TEST_PANIC_JOB", "1")],
    );
    assert_eq!(code, 101, "{out}{err}");
    assert!(
        err.contains("a helper thread's job panicked (QUARZ_TEST_PANIC_JOB)"),
        "{err}"
    );
}

/// A job submitted while another worker's thread is still starting gets
/// a thread of its own: it is not queued behind the starting one's job.
/// Here the first job reads a FIFO and ends only when the second writes
/// it, so one thread for both never ends (#1128, review round 1). Two
/// workers, a spawn that takes 300 ms, the write 100 ms after the read.
#[cfg(debug_assertions)]
#[test]
fn a_job_submitted_while_a_helper_starts_gets_its_own() {
    let (code, out, err) = run_with_env_in(
        "helper-starting",
        "a = Task.spawn { File.read(\"fifo\") }\n\
         b = Task.spawn { Task.sleep(100.ms); File.write(\"fifo\", \"through\"); nil }\n\
         b.await\nputs a.await\n",
        &[("QUARZ_THREADS", "2"), ("QUARZ_TEST_SPAWN_DELAY", "300")],
        |dir| {
            let made = std::process::Command::new("mkfifo")
                .arg(dir.join("fifo"))
                .status();
            assert!(made.unwrap().success());
        },
    );
    assert_eq!((code, out.as_str()), (0, "through\n"), "{err}");
}

/// A job queued while the pool's only thread is still starting, whose
/// own start fails, is not left without a thread when that one fails
/// too: both tasks get the error (#1128, review round 1). Two workers, no
/// start allowed, each taking 300 ms; the second lookup 100 ms after the
/// first.
#[cfg(debug_assertions)]
#[test]
fn jobs_queued_on_a_starting_helper_fail_with_it() {
    let (code, out, err) = run_with_env(
        "helper-start-fails",
        "require \"socket\"\n\
         def look(wait: Duration) -> String\n  Task.sleep(wait)\n  Socket.getaddrinfo(\"localhost\", 80)\n  \"resolved\"\n\
         rescue SystemCallError => e\n  e.message\nend\n\
         a = Task.spawn { look(0.ms) }\nb = Task.spawn { look(100.ms) }\nputs a.await\nputs b.await\n",
        &[
            ("QUARZ_THREADS", "2"),
            ("QUARZ_TEST_SPAWN_DELAY", "300"),
            ("QUARZ_TEST_HELPER_SPAWNS", "0"),
        ],
    );
    let failed = "start a helper thread: Resource temporarily unavailable (os error 11)\n";
    assert_eq!((code, out), (0, format!("{failed}{failed}")), "{err}");
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
        c.write("GET #{target} HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n")
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

/// `CommandLine.parse(ARGV)` ends the program on a mistake, with the
/// error, the usage and a pointer to `--help` on STDERR and the status
/// 2, and on `--help` with the help on STDOUT and the status 0.
#[test]
fn command_line_parse_exits_on_a_mistake_and_on_help() {
    let dir = std::env::temp_dir().join(format!("quarz-run-cl-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("tool.qz");
    std::fs::write(
        &path,
        r#"require "command_line"

class Tool < CommandLine
  option :jobs, Int, short: "j", default: 1, help: "workers"
end

puts "jobs=#{Tool.parse(ARGV).jobs}"
"#,
    )
    .unwrap();
    let run = |args: &[&str]| {
        let out = std::process::Command::new(env!("CARGO_BIN_EXE_quarz"))
            .arg("run")
            .arg(&path)
            .args(args)
            .output()
            .unwrap();
        (
            out.status.code(),
            String::from_utf8_lossy(&out.stdout).into_owned(),
            String::from_utf8_lossy(&out.stderr).into_owned(),
        )
    };
    let ok = run(&["-j3"]);
    let mistake = run(&["--jobs=many"]);
    let help = run(&["--help"]);
    let _ = std::fs::remove_dir_all(&dir);
    assert_eq!(ok, (Some(0), "jobs=3\n".to_string(), String::new()));
    assert_eq!(
        mistake,
        (
            Some(2),
            String::new(),
            "tool: option '--jobs': 'many' is not an integer\n\
             usage: tool [options]\n\
             Try 'tool --help' for more information.\n"
                .to_string()
        )
    );
    assert_eq!(
        help,
        (
            Some(0),
            "usage: tool [options]\n\
             \n\
             Options:\n  \
             -j, --jobs=JOBS  workers (default: 1)\n  \
             -h, --help       print this help and exit\n"
                .to_string(),
            String::new()
        )
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

/// The prelude's share of the runtime's tables comes from the snapshot
/// made when `quarz` was built, for a program that changes none of it
/// (#551), and is made at start-up otherwise; a debug build (this test's
/// `quarz`) compares the two every time it takes it. Seen through the
/// debug-only log `QUARZ_PRELUDE_SNAPSHOT_LOG`. "The prelude's" is by id
/// (the snapshot's first classes, methods and extensions), not by file:
/// a cog's root module has file 0, and it and what a program's
/// statements or declarations make all have ids past the prelude's. (A method generated into
/// a prelude class cannot be written: `def_method` generates into the
/// class whose `Meta::ClassDef` a statement runs on, a program's.)
#[test]
fn the_prelude_snapshot_is_taken_only_where_nothing_changes_it() {
    let dir = std::env::temp_dir().join(format!("quarz-prelude-snapshot-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let cases = [
        ("plain", "puts 1\n", &[][..], "taken, compared"),
        (
            "class",
            "module M\n  extension String\n    def shout -> String = upcase\n  end\nend\nputs 1\n",
            &[][..],
            "refused: prelude_unchanged",
        ),
        (
            "module",
            "module M\n  extension Comparable[T]\n    def same?(o: T) -> Bool = true\n  end\nend\nputs 1\n",
            &[][..],
            "refused: prelude_unchanged",
        ),
        ("off", "puts 1\n", &[("QUARZ_NO_PRELUDE_CACHE", "1")][..], "none"),
        // Programs started from a precompiled std set (#1115): the
        // prelude's ids come first there too.
        ("command_line", "require \"command_line\"\nputs 1\n", &[][..], "taken, compared"),
        ("json", "require \"json\"\nputs 1\n", &[][..], "taken, compared"),
        ("test", "require \"test\"\nputs 1\n", &[][..], "taken, compared"),
    ];
    for (name, src, env, expected) in cases {
        let file = dir.join(format!("{name}.qz"));
        let log = dir.join(format!("{name}.log"));
        std::fs::write(&file, src).unwrap();
        let out = std::process::Command::new(env!("CARGO_BIN_EXE_quarz"))
            .arg("run")
            .arg(&file)
            .env("QUARZ_NO_CACHE", "1")
            .env("QUARZ_PRELUDE_SNAPSHOT_LOG", &log)
            .envs(env.iter().copied())
            .output()
            .unwrap();
        assert!(
            out.status.success(),
            "{name}: {}",
            String::from_utf8_lossy(&out.stderr)
        );
        assert_eq!(String::from_utf8_lossy(&out.stdout), "1\n", "{name}");
        let logged = std::fs::read_to_string(&log).unwrap_or_default();
        assert!(
            !logged.is_empty() && logged.lines().all(|l| l == expected),
            "{name}: expected every start-up to log {expected:?}, got {logged:?}"
        );
    }
    // Methods made rather than declared, a `def_method`'s and a `data`
    // type's and an `attr_reader`'s, all of the program's classes: taken.
    std::fs::write(
        dir.join("lib.qz"),
        "class Base\n  static def self.gen -> Void\n    def_method(:made) { 7 }\n  end\nend\n",
    )
    .unwrap();
    std::fs::write(
        dir.join("made.qz"),
        "require_relative \"lib\"\ndata P = (x: Int)\nclass App < Base\n  gen\n  attr_reader :y\n  @y: Int = 1\nend\np App.new.made + P.new(1).x\n",
    )
    .unwrap();
    let log = dir.join("made.log");
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_quarz"))
        .arg("run")
        .arg(dir.join("made.qz"))
        .env("QUARZ_NO_CACHE", "1")
        .env("QUARZ_PRELUDE_SNAPSHOT_LOG", &log)
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "made: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&out.stdout), "8\n");
    let logged = std::fs::read_to_string(&log).unwrap_or_default();
    assert!(
        !logged.is_empty() && logged.lines().all(|l| l == "taken, compared"),
        "made: {logged:?}"
    );
    // A library cog: its root module is made, not declared in a file
    // (file 0), and is no prelude class (its id is past the prelude's):
    // the snapshot is taken.
    let cog = dir.join("tiny");
    std::fs::create_dir_all(cog.join("src")).unwrap();
    std::fs::write(
        cog.join("Cog.toml"),
        "[cog]\nname = \"tiny\"\nversion = \"0.1.0\"\n",
    )
    .unwrap();
    std::fs::write(
        cog.join("src/tiny.qz"),
        "class Tiny\n  def x -> Int = 1\nend\n",
    )
    .unwrap();
    let log = dir.join("cog.log");
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_quarz"))
        .arg("check")
        .current_dir(&cog)
        .env("QUARZ_NO_CACHE", "1")
        .env("QUARZ_PRELUDE_SNAPSHOT_LOG", &log)
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "cog: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let logged = std::fs::read_to_string(&log).unwrap_or_default();
    assert!(
        !logged.is_empty() && logged.lines().all(|l| l == "taken, compared"),
        "cog: {logged:?}"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// The run-time tables hash with keys chosen per process (#1124), so that
/// keys prepared in advance do not collide: two runs hash one string
/// apart, and alike only under one `QUARZ_HASH_SEED`. A debug build's
/// `QUARZ_TEST_TABLE_HASH` prints the hash.
#[cfg(debug_assertions)]
#[test]
fn tables_hash_with_keys_of_the_process() {
    let dir = std::env::temp_dir().join(format!("quarz-table-hash-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let file = dir.join("main.qz");
    std::fs::write(&file, "h = {\"key\" => 1}\nputs h[\"key\"]\n").unwrap();
    let hash = |seed: Option<&str>| -> String {
        let mut cmd = std::process::Command::new(env!("CARGO_BIN_EXE_quarz"));
        cmd.arg("run")
            .arg(&file)
            .env("QUARZ_TEST_TABLE_HASH", "key")
            .env_remove("QUARZ_HASH_SEED");
        if let Some(seed) = seed {
            cmd.env("QUARZ_HASH_SEED", seed);
        }
        let out = cmd.output().unwrap();
        assert_eq!(String::from_utf8_lossy(&out.stdout), "1\n");
        let err = String::from_utf8_lossy(&out.stderr).into_owned();
        let line = err
            .lines()
            .find(|l| l.starts_with("quarz: table hash "))
            .unwrap_or_else(|| panic!("{err}"));
        line.to_string()
    };
    let (a, b) = (hash(None), hash(None));
    assert_ne!(a, b, "two processes with random keys");
    assert_eq!(hash(Some("7")), hash(Some("7")));
    assert_ne!(hash(Some("7")), hash(Some("8")));
    let _ = std::fs::remove_dir_all(&dir);
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
            "super_other_extensions",
            "scoped_extension_after_own",
            "scoped_extension_after_own_file",
            "super_past_abstract",
            // (A `Decimal`'s descriptor names `Decimal.parse`, #889.)
            "decimal_json",
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
