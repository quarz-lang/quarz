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
