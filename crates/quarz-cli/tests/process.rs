//! Child processes (`Process.spawn`, `Process::Child`, `Process.exec`):
//! the programs in `process/` run interpreted and compiled and print
//! their `.out`.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn program(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/process")
        .join(name)
}

fn on_vm(path: &Path, envs: &[(&str, &str)]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_quarz"))
        .arg("run")
        .arg(path)
        .envs(envs.iter().copied())
        .output()
        .expect("run quarz")
}

/// Compile `path` into a directory of its own (the tests run in
/// parallel), run it, and remove the directory.
fn compiled(path: &Path, envs: &[(&str, &str)]) -> Output {
    static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!(
        "quarz-process-test-{}-{n}-{}",
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
        .envs(envs.iter().copied())
        .output()
        .expect("run the executable");
    let _ = std::fs::remove_dir_all(&dir);
    out
}

fn prints_its_out(name: &str) {
    prints_its_out_with(name, &[]);
}

/// With `envs` set for the program.
fn prints_its_out_with(name: &str, envs: &[(&str, &str)]) {
    let path = program(name);
    let want = std::fs::read_to_string(path.with_extension("out")).unwrap();
    for (out, what) in [
        (on_vm(&path, envs), "on the VM"),
        (compiled(&path, envs), "compiled"),
    ] {
        assert!(
            out.status.success(),
            "{name} {what} failed: {}",
            String::from_utf8_lossy(&out.stderr)
        );
        assert_eq!(String::from_utf8_lossy(&out.stdout), want, "{name} {what}");
    }
}

#[test]
fn pipes_carry_a_childs_streams() {
    prints_its_out("pipes.qz");
}

#[test]
fn an_inherited_stream_keeps_the_programs_order() {
    prints_its_out("inherit.qz");
}

#[test]
fn env_chdir_and_null_streams() {
    prints_its_out("env_chdir.qz");
}

#[test]
fn signals_end_a_child() {
    prints_its_out("signals.qz");
}

#[test]
fn a_timeout_interrupts_a_wait() {
    prints_its_out("timeout.qz");
}

#[test]
fn spawn_refuses_what_it_cannot_do() {
    prints_its_out("errors.qz");
}

#[test]
fn exec_replaces_the_program() {
    prints_its_out("exec.qz");
}

#[test]
fn a_child_inherits_no_runtime_descriptor() {
    if !Path::new("/proc/self/fd").is_dir() {
        return;
    }
    prints_its_out("fds.qz");
}

#[test]
fn waits_without_a_pidfd_on_a_helper_thread() {
    // The way other systems (and kernels before pidfds) wait: a helper
    // thread reaps the child, and an interrupted wait leaves its status
    // for the next one.
    for name in ["signals.qz", "timeout.qz", "pipes.qz"] {
        prints_its_out_with(name, &[("QUARZ_NO_PIDFD", "1")]);
    }
}
