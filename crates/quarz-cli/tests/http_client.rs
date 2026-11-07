//! `HTTP::Client` where the environment matters: `HTTP::Proxy.from_env`
//! (`tests/http/proxy_env.qz`, with the variables set here), and, opt in,
//! a GET of `QUARZ_HTTP_PUBLIC_URL` through the environment's proxy (not
//! in CI). The rest of the client's tests are `std/test/http_client_test.qz`.

use std::path::{Path, PathBuf};
use std::process::Command;

fn program(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/http")
        .join(name)
}

const PROXY_VARS: [&str; 6] = [
    "https_proxy",
    "HTTPS_PROXY",
    "http_proxy",
    "HTTP_PROXY",
    "no_proxy",
    "NO_PROXY",
];

/// What `proxy_env.qz` prints with `vars` as the only proxy variables.
fn from_env(vars: &[(&str, &str)]) -> String {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_quarz"));
    cmd.arg("run").arg(program("proxy_env.qz"));
    for v in PROXY_VARS {
        cmd.env_remove(v);
    }
    for (k, v) in vars {
        cmd.env(k, v);
    }
    let out = cmd.output().expect("run quarz");
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8(out.stdout).unwrap()
}

#[test]
fn proxy_from_env() {
    assert_eq!(from_env(&[]), "nil\n");
    assert_eq!(
        from_env(&[
            ("https_proxy", "http://u:p@proxy:3128"),
            ("NO_PROXY", "localhost, .internal")
        ]),
        "[\"http://u:p@proxy:3128\", nil, [\"localhost\", \".internal\"]]\n\
         https://example.com/ -> http://u:p@proxy:3128\n\
         http://example.com/ -> direct\n\
         https://api.internal/ -> direct\n\
         http://localhost:8080/ -> direct\n"
    );
    // Upper case too; lower case first; a URL without a scheme is http.
    assert_eq!(
        from_env(&[
            ("HTTPS_PROXY", "upper:1"),
            ("https_proxy", "lower:2"),
            ("HTTP_PROXY", "plain:3"),
            ("no_proxy", "*")
        ]),
        "[\"http://lower:2\", \"http://plain:3\", [\"*\"]]\n\
         https://example.com/ -> direct\n\
         http://example.com/ -> direct\n\
         https://api.internal/ -> direct\n\
         http://localhost:8080/ -> direct\n"
    );
    assert_eq!(
        from_env(&[("http_proxy", "http://p:8080")]),
        "[nil, \"http://p:8080\", []]\n\
         https://example.com/ -> direct\n\
         http://example.com/ -> http://p:8080\n\
         https://api.internal/ -> direct\n\
         http://localhost:8080/ -> http://p:8080\n"
    );
}

/// The `User-Agent` names this version.
#[test]
fn user_agent_names_the_version() {
    let http =
        std::fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("../../std/http.qz"))
            .unwrap();
    let want = format!("USER_AGENT = \"quarz-http/{}\"", env!("CARGO_PKG_VERSION"));
    assert!(http.contains(&want), "std/http.qz should have {want}");
}

#[test]
fn public_host() {
    let Ok(url) = std::env::var("QUARZ_HTTP_PUBLIC_URL") else {
        return;
    };
    let out = Command::new(env!("CARGO_BIN_EXE_quarz"))
        .arg("run")
        .arg(program("public.qz"))
        .arg(&url)
        .output()
        .expect("run quarz");
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "2\n\"HTTP/1.1\"\n\"https\"\n"
    );
}
