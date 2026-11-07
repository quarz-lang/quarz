//! `std/crypto.qz` against the `openssl` command, opt in
//! (`QUARZ_OPENSSL=1`, not in CI): a key made here, its PEM read by
//! openssl, and signatures made here verified by `openssl dgst`. The
//! other direction (OpenSSL's keys and signatures read here) is
//! `std/test/crypto_test.qz`, with checked-in fixtures.

use std::path::Path;
use std::process::Command;

fn openssl(args: &[&str], dir: &Path) -> String {
    let out = Command::new("openssl")
        .args(args)
        .current_dir(dir)
        .output()
        .expect("run openssl");
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(out.status.success(), "openssl {args:?}: {text}");
    text
}

#[test]
fn openssl_verifies_our_signatures() {
    if std::env::var_os("QUARZ_OPENSSL").is_none() {
        return;
    }
    let dir = std::env::temp_dir().join(format!("quarz-crypto-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    // Removed however the test ends: it holds a private key.
    struct Gone(std::path::PathBuf);
    impl Drop for Gone {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }
    let _gone = Gone(dir.clone());
    let program = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/crypto/openssl.qz");
    let out = Command::new(env!("CARGO_BIN_EXE_quarz"))
        .arg("run")
        .arg(&program)
        .arg(&dir)
        .output()
        .expect("run quarz");
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    // The PKCS#1 private key and the SPKI public key parse.
    openssl(&["rsa", "-in", "key.pem", "-check", "-noout"], &dir);
    openssl(&["pkey", "-pubin", "-in", "pub.pem", "-noout"], &dir);
    let v = openssl(
        &[
            "dgst",
            "-sha256",
            "-verify",
            "pub.pem",
            "-signature",
            "sig_pkcs1v15.bin",
            "message.txt",
        ],
        &dir,
    );
    assert!(v.contains("Verified OK"), "{v}");
    let v = openssl(
        &[
            "dgst",
            "-sha384",
            "-verify",
            "pub.pem",
            "-sigopt",
            "rsa_padding_mode:pss",
            "-sigopt",
            "rsa_pss_saltlen:digest",
            "-signature",
            "sig_pss.bin",
            "message.txt",
        ],
        &dir,
    );
    assert!(v.contains("Verified OK"), "{v}");
}
