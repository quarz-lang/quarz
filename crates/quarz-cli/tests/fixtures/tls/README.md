Test certificates for `tests/tls.rs`, valid until 2076 (not secret: the
key is for these tests only).

- `ca.pem`: the test CA (P-256), whose key was discarded.
- `server.pem`, `server.key`: `localhost` and `127.0.0.1`, signed by the CA.
- `other-ca.pem`: an unrelated CA, for the unknown-issuer test.
