//! `quarz check --tree`: the checked program as JSON, for formal/'s
//! differential tests.

use serde_json::Value;

fn tree(name: &str, source: &str) -> (bool, String, Value) {
    let dir = std::env::temp_dir().join(format!("quarz-tree-{}-{name}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("main.qz");
    std::fs::write(&path, source).unwrap();
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_quarz"))
        .args(["check", "--tree"])
        .arg(&path)
        .output()
        .unwrap();
    let _ = std::fs::remove_dir_all(&dir);
    let stdout = String::from_utf8_lossy(&out.stdout).into_owned();
    let v = serde_json::from_str(&stdout).unwrap_or(Value::Null);
    (out.status.success(), stdout, v)
}

/// The expressions of a tree, by id: (kind, node).
fn nodes<'a>(v: &'a Value, out: &mut Vec<(u64, &'a Value)>) {
    match v {
        Value::Object(o) => {
            if let (Some(id), true) = (o.get("id").and_then(Value::as_u64), o.contains_key("kind"))
            {
                if o.contains_key("span") {
                    out.push((id, v));
                }
            }
            o.values().for_each(|x| nodes(x, out));
        }
        Value::Array(a) => a.iter().for_each(|x| nodes(x, out)),
        _ => {}
    }
}

fn class_id(v: &Value, name: &str) -> u64 {
    v["classes"]
        .as_array()
        .unwrap()
        .iter()
        .find(|c| c["name"] == name)
        .and_then(|c| c["id"].as_u64())
        .unwrap()
}

#[test]
fn a_narrowed_read_has_the_narrowed_type() {
    let (ok, _, v) = tree(
        "narrowed",
        "def f(x: Int?) -> Int\n  if x\n    x + 1\n  else\n    0\n  end\nend\np f(1)\n",
    );
    assert!(ok);
    assert_eq!(v["format"], 3);
    let mut all = Vec::new();
    nodes(&v["definitions"], &mut all);
    let int = class_id(&v, "Int");
    let nil = class_id(&v, "Nil");
    // The reads of `x`: the test sees `Int?`, the `then` branch `Int`.
    let reads: Vec<&Value> = all
        .iter()
        .filter(|(_, n)| n["kind"] == serde_json::json!({ "Local": "x" }))
        .map(|(id, _)| &v["node_types"][id.to_string()])
        .collect();
    assert_eq!(reads.len(), 2, "{reads:?}");
    let members: Vec<u64> = reads[0]["members"]
        .as_array()
        .unwrap()
        .iter()
        .map(|m| m["id"].as_u64().unwrap())
        .collect();
    assert!(
        members.contains(&int) && members.contains(&nil),
        "{:?}",
        reads[0]
    );
    assert_eq!(reads[1]["t"], "class");
    assert_eq!(reads[1]["id"].as_u64(), Some(int));
    // The method, with its signature.
    let f = v["methods"]
        .as_array()
        .unwrap()
        .iter()
        .find(|m| m["name"] == "f")
        .unwrap();
    assert_eq!(f["ret"]["id"].as_u64(), Some(int));
}

#[test]
fn a_program_that_does_not_check_has_no_tree() {
    let (ok, stdout, _) = tree("fails", "x: Int = nil\n");
    assert!(!ok);
    assert_eq!(stdout, "");
}

#[test]
fn constants_and_field_defaults_are_there() {
    let (ok, _, v) = tree(
        "consts",
        "LIMIT = 3 + 4\nclass C\n  @n: Int = 1 + 2\nend\np LIMIT\np C.new\n",
    );
    assert!(ok);
    for (key, at) in [("consts", "value"), ("field_defaults", "value")] {
        let entries = v[key].as_array().unwrap();
        assert_eq!(entries.len(), 1, "{key}");
        let mut all = Vec::new();
        nodes(&entries[0][at], &mut all);
        assert!(!all.is_empty(), "{key}");
        for (id, _) in all {
            assert!(v["node_types"].get(id.to_string()).is_some(), "{key} {id}");
        }
    }
}
