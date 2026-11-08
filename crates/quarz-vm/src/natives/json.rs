//! `JSON.parse`, `JSON.generate` and `JSON.pretty_generate` (the rest of
//! the module is written in Quarz, see `std/json.qz`).

use crate::rc::Rc;

use quarz_ir::{ClassId, RtClassKind};
use smallvec::smallvec;

use crate::interp::{EvalResult, Flow, Interp, NativeFn};
use crate::value::*;

use super::string;

pub fn register(m: &mut super::Registry<NativeFn>) {
    native!(m, "JSON.parse", |i, _, a| {
        let text = string(i, a.arg(0), "text")?;
        let classes = classes(i)?;
        let mut p = Parser {
            interp: i,
            classes: &classes,
            src: text.as_bytes(),
            pos: 0,
            depth: 0,
        };
        p.skip_ws();
        let v = p.value()?;
        p.skip_ws();
        if p.pos < p.src.len() {
            return Err(p.error("unexpected token"));
        }
        Ok(v)
    });
    native!(m, "JSON.generate", |i, _, a| {
        let mut out = String::new();
        generate(i, a.arg(0), None, &mut out, 0)?;
        Ok(Value::string(out))
    });
    native!(m, "JSON.pretty_generate", |i, _, a| {
        let mut out = String::new();
        generate(i, a.arg(0), Some("  "), &mut out, 0)?;
        Ok(Value::string(out))
    });
    native!(m, "JSON.decode", |i, _, a| decode(i, &a, false));
    native!(m, "JSON.decode?", |i, _, a| decode(i, &a, true));
}

/// The classes of `std/json.qz`, looked up by name.
struct Classes {
    null: ClassId,
    boolean: ClassId,
    number: ClassId,
    string: ClassId,
    array: ClassId,
    object: ClassId,
    parse_error: ClassId,
    generator_error: ClassId,
    decode_error: ClassId,
}

fn classes(interp: &Interp) -> Result<Classes, Flow> {
    let world = &interp.program.world;
    let missing = || interp.err_type("the json library is not loaded");
    let Some(json) = world.top.get("JSON") else {
        return Err(missing());
    };
    let member = |name: &str| match world.class(*json).members.get(name) {
        Some(id) => Ok(*id),
        None => Err(missing()),
    };
    let value = member("Value")?;
    let variant = |name: &str| {
        world
            .class(value)
            .variants
            .iter()
            .copied()
            .find(|v| world.class(*v).short_name() == name)
            .ok_or_else(missing)
    };
    Ok(Classes {
        null: variant("Null")?,
        boolean: variant("Bool")?,
        number: variant("Number")?,
        string: variant("String")?,
        array: variant("Array")?,
        object: variant("Object")?,
        parse_error: member("ParseError")?,
        generator_error: member("GeneratorError")?,
        decode_error: member("DecodeError")?,
    })
}

fn variant(class: ClassId, field: Value) -> Value {
    Value::Object(Object::new(class, smallvec![field]))
}

// ----- decoding (`JSON.decode[T]`) ------------------------------------------------

/// A node of a type's descriptor (`quarz_types::json_decode`).
#[derive(Clone, Debug)]
enum Node {
    Int,
    Integer,
    Float,
    Str,
    Bool,
    Sym,
    Nil,
    Time,
    Bytes,
    Value,
    Opt(usize),
    Array(usize),
    Set(usize),
    HashStr(usize),
    HashSym(usize),
    /// A `data` class and its fields' nodes.
    Data(ClassId, Vec<usize>),
}

/// The nodes of descriptor `text`, the root first; `classes` are the
/// `data` classes it names by index. `None` for a malformed one (no
/// lowering makes it).
fn descriptor(text: &str, classes: &[ClassId]) -> Option<Vec<Node>> {
    let num = |s: &str| s.parse::<usize>().ok();
    text.split(';')
        .map(|n| {
            let (k, rest) = n.split_at(n.char_indices().nth(1).map_or(n.len(), |(i, _)| i));
            Some(match k {
                "i" => Node::Int,
                "I" => Node::Integer,
                "f" => Node::Float,
                "s" => Node::Str,
                "b" => Node::Bool,
                "y" => Node::Sym,
                "n" => Node::Nil,
                "t" => Node::Time,
                "B" => Node::Bytes,
                "v" => Node::Value,
                "?" => Node::Opt(num(rest)?),
                "a" => Node::Array(num(rest)?),
                "e" => Node::Set(num(rest)?),
                "h" => Node::HashStr(num(rest)?),
                "H" => Node::HashSym(num(rest)?),
                "d" => {
                    let (c, fields) = rest.split_once(':')?;
                    let fields = if fields.is_empty() {
                        Vec::new()
                    } else {
                        fields.split(',').map(num).collect::<Option<Vec<_>>>()?
                    };
                    Node::Data(*classes.get(num(c)?)?, fields)
                }
                _ => return None,
            })
        })
        .collect()
}

/// Why decoding stopped: the document's shape (`JSON::DecodeError`, or nil
/// for `decode?`), or anything else raised (a field's default).
enum DecodeFail {
    Shape(String),
    Raised(Flow),
}

impl From<Flow> for DecodeFail {
    fn from(f: Flow) -> Self {
        DecodeFail::Raised(f)
    }
}

/// `JSON.decode[T](text)` / `(value)` and `JSON.decode?[T](text)`.
fn decode(interp: &Interp, args: &crate::interp::Args, maybe: bool) -> EvalResult {
    let classes = classes(interp)?;
    let text = match args.kw(interp, quarz_ir::JSON_DECODE_TYPE) {
        Some(v) => string(interp, v, "type")?.to_string(),
        None => {
            return Err(
                interp.err_type("JSON.decode needs the type to decode into written at the call")
            )
        }
    };
    let data_classes: Vec<ClassId> = match args.kw(interp, quarz_ir::JSON_DECODE_CLASSES) {
        Some(Value::Array(items)) => items
            .values()
            .iter()
            .filter_map(|v| match v {
                Value::Class(c) => Some(*c),
                _ => None,
            })
            .collect(),
        _ => Vec::new(),
    };
    let Some(nodes) = descriptor(&text, &data_classes) else {
        return Err(interp.err_type("JSON.decode: a malformed type descriptor"));
    };
    let doc = match args.arg(0) {
        v @ (Value::Str(_) | Value::Short(_)) => {
            let text = string(interp, v, "text")?;
            let mut p = Parser {
                interp,
                classes: &classes,
                src: text.as_bytes(),
                pos: 0,
                depth: 0,
            };
            p.skip_ws();
            let parsed = p.value().and_then(|v| {
                p.skip_ws();
                if p.pos < p.src.len() {
                    Err(p.error("unexpected token"))
                } else {
                    Ok(v)
                }
            });
            match parsed {
                Ok(v) => v,
                Err(_) if maybe => return Ok(Value::Nil),
                Err(e) => return Err(e),
            }
        }
        v => v.clone(),
    };
    let mut d = Decoder {
        interp,
        classes: &classes,
        nodes: &nodes,
        path: String::from("$"),
    };
    match d.decode(&doc, 0) {
        Ok(v) => Ok(v),
        Err(DecodeFail::Shape(_)) if maybe => Ok(Value::Nil),
        Err(DecodeFail::Shape(m)) => Err(interp.raise(classes.decode_error, &m)),
        Err(DecodeFail::Raised(f)) => Err(f),
    }
}

struct Decoder<'a> {
    interp: &'a Interp,
    classes: &'a Classes,
    nodes: &'a [Node],
    /// Where in the document (`$.user.tags[2]`).
    path: String,
}

impl Decoder<'_> {
    /// The value `v` (a `JSON::Value`) decoded as node `n`.
    fn decode(&mut self, v: &Value, n: usize) -> Result<Value, DecodeFail> {
        let node = self.nodes[n].clone();
        // The variant and its field.
        let (class, inner) = match v {
            Value::Object(o) => (o.class, o.field(0)),
            _ => return Err(self.shape(&node, "something that is no JSON value")),
        };
        let c = self.classes;
        let is_null = class == c.null;
        match node {
            Node::Value => Ok(v.clone()),
            Node::Opt(m) => {
                if is_null {
                    Ok(Value::Nil)
                } else {
                    self.decode(v, m)
                }
            }
            Node::Nil if is_null => Ok(Value::Nil),
            Node::Bool if class == c.boolean => Ok(inner.unwrap_or(Value::Nil)),
            Node::Str if class == c.string => Ok(inner.unwrap_or(Value::Nil)),
            Node::Sym if class == c.string => {
                let s = string(self.interp, &inner.unwrap_or(Value::Nil), "string")?.to_string();
                Ok(Value::Symbol(self.interp.intern(&s)))
            }
            Node::Int if class == c.number => match inner {
                Some(Value::Int(i)) => Ok(Value::Int(i)),
                _ => Err(self.shape(&node, &self.found(v))),
            },
            Node::Integer if class == c.number => match inner {
                Some(Value::Int(i)) => Ok(Value::BigInt(Rc::new(num_bigint::BigInt::from(i)))),
                Some(b @ Value::BigInt(_)) => Ok(b),
                _ => Err(self.shape(&node, &self.found(v))),
            },
            Node::Float if class == c.number => match inner {
                Some(Value::Int(i)) => Ok(Value::Float(i as f64)),
                Some(Value::BigInt(b)) => {
                    use num_traits::ToPrimitive;
                    Ok(Value::Float(b.to_f64().unwrap_or(f64::NAN)))
                }
                Some(f @ Value::Float(_)) => Ok(f),
                _ => Err(self.shape(&node, &self.found(v))),
            },
            Node::Time if class == c.string => {
                let s = string(self.interp, &inner.unwrap_or(Value::Nil), "string")?.to_string();
                super::time::parse_rfc3339(&s).ok_or_else(|| self.shape(&node, &self.found(v)))
            }
            Node::Bytes if class == c.string => {
                use base64::Engine;
                let s = string(self.interp, &inner.unwrap_or(Value::Nil), "string")?.to_string();
                match base64::engine::general_purpose::STANDARD.decode(s.as_bytes()) {
                    Ok(b) => Ok(Value::bytes(b)),
                    Err(_) => Err(self.shape(&node, &self.found(v))),
                }
            }
            Node::Array(m) | Node::Set(m) if class == c.array => {
                let items = match inner {
                    Some(Value::Array(items)) => items.values().to_vec(),
                    _ => Vec::new(),
                };
                let mut out = Vec::with_capacity(items.len());
                for (i, item) in items.iter().enumerate() {
                    let len = self.path.len();
                    self.path.push_str(&format!("[{i}]"));
                    out.push(self.decode(item, m)?);
                    self.path.truncate(len);
                }
                Ok(match node {
                    Node::Set(_) => Value::Set(Rc::new(out.into_iter().collect())),
                    _ => Value::array(out),
                })
            }
            Node::HashStr(m) | Node::HashSym(m) if class == c.object => {
                let members = self.members(inner);
                let mut map = ValueMap::default();
                for (k, item) in members {
                    let len = self.path.len();
                    self.push_key(&k);
                    let value = self.decode(&item, m)?;
                    self.path.truncate(len);
                    let key = match node {
                        Node::HashSym(_) => Value::Symbol(self.interp.intern(&k)),
                        _ => Value::string(k),
                    };
                    map.insert(key, value);
                }
                Ok(Value::Hash(Rc::new(HashData::from(map))))
            }
            Node::Data(cid, ref fields) if class == c.object => {
                let members: ValueMap = self
                    .members(inner)
                    .into_iter()
                    .map(|(k, v)| (Value::string(k), v))
                    .collect();
                // Built from its fields, no `initialize` of its own run.
                let obj = self
                    .interp
                    .construct(cid, None, smallvec![], Vec::new(), None)?;
                let Value::Object(o) = &obj else {
                    return Err(DecodeFail::Raised(
                        self.interp.err_type("JSON.decode: not a data type"),
                    ));
                };
                let rc = self.interp.program.world.class(cid);
                for (i, (f, &m)) in rc.ivars.iter().zip(fields.iter()).enumerate() {
                    let value = match members.get(&Value::string(f.name.clone())) {
                        Some(item) => {
                            let len = self.path.len();
                            self.push_key(&f.name);
                            let value = self.decode(item, m)?;
                            self.path.truncate(len);
                            value
                        }
                        None => match f.default {
                            Some(d) => self.interp.run_init(d, obj.clone(), rc.file)?,
                            None => {
                                return Err(DecodeFail::Shape(format!(
                                    "{}: missing field `{}` of {}",
                                    self.path, f.name, rc.name
                                )))
                            }
                        },
                    };
                    self.interp.logical_set(o, i, value);
                }
                Ok(obj)
            }
            _ => Err(self.shape(&node, &self.found(v))),
        }
    }

    /// An object's members, by key.
    fn members(&self, inner: Option<Value>) -> Vec<(String, Value)> {
        match inner {
            Some(Value::Hash(h)) => h
                .as_map()
                .iter()
                .map(|(k, v)| {
                    let k = match k {
                        Value::Str(s) => s.to_string(),
                        Value::Short(s) => s.as_str().to_string(),
                        _ => String::new(),
                    };
                    (k, v.clone())
                })
                .collect(),
            _ => Vec::new(),
        }
    }

    fn push_key(&mut self, k: &str) {
        let plain = !k.is_empty()
            && k.chars().all(|c| c.is_alphanumeric() || c == '_')
            && !k.starts_with(|c: char| c.is_ascii_digit());
        if plain {
            self.path.push('.');
            self.path.push_str(k);
        } else {
            let mut quoted = String::new();
            escape(k, &mut quoted);
            self.path.push_str(&format!("[{quoted}]"));
        }
    }

    /// What `v` is, for an error: a scalar as written, an array or an
    /// object by its kind.
    fn found(&self, v: &Value) -> String {
        let Value::Object(o) = v else {
            return "something else".to_string();
        };
        let c = self.classes;
        let inner = o.field(0);
        if o.class == c.null {
            "null".to_string()
        } else if o.class == c.array {
            "an array".to_string()
        } else if o.class == c.object {
            "an object".to_string()
        } else if o.class == c.string {
            let mut s = String::new();
            if let Some(Value::Str(t)) = &inner {
                escape(t, &mut s);
            } else if let Some(Value::Short(t)) = &inner {
                escape(t.as_str(), &mut s);
            }
            s
        } else {
            match inner {
                Some(Value::Bool(b)) => b.to_string(),
                Some(Value::Int(i)) => i.to_string(),
                Some(Value::BigInt(b)) => b.to_string(),
                Some(Value::Float(f)) => crate::interp::format_float(f),
                _ => "something else".to_string(),
            }
        }
    }

    /// The error for a value that is not what `node` decodes.
    fn shape(&self, node: &Node, found: &str) -> DecodeFail {
        let expected = match node {
            Node::Int => "an integer that fits an Int".to_string(),
            Node::Integer => "an integer".to_string(),
            Node::Float => "a number".to_string(),
            Node::Str => "a string".to_string(),
            Node::Bool => "true or false".to_string(),
            Node::Sym => "a string (for a Symbol)".to_string(),
            Node::Nil => "null".to_string(),
            Node::Time => "an RFC 3339 time string".to_string(),
            Node::Bytes => "a Base64 string".to_string(),
            Node::Value => "a JSON value".to_string(),
            Node::Opt(_) => "a value or null".to_string(),
            Node::Array(_) | Node::Set(_) => "an array".to_string(),
            Node::HashStr(_) | Node::HashSym(_) => "an object".to_string(),
            Node::Data(cid, _) => format!(
                "an object (for {})",
                self.interp.program.world.class(*cid).name
            ),
        };
        DecodeFail::Shape(format!("{}: expected {expected}, found {found}", self.path))
    }
}

// ----- parsing ------------------------------------------------------------------

const MAX_NESTING: usize = 100;

struct Parser<'a> {
    interp: &'a Interp,
    classes: &'a Classes,
    src: &'a [u8],
    pos: usize,
    depth: usize,
}

impl Parser<'_> {
    fn error(&self, what: &str) -> Flow {
        let (mut line, mut col) = (1, 1);
        for &b in &self.src[..self.pos.min(self.src.len())] {
            if b == b'\n' {
                line += 1;
                col = 1;
            } else {
                col += 1;
            }
        }
        self.interp.raise(
            self.classes.parse_error,
            &format!("{what} at line {line} column {col}"),
        )
    }

    fn peek(&self) -> Option<u8> {
        self.src.get(self.pos).copied()
    }

    fn skip_ws(&mut self) {
        while matches!(self.peek(), Some(b' ' | b'\t' | b'\n' | b'\r')) {
            self.pos += 1;
        }
    }

    fn expect_word(&mut self, word: &str) -> Result<(), Flow> {
        if self.src[self.pos..].starts_with(word.as_bytes()) {
            self.pos += word.len();
            Ok(())
        } else {
            Err(self.error("unexpected token"))
        }
    }

    fn value(&mut self) -> EvalResult {
        match self.peek() {
            Some(b'{') => self.object(),
            Some(b'[') => self.array(),
            Some(b'"') => Ok(variant(self.classes.string, Value::string(self.string()?))),
            Some(b't') => {
                self.expect_word("true")?;
                Ok(variant(self.classes.boolean, Value::Bool(true)))
            }
            Some(b'f') => {
                self.expect_word("false")?;
                Ok(variant(self.classes.boolean, Value::Bool(false)))
            }
            Some(b'n') => {
                self.expect_word("null")?;
                Ok(self.interp.variant_singleton(self.classes.null))
            }
            Some(b'-' | b'0'..=b'9') => self.number(),
            Some(_) => Err(self.error("unexpected token")),
            None => Err(self.error("unexpected end of input")),
        }
    }

    fn enter(&mut self) -> Result<(), Flow> {
        self.depth += 1;
        if self.depth > MAX_NESTING {
            return Err(self.error(&format!("nesting of {} is too deep", self.depth)));
        }
        Ok(())
    }

    fn object(&mut self) -> EvalResult {
        self.enter()?;
        self.pos += 1;
        let mut members = ValueMap::default();
        self.skip_ws();
        if self.peek() == Some(b'}') {
            self.pos += 1;
            self.depth -= 1;
            return Ok(variant(
                self.classes.object,
                Value::Hash(Rc::new(crate::value::HashData::from(members))),
            ));
        }
        loop {
            self.skip_ws();
            if self.peek() != Some(b'"') {
                return Err(self.error("expected a string key"));
            }
            let key = self.string()?;
            self.skip_ws();
            if self.peek() != Some(b':') {
                return Err(self.error("expected ':'"));
            }
            self.pos += 1;
            self.skip_ws();
            let v = self.value()?;
            members.insert(Value::string(key), v);
            self.skip_ws();
            match self.peek() {
                Some(b',') => self.pos += 1,
                Some(b'}') => {
                    self.pos += 1;
                    break;
                }
                Some(_) => return Err(self.error("expected ',' or '}'")),
                None => return Err(self.error("unexpected end of input")),
            }
        }
        self.depth -= 1;
        Ok(variant(
            self.classes.object,
            Value::Hash(Rc::new(crate::value::HashData::from(members))),
        ))
    }

    fn array(&mut self) -> EvalResult {
        self.enter()?;
        self.pos += 1;
        let mut items = Vec::new();
        self.skip_ws();
        if self.peek() == Some(b']') {
            self.pos += 1;
            self.depth -= 1;
            return Ok(variant(self.classes.array, Value::array(items)));
        }
        loop {
            self.skip_ws();
            items.push(self.value()?);
            self.skip_ws();
            match self.peek() {
                Some(b',') => self.pos += 1,
                Some(b']') => {
                    self.pos += 1;
                    break;
                }
                Some(_) => return Err(self.error("expected ',' or ']'")),
                None => return Err(self.error("unexpected end of input")),
            }
        }
        self.depth -= 1;
        Ok(variant(self.classes.array, Value::array(items)))
    }

    fn number(&mut self) -> EvalResult {
        let start = self.pos;
        if self.peek() == Some(b'-') {
            self.pos += 1;
        }
        let int_start = self.pos;
        while matches!(self.peek(), Some(b'0'..=b'9')) {
            self.pos += 1;
        }
        let digits = &self.src[int_start..self.pos];
        if digits.is_empty() || (digits.len() > 1 && digits[0] == b'0') {
            return Err(self.error("invalid number"));
        }
        let mut is_float = false;
        if self.peek() == Some(b'.') {
            is_float = true;
            self.pos += 1;
            let frac_start = self.pos;
            while matches!(self.peek(), Some(b'0'..=b'9')) {
                self.pos += 1;
            }
            if self.pos == frac_start {
                return Err(self.error("invalid number"));
            }
        }
        if matches!(self.peek(), Some(b'e' | b'E')) {
            is_float = true;
            self.pos += 1;
            if matches!(self.peek(), Some(b'+' | b'-')) {
                self.pos += 1;
            }
            let exp_start = self.pos;
            while matches!(self.peek(), Some(b'0'..=b'9')) {
                self.pos += 1;
            }
            if self.pos == exp_start {
                return Err(self.error("invalid number"));
            }
        }
        let text = std::str::from_utf8(&self.src[start..self.pos]).unwrap_or("0");
        if is_float {
            let f: f64 = text.parse().map_err(|_| self.error("invalid number"))?;
            Ok(variant(self.classes.number, Value::Float(f)))
        } else {
            // An integer: an `Int`, or an `Integer` (exact) when too large.
            match text.parse::<i64>() {
                Ok(i) => Ok(variant(self.classes.number, Value::Int(i))),
                Err(_) => Ok(variant(
                    self.classes.number,
                    crate::interp::parse_integer(text, 10),
                )),
            }
        }
    }

    /// A string literal starting at the opening quote.
    fn string(&mut self) -> Result<String, Flow> {
        self.pos += 1;
        let mut out = String::new();
        loop {
            let start = self.pos;
            while let Some(b) = self.peek() {
                if b == b'"' || b == b'\\' || b < 0x20 {
                    break;
                }
                self.pos += 1;
            }
            out.push_str(
                std::str::from_utf8(&self.src[start..self.pos])
                    .map_err(|_| self.error("invalid UTF-8"))?,
            );
            match self.peek() {
                Some(b'"') => {
                    self.pos += 1;
                    return Ok(out);
                }
                Some(b'\\') => {
                    self.pos += 1;
                    let c = self
                        .peek()
                        .ok_or_else(|| self.error("unexpected end of input"))?;
                    self.pos += 1;
                    match c {
                        b'"' => out.push('"'),
                        b'\\' => out.push('\\'),
                        b'/' => out.push('/'),
                        b'b' => out.push('\u{8}'),
                        b'f' => out.push('\u{c}'),
                        b'n' => out.push('\n'),
                        b'r' => out.push('\r'),
                        b't' => out.push('\t'),
                        b'u' => {
                            let mut code = self.hex4()?;
                            if (0xD800..0xDC00).contains(&code) {
                                // A surrogate pair.
                                if self.src[self.pos..].starts_with(b"\\u") {
                                    self.pos += 2;
                                    let low = self.hex4()?;
                                    if (0xDC00..0xE000).contains(&low) {
                                        code = 0x10000 + ((code - 0xD800) << 10) + (low - 0xDC00);
                                    } else {
                                        return Err(self.error("invalid surrogate pair"));
                                    }
                                } else {
                                    return Err(self.error("invalid surrogate pair"));
                                }
                            }
                            out.push(char::from_u32(code).unwrap_or('\u{FFFD}'));
                        }
                        _ => return Err(self.error("invalid escape")),
                    }
                }
                Some(_) => return Err(self.error("control character in string")),
                None => return Err(self.error("unexpected end of input")),
            }
        }
    }

    fn hex4(&mut self) -> Result<u32, Flow> {
        let mut code = 0u32;
        for _ in 0..4 {
            let d = self
                .peek()
                .and_then(|b| (b as char).to_digit(16))
                .ok_or_else(|| self.error("invalid Unicode escape"))?;
            code = code * 16 + d;
            self.pos += 1;
        }
        Ok(code)
    }
}

// ----- generation ---------------------------------------------------------------

fn generate(
    interp: &Interp,
    v: &Value,
    indent: Option<&str>,
    out: &mut String,
    depth: usize,
) -> Result<(), Flow> {
    if depth > MAX_NESTING {
        return Err(generator_error(
            interp,
            &format!("nesting of {depth} is too deep"),
        ));
    }
    match v {
        Value::Nil => out.push_str("null"),
        Value::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
        Value::Int(i) => out.push_str(&i.to_string()),
        Value::BigInt(b) => out.push_str(&b.to_string()),
        Value::Float(f) => {
            if !f.is_finite() {
                return Err(generator_error(
                    interp,
                    &format!("{} not allowed in JSON", crate::interp::format_float(*f)),
                ));
            }
            out.push_str(&crate::interp::format_float(*f));
        }
        Value::Str(s) => escape(s, out),
        Value::Short(s) => escape(s.as_str(), out),
        Value::Symbol(s) => escape(&interp.symbol_name(*s), out),
        Value::Array(items) => {
            generate_seq(interp, items.values().iter(), indent, out, depth)?;
        }
        Value::Set(items) => {
            generate_seq(interp, items.iter(), indent, out, depth)?;
        }
        Value::Hash(h) => {
            let mut members = Vec::with_capacity(h.len());
            for (k, v) in h.as_map().iter() {
                let key = match k {
                    Value::Str(s) => s.to_string(),
                    Value::Short(s) => s.as_str().to_string(),
                    Value::Symbol(s) => interp.symbol_name(*s).to_string(),
                    other => interp.to_s(other)?.to_string(),
                };
                members.push((key, v.clone()));
            }
            generate_map(interp, &members, indent, out, depth)?;
        }
        Value::Class(c) => escape(&interp.program.world.class(*c).name, out),
        // (What `JSON.decode` reads back: RFC 3339 in UTC, and Base64.)
        Value::Time(t) => escape(&super::time::json_time(t), out),
        Value::Bytes(b) => {
            use base64::Engine;
            escape(
                &base64::engine::general_purpose::STANDARD.encode(&b[..]),
                out,
            )
        }
        Value::Duration(_) | Value::Range(_) | Value::Regexp(_) => escape(&interp.to_s(v)?, out),
        Value::Object(o) => {
            let class = interp.program.world.class(o.class);
            // `JSON::Value` is generated as the document it represents.
            if let Some(value_class) = class.variant_of {
                if interp.program.world.class(value_class).name == "JSON::Value" {
                    let field = o.field(0);
                    return match (class.short_name(), field) {
                        ("Null", _) => {
                            out.push_str("null");
                            Ok(())
                        }
                        (_, Some(inner)) => generate(interp, &inner, indent, out, depth),
                        _ => Ok(()),
                    };
                }
            }
            if let Some(mid) = interp.has_user_method(v, "to_json", 0) {
                let r = interp.invoke(mid, v.clone(), smallvec![], vec![], None)?;
                out.push_str(&interp.to_s(&r)?);
                return Ok(());
            }
            if class.kind == RtClassKind::Variant && o.field_count() == 0 {
                escape(class.short_name(), out);
                return Ok(());
            }
            if interp.program.world.is_exception_class(o.class) {
                escape(&interp.to_s(v)?, out);
                return Ok(());
            }
            let members: Vec<(String, Value)> = class
                .ivars
                .iter()
                .zip(interp.logical_values(o))
                .map(|(f, v)| (f.name.clone(), v))
                .collect();
            generate_map(interp, &members, indent, out, depth)?;
        }
        other => {
            return Err(generator_error(
                interp,
                &format!("cannot generate JSON for {}", interp.class_name(other)),
            ))
        }
    }
    Ok(())
}

fn generate_seq<'a>(
    interp: &Interp,
    items: impl ExactSizeIterator<Item = &'a Value>,
    indent: Option<&str>,
    out: &mut String,
    depth: usize,
) -> Result<(), Flow> {
    if items.len() == 0 {
        out.push_str("[]");
        return Ok(());
    }
    out.push('[');
    for (k, item) in items.enumerate() {
        if k > 0 {
            out.push(',');
        }
        newline(indent, out, depth + 1);
        generate(interp, item, indent, out, depth + 1)?;
    }
    newline(indent, out, depth);
    out.push(']');
    Ok(())
}

fn generate_map(
    interp: &Interp,
    members: &[(String, Value)],
    indent: Option<&str>,
    out: &mut String,
    depth: usize,
) -> Result<(), Flow> {
    if members.is_empty() {
        out.push_str("{}");
        return Ok(());
    }
    out.push('{');
    for (k, (key, value)) in members.iter().enumerate() {
        if k > 0 {
            out.push(',');
        }
        newline(indent, out, depth + 1);
        escape(key, out);
        out.push(':');
        if indent.is_some() {
            out.push(' ');
        }
        generate(interp, value, indent, out, depth + 1)?;
    }
    newline(indent, out, depth);
    out.push('}');
    Ok(())
}

fn newline(indent: Option<&str>, out: &mut String, depth: usize) {
    if let Some(unit) = indent {
        out.push('\n');
        for _ in 0..depth {
            out.push_str(unit);
        }
    }
}

fn escape(s: &str, out: &mut String) {
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\u{8}' => out.push_str("\\b"),
            '\u{c}' => out.push_str("\\f"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
}

fn generator_error(interp: &Interp, message: &str) -> Flow {
    match classes(interp) {
        Ok(c) => interp.raise(c.generator_error, message),
        Err(_) => interp.raise(interp.program.exc.runtime_error, message),
    }
}
