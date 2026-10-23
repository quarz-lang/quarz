//! `JSON.parse`, `JSON.generate` and `JSON.pretty_generate` (the rest of
//! the module is written in Quarz, see `std/json.qz`).

use crate::rc::Rc;

use quarz_ir::{ClassId, RtClassKind};
use smallvec::smallvec;

use crate::interp::{EvalResult, Flow, Interp, NativeFn};
use crate::value::*;

use super::string;

pub fn register(m: &mut super::Registry<NativeFn>) {
    m.insert("JSON.parse", |i, _, a| {
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
    m.insert("JSON.generate", |i, _, a| {
        let mut out = String::new();
        generate(i, a.arg(0), None, &mut out, 0)?;
        Ok(Value::string(out))
    });
    m.insert("JSON.pretty_generate", |i, _, a| {
        let mut out = String::new();
        generate(i, a.arg(0), Some("  "), &mut out, 0)?;
        Ok(Value::string(out))
    });
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
    })
}

fn variant(class: ClassId, field: Value) -> Value {
    Value::Object(Object::new(class, smallvec![field]))
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
        Value::Time(_) | Value::Duration(_) | Value::Range(_) | Value::Regexp(_) => {
            escape(&interp.to_s(v)?, out)
        }
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
