//! Bytes, Time and the `json` library.

mod common;

use std::path::Path;

use common::expect;

#[test]
fn bytes() {
    expect(
        r#"
b = b"\x00\xffab\n"
p b
puts b.size, b[1]
p b[0..1], b.to_a, b.hex
p Bytes.from_hex("48 65 6c 6c 6f").decode
p "héllo".to_bytes, "héllo".to_bytes.decode, b"\xff".decode?
begin
  b"\xff".decode
rescue ArgumentError => e
  puts "error: #{e.message}"
end
p "é".encode("ISO-8859-1"), b"\xe9".decode("latin1")
p Bytes.build { |w| w << 1 << b"\x02" << "c" }
p Bytes[1, 2, 3] + Bytes[4], Bytes[1, 2, 3] == Bytes[1, 2, 3], Bytes[1, 2] < Bytes[1, 3]
p Bytes[3, 1, 2].map { |x| x * 2 }, Bytes[1, 2, 3].include?(2)
p({ b"\x01" => "one" }[b"\x01"])
p b"\x01\x02".reverse, b"abc".slice(1, 5), Bytes.new.empty?, b'\x41\n'
"#,
        "b\"\\x00\\xffab\\n\"\n5\n255\nb\"\\x00\\xff\"\n[0, 255, 97, 98, 10]\n\"00ff61620a\"\n\"Hello\"\nb\"h\\xc3\\xa9llo\"\n\"héllo\"\nnil\nerror: invalid UTF-8 byte sequence at offset 0\nb\"\\xe9\"\n\"é\"\nb\"\\x01\\x02c\"\nb\"\\x01\\x02\\x03\\x04\"\ntrue\ntrue\n[6, 2, 4]\ntrue\n\"one\"\nb\"\\x02\\x01\"\nb\"bc\"\ntrue\nb\"A\\n\"\n",
    );
}

#[test]
fn time() {
    expect(
        r#"
t = Time.utc(2026, 10, 19, 12, 34, 56)
puts t, t.inspect
puts [t.year, t.month, t.day, t.hour, t.min, t.sec, t.wday, t.yday, t.to_i].join(" ")
puts t.iso8601, t.iso8601(3)
puts (t + 1.5.seconds).inspect
puts (t + 90.minutes).strftime("%Y/%m/%d %H:%M:%S %Z %L %-d %A %j")
puts t - Time.utc(2026, 10, 18)
puts t.monday?, t.utc?, t.zone, t.utc_offset
puts Time.at(0).utc
puts Time.parse("2026-01-02T03:04:05Z").inspect
puts Time.parse("2026-01-02 03:04:05.5 +0900").inspect
puts Time.parse("2026-01-02 03:04:05 +09:00").utc.iso8601
puts Time.iso8601("2026-01-02T03:04:05.25+09:00").iso8601(2)
puts Time.utc(2026, 1, 1) < Time.utc(2026, 1, 2)
puts [Time.utc(2026, 1, 2), Time.utc(2026, 1, 1)].min
puts({ Time.utc(2000) => "y2k" }[Time.utc(2000)])
puts (Time.utc(2026, 1, 1) + 2.days).day
now = Time.now
puts now.to_f > 1.0e9, (Time.now - now) < 1.second, Time.monotonic >= 0.ms
puts t.getlocal.to_i == t.to_i
begin
  Time.parse("garbage")
rescue ArgumentError => e
  puts "error: #{e.message}"
end
"#,
        "2026-10-19 12:34:56 UTC\n2026-10-19 12:34:56 UTC\n2026 10 19 12 34 56 1 292 1792413296\n2026-10-19T12:34:56Z\n2026-10-19T12:34:56.000Z\n2026-10-19 12:34:57.5 UTC\n2026/10/19 14:04:56 UTC 000 19 Monday 292\n131696s\ntrue\ntrue\nUTC\n0\n1970-01-01 00:00:00 UTC\n2026-01-02 03:04:05 UTC\n2026-01-02 03:04:05.5 +0900\n2026-01-01T18:04:05Z\n2026-01-02T03:04:05.25+09:00\ntrue\n2026-01-01 00:00:00 UTC\ny2k\n3\ntrue\ntrue\ntrue\ntrue\nerror: no time information in \"garbage\"\n",
    );
}

#[test]
fn json() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/json.qz");
    let (code, out) = common::run_path(&path, &[]);
    assert_eq!(code, 0, "output:\n{out}");
    assert_eq!(
        out,
        concat!(
            "\"quarz\"\n1\n3.5\n\"vm\"\ntrue\ntrue\n\"é😀\"\nnil\n2\n[\"lang\", \"vm\"]\n",
            "{\"name\":\"quarz\",\"version\":1,\"pi\":3.5,\"tags\":[\"lang\",\"vm\"],\"ok\":true,\"none\":null,\"nested\":{\"a\":[1,{\"b\":\"é😀\"}]}}\n",
            "{\n  \"a\": [\n    1,\n    {\n      \"b\": \"é😀\"\n    }\n  ]\n}\n",
            "name,version,pi,tags,ok,none,nested\n",
            "{\"a\":1,\"b\":[true,null,2.5],\"c\":{\"x\":1,\"y\":2},\"d\":\"sym\",\"e\":\"q\\\"\\n\"}\n",
            "[]\n{}\n",
            "{\n  \"a\": [],\n  \"b\": {},\n  \"c\": [\n    1,\n    [\n      2\n    ]\n  ]\n}\n",
            "[{\"unit\":\"C\",\"value\":21.5}]\n",
            "\"Red\"\n",
            "\"2026-01-02 03:04:05 UTC\"\n",
            "parse error: expected a string key at line 1 column 2\n",
            "parse error: unexpected end of input at line 1 column 6\n",
            "parse error: nesting of 101 is too deep at line 1 column 101\n",
            "generator error: NaN not allowed in JSON\n",
            "type error: not a JSON number: JSON::Value::Text(value: \"quarz\")\n",
            "12345678901234567890\n-1500.0\n\"a\\tb\"\ntrue\n",
            "JSON::Value::List(items: [JSON::Value::Integer(value: 1), JSON::Value::Null])\n",
            "\"0.1.0\"\n",
        )
    );
}

/// The `&block` parameter is an ordinary procedure value: `yield`,
/// `block.call`, `block.()` and `block[]` are interchangeable, and it can
/// be forwarded or returned.
#[test]
fn block_parameters_are_procedures() {
    expect(
        r#"def twice(&block: (Int) -> Int) -> Int = block.call(1) + block.(2) + block[3] + yield(4)
def forward(&block: (Int) -> Int) -> Int = twice(&block)
def forward2(&: (Int) -> Int) -> Int = twice(&)
def pick(&block: (Int) -> Int) -> (Int) -> Int = block
def anon(&: (Int) -> Int) -> Int = yield(2)
puts twice { |x| x * 10 }
puts forward { |x| x + 1 }
puts forward2 { |x| x + 2 }
puts pick { |x| x - 1 }.call(5)
puts anon { |x| x * 3 }
"#,
        "100\n14\n18\n4\n6\n",
    );
}

#[test]
fn backtraces_and_line_numbers() {
    expect(
        r#"def inner(n: Int) -> Int
  raise ArgumentError, "n=#{n}" if n > 1
  inner(n + 1)
end
begin
  inner(0)
rescue ArgumentError => e
  puts e.message
  puts e.backtrace.join("\n")
end
puts __LINE__
[1].each { |x| puts __LINE__ + x }
"#,
        "n=2\ntest:2:in main#inner\ntest:3:in main#inner\ntest:3:in main#inner\ntest:6:in <main>\n11\n13\n",
    );
}

/// Overloads resolved statically must stay on the same overload when the
/// receiver's run-time class is a subclass or an enum variant.
#[test]
fn overloads_through_dynamic_dispatch() {
    expect(
        r#"
enum Shape
  Dot
  | Line(len: Int)

  def scale(factor: Int) -> String = "int #{factor}"
  def scale(factor: String) -> String = "str #{factor}"
end
puts Shape::Dot.scale(2)
puts Shape::Line.new(len: 1).scale("x")

class Base
  def f(x: Int) -> String = "base int"
  def f(x: String) -> String = "base str"
  def g(x: Int) -> String = "base g"
end

class Sub < Base
  def f(x: String) -> String = "sub str"
  def g(x: Int) -> String = "sub g"
end

def call(b: Base) -> Nil
  puts b.f(1)
  puts b.f("s")
  puts b.g(1)
end
call(Sub.new)
call(Base.new)
"#,
        "int 2\nstr x\nbase int\nsub str\nsub g\nbase int\nbase str\nbase g\n",
    );
}

/// Blocks with a receiver: what the checker rejects.
#[test]
fn receiver_block_errors() {
    let out = common::diagnostics(
        r#"class Box
  var @n: Int = 0
  def bump(&b: Box.() -> Nil) -> Nil
    instance_exec(&b)
  end
  def n -> Int = @n
end
Box.new.bump { @n = 1 }
def run(&b: Box.() -> Nil) -> Nil
  yield
end
f: (Int) -> Int = -> (x: Int) { x }
g: Box.() -> Nil = f
Box.new.bump { nothing_here }
def n -> Int = 42
Box.new.bump { n }
class Inner
  include DslScope
  def leaf -> Int = 1
end
class Builder
  include DslScope
  def item -> Int = 2
  def inner(&b: Inner.() -> Int) -> Int = Inner.new.instance_exec(&b)
end
Builder.new.instance_exec { inner { item } }
"#,
    )
    .join("\n");
    assert!(out.contains("not accessible from this block"), "{out}");
    assert!(
        out.contains("`yield` cannot run a block with a receiver"),
        "{out}"
    );
    assert!(
        out.contains("cannot assign (Int) -> Int to `g` of type Box.() -> Nil"),
        "{out}"
    );
    assert!(
        out.contains("undefined local variable or method `nothing_here` for Box"),
        "{out}"
    );
    assert!(out.contains("warning: `n` is a method of both"), "{out}");
    assert!(
        out.contains("undefined local variable or method `item` for Inner"),
        "{out}"
    );
}

/// `using` in bodies and on block parameters is lexically scoped.
#[test]
fn using_scoping() {
    let out = common::diagnostics(
        r#"module Shout
  extension String
    def shout -> String = upcase + "!"
  end
end
def a -> String
  using Shout
  "x".shout
end
def b -> String = "y".shout
v = using Shout { "z".shout }
w = "w".shout
def c(&: () -> String using Shout) -> String = yield
p c { "c".shout }
f = -> { "f".shout }
p c(&f)
"#,
    )
    .join("\n");
    assert!(
        out.contains("test:10:19: error: undefined method `shout` for String"),
        "{out}"
    );
    assert!(
        out.contains("test:12:5: error: undefined method `shout` for String"),
        "{out}"
    );
    assert!(
        out.contains("test:15:10: error: undefined method `shout` for String"),
        "{out}"
    );
    assert!(!out.contains("test:8:"), "{out}");
    assert!(!out.contains("test:11:"), "{out}");
    assert!(!out.contains("test:14:"), "{out}");
    // A declaration error is reported where the parameter is.
    let out =
        common::diagnostics("def d(&: () -> String using String) -> String = yield\n").join("\n");
    assert!(
        out.contains("test:1:7: error: `using String`: not a module"),
        "{out}"
    );
}
