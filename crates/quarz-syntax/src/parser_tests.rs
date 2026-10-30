use crate::parser::parse;
use crate::sexp::program_to_sexp;

fn sexp(src: &str) -> String {
    let parsed = parse(src);
    let errors: Vec<String> = parsed
        .diagnostics
        .iter()
        .filter(|d| d.is_error())
        .map(|d| d.message.clone())
        .collect();
    assert!(errors.is_empty(), "errors for {src:?}: {errors:?}");
    program_to_sexp(&parsed.program).trim_end().to_string()
}

fn errors(src: &str) -> Vec<String> {
    parse(src)
        .diagnostics
        .into_iter()
        .filter(|d| d.is_error())
        .map(|d| d.message)
        .collect()
}

#[test]
fn precedence() {
    assert_eq!(sexp("1 + 2 * 3"), "(call 1 + (call 2 * 3))");
    assert_eq!(sexp("1 * 2 + 3"), "(call (call 1 * 2) + 3)");
    assert_eq!(sexp("-2 ** 2"), "(call (call 2 ** 2) -@)");
    assert_eq!(sexp("2 ** -1"), "(call 2 ** -1)");
    assert_eq!(sexp("-2.abs"), "(call -2 abs)");
    assert_eq!(sexp("-x.abs"), "(call (call (call _ x) abs) -@)");
    assert_eq!(
        sexp("a || b && c"),
        "(or (call _ a) (and (call _ b) (call _ c)))"
    );
    assert_eq!(
        sexp("a and b or c"),
        "(or (and (call _ a) (call _ b)) (call _ c))"
    );
    assert_eq!(sexp("not a == b"), "(not (call (call _ a) == (call _ b)))");
    assert_eq!(sexp("!a == b"), "(call (not (call _ a)) == (call _ b))");
    assert_eq!(
        sexp("a ? b : c"),
        "(if (call _ a) (then (call _ b)) (else (call _ c)))"
    );
    assert_eq!(sexp("1..10"), "(range 1 .. 10)");
    assert_eq!(sexp("x = 1...y"), "(= x (range 1 ... (call _ y)))");
    assert_eq!(sexp("(1..)"), "(range 1 .. )");
    assert_eq!(sexp("a = b = 1"), "(= a (= b 1))");
    assert_eq!(sexp("x = 1\nx += 2"), "(= x 1)\n(+= x 2)");
    assert_eq!(
        sexp("a <=> b == c"),
        "(call (call (call _ a) <=> (call _ b)) == (call _ c))"
    );
}

#[test]
fn anonymous_block_parameter() {
    assert_eq!(
        sexp("def f(&: (Int) -> Int) -> Int = g(&)"),
        "(def f (params &&:(Int) -> Int) -> Int (call _ g (blockpass &)))"
    );
}

#[test]
fn shareable_procedure_types() {
    assert_eq!(
        sexp("def f(&h: shareable (Int) -> Nil, g: (shareable () -> Int)? = nil) -> Nil = nil"),
        "(def f (params &h:shareable (Int) -> Nil g:shareable () -> Int?=nil) -> Nil nil)"
    );
    assert_eq!(
        sexp("def f(&: (Int) -> Void) -> Void = nil"),
        "(def f (params &&:(Int) -> Void) -> Void nil)"
    );
    assert_eq!(
        errors("x: shareable Int = 1"),
        vec!["`shareable` applies to a procedure type"]
    );
}

#[test]
fn bytes_literals() {
    assert_eq!(sexp("b\"\\x00a\\n\\377\""), "(bytes 00610aff)");
    // Single quotes as Ruby's: only `\\` and `\'` are escapes.
    assert_eq!(sexp("b'\\x41\\\\\\''"), "(bytes 5c7834315c27)");
    assert_eq!(sexp("b\"\\u0041\\\"\""), "(bytes 4122)");
    // Beyond ASCII, written or escaped, is text, not bytes.
    for src in ["b\"é\"", "b'é'", "b\"\\u00e9\""] {
        assert!(
            errors(src)[0].contains("a Bytes literal holds ASCII"),
            "{src}"
        );
    }
}

#[test]
fn locals_versus_calls() {
    assert_eq!(sexp("x = 1\nx"), "(= x 1)\nx");
    assert_eq!(sexp("x"), "(call _ x)");
    assert_eq!(sexp("x = 1\nx(2)"), "(= x 1)\n(call _ x 2)");
    assert_eq!(sexp("x = 1\nx [1]"), "(= x 1)\n(call x [] 1)");
    assert_eq!(sexp("foo [1]"), "(call _ foo (array 1))");
    assert_eq!(sexp("foo[1]"), "(call (call _ foo) [] 1)");
    assert_eq!(sexp("y = 2\ny /2"), "(= y 2)\n(call y / 2)");
}

#[test]
fn command_calls() {
    assert_eq!(sexp("puts 1, 2"), "(call _ puts 1 2)");
    assert_eq!(sexp("puts(1)"), "(call _ puts 1)");
    assert_eq!(sexp("puts (1)"), "(call _ puts 1)");
    assert_eq!(sexp("foo -x"), "(call _ foo (call (call _ x) -@))");
    assert_eq!(sexp("foo - x"), "(call (call _ foo) - (call _ x))");
    assert_eq!(sexp("foo-x"), "(call (call _ foo) - (call _ x))");
    assert_eq!(sexp("foo *x"), "(call _ foo (splat (call _ x)))");
    assert_eq!(sexp("foo &blk"), "(call _ foo (blockpass (call _ blk)))");
    assert_eq!(
        sexp("obj.meth x, y: 1"),
        "(call (call _ obj) meth (call _ x) y: 1)"
    );
    assert_eq!(
        sexp("raise Foo, \"m\" unless x"),
        "(if (not (call _ x)) (then (call _ raise Foo (str \"m\"))))"
    );
    assert_eq!(sexp("return 1, 2"), "(return (array 1 2))");
    assert_eq!(sexp("return if x"), "(if (call _ x) (then (return)))");
    assert_eq!(sexp("yield a, b"), "(yield (call _ a) (call _ b))");
    assert_eq!(sexp("super"), "(super zsuper)");
    assert_eq!(sexp("super(1)"), "(super 1)");
}

#[test]
fn blocks_and_do_binding() {
    assert_eq!(
        sexp("foo bar do |x| x end"),
        "(call _ foo (call _ bar) (block (params x) x))"
    );
    assert_eq!(
        sexp("foo bar { |x| x }"),
        "(call _ foo (call _ bar (block (params x) x)))"
    );
    assert_eq!(
        sexp("foo(bar) do |x| x end"),
        "(call _ foo (call _ bar) (block (params x) x))"
    );
    assert_eq!(sexp("while x do y end"), "(while (call _ x) (call _ y))");
    assert_eq!(
        sexp("a.b(c) { 1 }.d"),
        "(call (call (call _ a) b (call _ c) (block (params) 1)) d)"
    );
    assert_eq!(sexp("f { }"), "(call _ f (block (params)))");
    assert_eq!(sexp("x = {}"), "(= x (hash))");
    assert_eq!(sexp("f({})"), "(call _ f (hash))");
    assert_eq!(sexp("map(&:to_s)"), "(call _ map (blockpass :to_s))");
    assert_eq!(
        sexp("xs.each { |x: Int, *rest, k: Int = 1, &b| }"),
        "(call (call _ xs) each (block (params x:Int *rest kw:k:Int=1 &b)))"
    );
    assert_eq!(
        sexp("f = ->(x: Int) { x }\nf.(1)\nf.call(2)"),
        "(= f (lambda (params x:Int) x))\n(call f call 1)\n(call f call 2)"
    );
    assert_eq!(sexp("-> { 1 }"), "(lambda (params) 1)");
    assert_eq!(sexp("-> x { x }"), "(lambda (params x) x)");
}

#[test]
fn labels_hashes_and_keywords() {
    assert_eq!(
        sexp("{ a: 1, \"b c\": 2, \"d\" => 3, e => 4, **h }"),
        "(hash (pair :a 1) (pair :\"b c\" 2) (pair (str \"d\") 3) (pair (call _ e) 4) (splat2 (call _ h)))"
    );
    assert_eq!(
        sexp("x = 1\n{ x:, y: }"),
        "(= x 1)\n(hash (pair :x x) (pair :y (call _ y)))"
    );
    assert_eq!(sexp("f(a: 1, b:2)"), "(call _ f a: 1 b: 2)");
    assert_eq!(sexp("f(if: 1)"), "(call _ f if: 1)");
    assert_eq!(sexp("x: Int? = nil"), "(decl x:Int? nil)");
    assert_eq!(
        sexp("a ? b : c"),
        "(if (call _ a) (then (call _ b)) (else (call _ c)))"
    );
}

#[test]
fn multiple_assignment() {
    assert_eq!(sexp("a, b = 1, 2"), "(masgn (targets a b) (array 1 2))");
    assert_eq!(sexp("a, *b = xs"), "(masgn (targets a *b) (call _ xs))");
    assert_eq!(sexp("*a, b = xs"), "(masgn (targets *a b) (call _ xs))");
    assert_eq!(
        sexp("a, (b, c) = xs"),
        "(masgn (targets a (nested b c)) (call _ xs))"
    );
    assert_eq!(
        sexp("@a, b.c = 1, 2"),
        "(masgn (targets @a (attr (call _ b) .c)) (array 1 2))"
    );
    assert_eq!(
        sexp("a, b = 1, 2\na"),
        "(masgn (targets a b) (array 1 2))\na"
    );
}

#[test]
fn assignment_targets() {
    assert_eq!(sexp("a.b = 1"), "(= (attr (call _ a) .b) 1)");
    assert_eq!(sexp("a[1] = 2"), "(= (index (call _ a) 1) 2)");
    assert_eq!(sexp("a[1] += 2"), "(+= (index (call _ a) 1) 2)");
    assert_eq!(sexp("a[1]?"), "(call (call _ a) []? 1)");
    assert_eq!(
        sexp("def []?(i: Int) -> Int? = nil"),
        "(def []? (params i:Int) -> Int? nil)"
    );
    assert_eq!(sexp("@x ||= 1"), "(||= @x 1)");
    assert_eq!(sexp("Foo = 1"), "(const Foo 1)");
    assert_eq!(
        sexp("x = risky rescue 0"),
        "(= x (begin (call _ risky) (rescue 0)))"
    );
    assert!(!errors("1 = 2").is_empty());
    assert!(!errors("x += 1").is_empty());
}

#[test]
fn control_flow() {
    assert_eq!(
        sexp("if a then 1 elsif b then 2 else 3 end"),
        "(if (call _ a) (then 1) (else (if (call _ b) (then 2) (else 3))))"
    );
    assert_eq!(sexp("unless a\n1\nend"), "(if (not (call _ a)) (then 1))");
    assert_eq!(sexp("x = 1 if a"), "(if (call _ a) (then (= x 1)))");
    assert_eq!(
        sexp("begin\n1\nend while a"),
        "(do-while (call _ a) (begin 1))"
    );
    assert_eq!(sexp("until a\n1\nend"), "(until (call _ a) 1)");
    assert_eq!(
        sexp("case x\nwhen 1, 2 then :a\nwhen String\n:b\nelse :c\nend"),
        "(case (call _ x) (when (conds 1 2) :a) (when (conds String) :b) (else :c))"
    );
    assert_eq!(
        sexp("begin\nf\nrescue A, B => e\ng\nrescue\nh\nelse\ni\nensure\nj\nend"),
        "(begin (call _ f) (rescue A B => e (call _ g)) (rescue (call _ h)) (else (call _ i)) (ensure (call _ j)))"
    );
    assert_eq!(
        sexp("def f\n1\nrescue => e\n2\nend"),
        "(def f (params) (begin 1 (rescue => e 2)))"
    );
    assert_eq!(
        sexp("loop { break 1 }"),
        "(call _ loop (block (params) (break 1)))"
    );
    assert_eq!(sexp("(a; b)"), "(seq (call _ a) (call _ b))");
}

#[test]
fn patterns() {
    assert_eq!(
        sexp("x = 1\ncase v\nin Int => n if n > 0 then 1\nin [a, *rest] then 2\nin {name: String => s, age:} then 3\nin Point(x:, y: 0) then 4\nin Foo[a, b] then 5\nin ^x | nil then 6\nin 1..5 then 7\nin [*, :x, *post] then 8\nend"),
        "(= x 1)\n(case-in (call _ v) (in (capture Int n) (if (call n > 0)) 1) (in (arr a *rest) 2) (in (hash name: (capture String s) age:) 3) (in (Point x: y: 0) 4) (in (Foo a b) 5) (in (alt ^x nil) 6) (in (range 1 .. 5) 7) (in (find * :x *post) 8))"
    );
    assert_eq!(sexp("v => [a, b]"), "(=> (call _ v) (arr a b))");
    assert_eq!(sexp("v => Point(x:, y:)"), "(=> (call _ v) (Point x: y:))");
    assert_eq!(
        sexp("if v in Int then 1 end"),
        "(if (in (call _ v) Int) (then 1))"
    );
    assert_eq!(
        sexp("case v\nin a, b then 1\nend"),
        "(case-in (call _ v) (in (arr a b) 1))"
    );
    assert_eq!(
        sexp("case v\nin x:, y: then 1\nend"),
        "(case-in (call _ v) (in (hash x: y:) 1))"
    );
    // Pattern variables are locals afterwards.
    assert_eq!(sexp("v => [a]\na"), "(=> (call _ v) (arr a))\na");
}

#[test]
fn declarations() {
    assert_eq!(
        sexp("class Foo[T] < Bar[T]\n@x: Int\nvar @y: T? = nil\nattr_reader :x, :y\ninclude Comparable[Foo[T]]\nprivate\ndef initialize(@x: Int, k: Bool = false, *, opt: Int? = nil, **rest: String, &blk: (Int) -> Nil) -> Nil\nend\nend"),
        "(class Foo (tparams T) < Bar[T] (field x:Int) (var y:T?=nil) (attr_reader x y) (include Comparable[Foo[T]]) (private) (def initialize (params @x:Int k:Bool=false kw:opt:Int?=nil **rest:String &blk:(Int) -> Nil) -> Nil))"
    );
    assert_eq!(
        sexp("abstract class A\nabstract def f -> Int\nend"),
        "(abstract-class A (def abstract f (params) -> Int))"
    );
    assert_eq!(
        sexp("private def f -> Int = 1"),
        "(def Private f (params) -> Int 1)"
    );
    assert_eq!(
        sexp("def to_s -> String = \"x\""),
        "(def to_s (params) -> String (str \"x\"))"
    );
    assert_eq!(
        sexp("def self.create(x: Int) -> Self = new(x)"),
        "(defs create (params x:Int) -> self (call _ new x))"
    );
    assert_eq!(
        sexp("def ==(o: Foo) -> Bool = true"),
        "(def == (params o:Foo) -> Bool true)"
    );
    assert_eq!(
        sexp("def []=(k: Int, v: Int)\nend"),
        "(def []= (params k:Int v:Int))"
    );
    assert_eq!(
        sexp("def -@ -> Foo = self"),
        "(def -@ (params) -> Foo self)"
    );
    assert_eq!(
        sexp("def name=(v: String)\n@name = v\nend"),
        "(def name= (params v:String) (= @name v))"
    );
    assert_eq!(sexp("module M[out T]\nend"), "(module M (tparams out T))");
    assert_eq!(
        sexp("def push[U >: T](value: U) -> Array[U]\nend"),
        "(def push (tparams U>:T) (params value:U) -> Array[U])"
    );
    assert_eq!(
        sexp("xs.each { |x: Int| x }"),
        "(call (call _ xs) each (block (params x:Int) x))"
    );
    assert_eq!(
        sexp("data P = (x: Int, y: Int = 0)"),
        "(data P (fields x:Int y:Int=0))"
    );
    assert_eq!(
        sexp("data P(x: Int)\ndef f -> Int = x\nend"),
        "(data P (fields x:Int) (def f (params) -> Int (call _ x)))"
    );
    assert_eq!(
        sexp("enum E[T]\n  variant A\n  variant B(v: T)\ndef f -> Int = 1\nend"),
        "(enum E (tparams T) (A) (B v:T) (def f (params) -> Int 1))"
    );
    // The one-line form: variants separated by `|`, as in a union type.
    assert_eq!(sexp("enum C = A | B(x: Int)"), "(enum C (A) (B x:Int))");
    // `data Name = (fields)` is the form without a body, like `enum Name
    // = A | B`; without `=` a body follows and `end` closes it.
    assert_eq!(
        sexp("data Pair[A, B] = (first: A, second: B)\nx = 1"),
        "(data Pair (tparams A B) (fields first:A second:B))\n(= x 1)"
    );
    assert_eq!(sexp("data U = ()"), "(data U (fields))");
    assert_eq!(
        sexp("data C = (\n  host: String,\n  port: Int = 80\n)"),
        "(data C (fields host:String port:Int=80))"
    );
    assert_eq!(sexp("data P(x: Int)\nend"), "(data P (fields x:Int))");
    // A forgotten `=` takes the rest of the file for the body.
    assert!(errors("data P(x: Int)\np P.new(1)")[0]
        .contains("a data type without a body is written `data P = (...)`"));
    assert!(errors("data P = (x: Int) is")[0].contains("end of line after the fields"));
    // `for` comprehensions desugar to filter / flat_map / map.
    assert_eq!(
        sexp("for x in xs when x.even?, y in ys do [x, y] end"),
        "(call (call (call _ xs) filter (block (params x) (call x even?))) flat_map (block (params x) (call (call _ ys) map (block (params y) (array x y)))))"
    );
    assert_eq!(
        sexp("for k, v in h do k end"),
        "(call (call _ h) map (block (params k v) k))"
    );
    assert!(errors("for x in xs do break end")[0].contains("`break` cannot be used"));
    // Without `do`, the body starts on the next line.
    assert_eq!(sexp("for x in xs\n  x\nend"), sexp("for x in xs do x end"));
    assert_eq!(
        sexp("for x in xs, y in ys do x end"),
        "(call (call _ xs) flat_map (block (params x) (call (call _ ys) map (block (params y) x))))"
    );
    assert!(errors("for x in xs x end")[0].contains("`do` or a new line"));
    assert!(errors("for x in xs then x end")[0].contains("`do` or a new line"));
    assert_eq!(sexp("for(1)"), "(call _ for 1)");
    // `Self` is the self type; `self` is a value only.
    assert_eq!(
        sexp("def d -> Self = self"),
        sexp("def d -> Self\n  self\nend")
    );
    assert!(!errors("def d -> self = self").is_empty());
    // The one-line form continues after a `|` that ends a line.
    assert_eq!(
        sexp("enum C = A |\n  B(x: Int) |\n  D"),
        "(enum C (A) (B x:Int) (D))"
    );
    assert_eq!(
        sexp("enum C\n  variant A, B\n  variant D\n  def f -> Int = 1\nend"),
        "(enum C (A) (B) (D) (def f (params) -> Int 1))"
    );
    assert_eq!(
        sexp("enum C\n  variant Only(x: Int)\nend"),
        "(enum C (Only x:Int))"
    );
    // Variants and other declarations can be mixed, and `variant` is a
    // keyword only before a constant.
    assert_eq!(
        sexp("enum C\n  variant A\n  def f -> Int = 1\n  variant B(\n    x: Int\n  ),\n    D\nend"),
        "(enum C (A) (B x:Int) (D) (def f (params) -> Int 1))"
    );
    assert_eq!(sexp("variant = 1"), "(= variant 1)");
    assert!(errors("enum C =\nputs 1")[0].contains("a variant after `=`"));
    assert_eq!(
        sexp("extension Array[T <: Comparable[T]]\ndef m -> Int = 1\nend"),
        "(extension Array[T] (tparams T<:Comparable[T]) (def m (params) -> Int 1))"
    );
    assert_eq!(sexp("type Id = Int"), "(type Id Int)");
    assert_eq!(
        sexp("type H[K] = Hash[K, Int | Nil]"),
        "(type H (tparams K) Hash[K, Int | Nil])"
    );
    assert_eq!(sexp("using Foo::Bar"), "(using Foo::Bar)");
    assert_eq!(sexp("require \"json\""), "(require \"json\")");
    assert_eq!(sexp("alias to_str to_s"), "(alias to_str to_s)");
    assert_eq!(
        sexp("extern \"C\"\ndef strlen(s: CString) -> SizeT\nend"),
        "(extern \"C\" (def native strlen (params s:CString) -> SizeT))"
    );
    // Contextual keywords remain usable as identifiers.
    assert_eq!(sexp("data = 1\ntype = data"), "(= data 1)\n(= type data)");
}

#[test]
fn types_in_expressions() {
    assert_eq!(sexp("Array[Int].new"), "(call (type Array[Int]) new)");
    assert_eq!(
        sexp("Hash[String, Int].new"),
        "(call (type Hash[String, Int]) new)"
    );
    assert_eq!(sexp("ARGV[0]"), "(call ARGV [] 0)");
    assert_eq!(sexp("Set[1, 2]"), "(call Set [] 1 2)");
    assert_eq!(sexp("x.as(Int)"), "(call (call _ x) as Int)");
    assert_eq!(
        sexp("max_by[Int, String](xs)"),
        "(call _ max_by[Int, String] (call _ xs))"
    );
    assert_eq!(sexp("Foo::Bar.new"), "(call Foo::Bar new)");
    assert_eq!(sexp("Foo::bar"), "(call Foo bar)");
    assert_eq!(sexp("::Foo"), "::Foo");
    assert_eq!(sexp("Integer(\"3\")"), "(call _ Integer (str \"3\"))");
}

#[test]
fn literals() {
    assert_eq!(sexp("\"a#{b}c\""), "(str \"a\" (interp (call _ b)) \"c\")");
    assert_eq!(sexp("\"a\" \"b\""), "(str \"ab\")");
    assert_eq!(sexp(":\"a b\""), ":\"a b\"");
    assert_eq!(sexp(":\"a#{b}\""), "(dsym \"a\" (interp (call _ b)))");
    assert_eq!(sexp("/a#{b}/i"), "(regexp \"a\" (interp (call _ b)) /i)");
    assert_eq!(sexp("%w[a b]"), "(array (str \"a\") (str \"b\"))");
    assert_eq!(sexp("%i[a b]"), "(array :a :b)");
    assert_eq!(sexp("[1, *xs, 3]"), "(array 1 (splat (call _ xs)) 3)");
    assert_eq!(
        sexp("x = <<~EOS\n  hi #{y}\nEOS\n"),
        "(= x (str \"hi \" (interp (call _ y)) \"\\n\"))"
    );
    assert_eq!(sexp("__FILE__"), "File");
    assert_eq!(sexp("a\n  .b\n  .c"), "(call (call (call _ a) b) c)");
    assert_eq!(sexp("a&.b"), "(call&. (call _ a) b)");
    assert_eq!(sexp("a.:b"), "(methodref (call _ a) b)");
    assert_eq!(sexp("0x1f"), "1fr16");
}

#[test]
fn error_recovery() {
    let errs = errors("x = (1 + \ny = 2\nz = )\nw = 3");
    assert!(!errs.is_empty());
    // Parsing continues after an error.
    let parsed = parse("def f(\nend\nx = 1");
    assert!(!parsed.diagnostics.is_empty());
    assert!(!parsed.program.body.is_empty());
}

#[test]
fn cog_keyword() {
    assert_eq!(sexp("cog::Response"), "cog::Response");
    assert_eq!(sexp("cog::A::B.new"), "(call cog::A::B new)");
    assert_eq!(sexp("cog"), "cog");
    assert_eq!(sexp("cog.get(1)"), "(call cog get 1)");
    // `cog.name` and `cog.version` are the manifest's, as literals.
    assert_eq!(sexp("cog.name"), "(str \"main\")");
    assert_eq!(sexp("cog.version.size"), "(call (str \"0.0.0\") size)");
    let meta = crate::parser::CogMeta {
        name: "httpx".into(),
        version: "1.4.0".into(),
    };
    let parsed = crate::parser::parse_cog_file("puts cog.name + cog.version", 0, 0, &meta);
    assert_eq!(
        program_to_sexp(&parsed.program).trim_end(),
        "(call _ puts (call (str \"httpx\") + (str \"1.4.0\")))"
    );
    assert!(sexp("def f(x: cog::T) -> cog::U = x").contains("cog::T"));
    assert_eq!(
        sexp("case x\nin cog::A then 1\nend"),
        "(case-in (call _ x) (in cog::A 1))"
    );
    assert!(!errors("cog = 1").is_empty());
}

#[test]
fn type_param_bounds() {
    assert_eq!(sexp("class A[T<:X]\nend"), "(class A (tparams T<:X))");
    assert_eq!(sexp("class A[T <: X]\nend"), "(class A (tparams T<:X))");
    assert_eq!(sexp("class A[T <:X]\nend"), "(class A (tparams T<:X))");
    assert_eq!(
        sexp("def f[U>:T<:Object](x: U) -> U = x"),
        "(def f (tparams U>:T<:Object) (params x:U) -> U x)"
    );
    assert_eq!(
        sexp("def f[U <: Object >: T](x: U) -> U = x"),
        "(def f (tparams U>:T<:Object) (params x:U) -> U x)"
    );
    assert_eq!(
        sexp("class A[out T <: Shape, in U]\nend"),
        "(class A (tparams out T<:Shape in U))"
    );
    assert_eq!(
        sexp("def f[T <: Comparable[T] & Describable](x: T) -> T = x"),
        "(def f (tparams T<:Comparable[T]&Describable) (params x:T) -> T x)"
    );
    assert_eq!(
        sexp("def f[T<:M::Shape?](x: T) -> T = x"),
        "(def f (tparams T<:M::Shape?) (params x:T) -> T x)"
    );
    assert_eq!(
        sexp("class Box[T <: Shape] < Base[T]\nend"),
        "(class Box (tparams T<:Shape) < Base[T])"
    );
    // Outside a type parameter list `<:` is still `<` and a symbol.
    assert_eq!(sexp("a <:b"), "(call (call _ a) < :b)");

    let old = errors("def f[T: Comparable[T]](x: T) -> T = x");
    assert!(
        old[0].contains("upper bound is written `T <: X`, not `T: X`"),
        "{old:?}"
    );
    for src in [
        "class A[T < : X]\nend",
        "class A[T < :X]\nend",
        "def f[U > : T](x: U) -> U = x",
    ] {
        let errs = errors(src);
        assert!(
            errs[0].contains("is written without a space"),
            "{src}: {errs:?}"
        );
    }
    assert!(errors("class A[T <: X <: Y]\nend")[0].contains("two upper bounds"));
    assert!(errors("def f[U >: X >: Y](x: U) -> U = x")[0].contains("two lower bounds"));
    assert!(errors("class A[T < X]\nend")[0].contains("expected `<:` or `>:`"));
    assert!(errors("class A[T :X]\nend")[0].contains("upper bound is written `T <: X`"));
    // Without spaces, the same errors as with them.
    for (tight, spaced) in [
        ("T<::X", "T <: :X"),
        ("T<:<=>", "T <: <=>"),
        ("T<:\"X\"", "T <: \"X\""),
        ("T<:X=", "T <: X ="),
        ("T<:x=", "T <: x ="),
        ("T<:[]=", "T <: [] ="),
        ("U>:X>:Y=", "U >: X >: Y ="),
        ("T<:X>:Y<:Z", "T <: X >: Y <: Z"),
        ("T<:X<Y", "T <: X < Y"),
        ("U>:X>Y", "U >: X > Y"),
        ("T<:X<:\"Y\"", "T <: X <: \"Y\""),
        ("T<\"Y\"", "T < \"Y\""),
        ("T<:X>\"Y\"", "T <: X > \"Y\""),
    ] {
        let (a, b) = (
            errors(&format!("class A[{tight}]\nend")),
            errors(&format!("class A[{spaced}]\nend")),
        );
        assert_eq!(a[0], b[0], "{tight} / {spaced}");
    }
    assert!(errors("class A[T :\"X\"]\nend")[0].contains("upper bound is written `T <: X`"));
    for src in [
        "class A[T<:X=]\nend",
        "class A[T<:[]=]\nend",
        "class A[T<:::X=]\nend",
    ] {
        let errs = errors(src);
        assert!(
            errs[0].contains("expected `,` or `]`, found `=`"),
            "{src}: {errs:?}"
        );
    }
    assert_eq!(sexp("class A[T<:[]]\nend"), sexp("class A[T <: []]\nend"));
    assert_eq!(sexp("class A[T<:::X]\nend"), sexp("class A[T <: ::X]\nend"));
    assert_eq!(
        sexp("def f[U>:cog::A](x: U) -> U = x"),
        "(def f (tparams U>:cog::A) (params x:U) -> U x)"
    );
}

/// A block's result type after its parameters, and the `->` that starts
/// a lambda instead (`parse_block_result_type`'s table).
#[test]
fn block_result_type() {
    assert_eq!(
        sexp("xs.map do |x: Int| -> String\n  x.to_s\nend"),
        "(call (call _ xs) map (block (params x:Int) -> String (call x to_s)))"
    );
    assert_eq!(
        sexp("xs.map { |x| -> Int x + 1 }"),
        "(call (call _ xs) map (block (params x) -> Int (call x + 1)))"
    );
    assert_eq!(
        sexp("f do -> Void\n  1\nend"),
        "(call _ f (block (params) -> Void 1))"
    );
    assert_eq!(
        sexp("f { -> Void 1 }"),
        "(call _ f (block (params) -> Void 1))"
    );
    assert_eq!(
        sexp("f { |x| -> Int | String x }"),
        "(call _ f (block (params x) -> Int | String x))"
    );
    assert_eq!(
        sexp("f { |x| -> Foo [1] }"),
        "(call _ f (block (params x) -> Foo (array 1)))"
    );
    assert_eq!(
        sexp("f { -> ::Foo 1 }"),
        "(call _ f (block (params) -> ::Foo 1))"
    );
    assert_eq!(
        sexp("f { -> [Int, String] [1, \"a\"] }"),
        "(call _ f (block (params) -> [Int, String] (array 1 (str \"a\"))))"
    );
    assert_eq!(
        sexp("f { -> (Int) -> Bool nil }"),
        "(call _ f (block (params) -> (Int) -> Bool nil))"
    );
    assert_eq!(
        sexp("f { -> () -> Int nil }"),
        "(call _ f (block (params) -> () -> Int nil))"
    );
    assert_eq!(
        sexp("f { -> shareable (Int) -> Int nil }"),
        "(call _ f (block (params) -> shareable (Int) -> Int nil))"
    );
    assert_eq!(
        sexp("f { -> ((Int) -> Int)? nil }"),
        "(call _ f (block (params) -> (Int) -> Int? nil))"
    );
    // The body's first statement is a lambda.
    assert_eq!(
        sexp("f do ->(y) { y } end"),
        "(call _ f (block (params) (lambda (params y) y)))"
    );
    assert_eq!(
        sexp("f do -> x { x } end"),
        "(call _ f (block (params) (lambda (params x) x)))"
    );
    assert_eq!(
        sexp("f do -> { 1 } end"),
        "(call _ f (block (params) (lambda (params) 1)))"
    );
    assert_eq!(
        sexp("f do -> do 1 end end"),
        "(call _ f (block (params) (lambda (params) 1)))"
    );
    assert_eq!(
        sexp("f do -> shareable { shareable } end"),
        "(call _ f (block (params) (lambda (params shareable) shareable)))"
    );
    assert_eq!(
        sexp("f do ->() -> Int { 1 } end"),
        "(call _ f (block (params) (lambda (params) -> Int 1)))"
    );
    assert_eq!(
        sexp("f do ->(*a) { a } end"),
        "(call _ f (block (params) (lambda (params *a) a)))"
    );
    assert_eq!(
        sexp("f do |x| ->() { x } end"),
        "(call _ f (block (params x) (lambda (params) x)))"
    );
    // A `->` beginning a line begins the body, with or without
    // parameters.
    assert_eq!(
        sexp("f do\n  -> { 1 }\nend"),
        "(call _ f (block (params) (lambda (params) 1)))"
    );
    assert_eq!(
        sexp("f do |x|\n  -> { x }\nend"),
        "(call _ f (block (params x) (lambda (params) x)))"
    );
    assert_eq!(
        sexp("f do ->(shareable) { shareable } end"),
        "(call _ f (block (params) (lambda (params shareable) shareable)))"
    );
    assert_eq!(
        sexp("f { -> (shareable (Int) -> Int) nil }"),
        "(call _ f (block (params) -> shareable (Int) -> Int nil))"
    );
    assert_eq!(
        errors("f { -> 1 }"),
        vec!["expected a type after `->` (the block's result type) or a lambda"]
    );
}

/// `y := e` and `y: T = e` declare a local in the innermost scope, also
/// where an outer `y` exists; the value is read before the declaration.
#[test]
fn local_declarations() {
    assert_eq!(sexp("y := 1"), "(decl y:= 1)");
    assert_eq!(sexp("y:=1"), "(decl y:= 1)");
    assert_eq!(
        sexp("y = 1\ny := y + 1"),
        "(= y 1)\n(decl y:= (call y + 1))"
    );
    assert_eq!(sexp("y = 1\ny: Int = 2"), "(= y 1)\n(decl y:Int 2)");
    // Not yet a local in its own value: `y` there is a call.
    assert_eq!(sexp("y := y"), "(decl y:= (call _ y))");
    assert_eq!(
        sexp("f { |x| y := x }"),
        "(call _ f (block (params x) (decl y:= x)))"
    );
    // `:==` and `:=~` stay the operators' symbols.
    assert_eq!(sexp("p :==, :=~"), "(call _ p :== :\"=~\")");
    // A name declared in a `case/in` arm or a rescue clause is out of
    // scope after it (a call there); one assigned there stays.
    assert_eq!(
        sexp("case 1\nin Int\n  k := 2\n  j = 3\nend\nk\nj"),
        "(case-in 1 (in Int (decl k:= 2) (= j 3)))\n(call _ k)\nj"
    );
    assert_eq!(
        sexp("begin\n  1\nrescue\n  k := 2\nend\nk"),
        "(begin 1 (rescue (decl k:= 2)))\n(call _ k)"
    );
    // ... unless it was one before.
    assert_eq!(
        sexp("k = 0\ncase 1\nin Int\n  k := 2\nend\nk"),
        "(= k 0)\n(case-in 1 (in Int (decl k:= 2)))\nk"
    );
    assert_eq!(errors("y : = 1"), vec!["expected end of line, found `:`"]);
    assert_eq!(
        errors("@x := 1"),
        vec!["`:=` declares a local variable, not a field: declare `@x` in the class body, or with `@x: T = value` in `initialize`"]
    );
    assert_eq!(
        errors("X := 1"),
        vec!["`:=` declares a local variable: a constant is assigned with `X = value`"]
    );
    assert_eq!(
        errors("a, b := 1, 2"),
        vec!["`:=` declares one local variable; assign several with `a, b = ...`"]
    );
}

/// `::name(...)`: a function call (docs/01 §1). `foo ::bar` passes it,
/// as `foo ::Bar` passes the constant; `x::bar` is a method call.
#[test]
fn function_calls() {
    assert_eq!(sexp("::puts \"x\""), "(call :: puts (str \"x\"))");
    assert_eq!(sexp("::f(1, 2)"), "(call :: f 1 2)");
    assert_eq!(sexp("::loop { 1 }"), "(call :: loop (block (params) 1))");
    assert_eq!(sexp("p ::f"), "(call _ p (call :: f))");
    assert_eq!(sexp("p ::Foo"), "(call _ p ::Foo)");
    assert_eq!(sexp("x = 1\nx::abs"), "(= x 1)\n(call x abs)");
    assert_eq!(sexp("::Integer(\"3\")"), "(call :: Integer (str \"3\"))");
    assert_eq!(sexp("Integer(\"3\")"), "(call _ Integer (str \"3\"))");
    assert_eq!(sexp("p ::Integer"), "(call _ p ::Integer)");
    assert_eq!(sexp("::Foo::Bar"), "::Foo::Bar");
    // A function call is no variable to assign.
    for src in ["::foo = 1", "::x += 1", "::q ||= 4", "::a, ::b = 1, 2"] {
        assert!(!errors(src).is_empty(), "{src}");
    }
}

#[test]
fn procedure_types_as_explicit_type_arguments() {
    // A `(` after a call's `[` starts types when `(` follows the `]`
    // (`method_ref[(Int) -> Int](:fact)`, docs/14 §5); otherwise an index.
    assert_eq!(
        sexp("f[(Int) -> Int](x)"),
        "(call _ f[(Int) -> Int] (call _ x))"
    );
    assert_eq!(
        sexp("f[(Int) -> Int, String](x)"),
        "(call _ f[(Int) -> Int, String] (call _ x))"
    );
    assert_eq!(sexp("a[(1 + 2)]"), "(call (call _ a) [] (call 1 + 2))");
    assert_eq!(sexp("a[(1 + 2)]"), sexp("a[1 + 2]"));
    assert_eq!(sexp("h[(k)]"), sexp("h[k]"));
    assert!(errors("x = a[(1 + 2)]\ny = h[(k)]").is_empty());
}
