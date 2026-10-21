//! Semantics of the interpreter, checked by running small programs.

mod common;
use common::{expect, run};

#[test]
fn arithmetic() {
    expect(
        "puts 7 / 2, -7 / 2, 7 % -2, 2 ** 10, 2 ** 100, 10.0 / 4, 1 + 1.5",
        "3\n-4\n-1\n1024\n1267650600228229401496703205376\n2.5\n2.5\n",
    );
    expect("puts 9223372036854775807 + 1", "9223372036854775808\n");
    expect(
        "puts (9223372036854775807 + 1) - 1",
        "9223372036854775807\n",
    );
    expect(
        "puts 1.0, 1.5, 1e20, 1.0 / 3, -0.5, 100.0, 1e-7",
        "1.0\n1.5\n1.0e+20\n0.3333333333333333\n-0.5\n100.0\n1.0e-07\n",
    );
    expect(
        "puts 10.divmod(3).inspect, (-7).abs, 3.7.floor, 3.2.ceil, 3.5.round, 3.14159.round(2)",
        "[3, 1]\n7\n3\n4\n4\n3.14\n",
    );
    expect(
        "puts 255.to_s(16), \"ff\".hex, \"0b101\".to_i, \"42abc\".to_i, \"3.5x\".to_f",
        "ff\n255\n0\n42\n3.5\n",
    );
    expect(
        "puts 5.clamp(1, 3), 0.clamp(1, 3), 2.clamp(1, 3)",
        "3\n1\n2\n",
    );
    expect("puts 6.gcd(4), 6.lcm(4), 2.pow(10, 1000)", "2\n12\n24\n");
    let (code, out) = run(
        "begin\n  puts 1 / 0\nrescue ZeroDivisionError => e\n  puts e.message\nend",
        &[],
    );
    assert_eq!((code, out.as_str()), (0, "divided by 0\n"));
}

#[test]
fn strings() {
    expect(
        "s = \"ab\"\nputs s * 3, s + \"c\", \"x#{s}y#{1 + 2}\", s.size, s.upcase",
        "ababab\nabc\nxaby3\n2\nAB\n",
    );
    expect(
        "puts format(\"%05.2f|%-4s|%x|%+d|%s\", 3.14159, \"ab\", 255, 7, nil)",
        "03.14|ab  |ff|+7|\n",
    );
    expect(
        "puts \"%d items\" % [3], \"hello world\".split.inspect, \"a,b,,c\".split(\",\").inspect",
        "3 items\n[\"hello\", \"world\"]\n[\"a\", \"b\", \"\", \"c\"]\n",
    );
    expect("puts \"hello\".center(9, \"*\"), \"hi\".ljust(4) + \"|\", \"hi\".rjust(4), \"Hello World\".swapcase", "**hello**\nhi  |\n  hi\nhELLO wORLD\n");
    expect(
        "puts \"héllo\"[1], \"héllo\"[-1], \"héllo\"[1..3], \"héllo\".reverse, \"héllo\".bytesize",
        "é\no\néll\nolléh\n6\n",
    );
    expect("puts \"a-b_c\".tr(\"-_\", \"  \"), \"hello\".delete(\"l\"), \"aaabbb\".squeeze, \"banana\".count(\"a\")", "a b c\nheo\nab\n3\n");
    expect(
        "puts \"abc\".succ, \"az\".succ, \"zz\".succ, \"a9\".succ",
        "abd\nba\naaa\nb0\n",
    );
    expect("puts \"Hello\".start_with?(\"He\"), \"Hello\".index(\"l\").inspect, \"Hello\".index(\"z\").inspect, \"Hello\".chars.inspect", "true\n2\nnil\n[\"H\", \"e\", \"l\", \"l\", \"o\"]\n");
    expect(
        "p \"a\\tb\", :sym, :\"with space\", 'single', \"quote\\\"d\"",
        "\"a\\tb\"\n:sym\n:\"with space\"\n\"single\"\n\"quote\\\"d\"\n",
    );
    expect("s = String.build do |b|\n  b << \"x\" << \"y\"\n  3.times { |i| b << i.to_s }\nend\nputs s", "xy012\n");
    expect(
        "puts \"line1\\nline2\".lines.inspect, \"  pad  \".strip + \"|\", \"abc\\n\".chomp",
        "[\"line1\\n\", \"line2\"]\npad|\nabc\n",
    );
    expect(
        "puts \"CamelCase\".downcase.capitalize, \"abc\" <=> \"abd\", \"b\" > \"a\"",
        "Camelcase\n-1\ntrue\n",
    );
}

#[test]
fn regexps() {
    expect(
        "puts \"foo123bar\" =~ /\\d+/, (\"abc\" =~ /x/).inspect",
        "3\nnil\n",
    );
    expect("m = \"John Smith\".match(/(\\w+) (\\w+)/)\nif m\n  puts m[1], m[2], m.pre_match.inspect, m.captures.inspect\nend", "John\nSmith\n\"\"\n[\"John\", \"Smith\"]\n");
    expect(
        "puts \"a1b22c333\".scan(/\\d+/).inspect, \"a1b2\".scan(/([a-z])(\\d)/).inspect",
        "[\"1\", \"22\", \"333\"]\n[[\"a\", \"1\"], [\"b\", \"2\"]]\n",
    );
    expect("puts \"hello world\".gsub(/o/, \"0\"), \"hello\".sub(/l/, \"L\"), \"2024-01-02\".gsub(/(\\d+)-(\\d+)-(\\d+)/, \"\\\\3/\\\\2/\\\\1\")", "hell0 w0rld\nheLlo\n02/01/2024\n");
    expect(
        "puts \"a, b;c\".split(/[,;]\\s*/).inspect, \"ABC\".match?(/b/i), \"x\".match?(/y/)",
        "[\"a\", \"b\", \"c\"]\ntrue\nfalse\n",
    );
    expect("case \"hello42\"\nwhen /^\\d+$/ then puts \"digits\"\nwhen /\\d/ then puts \"has digit\"\nend", "has digit\n");
}

#[test]
fn control_flow() {
    expect("i = 0\nwhile i < 5\n  i += 1\n  next if i == 2\n  break if i == 4\n  puts i\nend\nputs \"done #{i}\"", "1\n3\ndone 4\n");
    expect("r = loop do\n  break 42\nend\nputs r", "42\n");
    expect("i = 10\nuntil i <= 7\n  i -= 1\nend\nputs i", "7\n");
    expect("i = 0\nbegin\n  i += 1\nend while i < 0\nputs i", "1\n");
    expect(
        "x = if false then 1 elsif nil then 2 else 3 end\nputs x",
        "3\n",
    );
    expect(
        "puts(true ? \"y\" : \"n\")\nputs 1 if true\nputs 2 unless true\nputs 3 unless false",
        "y\n1\n3\n",
    );
    expect("def f(n: Int) -> String\n  case n\n  when 1, 2 then \"small\"\n  when 3..5 then \"medium\"\n  when Int then \"big\"\n  end\nend\nputs f(1), f(4), f(9)", "small\nmedium\nbig\n");
    expect(
        "v: Int | String = 5\ncase v\nwhen String then puts \"s\"\nwhen Int then puts \"i\"\nend",
        "i\n",
    );
    expect(
        "puts [1, 2, 3].each { |x| break x * 10 if x == 2 }.inspect",
        "20\n",
    );
    expect(
        "r = [1, 2, 3].map { |x| next 0 if x == 2; x }\nputs r.inspect",
        "[1, 0, 3]\n",
    );
    expect("def find_first(xs: Array[Int]) -> Int?\n  xs.each { |x| return x if x > 1 }\n  nil\nend\nputs find_first([1, 2, 3]).inspect, find_first([0]).inspect", "2\nnil\n");
    expect("def outer -> Int\n  [1, 2].each do |x|\n    [3, 4].each do |y|\n      return x * y if y == 4\n    end\n  end\n  0\nend\nputs outer", "4\n");
    expect("a = 1\nb = 2\na, b = b, a\nputs a, b\nx, *ys = [1, 2, 3]\nputs x, ys.inspect\n*init, last = [1, 2, 3]\nputs init.inspect, last", "2\n1\n1\n[2, 3]\n[1, 2]\n3\n");
    expect(
        "def pair -> [Int, String] = [1, \"one\"]\nn, s = pair\nputs n + 1, s.upcase",
        "2\nONE\n",
    );
    expect("(1..3).each { |i| puts i }\n(1...3).each { |i| puts i }\n1.step(10, 4) { |i| puts i }\n3.downto(1) { |i| print i }\nputs", "1\n2\n3\n1\n2\n1\n5\n9\n321\n");
}

#[test]
fn exceptions() {
    expect("begin\n  raise ArgumentError, \"bad\"\nrescue TypeError\n  puts \"type\"\nrescue ArgumentError => e\n  puts \"arg: #{e.message}\"\nensure\n  puts \"ensure\"\nend", "arg: bad\nensure\n");
    expect("class MyError < StandardError\n  @code: Int\n  attr_reader :code\n  def initialize(message: String, @code: Int)\n    super(message)\n  end\nend\nbegin\n  raise MyError.new(\"boom\", 7)\nrescue MyError => e\n  puts e.message, e.code, e.class.name, e.is_a?(StandardError)\nend", "boom\n7\nMyError\ntrue\n");
    expect("tries = 0\nbegin\n  tries += 1\n  raise \"fail\" if tries < 3\n  puts \"ok after #{tries}\"\nrescue\n  retry\nend", "ok after 3\n");
    expect("x = begin\n  Integer(\"zz\")\nrescue ArgumentError\n  -1\nend\nputs x\ny = Integer(\"zz\") rescue -2\nputs y", "-1\n-2\n");
    expect(
        "def f -> Int\n  return 1\nensure\n  puts \"cleanup\"\nend\nputs f",
        "cleanup\n1\n",
    );
    expect("begin\n  puts \"body\"\nrescue\n  puts \"never\"\nelse\n  puts \"else\"\nensure\n  puts \"ensure\"\nend", "body\nelse\nensure\n");
    expect("def risky -> Nil\n  raise KeyError, \"k\"\nend\nbegin\n  risky\nrescue IndexError => e\n  puts \"caught #{e.class.name}: #{e.message}\"\nend", "caught KeyError: k\n");
    let (code, out) = run("puts \"before\"\nraise \"unhandled\"\nputs \"after\"", &[]);
    assert_eq!(code, 1);
    assert_eq!(out, "before\n");
    let (code, _) = run("exit(3)", &[]);
    assert_eq!(code, 3);
    expect("r = [1, 2, 3].first(2)\nbegin\n  puts [1][5]\nrescue IndexError => e\n  puts \"index: #{e.message}\"\nend\nbegin\n  { a: 1 }[:b]\nrescue KeyError => e\n  puts \"key: #{e.message}\"\nend\nputs r.inspect", "index: index 5 out of bounds (size 1)\nkey: key not found: :b\n[1, 2]\n");
}

#[test]
fn classes() {
    expect("class Animal\n  @name: String\n  attr_reader :name\n  def initialize(@name: String); end\n  def speak -> String = \"...\"\n  def to_s -> String = \"#{self.class.name}(#{name}): #{speak}\"\nend\nclass Dog < Animal\n  override def speak -> String = \"Woof\"\nend\nclass Puppy < Dog\n  override def speak -> String = super + \"!\"\nend\nputs Animal.new(\"a\"), Dog.new(\"d\"), Puppy.new(\"p\")\nanimals: Array[Animal] = [Dog.new(\"x\"), Puppy.new(\"y\")]\nanimals.each { |a| puts a.speak }", "Animal(a): ...\nDog(d): Woof\nPuppy(p): Woof!\nWoof\nWoof!\n");
    expect("class Counter\n  var @n: Int = 0\n  attr_accessor :n\n  def bump -> Counter\n    @n += 1\n    self\n  end\nend\nc = Counter.new\nc.bump.bump\nc.n += 10\nputs c.n", "12\n");
    expect("class V\n  @x: Int\n  @y: Int\n  attr_reader :x, :y\n  def initialize(@x: Int, @y: Int); end\n  def +(o: V) -> V = V.new(x + o.x, y + o.y)\n  def ==(o: Object) -> Bool\n    case o\n    in V then x == o.x && y == o.y\n    else false\n    end\n  end\n  def -@ -> V = V.new(-x, -y)\n  def [](i: Int) -> Int = i == 0 ? x : y\n  def to_s -> String = \"(#{x}, #{y})\"\nend\na = V.new(1, 2)\nputs a + a, -a, a[1], a == V.new(1, 2), a == V.new(0, 0), a != V.new(1, 2)", "(2, 4)\n(-1, -2)\n2\ntrue\nfalse\nfalse\n");
    expect("class Stack[T]\n  @items: Array[T]\n  def initialize(items: Array[T] = [])\n    @items = items\n  end\n  def push(x: T) -> Stack[T] = Stack[T].new(@items.push(x))\n  def peek -> T? = @items.last\n  def size -> Int = @items.size\nend\ns = Stack[Int].new.push(1).push(2)\nputs s.size, s.peek.inspect, Stack[String].new.peek.inspect", "2\n2\nnil\n");
    expect("abstract class Shape\n  abstract def area -> Float\n  def describe -> String = \"#{self.class.name} #{area}\"\nend\nclass Sq < Shape\n  @s: Float\n  def initialize(@s: Float); end\n  override def area -> Float = @s * @s\nend\nputs Sq.new(3.0).describe", "Sq 9.0\n");
    expect("class A\n  def self.create(n: Int) -> A = new(n)\n  @n: Int\n  def initialize(@n: Int); end\n  def n -> Int = @n\n  private def secret -> Int = 42\n  def reveal -> Int = secret\nend\nputs A.create(5).n, A.new(1).reveal", "5\n42\n");
    expect("module Greeter\n  abstract def name -> String\n  def greet -> String = \"Hi, #{name}\"\nend\nclass P\n  include Greeter\n  def name -> String = \"Bob\"\nend\ndef welcome(g: Greeter) -> Nil\n  puts g.greet\nend\nwelcome(P.new)", "Hi, Bob\n");
    expect("class Node\n  @val: Int\n  @next: Node?\n  attr_reader :val, :next\n  def initialize(@val: Int, @next: Node? = nil); end\n  def sum -> Int\n    n = self.next\n    n ? val + n.sum : val\n  end\nend\nputs Node.new(1, Node.new(2, Node.new(3))).sum", "6\n");
}

#[test]
fn data_and_enums() {
    expect("data P = (x: Int, y: Int = 0)\np = P.new(1)\nq = p.with(y: 5)\nputs p, q.inspect, p == P.new(1, 0), p == q, p.to_h.inspect\nputs P.new(x: 2, y: 3).x", "P(x: 1, y: 0)\nP(x: 1, y: 5)\ntrue\nfalse\n{x: 1, y: 0}\n2\n");
    expect("data P(x: Int, y: Int)\n  def norm -> Int = x * x + y * y\nend\nh = { P.new(1, 2) => \"a\" }\nputs h[P.new(1, 2)], P.new(3, 4).norm, [P.new(1, 1), P.new(1, 1)].uniq.size", "a\n25\n1\n");
    expect("enum Color\n  Red\n  | Green\n  | Rgb(r: Int, g: Int, b: Int)\n  def to_s -> String\n    case self\n    in Red then \"red\"\n    in Green then \"green\"\n    in Rgb(r:, g:, b:) then \"rgb(#{r},#{g},#{b})\"\n    end\n  end\nend\nputs Color::Red, Color::Rgb.new(1, 2, 3), Color::Red == Color::Red, Color::Red == Color::Green\nputs Color::Rgb.new(1, 2, 3) == Color::Rgb.new(1, 2, 3), Color::Rgb.new(1, 2, 3).inspect", "red\nrgb(1,2,3)\ntrue\nfalse\ntrue\nColor::Rgb(r: 1, g: 2, b: 3)\n");
    expect("r: Result[Int, String] = Result::Ok.new(2)\nputs r.ok?, r.unwrap, r.map { |x| x * 10 }.unwrap, r.unwrap_or(0)\ne: Result[Int, String] = Result::Err.new(\"no\")\nputs e.err?, e.unwrap_or(9), e.map { |x| x + 1 }.err?\nbegin\n  e.unwrap\nrescue RuntimeError => ex\n  puts ex.message\nend", "true\n2\n20\n2\ntrue\n9\ntrue\nunwrap called on an Err: no\n");
    expect("enum Color = Red | Green | Blue\nenum Suit =\n  | Hearts\n  | Spades\nenum Pair[T] = Two(a: T, b: T)\n  | Empty\nenum Shape\n  | Circle(radius: Float)\n  | Point\n  def area -> Float\n    case self\n    in Circle(radius:) then 3.0 * radius * radius\n    in Point then 0.0\n    end\n  end\nend\np Color::Red, Suit::Spades, Pair::Two.new(1, 2), Shape::Circle.new(2.0).area, Shape::Point.area\ncase Color::Green\nin Color::Red then puts \"r\"\nelse puts \"gb\"\nend", "Color::Red\nSuit::Spades\nPair::Two(a: 1, b: 2)\n12.0\n0.0\ngb\n");
    expect("module Named\n  abstract def label -> String\n  def greeting -> String = \"I am #{label}\"\nend\nmodule Counting\n  abstract def count -> Int\n  def twice -> Int = count * 2\nend\nclass Thing\n  extend Named\n  extend Counting\n  def self.label -> String = \"Thing\"\n  def self.count -> Int = 21\nend\nclass Sub < Thing\n  def self.label -> String = \"Sub\"\nend\nputs Thing.greeting, Thing.twice, Sub.greeting, Sub.twice", "I am Thing\n42\nI am Sub\n42\n");
    expect("def pairs(n: Int, v: Int) -> Array[[Int, Int]]\n  for i in 0...n,\n      j in 0...n when i + j == v then\n    [i, j]\n  end\nend\np pairs(6, 6)\np for x in [1, 2, 3, 4] when x.even? then x * 10 end\np for k, v in { a: 1, b: 2 } then \"#{k}=#{v}\" end\np for xs in [[1, 2], [3]], x in xs then x + 100 end\ndef find(id: Int) -> Result[String, String] = id > 0 ? Result::Ok[String, String].new(\"u#{id}\") : Result::Err[String, String].new(\"bad\")\np for u in find(1), n in Result::Ok[Int, String].new(u.size) then [u, n] end\np for u in find(0), n in Result::Ok[Int, String].new(u.size) then [u, n] end\np (for s in [\"a\", \"bb\"] then s.size end).sum", "[[1, 5], [2, 4], [3, 3], [4, 2], [5, 1]]\n[20, 40]\n[\"a=1\", \"b=2\"]\n[101, 102, 103]\nResult::Ok(value: [\"u1\", 2])\nResult::Err(error: \"bad\")\n3\n");
    expect("enum Tree\n  Leaf\n  | Node(left: Tree, value: Int, right: Tree)\n  def sum -> Int\n    case self\n    in Leaf then 0\n    in Node(left:, value:, right:) then left.sum + value + right.sum\n    end\n  end\nend\nt = Tree::Node.new(Tree::Node.new(Tree::Leaf, 1, Tree::Leaf), 2, Tree::Leaf)\nputs t.sum", "3\n");
}

#[test]
fn patterns() {
    expect("def f(v: Object) -> String\n  case v\n  in Int => n if n > 100 then \"big #{n}\"\n  in Int | Float => n then \"num #{n}\"\n  in String => s then \"str #{s}\"\n  in [x, *rest] then \"arr #{x} + #{rest.size}\"\n  in {name: String => name, age:} then \"#{name} #{age}\"\n  in nil then \"nil\"\n  else \"other\"\n  end\nend\nputs f(5), f(500), f(1.5), f(\"s\"), f([1, 2, 3]), f({name: \"A\", age: 3}), f(nil), f(:sym)", "num 5\nbig 500\nnum 1.5\nstr s\narr 1 + 2\nA 3\nnil\nother\n");
    expect("expected = 3\ncase 3\nin ^expected then puts \"pinned\"\nend\ncase [1, [2, 3]]\nin [Int => a, [Int => b, Int => c]] then puts a + b + c\nend\ncase [1, 2, 3, 4, 5]\nin [*, 3, *post] then puts post.inspect\nend", "pinned\n6\n[4, 5]\n");
    expect("config = {host: \"h\", port: 80}\nconfig => {host:, port:}\nputs host, port\nif config in {host: String}\n  puts \"has host\"\nend\nputs(5 in Int)\nbegin\n  5 => String\nrescue NoMatchingPatternError => e\n  puts \"no match\"\nend", "h\n80\nhas host\ntrue\nno match\n");
    expect("case [1, \"a\"]\nin [Int => n, String => s] then puts \"#{n}#{s}\"\nend\ncase {x: 1, y: 2, z: 3}\nin {x:, **rest} then puts x, rest.inspect\nend", "1a\n1\n{y: 2, z: 3}\n");
    expect("case 7\nin 1..5 then puts \"low\"\nin 6.. then puts \"high\"\nend\ncase \"b\"\nin \"a\" | \"b\" then puts \"ab\"\nend", "high\nab\n");
}

#[test]
fn collections() {
    expect("xs = [3, 1, 2]\nputs xs.sort.inspect, xs.max, xs.min, xs.sum, xs.reverse.inspect, xs.include?(2), xs.index(1).inspect", "[1, 2, 3]\n3\n1\n6\n[2, 1, 3]\ntrue\n1\n");
    expect("xs = [1, 2, 3, 4, 5, 6]\nputs xs.select(&:even?).inspect, xs.reject(&:even?).inspect, xs.map { |x| x * x }.inspect, xs.reduce(0) { |a, b| a + b }", "[2, 4, 6]\n[1, 3, 5]\n[1, 4, 9, 16, 25, 36]\n21\n");
    expect("xs = [1, 2, 3, 4, 5, 6]\nxs.each_slice(4) { |s| puts s.inspect }\nputs xs.partition(&:even?).inspect, xs.group_by { |x| x % 3 }.inspect, xs.take_while { |x| x < 3 }.inspect, xs.drop(4).inspect", "[1, 2, 3, 4]\n[5, 6]\n[[2, 4, 6], [1, 3, 5]]\n{1 => [1, 4], 2 => [2, 5], 0 => [3, 6]}\n[1, 2]\n[5, 6]\n");
    expect("words = %w[apple banana cherry]\nputs words.sort_by { |w| -w.size }.inspect, words.max_by(&:size), words.min_by(&:size), words.map(&:size).inspect, words.join(\", \"), words.first(2).inspect, words.last", "[\"banana\", \"cherry\", \"apple\"]\nbanana\napple\n[5, 6, 6]\napple, banana, cherry\n[\"apple\", \"banana\"]\ncherry\n");
    expect("puts [1, 2].zip([3, 4]).inspect, [[1, 2], [3]].flat_map { |a| a }.inspect, [1, nil, 2].compact.inspect, [1, 2, 2, 3].tally.inspect", "[[1, 3], [2, 4]]\n[1, 2, 3]\n[1, 2]\n{1 => 1, 2 => 2, 3 => 1}\n");
    expect("[\"a\", \"b\"].each_with_index { |x, i| puts \"#{i}:#{x}\" }\nputs [1, 2, 3].filter_map { |x| x * 2 if x.odd? }.inspect, [1, 2, 3].find { |x| x > 1 }.inspect, [1, 2].any? { |x| x > 1 }, [1, 2].all? { |x| x > 1 }, [].any?, [1, 2, 3].count(&:odd?)", "0:a\n1:b\n[2, 6]\n2\ntrue\nfalse\nfalse\n2\n");
    expect("h = { a: 1, b: 2 }\nh2 = h.put(:c, 3).delete(:a)\nputs h.inspect, h2.inspect, h.keys.inspect, h.values.sum, h.key?(:a), h[:b], h.fetch(:z, 0), h.fetch(:z) { |k| k.to_s.size }, h.merge({ b: 20 }).inspect", "{a: 1, b: 2}\n{b: 2, c: 3}\n[:a, :b]\n3\ntrue\n2\n0\n1\n{a: 1, b: 20}\n");
    expect("h = { \"x\" => 1, \"y\" => 2 }\nputs h.map { |k, v| \"#{k}=#{v}\" }.join(\"&\"), h.select { |k, v| v > 1 }.inspect, h.transform_values { |v| v * 10 }.inspect, h.to_a.inspect, h.min_by { |k, v| v }.inspect, h.sort_by { |k, v| -v }.inspect", "x=1&y=2\n{\"y\" => 2}\n{\"x\" => 10, \"y\" => 20}\n[[\"x\", 1], [\"y\", 2]]\n[\"x\", 1]\n[[\"y\", 2], [\"x\", 1]]\n");
    expect("h = { a: 1 }.merge({ a: 2, b: 3 }) { |k, old, new| old + new }\nputs h.inspect\ncounts = %w[a b a].reduce({}) { |acc, w| acc.update(w) { |n| (n || 0) + 1 } }\nputs counts.inspect\nh.each_pair { |k, v| puts \"#{k}#{v}\" }", "{a: 3, b: 3}\n{\"a\" => 2, \"b\" => 1}\na3\nb3\n");
    expect("s = Set[1, 2, 2, 3]\nputs s.size, s.include?(2), s.add(4).size, (s | Set[9]).to_a.inspect, (s & Set[2, 3, 7]).to_a.inspect, (s - Set[1]).to_a.inspect, [1, 1, 2].to_set.inspect", "3\ntrue\n4\n[1, 2, 3, 9]\n[2, 3]\n[2, 3]\nSet[1, 2]\n");
    expect("puts (1..5).to_a.inspect, (1..5).sum, (1...5).size\n(1..10).step(3) { |x| print x, \" \" }\nputs\nputs (1..3).include?(2), (1..3).cover?(5), (\"a\"..\"d\").to_a.inspect, (1..Float::INFINITY).first(3).inspect", "[1, 2, 3, 4, 5]\n15\n4\n1 4 7 10 \ntrue\nfalse\n[\"a\", \"b\", \"c\", \"d\"]\n[1, 2, 3]\n");
    expect("b = Array::Builder[Int].new\nb << 3 << 1 << 2\nb.sort!\nb[0] = 10\nb.map! { |x| x + 1 }\nputs b.to_a.inspect, b.size", "[11, 3, 4]\n0\n");
    expect("xs = [1, 2, 3]\nys = xs.push(4)\nputs xs.inspect, ys.inspect, xs.set(0, 9).inspect, xs.inspect, xs.insert(1, 7).inspect, xs.delete_at(0).inspect, (xs + [4]).inspect, (xs - [2]).inspect, (xs * 2).inspect", "[1, 2, 3]\n[1, 2, 3, 4]\n[9, 2, 3]\n[1, 2, 3]\n[1, 7, 2, 3]\n[2, 3]\n[1, 2, 3, 4]\n[1, 3]\n[1, 2, 3, 1, 2, 3]\n");
    expect("acc: Array[Int] = []\n1000.times { |i| acc = acc.push(i) }\nputs acc.size, acc[999], acc.first.inspect\nm: Hash[Int, Int] = {}\n100.times { |i| m = m.put(i, i * i) }\nputs m.size, m[50]", "1000\n999\n0\n100\n2500\n");
    expect("e = 3.times\nputs e.map { |i| i * 2 }.inspect, e.next, e.next, 5.times.select(&:even?).inspect", "[0, 2, 4]\n0\n1\n[0, 2, 4]\n");
}

#[test]
fn procs_and_blocks() {
    expect(
        "add = ->(a: Int, b: Int) { a + b }\nputs add.call(1, 2), add.(3, 4), add.arity",
        "3\n7\n2\n",
    );
    expect("def make_counter -> () -> Int\n  n = 0\n  -> { n += 1 }\nend\nc = make_counter\nc.call\nputs c.call, make_counter.call", "2\n1\n");
    expect("def twice(&block: (Int) -> Int) -> Int = yield(yield(1))\nputs twice { |x| x * 3 }\ndef apply(f: (Int) -> Int, x: Int) -> Int = f.call(x)\nputs apply(->(x: Int) { x + 1 }, 41)\nsq = ->(x: Int) { x * x }\nputs [1, 2, 3].map(&sq).inspect", "9\n42\n[1, 4, 9]\n");
    expect("def each_pair_sum(&block: (Int, Int) -> Nil) -> Nil\n  yield 1, 2\n  yield 3, 4\nend\neach_pair_sum { |a, b| puts a + b }\nputs [[1, 2], [3, 4]].map { |a, b| a * b }.inspect", "3\n7\n[2, 12]\n");
    expect("xs = [\"b\", \"a\"]\nputs xs.map(&:upcase).inspect, xs.sort.map(&:to_sym).inspect\nup = \"x\".:upcase\nputs up.call", "[\"B\", \"A\"]\n[:a, :b]\nX\n");
    expect("def run_it(&block: () -> Int) -> Int\n  v = yield\n  v * 2\nend\nputs run_it { 21 }\ndef with_default(x: Int, y: Int = x * 2, *rest: Int, flag: Bool = false, **opts: Int) -> String\n  \"#{x} #{y} #{rest.inspect} #{flag} #{opts.inspect}\"\nend\nputs with_default(1), with_default(1, 5, 7, 8, flag: true, extra: 9)", "42\n1 2 [] false {}\n1 5 [7, 8] true {extra: 9}\n");
    expect("total = 0\n[1, 2, 3].each { |x| total += x }\nputs total\nl = ->(x: Int) { return x * 2 }\nputs l.call(4)", "6\n8\n");
}

#[test]
fn extensions_and_misc() {
    expect("module Shout\n  extension String\n    def shout -> String = upcase + \"!\"\n  end\n  extension Int\n    def double -> Int = self * 2\n  end\nend\nusing Shout\nputs \"hi\".shout, 4.double", "HI!\n8\n");
    expect("x: Object = 5\nputs x.is_a?(Int), x.is_a?(String), x.as(Int) + 1, x.as?(String).inspect, 5.respond_to?(:even?), 5.respond_to?(:nope)\nbegin\n  x.as(String)\nrescue TypeError => e\n  puts \"cast failed\"\nend", "true\nfalse\n6\nnil\ntrue\nfalse\ncast failed\n");
    expect("puts nil.to_s.inspect, nil.inspect, true & false, 1.class.name, \"s\".class.name, [1].class.name, nil.class.name, 1.5.class.name, :s.class.name", "\"\"\nnil\nfalse\nInt\nString\nArray\nNil\nFloat\nSymbol\n");
    expect("def fib(n: Int) -> Int = n < 2 ? n : fib(n - 1) + fib(n - 2)\nputs fib(20)\ndef depth(n: Int) -> Int = n == 0 ? 0 : 1 + depth(n - 1)\nputs depth(2000)", "6765\n2000\n");
    expect(
        "a = [1, 2]\nb = a\na = a.push(3)\nputs a.inspect, b.inspect",
        "[1, 2, 3]\n[1, 2]\n",
    );
    expect("puts ARGV.inspect", "[]\n");
    let (code, out) = run("puts ARGV.inspect, ARGV.size", &["x", "y"]);
    assert_eq!((code, out.as_str()), (0, "[\"x\", \"y\"]\n2\n"));
    expect("x = 5\ny = x.then { |v| v + 1 }.tap { |v| puts \"tapped #{v}\" }\nputs y\nputs __method__.inspect\ndef m -> String = __method__.to_s\nputs m", "tapped 6\n6\nnil\nm\n");
    expect(
        "puts [1, [2, [3, nil]], \"s\", :sym, {k: [1]}, 1.5, 2..3, Set[1]].inspect",
        "[1, [2, [3, nil]], \"s\", :sym, {k: [1]}, 1.5, 2..3, Set[1]]\n",
    );
    expect("STDOUT.puts \"to stdout\"\nSTDOUT.print \"a\", \"b\\n\"\nputs 1.second.to_s, 500.ms.to_s, (1.5.seconds + 500.ms).to_ms", "to stdout\nab\n1s\n500ms\n2000\n");
}

#[test]
fn concurrency() {
    expect("ch = Channel[Int].new\nTask.scope do |s|\n  s.spawn { 3.times { |i| ch.send(i) }; ch.close }\n  ch.each { |v| puts v }\nend\nputs \"done\"", "0\n1\n2\ndone\n");
    expect("ch = Channel[String].new(capacity: 2)\nt = spawn { ch.send(\"a\"); ch.send(\"b\"); \"sent\" }\nputs ch.receive, ch.receive, t.await", "a\nb\nsent\n");
    expect("results = Task.scope do |s|\n  ts = [3, 1, 2].map { |n| s.spawn { Task.sleep((n * 5).ms); n } }\n  ts.map(&:await)\nend\nputs results.inspect", "[3, 1, 2]\n");
    expect("order = Atom[Array[Int]].new([])\nTask.scope do |s|\n  s.spawn { Task.sleep(20.ms); order.update { |o| o.push(2) } }\n  s.spawn { Task.sleep(5.ms); order.update { |o| o.push(1) } }\nend\nputs order.value.inspect", "[1, 2]\n");
    expect("n = Atom.new(0)\nTask.scope do |s|\n  100.times { s.spawn { n.update { |v| v + 1 } } }\nend\nputs n.value", "100\n");
    expect("begin\n  Task.scope do |s|\n    s.spawn { Task.sleep(1.second); puts \"never\" }\n    s.spawn { raise ArgumentError, \"child failed\" }\n  end\nrescue ArgumentError => e\n  puts \"scope raised: #{e.message}\"\nend", "scope raised: child failed\n");
    expect("begin\n  Task.timeout(10.ms) { Task.sleep(1.second) }\nrescue Task::Timeout\n  puts \"timed out\"\nend\nputs Task.timeout(1.second) { 5 }", "timed out\n5\n");
    expect("a = Channel[Int].new\nb = Channel[Int].new\nspawn { Task.sleep(5.ms); b.send(2) }\nselect do |s|\n  s.receive(a) { |v| puts \"a #{v}\" }\n  s.receive(b) { |v| puts \"b #{v}\" }\nend\nselect do |s|\n  s.receive(a) { |v| puts \"a #{v}\" }\n  s.after(5.ms) { puts \"timeout\" }\nend\nselect do |s|\n  s.receive(a) { |v| puts \"a #{v}\" }\n  s.default { puts \"default\" }\nend", "b 2\ntimeout\ndefault\n");
    expect("jobs = Channel[Int].new(capacity: 10)\ndone = Channel[Int].new(capacity: 10)\nTask.scope do |s|\n  2.times { |w| s.spawn { jobs.each { |j| done.send(j * 10) } } }\n  5.times { |j| jobs.send(j) }\n  jobs.close\nend\ndone.close\nputs done.to_a.sort.inspect", "[0, 10, 20, 30, 40]\n");
    let (code, out) = run("ch = Channel[Int].new\nputs \"waiting\"\nch.receive", &[]);
    assert_eq!(code, 1);
    assert_eq!(out, "waiting\n");
    expect("t = spawn { Task.sleep(1.second); 1 }\nt.cancel\nbegin\n  t.await\nrescue Task::Cancelled\n  puts \"cancelled\"\nend", "cancelled\n");
    expect("ch = Channel[Int].new\nt = spawn { ch.receive }\nTask.yield\nch.send(7)\nputs t.await\nputs ch.closed?, Task.current.done?", "7\nfalse\nfalse\n");
    expect("ch = Channel[Int].new(capacity: 1)\nch.send(1)\nputs ch.try_send(2), ch.size, ch.try_receive.inspect, ch.try_receive.inspect\nch.close\nputs ch.receive?.inspect\nbegin\n  ch.send(3)\nrescue Channel::Closed\n  puts \"closed\"\nend", "false\n1\n1\nnil\nnil\nclosed\n");
}
