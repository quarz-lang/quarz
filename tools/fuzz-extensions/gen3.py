#!/usr/bin/env python3
"""Random programs aimed at the witness record's rarer rules (#536 step 3):
generic targets under different arguments, a subclass's top-level
extension method below a conformance, an own include whose only method of
the name has another result type, and two extensions' conformances to one
module up a chain. Prints a .qz program for a seed."""
import random, sys

def gen(seed):
    r = random.Random(seed)
    L = []
    w = L.append
    w("module M")
    w("  abstract def m -> Int")
    w('  def mm -> String = "#{m + 1}!"')
    w("end")
    # A generic base whose `m -> T` takes M's calls by type only for Int.
    w("class G[T]")
    w("  @v: T")
    w("  def initialize(@v: T); end")
    g_has_m = r.random() < 0.7
    if g_has_m:
        w("  def m -> T = @v")
    w("end")
    w("class A < G[Int]")
    w("  def initialize; super(1); end")
    if r.random() < 0.3:
        w("  def m -> Int = 10")
    w("end")
    w("class B < G[String]")
    w("  def initialize; super(\"s\"); end")
    if r.random() < 0.3:
        w("  def m -> Int = 20")
    w("end")
    w("class C < A")
    w("  def initialize; super; end")
    if r.random() < 0.4:
        w("  def m -> Int = 30")
    w("end")
    # An own include of M somewhere (rule 3).
    if r.random() < 0.4:
        own = r.choice(["A", "B", "C"])
        w(f"class D < {own}")
        w("  include M")
        w("  def initialize; super; end")
        w("end")
        classes = ["A", "B", "C", "D"]
    else:
        classes = ["A", "B", "C"]
    sup = {"A": "G", "B": "G", "C": "A", "D": None}
    ups = []
    n = r.randint(1, 3)
    chain = {"G": ["G", "A", "B", "C"], "A": ["A", "C"], "B": ["B"], "C": ["C"]}
    conformed = set()
    for i in range(n):
        target = r.choice(["G", "A", "B", "C"] if not g_has_m else ["A", "B", "C", "C"])
        scoped = r.random() < 0.5
        # (A second conformance on one chain only sometimes: the nearer
        # one's choice, rule 1; else a class conforms once, #517.)
        clash = any(c in conformed for c in chain[target]) or any(target in chain[k] for k in conformed)
        includes = r.random() < 0.8 and (not clash or r.random() < 0.3)
        # (An extension giving only `m`, below a conformance: rule 2.)
        own_m = r.random() < (0.7 if not includes else 0.35)
        if includes:
            conformed.add(target)
        gen_t = target == "G"
        head = f"extension {target}[T]" if gen_t else f"extension {target}"
        ind = "  " if scoped else ""
        if scoped:
            w(f"module Sc{i}")
        w(f"{ind}{head}")
        if includes:
            w(f"{ind}  include M")
        if own_m:
            # Sometimes of another result type: refused, or not a witness.
            if r.random() < 0.25:
                w(f'{ind}  def m -> String = "x{i}"')
            else:
                w(f"{ind}  def m -> Int = {100 + i}")
        w(f"{ind}end")
        if includes:
            reach = [c for c in classes if c == target or target == "G" or (target == "A" and c == "C")]
            for c in reach:
                name = f"up{i}{c}"
                if scoped:
                    w(f"  def self.{name}(x: {c}) -> M = x")
                    ups.append((f"Sc{i}.{name}", c))
                else:
                    w(f"def {name}(x: {c}) -> M = x")
                    ups.append((name, c))
        if scoped:
            w("end")
    if "D" in classes:
        w("def upD(x: D) -> M = x")
        ups.append(("upD", "D"))
    w("def via(v: M) -> String = v.mm")
    for (f, c) in ups:
        w(f"puts \"{f} \" + via({f}({c}.new))")
    return "\n".join(L) + "\n"

if __name__ == "__main__":
    sys.stdout.write(gen(int(sys.argv[1])))
