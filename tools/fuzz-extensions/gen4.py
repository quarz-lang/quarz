#!/usr/bin/env python3
"""Random programs over an extension's class-side conformance (#504,
#669): a module's class method (abstract or with a body) and the class
methods that may be its witness: the extension's own, the target's own,
a module the target includes itself, the extension's includes (earlier,
later, brought), a superclass's and its includes; some of another result
type. Called through `Type[R]`, a `T <: R` parameter, an implicit call in
the module's own class method, and directly. Prints a .qz program for a
seed."""
import random, sys


def gen(seed):
    r = random.Random(seed)
    L = []
    w = L.append

    def label(tag, p_none):
        if r.random() < p_none:
            return None
        if r.random() < 0.15:
            return "  def self.label -> Int = 1"
        return f'  def self.label -> String = "{tag}"'

    r_abs = r.random() < 0.5
    w("module R")
    w("  abstract def self.label -> String" if r_abs else '  def self.label -> String = "R"')
    w('  def self.mm -> String = label + "!"')
    w("end")
    # O is a module a class may include itself (with or without R); N
    # includes R (the extension may include it to bring R) and may include
    # O too, so that its `label` overrides one the class has from its own
    # include (#680); E and L are plain modules (an earlier or later
    # include of the extension).
    w("module O")
    if r.random() < 0.3:
        w("  include R")
    b = label("O", 0.3)
    if b:
        w(b)
    w("end")
    w("module N")
    if r.random() < 0.7:
        w("  include R")
    if r.random() < 0.3:
        w("  include O")
    b = label("N", 0.4)
    if b:
        w(b)
    w("end")
    for m in ["E", "L"]:
        w(f"module {m}")
        b = label(m, 0.3)
        if b:
            w(b)
        w("end")
    classes = ["B", "K", "S"]
    sup = {"B": None, "K": "B", "S": "K"}
    for c in classes:
        w(f"class {c}" + (f" < {sup[c]}" if sup[c] else ""))
        if r.random() < 0.3:
            w("  include O")
        w("  def initialize; end")
        b = label(c, 0.6)
        if b:
            w(b)
        w("end")
    scoped = r.random() < 0.4
    target = r.choice(["B", "K", "K", "S"])
    # The extension's includes: R itself or N (which may bring R), with E
    # before and L after, in a random order.
    core = r.choice(["R", "R", "N", "N"])
    incs = [core]
    if r.random() < 0.4:
        incs.insert(0, "E")
    if r.random() < 0.4:
        incs.append("L")
    if r.random() < 0.2:
        r.shuffle(incs)
    ind = "  " if scoped else ""
    if scoped:
        w("module X")
    w(f"{ind}extension {target}")
    for i in incs:
        w(f"{ind}  include {i}")
    b = label("ext", 0.7)
    if b:
        w(ind + b)
    w(f"{ind}end")
    below = classes[classes.index(target):]
    pfx = "self." if scoped else ""
    w(f"{ind}def {pfx}via(t: Type[R]) -> String = t.label")
    w(f"{ind}def {pfx}gen[T <: R](t: Type[T]) -> String = t.label")
    w(f"{ind}def {pfx}imp(t: Type[R]) -> String = t.mm")
    if core == "N":
        w(f"{ind}def {pfx}vn(t: Type[N]) -> String = t.label.to_s")
    body = []
    for c in below:
        body.append(f'puts "{c} " + via({c}) + " " + gen({c}) + " " + imp({c})')
        if r.random() < 0.5:
            body.append(f'puts "{c} direct " + {c}.label.to_s')
        if core == "N":
            body.append(f'puts "{c} through N " + vn({c})')
    if scoped:
        w("  def self.run -> Void")
        for line in body:
            w("    " + line)
        w("  end")
        w("end")
        w("X.run")
    else:
        for line in body:
            w(line)
    return "\n".join(L) + "\n"


if __name__ == "__main__":
    sys.stdout.write(gen(int(sys.argv[1])))
