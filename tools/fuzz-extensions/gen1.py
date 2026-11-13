#!/usr/bin/env python3
"""Random programs over extension conformance; prints a .qz program for a seed."""
import random, sys

def gen(seed):
    r = random.Random(seed)
    param = r.random() < 0.5
    sig = "(x: String)" if param else ""
    arg = '("s")' if param else ""
    def body(tag, kind):
        # kind: ok | int | overload | wide
        if kind == "ok":
            return f'  def m{sig} -> String = "{tag}"'
        if kind == "int":
            return f'  def m{sig} -> Int = 1'
        if kind == "overload":
            return f'  def m(x: Int) -> String = "{tag}o#{{x + 1}}"'
        if kind == "wide":
            return f'  def m(x: Object) -> String = "{tag}w"'
    def pick(tag, p_none=0.5):
        if r.random() < p_none:
            return None
        ks = ["ok", "ok", "ok", "int"]
        if param:
            ks += ["overload", "overload", "wide"]
        return body(tag, r.choice(ks))
    L = []
    w = L.append
    m_abs = r.random() < 0.5
    w("module M")
    w(f"  abstract def m{sig} -> String" if m_abs else f'  def m{sig} -> String = "M"')
    w(f'  def mm -> String = m{arg} + "!"')
    w("end")
    w("module N")
    w("  include M")
    b = pick("N")
    if b: w(b)
    w("end")
    w("module E")
    b = pick("E", 0.3)
    if b: w(b)
    w("end")
    mods = ["M", "N", "E"]
    classes = ["B", "K", "S"]
    sup = {"B": None, "K": "B", "S": "K"}
    own_inc = {}
    for c in classes:
        w(f"class {c}" + (f" < {sup[c]}" if sup[c] else ""))
        incs = [m for m in mods if r.random() < 0.12]
        own_inc[c] = incs
        for i in incs:
            w(f"  include {i}")
        w("  def initialize; end")
        b = pick(c, 0.6)
        if b: w(b)
        w("end")
    nx = r.randint(1, 3)
    ups = []
    for i in range(nx):
        target = r.choice(["B", "K", "K", "S", "N", "E"])
        scoped = r.random() < 0.5
        incs = [m for m in r.sample(mods, 3) if r.random() < 0.45 and m != target]
        if not incs and r.random() < 0.6:
            incs = [r.choice([m for m in mods if m != target])]
        b = pick(f"x{i}", 0.5)
        ind = "  " if scoped else ""
        if scoped:
            w(f"module Sc{i}")
        w(f"{ind}extension {target}")
        for m in incs:
            w(f"{ind}  include {m}")
        if b: w(ind + b)
        w(f"{ind}end")
        # upcasts where this extension is active, for the classes it reaches
        brings = any(m in ("M", "N") for m in incs)
        below = {"B": ["B", "K", "S"], "K": ["K", "S"], "S": ["S"]}
        if target in classes:
            reach = below[target]
        else:
            reach = []
            for c in classes:
                if target in own_inc[c] or (target == "M" and "N" in own_inc[c]):
                    reach = below[c]
                    break
        for c in (reach if brings else []):
            name = f"up{i}{c}"
            if scoped:
                w(f"  def self.{name}(x: {c}) -> M = x")
                ups.append((f"Sc{i}.{name}", c))
            else:
                w(f"def {name}(x: {c}) -> M = x")
                ups.append((name, c))
        if scoped:
            w("end")
    w("def via(v: M) -> String = v.mm")
    for (f, c) in ups:
        w(f"puts \"{f} \" + via({f}({c}.new))")
    return "\n".join(L) + "\n"

if __name__ == "__main__":
    sys.stdout.write(gen(int(sys.argv[1])))
