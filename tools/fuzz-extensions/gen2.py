#!/usr/bin/env python3
"""Second generator: two-hop bringers; N does not always include M."""
import random, sys

def gen(seed):
    r = random.Random(seed * 7919 + 13)
    param = r.random() < 0.6
    sig = "(x: String)" if param else ""
    arg = '("s")' if param else ""
    def body(tag, kind):
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
        ks = ["ok", "ok", "int", "int"]
        if param:
            ks += ["overload", "overload", "overload", "wide"]
        return body(tag, r.choice(ks))
    L = []
    w = L.append
    m_abs = r.random() < 0.6
    w("module M")
    w(f"  abstract def m{sig} -> String" if m_abs else f'  def m{sig} -> String = "M"')
    w(f'  def mm -> String = m{arg} + "!"')
    w("end")
    n_inc = r.random() < 0.3
    w("module N")
    if n_inc: w("  include M")
    b = pick("N", 0.7)
    if b: w(b)
    w("end")
    w("module E")
    b = pick("E", 0.7)
    if b: w(b)
    w("end")
    mods = ["M", "N", "E"]
    classes = ["B", "K", "S"]
    sup = {"B": None, "K": "B", "S": "K"}
    own_inc = {}
    for c in classes:
        w(f"class {c}" + (f" < {sup[c]}" if sup[c] else ""))
        incs = [m for m in mods if r.random() < 0.08]
        own_inc[c] = incs
        for i in incs:
            w(f"  include {i}")
        w("  def initialize; end")
        b = pick(c, 0.6)
        if b: w(b)
        w("end")
    nx = r.randint(2, 4)
    exts = []
    for i in range(nx):
        target = r.choice(["B", "K", "K", "S", "N", "N", "E", "E"])
        scoped = r.random() < 0.4
        cand = [m for m in mods if m != target]
        incs = [m for m in r.sample(cand, len(cand)) if r.random() < 0.4]
        if not incs and r.random() < 0.7:
            incs = [r.choice(cand)]
        b = pick(f"x{i}", 0.55)
        exts.append((i, target, scoped, incs, b))
    # which modules bring M, through top-level extensions (active everywhere)
    brings = {"M": True, "N": n_inc, "E": False}
    changed = True
    while changed:
        changed = False
        for (i, target, scoped, incs, b) in exts:
            if target in ("N", "E") and not scoped and not brings[target] and any(brings[m] for m in incs):
                brings[target] = True
                changed = True
    below = {"B": ["B", "K", "S"], "K": ["K", "S"], "S": ["S"]}
    ups = []
    for (i, target, scoped, incs, b) in exts:
        ind = "  " if scoped else ""
        if scoped:
            w(f"module Sc{i}")
        w(f"{ind}extension {target}")
        for m in incs:
            w(f"{ind}  include {m}")
        if b: w(ind + b)
        w(f"{ind}end")
        if target in classes and any(brings[m] for m in incs):
            for c in below[target]:
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
