#!/usr/bin/env python3
"""Random programs over an abstract class's requirements (#686's review):
an abstract class `A < Base` declares `abstract def to_s`/`m`, implemented
further up (`Base`), by a module `Base` or the subclass includes, or by
the subclass itself; called by name (`puts`, interpolation, `inspect` of
an array, a call) and through the abstract type. Prints a .qz program
for a seed."""
import random, sys


def gen(seed):
    r = random.Random(seed)
    L = []
    w = L.append
    reqs = [q for q in ["to_s", "m"] if r.random() < 0.8] or ["m"]
    sig = {"to_s": "-> String", "m": "-> Int"}

    def impl(tag, q):
        if q == "to_s":
            return f'  def to_s -> String = "{tag}"'
        return f"  def m -> Int = {len(tag)}"

    w("module N")
    for q in reqs:
        if r.random() < 0.5:
            w(impl("n", q))
    w("end")
    w("class Base")
    if r.random() < 0.3:
        w("  include N")
    w("  def initialize; end")
    for q in reqs:
        if r.random() < 0.6:
            w(impl("base", q))
    w("end")
    w("abstract class A < Base")
    for q in reqs:
        w(f"  abstract def {q} {sig[q]}")
    w("end")
    w("class C < A")
    if r.random() < 0.3:
        w("  include N")
    w("  def initialize; super; end")
    for q in reqs:
        if r.random() < 0.3:
            w(impl("cc", q))
    w("end")
    w("c = C.new")
    w("a: A = c")
    if "to_s" in reqs:
        w("puts c")
        w('puts "#{c}"')
        w("puts a.to_s")
        w("puts [c].inspect")
    if "m" in reqs:
        w("puts c.m")
        w("puts a.m")
    return "\n".join(L) + "\n"


if __name__ == "__main__":
    sys.stdout.write(gen(int(sys.argv[1])))
