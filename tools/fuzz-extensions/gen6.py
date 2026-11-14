#!/usr/bin/env python3
"""Random programs over an abstract class's requirement whose
implementation is not the first method of the name by arity (#536 step
3's S3, item (b)): `abstract def m(x: String) -> String` in `A` (generic
or not), and a concrete class whose first `m` is an overload of another
parameter type, with the implementation in (i) the class's own later
overload, (ii) one or two modules it includes, (iii) a class between it
and the abstract class, or (iv) a top-level extension's module of it; a
subclass may override it. Called through the abstract type (a dynamic
call: `find_override`), by name, and over an array. Prints a .qz program
for a seed."""
import random, sys


def gen(seed):
    r = random.Random(seed)
    L = []
    w = L.append
    generic = r.random() < 0.3
    ap = "[T]" if generic else ""
    aa = "[Int]" if generic else ""
    for k in ("N1", "N2", "N3"):
        w(f"module {k}")
        if r.random() < 0.7:
            w(f'  def m(x: String) -> String = "{k.lower()}:" + x')
        w("end")
    if generic:
        w("class Base[T]")
        w("  def initialize; end")
        w("end")
        w("abstract class A[T] < Base[T]")
    else:
        w("abstract class A")
    w("  abstract def m(x: String) -> String")
    w("end")
    parent = f"A{aa}"
    # (iii) a class between, implementing it, the subclass adding an overload
    if r.random() < 0.3:
        w(f"abstract class B < {parent}")
        if r.random() < 0.8:
            w('  def m(x: String) -> String = "b:" + x')
        w("end")
        parent = "B"
    w(f"class C < {parent}")
    incs = [k for k in ("N1", "N2") if r.random() < 0.5]
    r.shuffle(incs)
    for k in incs:
        w(f"  include {k}")
    w("  def initialize; end")
    w('  def m(x: Int) -> String = "int"')
    if r.random() < 0.35:
        w('  def m(x: String) -> String = "c:" + x')
    w("end")
    if r.random() < 0.3:
        w("extension C")
        w("  include N3")
        w("end")
    sub = r.random() < 0.4
    if sub:
        w("class D < C")
        w("  def initialize; super; end")
        if r.random() < 0.5:
            w('  def m(x: String) -> String = "d:" + x')
        if r.random() < 0.3:
            w('  def m(x: Float) -> String = "float"')
        w("end")
    w(f"def f(a: A{aa}) -> String = a.m(\"s\")")
    w("puts f(C.new)")
    w('puts C.new.m("t"), C.new.m(1)')
    if sub:
        w("puts f(D.new)")
        w(f"xs: Array[A{aa}] = [C.new, D.new]")
        w(f'puts xs.map {{ |a: A{aa}| a.m("v") }}.join(",")')
    return "\n".join(L) + "\n"


if __name__ == "__main__":
    sys.stdout.write(gen(int(sys.argv[1])))
