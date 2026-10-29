/-
QCore's abstract syntax (design §1.2, §1.3), v1: no closures (no lambda,
no named block, no `call`). A call takes no block or an anonymous one,
which runs only while the call does (`yield`).

A read of a local or of an immutable field carries the type the checker
gave it there (after narrowing): the interpreter checks the value it
reads against it, so that narrowing being sound is part of "a checked
program never gets stuck" (design §3).
-/

import QuarzCore.Types

namespace QuarzCore

inductive Expr where
  | nil
  | tru
  | fls
  | int (n : Int)
  | str (s : String)
  /-- A `Float` literal (its digits: the model needs no arithmetic). -/
  | flt (s : String)
  /-- A local's read, with the type the checker gave it there. -/
  | var (x : String) (t : Ty)
  | assign (x : String) (e : Expr)
  /-- A field of `self`, with the type the checker gave the read. -/
  | field (f : String) (t : Ty)
  /-- Assigning a field of `self` (an immutable one in `initialize`). -/
  | setField (f : String) (e : Expr)
  | self
  /-- `C[targs].new(args)`: the fields' defaults, then `initialize(args)`;
  `targs` (which may name the enclosing class's parameters) are the
  object's type arguments. -/
  | new (c : Nat) (targs : List Ty) (args : List Expr)
  /-- `super(args)` in `initialize`: the `initialize` class `d` (the
  superclass) has, run on `self`, which assigns the inherited fields. -/
  | superInit (d : Nat) (args : List Expr)
  /-- `recv.m(args)`. -/
  | call (recv : Expr) (m : String) (args : List Expr)
  /-- `recv.m(args) { |params| body }`: an anonymous block. Its parameters
  are locals of the method it is written in. -/
  | callBlk (recv : Expr) (m : String) (args : List Expr) (params : List String) (body : Expr)
  | yield (args : List Expr)
  /-- A call of a built-in method (a native): opaque, its arguments of at
  most the parameters' types, its result of type `ret`. It runs no user
  code here (v1: no call can change what was narrowed). -/
  | prim (name : String) (args : List Expr) (params : List Ty) (ret : Ty)
  | seq (a b : Expr)
  | ite (c t e : Expr)
  | while (c b : Expr)
  | ret (e : Expr)
  /-- `raise e`: `e` an exception (of the program's exception class). -/
  | raise (e : Expr)
  /-- `begin body rescue => x; handler else els end`: an exception the body
  raises goes to `x`, then the handler (which tests its class and raises it
  again when no clause takes it: the translator writes the clauses so);
  otherwise `els`. -/
  | rescue (body : Expr) (x : String) (handler : Expr) (els : Expr)
  /-- `begin body ensure ens end`: `ens` after the body however it ends. -/
  | ensure (body : Expr) (ens : Expr)
  /-- `->(x: T, ...) -> R { body }`: a procedure, closed over this frame's
  locals (by reference, read only: design §13.8, C0); its parameters and
  `own` locals (those first assigned in it) fresh at each call. -/
  | lambda (ps : List (String × Ty)) (own : List (String × Ty)) (ret : Ty) (body : Expr)
  /-- `f.call(args)`: run procedure `f`. -/
  | callProc (f : Expr) (args : List Expr)
  /-- What a `case/in` without `else` reaches when no arm matches, on a
  closed type (docs/01 §11): never, as the checker requires the arms to
  cover the type (it accepts the form only where control cannot get). -/
  | absurd
  /-- `e.nil?`, `e.is_a?(a)`, `e == nil`, `e != nil`, `e == true`,
  `e == false`: forms, not calls (`nil?` and `is_a?` cannot be
  redefined, e63bc57; `==` is the built-in one). `is_a?` names a class
  with its arguments (`Box[Int]`), closed; at run time it tests the
  class only (docs/02 §7 says which are allowed). -/
  | isNil (e : Expr)
  | isA (e : Expr) (a : Atom)
  | eqNil (e : Expr)
  | neNil (e : Expr)
  | eqTrue (e : Expr)
  | eqFalse (e : Expr)
  | and (a b : Expr)
  | or (a b : Expr)
  | not (a : Expr)
  deriving Repr, Inhabited

/-- What a block a method takes looks like: anonymous (`yield` only, live
during the call) with its parameter and result types. -/
structure BlockSig where
  params : List Ty
  ret : Ty
  deriving DecidableEq, Repr, Inhabited

structure Method where
  owner : Nat
  name : String
  params : List (String × Ty)
  ret : Ty
  block : Option BlockSig
  /-- The declared type of each local (the parameters', and the type of
  each other local's first assignment, docs/02 §6). -/
  locals : List (String × Ty)
  body : Expr
  deriving Repr, Inhabited

structure Program where
  classes : ClassTable
  methods : List Method
  /-- The top level: a method of class 0 with no parameters. -/
  main : Method
  /-- The fields' defaults (`Field.default`), each run with `self` the
  object being made, before its `initialize`. -/
  defaults : List Expr := []
  deriving Repr, Inhabited

/-- The class every exception is of: the one named `Exception`, or
`Object` in a program without it. -/
def Program.exn (P : Program) : Nat :=
  (P.classes.findIdx? (·.name == "Exception")).getD 0

/-- The class of procedures of `n` parameters (`ProcN[in A1, .., in An,
out R]`): the first of kind `proc` with `n + 1` parameters. -/
def Program.procClass (P : Program) (n : Nat) : Option Nat :=
  P.classes.findIdx? fun cl => cl.kind == .proc && cl.params.length == n + 1

/-- What can be narrowed: a local, or an immutable field of `self`. -/
inductive Path where
  | local (x : String)
  | field (f : String)
  deriving DecidableEq, Repr, Inhabited

end QuarzCore
