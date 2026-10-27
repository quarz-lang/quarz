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
  /-- A local's read, with the type the checker gave it there. -/
  | var (x : String) (t : Ty)
  | assign (x : String) (e : Expr)
  /-- A field of `self`, with the type the checker gave the read. -/
  | field (f : String) (t : Ty)
  /-- Assigning a `var` field of `self`. -/
  | setField (f : String) (e : Expr)
  | self
  /-- `C.new(args)`: the arguments are its fields, inherited ones first. -/
  | new (c : ClassId) (args : List Expr)
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
  | raise
  /-- `e.nil?`, `e.is_a?(a)`, `e == nil`, `e != nil`, `e == true`,
  `e == false`: forms, not calls (`nil?` and `is_a?` cannot be
  redefined, e63bc57; `==` is the built-in one). -/
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
  owner : ClassId
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
  deriving Repr, Inhabited

/-- What can be narrowed: a local, or an immutable field of `self`. -/
inductive Path where
  | local (x : String)
  | field (f : String)
  deriving DecidableEq, Repr, Inhabited

end QuarzCore
