/-
QCore's types (design §1.1): a type is a finite set of atoms, kept as a
list (order and repetition do not matter: every definition below goes by
membership). The empty type is `Nothing`.
-/

namespace QuarzCore

/-- An atom of a union (a class by its index in the class table). `Nil`,
`Bool`, `Int`, `Str` and `Float` are the value classes: final (nothing subclasses them), so `==` against them may
narrow. A user class is never final: a subclass elsewhere may define
`==` (09b19e3). -/
inductive Atom where
  | nil
  | bool
  | int
  | str
  | float
  | cls (c : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- A type: a union of atoms. -/
abbrev Ty := List Atom

def Atom.final : Atom → Bool
  | .cls _ => false
  | _ => true

/-- A field of a class: its name, declared type, whether it is `var`
(only an immutable field is narrowed, and outside `initialize` only a
`var` one assigned), and its default (an index into `Program.defaults`). -/
structure Field where
  name : String
  ty : Ty
  var : Bool
  default : Option Nat := none
  deriving Repr, Inhabited

/-- A class: its superclass (none for the root, `Object`) and its own
fields. Class 0 is `Object`. -/
structure Class where
  name : String
  super : Option Nat
  fields : List Field
  deriving Repr, Inhabited

abbrev ClassTable := List Class

namespace ClassTable

/-- The superclass chain of `c`, `c` first (at most as long as the table:
a cycle is cut there, and `wf` rules it out). -/
def ancestorsAux (ct : ClassTable) : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, c =>
    c :: match (ct[c]?).bind (·.super) with
      | some d => ancestorsAux ct n d
      | none => []

def ancestors (ct : ClassTable) (c : Nat) : List Nat :=
  ancestorsAux ct ct.length c

/-- `c` is `d` or a subclass of it. -/
def subclass (ct : ClassTable) (c d : Nat) : Bool :=
  (ct.ancestors c).contains d

/-- Every field of an instance of `c`, inherited ones first: the layout
`new` fills in order. -/
def allFields (ct : ClassTable) (c : Nat) : List Field :=
  ((ct.ancestors c).reverse.filterMap (ct[·]?)).flatMap (·.fields)

def field? (ct : ClassTable) (c : Nat) (f : String) : Option Field :=
  (ct.allFields c).find? (·.name == f)

end ClassTable

/-- Atom order. The value classes are direct subclasses of `Object`
(class 0) and have no subclasses. -/
def Atom.le (ct : ClassTable) : Atom → Atom → Bool
  | .cls c, .cls d => ct.subclass c d
  | .cls _, _ => false
  | _, .cls d => d == 0
  | a, b => a == b

/-- `S ≤ T`: each atom of `S` is below one of `T`. -/
def Ty.le (ct : ClassTable) (s t : Ty) : Bool :=
  s.all fun a => t.any fun b => a.le ct b

def Ty.nothing : Ty := []

def Ty.union (s t : Ty) : Ty := s ++ t

/-- `T ∖ {a}` and `T ∩ {as}`, atom by atom (design §2.1). -/
def Ty.remove (t : Ty) (a : Atom) : Ty := t.filter (· != a)

def Ty.keep (t : Ty) (as : List Atom) : Ty := t.filter (as.contains ·)

def Ty.allFinal (t : Ty) : Bool := t.all Atom.final

/-- A field that must be assigned in `initialize`: no default, and a type
without `nil` (docs/01 §3; `var` or not). -/
def Field.required (ct : ClassTable) (f : Field) : Bool :=
  f.default.isNone && !Ty.le ct [.nil] f.ty

end QuarzCore
