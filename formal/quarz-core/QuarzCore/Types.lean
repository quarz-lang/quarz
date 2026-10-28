/-
QCore's types (design §1.1): a type is a finite set of atoms, kept as a
list (order and repetition do not matter: every definition below goes by
membership, but for a class's type arguments, which are compared as
lists: `Box[Int | Nil]` and `Box[Nil | Int]` are unrelated here, where
the Rust checker takes them as the same argument). The empty type is
`Nothing`.
-/

namespace QuarzCore

/-- The variance of a class's type parameter (docs/02 §3): `out`, `in`,
or none (invariant). -/
inductive Variance where
  | co
  | contra
  | inv
  deriving DecidableEq, Repr, Inhabited

/-- An atom of a union (a class by its index in the class table, with its
type arguments; a type parameter of the enclosing class by its position).
`Nil`, `Bool`, `Int`, `Str` and `Float` are the value classes: final
(nothing subclasses them), so `==` against them may narrow. A user class
is never final: a subclass elsewhere may define `==` (09b19e3). -/
inductive Atom where
  | nil
  | bool
  | int
  | str
  | float
  | cls (c : Nat) (args : List (List Atom))
  | param (i : Nat)
  deriving Repr, Inhabited

/-- A type: a union of atoms. -/
abbrev Ty := List Atom

-- Equality, by hand: the deriving handler does not take the nested
-- inductive.
mutual
def Atom.beq : Atom → Atom → Bool
  | .nil, .nil | .bool, .bool | .int, .int | .str, .str | .float, .float => true
  | .param i, .param j => i == j
  | .cls c as, .cls d bs => c == d && Ty.beqArgs as bs
  | _, _ => false
def Ty.beq : Ty → Ty → Bool
  | [], [] => true
  | a :: s, b :: t => Atom.beq a b && Ty.beq s t
  | _, _ => false
def Ty.beqArgs : List Ty → List Ty → Bool
  | [], [] => true
  | a :: as, b :: bs => Ty.beq a b && Ty.beqArgs as bs
  | _, _ => false
end

mutual
theorem Atom.beq_eq : ∀ a b : Atom, Atom.beq a b = true → a = b
  | .nil, .nil, _ | .bool, .bool, _ | .int, .int, _ | .str, .str, _ | .float, .float, _ => rfl
  | .param i, .param j, h => by simp [Atom.beq] at h; subst h; rfl
  | .cls c as, .cls d bs, h => by
    simp [Atom.beq] at h
    obtain ⟨rfl, h⟩ := h
    rw [Ty.beqArgs_eq as bs h]
theorem Ty.beq_eq : ∀ s t : Ty, Ty.beq s t = true → s = t
  | [], [], _ => rfl
  | a :: s, b :: t, h => by
    simp [Ty.beq] at h
    rw [Atom.beq_eq a b h.1, Ty.beq_eq s t h.2]
theorem Ty.beqArgs_eq : ∀ as bs : List Ty, Ty.beqArgs as bs = true → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp [Ty.beqArgs] at h
    rw [Ty.beq_eq a b h.1, Ty.beqArgs_eq as bs h.2]
end

mutual
theorem Atom.beq_refl : ∀ a : Atom, Atom.beq a a = true
  | .nil | .bool | .int | .str | .float => rfl
  | .param i => by simp [Atom.beq]
  | .cls c as => by simp [Atom.beq, Ty.beqArgs_refl as]
theorem Ty.beq_refl : ∀ s : Ty, Ty.beq s s = true
  | [] => rfl
  | a :: s => by simp [Ty.beq, Atom.beq_refl a, Ty.beq_refl s]
theorem Ty.beqArgs_refl : ∀ as : List Ty, Ty.beqArgs as as = true
  | [] => rfl
  | a :: as => by simp [Ty.beqArgs, Ty.beq_refl a, Ty.beqArgs_refl as]
end

instance : DecidableEq Atom := fun a b =>
  decidable_of_iff (Atom.beq a b = true) ⟨Atom.beq_eq a b, fun h => h ▸ Atom.beq_refl a⟩

def Atom.final : Atom → Bool
  | .cls _ _ => false
  | .param _ => false
  | _ => true

def Atom.isParam : Atom → Bool
  | .param _ => true
  | _ => false

def Atom.paramIdx : Atom → Nat
  | .param i => i
  | _ => 0

-- The enclosing class's parameters substituted: `.param i` becomes
-- `as[i]` (`Object` past the end).
mutual
def Atom.subst (as : List Ty) : Atom → Ty
  | .param i => (as[i]?).getD [.cls 0 []]
  | .cls c args => [.cls c (Ty.substArgs as args)]
  | a => [a]
def Ty.subst (as : List Ty) : Ty → Ty
  | [] => []
  | a :: t => a.subst as ++ Ty.subst as t
def Ty.substArgs (as : List Ty) : List Ty → List Ty
  | [] => []
  | t :: ts => Ty.subst as t :: Ty.substArgs as ts
end

-- Whether a type mentions no type parameter (a value's type).
mutual
def Atom.closed : Atom → Bool
  | .param _ => false
  | .cls _ args => Ty.closedArgs args
  | _ => true
def Ty.closed : Ty → Bool
  | [] => true
  | a :: t => a.closed && Ty.closed t
def Ty.closedArgs : List Ty → Bool
  | [] => true
  | t :: ts => t.closed && Ty.closedArgs ts
end

-- Every parameter named, at any depth, is one of the first `n`: what a
-- class's own declarations (its superclass's arguments) and the type
-- arguments of a `new` in its methods may name.
mutual
def Atom.paramsBelow (n : Nat) : Atom → Bool
  | .param i => decide (i < n)
  | .cls _ args => Ty.argsParamsBelow n args
  | _ => true
def Ty.paramsBelow (n : Nat) : Ty → Bool
  | [] => true
  | a :: t => a.paramsBelow n && Ty.paramsBelow n t
def Ty.argsParamsBelow (n : Nat) : List Ty → Bool
  | [] => true
  | t :: ts => t.paramsBelow n && Ty.argsParamsBelow n ts
end

/-- A field of a class: its name, declared type, whether it is `var`
(only an immutable field is narrowed, and outside `initialize` only a
`var` one assigned), and its default (an index into `Program.defaults`). -/
structure Field where
  name : String
  ty : Ty
  var : Bool
  default : Option Nat := none
  deriving Repr, Inhabited

/-- A class: its superclass (none for the root, `Object`) with the type
arguments it is given (which may name the class's own parameters:
`class IntBox < Box[Int]`, `class Pair[A, B] < Box[A]`), its type
parameters' variances, and its own fields (whose types may name its
parameters). Class 0 is `Object`. -/
structure Class where
  name : String
  super : Option Nat
  fields : List Field
  params : List Variance := []
  superArgs : List Ty := []
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

/-- Every field of an instance of `c` with its declaring class, inherited
ones first: the layout `new` fills in order. -/
def allFieldsDecl (ct : ClassTable) (c : Nat) : List (Nat × Field) :=
  ((ct.ancestors c).reverse.filterMap fun d => (ct[d]?).map (d, ·)).flatMap fun (d, k) =>
    k.fields.map (d, ·)

/-- Every field of an instance of `c`, inherited ones first, their types as
declared (naming the declaring class's parameters: `allFieldsAt` gives
them as seen from `c`). -/
def allFields (ct : ClassTable) (c : Nat) : List Field :=
  (ct.allFieldsDecl c).map (·.2)

def field? (ct : ClassTable) (c : Nat) (f : String) : Option Field :=
  (ct.allFields c).find? (·.name == f)

/-- The arguments of ancestor `d` as seen from `c` given `as`: the
superclass arguments substituted along the chain (`none`: not an
ancestor). -/
def ancestorArgsAux (ct : ClassTable) : Nat → Nat → List Ty → Nat → Option (List Ty)
  | 0, _, _, _ => none
  | n + 1, c, as, d =>
    if c == d then some as else
    match ct[c]? with
    | some k => match k.super with
      | some p => ancestorArgsAux ct n p (Ty.substArgs as k.superArgs) d
      | none => none
    | none => none

def ancestorArgs (ct : ClassTable) (c : Nat) (as : List Ty) (d : Nat) : Option (List Ty) :=
  ancestorArgsAux ct ct.length c as d

/-- A class's own parameters, as the arguments its body sees itself with. -/
def selfArgs (ct : ClassTable) (c : Nat) : List Ty :=
  (List.range (((ct[c]?).map (·.params)).getD []).length).map fun i => [.param i]

/-- The fields of an instance of `c`, inherited ones first, their types
as seen from `c` given `as` (the declaring class's parameters
substituted). Same names and order as `allFields`. -/
def allFieldsAt (ct : ClassTable) (c : Nat) (as : List Ty) : List Field :=
  (ct.allFieldsDecl c).map fun (d, f) =>
    { f with ty := Ty.subst ((ct.ancestorArgs c as d).getD []) f.ty }

def fieldAt? (ct : ClassTable) (c : Nat) (as : List Ty) (f : String) : Option Field :=
  (ct.allFieldsAt c as).find? (·.name == f)

end ClassTable

/-- Atom order. The value classes are direct subclasses of `Object`
(class 0) and have no subclasses. A class with arguments is below an
ancestor given the same arguments, as the chain substitutes them (the
parameters are invariant here: variance is the next stage), and every
class is below `Object`. A parameter is only below itself and
`Object`. -/
def Atom.le (ct : ClassTable) : Atom → Atom → Bool
  | .cls c as, .cls d bs => (d == 0 && bs.isEmpty) || match ct.ancestorArgs c as d with
    | some as' => Ty.beqArgs as' bs
    | none => false
  | .cls _ _, _ => false
  | .param i, .param j => i == j
  | .param _, .cls d bs => d == 0 && bs.isEmpty
  | .param _, _ => false
  | _, .cls d bs => d == 0 && bs.isEmpty
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
