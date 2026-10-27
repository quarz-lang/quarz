/-
A whole program checked (design §1.2, §2): the class table and the
methods well formed, and every body checked.
-/

import QuarzCore.Typing

namespace QuarzCore

namespace Program

/-- Class 0 is the root; every other class's superclass comes before it
(so the chains end); a class's fields have distinct names. -/
def wfClasses (P : Program) : Bool :=
  0 < P.classes.length &&
  (List.range P.classes.length).all (fun i => match P.classes[i]? with
    | some k => if i == 0 then k.super.isNone else
      (match k.super with
        | some d => decide (d < i)
        | none => false)
    | none => true) &&
  -- A class's fields' names distinct, inherited ones included.
  (List.range P.classes.length).all fun i =>
    decide ((P.classes.allFields i).map (·.name)).Nodup

/-- An override takes at least what it overrides takes, gives at most
what it gives, and takes the same block. -/
def overrides (P : Program) (sub sup : Method) : Bool :=
  sub.params.length == sup.params.length &&
  (sup.params.zip sub.params).all (fun ((_, t), (_, u)) => t.le P.classes u) &&
  sub.ret.le P.classes sup.ret &&
  sub.block == sup.block

/-- A method's signature: its owner a class, its parameters locals of
those types (first), its locals' names distinct, what it overrides
overridden as it may be, and an `==` taking `nil` and booleans (what
`== nil` and `== true` give it), giving a boolean, taking no block. -/
def wfMethod (P : Program) (mt : Method) : Bool :=
  mt.owner < P.classes.length &&
  mt.params.length ≤ mt.locals.length &&
  decide (mt.locals.map (·.1)).Nodup &&
  (mt.params.zip mt.locals).all (fun (p, l) => p == l) &&
  -- `initialize` is not called by name (`Program.resolve`): its own.
  (mt.name == "initialize" || ((P.classes.ancestors mt.owner).drop 1).all (fun d =>
    match P.lookup d mt.name with
    | some sup => P.overrides mt sup
    | none => true)) &&
  (mt.name != "==" || (mt.ret.le P.classes [.bool] && mt.block.isNone && match mt.params with
    | [(_, t)] => Ty.le P.classes [.nil, .bool] t
    | _ => false))

/-- A field that must be assigned in `initialize`: no default, and a type
without `nil` (docs/01 §3; `var` or not). -/
def _root_.QuarzCore.Field.required (ct : ClassTable) (f : Field) : Bool :=
  f.default.isNone && !Ty.le ct [.nil] f.ty

/-- The fields of instances of `k` that hold a value before
`initialize` runs (those with a default, and those that admit `nil`),
as entries of an environment: what `initialize` may read. -/
def heldEnv (ct : ClassTable) (fs : List Field) : Env :=
  fs.filterMap fun f => if f.required ct then none else some (.field f.name, f.ty)

/-- A method's body, with its parameters assigned (and, for
`initialize`, the fields holding a value), giving its result type; an
`initialize` ends with every field set, its value dropped (`new` gives
the object). -/
def checkMethod (P : Program) (mt : Method) : Bool :=
  let c : Ctx := ⟨P, mt, false, false⟩
  let held := if c.inInit then heldEnv P.classes (P.classes.allFields mt.owner) else []
  match check c (mt.params.map (fun (x, t) => (.local x, t)) ++ held) mt.body with
  | some o => (c.inInit || o.out.isNone || o.ty.le P.classes mt.ret) &&
      (!c.inInit || o.out.all (c.allSet ·))
  | none => false

/-- Whether class `k` defines `initialize` itself. -/
def ownInit (P : Program) (k : Nat) : Bool :=
  P.methods.any fun mt => mt.owner == k && mt.name == "initialize"

/-- A class's fields and `initialize`: one with a field that must be
assigned defines `initialize`; one that defines it has no such field
above it (`super` is not in the model yet: out of range). -/
def wfInit (P : Program) (k : Nat) : Bool :=
  let own := ((P.classes[k]?).map (·.fields)).getD []
  let above := match (P.classes[k]?).bind (·.super) with
    | some d => P.classes.allFields d
    | none => []
  (!(own.any (·.required P.classes)) || P.ownInit k) &&
  (!P.ownInit k || !(above.any (·.required P.classes)))

/-- The context a field default of class `k` is checked in: `self` the
object being made, which may not be used (`Ctx.inDefault`), as in a
block of `initialize` (no `return`, no immutable field assigned). -/
def defaultCtx (P : Program) (k : Nat) (t : Ty) : Ctx :=
  ⟨P, ⟨k, "initialize", [], t, none, [], .nil⟩, true, true⟩

/-- Each of class `k`'s own fields' defaults: of the field's type, reading
only the fields before it that hold a value. -/
def checkDefaults (P : Program) (k : Nat) : Bool :=
  let fs := P.classes.allFields k
  fs.zipIdx.all fun (f, i) => match f.default with
    | none => true
    | some d => match P.defaults[d]? with
      | some e => match check (P.defaultCtx k f.ty) (heldEnv P.classes (fs.take i)) e with
        | some o => o.ty.le P.classes f.ty
        | none => false
      | none => false

def check (P : Program) : Bool :=
  P.wfClasses &&
  -- The top level runs with `self` an instance of its class, which has
  -- no fields (`run`).
  (P.main.owner < P.classes.length && (P.classes.allFields P.main.owner).isEmpty &&
    P.main.params.isEmpty && P.main.block.isNone) &&
  (P.main :: P.methods).all (fun mt => P.wfMethod mt && P.checkMethod mt) &&
  (List.range P.classes.length).all fun k => P.wfInit k && P.checkDefaults k

end Program

end QuarzCore
