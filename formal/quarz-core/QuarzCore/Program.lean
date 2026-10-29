/-
A whole program checked (design §1.2, §2): the class table and the
methods well formed, and every body checked.
-/

import QuarzCore.Typing

namespace QuarzCore

namespace Program

/-- Class 0 is the root (without parameters); every other class's
superclass comes before it (so the chains end) and gets as many
arguments as it has parameters, each naming only the class's own
parameters; a class's fields have distinct names. -/
def wfClasses (P : Program) : Bool :=
  0 < P.classes.length &&
  (List.range P.classes.length).all (fun i => match P.classes[i]? with
    | some k => if i == 0 then k.super.isNone && k.params.isEmpty && k.superArgs.isEmpty else
      (match k.super with
        | some d => decide (d < i) &&
            k.superArgs.length == (((P.classes[d]?).map (·.params)).getD []).length &&
            Ty.argsParamsBelow k.params.length k.superArgs &&
            -- The model's range (G1b): a superclass's arguments take no
            -- arguments themselves (`Box[T]`, `Box[Int?]`, not
            -- `Box[Box[T]]`), which bounds what `≤` compares; and they
            -- stand in a positive position (docs/02 §3).
            k.superArgs.all (fun t => t.all fun a => a.isParam || decide (a.depth ≤ 1)) &&
            Ty.argsPosOk P.classes k.params true (P.classes.variances d) k.superArgs &&
            -- Each within the superclass's parameter's bound.
            (k.superArgs.zipIdx.all fun (t, j) =>
              t.le P.classes k.bounds (Ty.boundOf (P.classes.boundsOf d) j))
        | none => false)
    | none => true) &&
  -- A class's fields' names distinct, inherited ones included.
  ((List.range P.classes.length).all fun i =>
    decide ((P.classes.allFields i).map (·.name)).Nodup) &&
  -- No more bounds than parameters.
  ((List.range P.classes.length).all fun i => match P.classes[i]? with
    | some k => decide (k.bounds.length ≤ k.params.length)
    | none => true) &&
  -- A `data` type and a variant have no subclasses, an `enum`'s are its
  -- variants, and the root is a class.
  (List.range P.classes.length).all fun i => match P.classes[i]? with
    | some k => (match k.super with
        | some d => P.classes.kindOf d != .data && P.classes.kindOf d != .variant &&
            (P.classes.kindOf d != .enumC || (k.kind == .variant && k.params.isEmpty))
        | none => true) && (i != 0 || k.kind == .cls)
    | none => true

/-- An override takes at least what it overrides takes, gives at most
what it gives, and takes the same block. -/
def overrides (P : Program) (sub sup : Method) : Bool :=
  sub.params.length == sup.params.length &&
  (sup.params.zip sub.params).all (fun ((_, t), (_, u)) => t.le P.classes (P.classes.boundsOf sub.owner) u) &&
  sub.ret.le P.classes (P.classes.boundsOf sub.owner) sup.ret &&
  sub.block == sup.block

/-- The variance check of a method's signature (docs/02 §3): its
parameters are negative positions, its result positive, the parameters
of the block it takes positive and that block's result negative. -/
def methodPosOk (P : Program) (mt : Method) : Bool :=
  mt.params.all (fun p => p.2.posOk P.classes (P.classes.variances mt.owner) false) &&
  mt.ret.posOk P.classes (P.classes.variances mt.owner) true &&
  match mt.block with
  | some sig => sig.params.all (·.posOk P.classes (P.classes.variances mt.owner) true) &&
      sig.ret.posOk P.classes (P.classes.variances mt.owner) false
  | none => true

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
  -- What it overrides is seen with the superclass's arguments.
  -- The variance check too (not for `initialize`, which sees the exact
  -- type, docs/02 §3).
  (mt.name == "initialize" || P.methodPosOk mt && ((P.classes.ancestors mt.owner).drop 1).all (fun d =>
    match P.lookupAt d ((P.classes.ancestorArgs mt.owner (P.classes.selfArgs mt.owner) d).getD []) mt.name with
    | some sup => P.overrides mt sup
    | none => true)) &&
  (mt.name != "==" || (mt.ret.le P.classes (P.classes.boundsOf mt.owner) [.bool] && mt.block.isNone &&
    match mt.params with
    | [(_, t)] => Ty.le P.classes (P.classes.boundsOf mt.owner) [.nil, .bool] t
    | _ => false))

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
  let held := if c.inInit then heldEnv P.classes c.fields else []
  match check c (mt.params.map (fun (x, t) => (.local x, t)) ++ held) mt.body with
  | some o => (c.inInit || o.out.isNone || o.ty.le P.classes c.bounds mt.ret) &&
      (!c.inInit || o.out.all (c.allSet ·))
  | none => false

/-- Whether class `k` defines `initialize` itself. -/
def ownInit (P : Program) (k : Nat) : Bool :=
  P.methods.any fun mt => mt.owner == k && mt.name == "initialize"

/-- A class's fields and `initialize`: one with a field that must be
assigned defines `initialize` (whose end, with every field set, needs
`super` for those above it). -/
def wfInit (P : Program) (k : Nat) : Bool :=
  let own := ((P.classes[k]?).map (·.fields)).getD []
  !(own.any (·.required P.classes)) || P.ownInit k

/-- The context a field default of class `k` is checked in: `self` the
object being made, which may not be used (`Ctx.inDefault`), as in a
block of `initialize` (no `return`, no immutable field assigned). -/
def defaultCtx (P : Program) (k : Nat) (t : Ty) : Ctx :=
  ⟨P, ⟨k, "initialize", [], t, none, [], .nil⟩, true, true⟩

/-- Each of class `k`'s own fields' defaults: of the field's type, reading
only the fields before it that hold a value. -/
def checkDefaults (P : Program) (k : Nat) : Bool :=
  let fs := P.classes.allFieldsAt k (P.classes.selfArgs k)
  fs.zipIdx.all fun (f, i) => match f.default with
    | none => true
    | some d => match P.defaults[d]? with
      | some e => match check (P.defaultCtx k f.ty) (heldEnv P.classes (fs.take i)) e with
        | some o => o.ty.le P.classes (P.classes.boundsOf k) f.ty
        | none => false
      | none => false

/-- The variance check of a class's own fields (docs/02 §3): an
immutable field's type is a positive position (it is read), a `var`
field's both (it is written too). The proof does not need it (a field is
read and written only by its object's methods, which see their class's
exact arguments); the Rust checker has it. -/
def fieldsPosOk (P : Program) (k : Nat) : Bool :=
  (((P.classes[k]?).map (·.fields)).getD []).all fun f =>
    f.ty.posOk P.classes (P.classes.variances k) true &&
    (!f.var || f.ty.posOk P.classes (P.classes.variances k) false)

def check (P : Program) : Bool :=
  P.wfClasses &&
  -- The top level runs with `self` an instance of its class, which has
  -- no fields and no parameters (`run`).
  (P.main.owner < P.classes.length && (P.classes.allFields P.main.owner).isEmpty &&
    (((P.classes[P.main.owner]?).map (·.params)).getD []).isEmpty &&
    P.main.params.isEmpty && P.main.block.isNone && P.classes.kindOf P.main.owner != .enumC) &&
  (P.main :: P.methods).all (fun mt => P.wfMethod mt && P.checkMethod mt) &&
  (List.range P.classes.length).all fun k => P.wfInit k && P.checkDefaults k && P.fieldsPosOk k

end Program

end QuarzCore
