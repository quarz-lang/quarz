/-
A whole program checked (design §1.2, §2): the class table and the
methods well formed, and every body checked.
-/

import QuarzCore.Typing

namespace QuarzCore

namespace Program

/-- Class 0 is the root; every other class's superclass comes before it
(so the chains end). -/
def wfClasses (P : Program) : Bool :=
  0 < P.classes.length &&
  (List.range P.classes.length).all fun i => match P.classes[i]? with
    | some k => if i == 0 then k.super.isNone else
      (match k.super with
        | some d => decide (d < i)
        | none => false)
    | none => true

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
  ((P.classes.ancestors mt.owner).drop 1).all (fun d =>
    match P.lookup d mt.name with
    | some sup => P.overrides mt sup
    | none => true) &&
  (mt.name != "==" || (mt.ret.le P.classes [.bool] && mt.block.isNone && match mt.params with
    | [(_, t)] => Ty.le P.classes [.nil, .bool] t
    | _ => false))

/-- A method's body, with its parameters assigned. -/
def checkMethod (P : Program) (mt : Method) : Bool :=
  let c : Ctx := ⟨P, mt, false⟩
  match check c (mt.params.map fun (x, t) => (.local x, t)) mt.body with
  | some o => o.out.isNone || o.ty.le P.classes mt.ret
  | none => false

def check (P : Program) : Bool :=
  P.wfClasses &&
  -- The top level runs with `self` an instance of its class, which has
  -- no fields (`run`).
  (P.main.owner < P.classes.length && (P.classes.allFields P.main.owner).isEmpty &&
    P.main.params.isEmpty && P.main.block.isNone) &&
  (P.main :: P.methods).all fun mt => P.wfMethod mt && P.checkMethod mt

end Program

end QuarzCore
