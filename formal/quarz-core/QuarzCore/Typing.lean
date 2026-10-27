/-
QCore's typing (design §2): `check`, the rules as a function (run by
`#eval` and by the conformance test), and `Typed`, the same rules as a
syntax-directed relation (Typed.lean), which the metatheory is about.

A judgment checks an expression in a narrowing environment `Γ` (what
each path holds there, where control reaches) and gives an `Out`: its
type, the environment after it (`none`: control does not get there, as
after `return`), and the environments where its value is truthy and
falsy (what a condition narrows).
-/

import QuarzCore.Syntax

namespace QuarzCore

/-- The narrowing environment: the type each path holds (a local not in
it is not assigned on every path there; a field not in it has its
declared type). The first entry for a path wins. -/
abbrev Env := List (Path × Ty)

namespace Env

def get : Env → Path → Option Ty
  | [], _ => none
  | (q, t) :: Γ, p => if q = p then some t else get Γ p

def set (Γ : Env) (p : Path) (t : Ty) : Env := (p, t) :: Γ.filter (·.1 != p)

/-- Where control may come from either side: the paths both have, with
either type. -/
def join : Env → Env → Env
  | [], _ => []
  | (p, t) :: Γ, Δ => match Δ.get p with
    | some u => (p, t ++ u) :: join Γ Δ
    | none => join Γ Δ

/-- `Γ` says at least what `Δ` says (each path of `Δ` is in `Γ`, with a
type below `Δ`'s). -/
def implies (ct : ClassTable) (Γ Δ : Env) : Bool :=
  Δ.all fun (p, t) => match Γ.get p with
    | some u => u.le ct t
    | none => false

end Env

/-- An environment where control may not get: `none`. -/
def ojoin : Option Env → Option Env → Option Env
  | none, d => d
  | g, none => g
  | some g, some d => some (g.join d)

/-- What checking an expression gives (see the module doc). -/
structure Out where
  ty : Ty
  out : Option Env
  tt : Option Env
  ff : Option Env
  deriving Repr, Inhabited

/-- Control does not get past it: `return`, `raise`, or dead code. -/
def Out.dead : Out := ⟨[], none, none, none⟩

/-- A value that tells nothing about any path when tested. -/
def Out.plain (t : Ty) (Γ : Env) : Out := ⟨t, some Γ, some Γ, some Γ⟩

/-- What the arguments of a call (or `new`, `yield`) give: their types
and the environment after them, or `dead` if one does not return. -/
inductive ArgsOut where
  | live (tys : List Ty) (Γ : Env)
  | dead
  deriving Repr, Inhabited

/-- The context: the program, the method the code is in (its class is
`self`'s, its locals' declared types `Σ`, its result and block types),
and whether the code is a block's body (where `return` is not in v1). -/
structure Ctx where
  prog : Program
  meth : Method
  inBlock : Bool
  deriving Inhabited

namespace Ctx

def ct (c : Ctx) : ClassTable := c.prog.classes

/-- `Σ(x)`: a local's declared type. -/
def decl (c : Ctx) (x : String) : Option Ty := (c.meth.locals.find? (·.1 == x)).map (·.2)

def field? (c : Ctx) (f : String) : Option Field := c.ct.field? c.meth.owner f

/-- What a path holds in `Γ`: a local only once assigned; an immutable
field its narrowed or declared type. -/
def pathTy (c : Ctx) (Γ : Env) : Path → Option Ty
  | .local x => Γ.get (.local x)
  | .field f => match c.field? f with
    | some fd => if fd.var then none else some ((Γ.get (.field f)).getD fd.ty)
    | none => none

end Ctx

/-- The path an expression reads, if it is one (a narrowable read). -/
def Expr.path? : Expr → Option Path
  | .var x _ => some (.local x)
  | .field f _ => some (.field f)
  | _ => none

/-- The locals an expression may assign (blocks' parameters included):
those a loop, or a block that may run again, starts with un-narrowed. -/
def Expr.assigned : Expr → List String
  | .assign x e => x :: e.assigned
  | .setField _ e | .ret e | .isNil e | .isA e _ | .eqNil e | .neNil e
  | .eqTrue e | .eqFalse e | .not e => e.assigned
  | .new _ args | .yield args | .prim _ args _ _ => assignedArgs args
  | .call r _ args => r.assigned ++ assignedArgs args
  | .callBlk r _ args ps b => r.assigned ++ assignedArgs args ++ ps ++ b.assigned
  | .seq a b | .while a b | .and a b | .or a b => a.assigned ++ b.assigned
  | .ite c t e => c.assigned ++ t.assigned ++ e.assigned
  | _ => []
where
  assignedArgs : List Expr → List String
    | [] => []
    | e :: es => e.assigned ++ assignedArgs es

/-- `Γ ∖ xs`: the locals in `xs` back to their declared types (design
§2.2, `while`): what a loop's body or a block assigns may differ on the
next pass. -/
def Ctx.reset (c : Ctx) : Env → List String → Env
  | [], _ => []
  | (.field f, t) :: Γ, xs => (.field f, t) :: c.reset Γ xs
  | (.local x, t) :: Γ, xs =>
    if x ∈ xs then match c.decl x with
      | some d => (.local x, d) :: c.reset Γ xs
      | none => c.reset Γ xs
    else (.local x, t) :: c.reset Γ xs

/-- The method `m` instances of class `c` run: the first of `c`'s
ancestors that defines it. -/
def Program.lookup (P : Program) (c : Nat) (m : String) : Option Method :=
  (P.classes.ancestors c).findSome? fun d => P.methods.find? fun mt => mt.owner == d && mt.name == m

/-- The methods a call of `m` on a receiver of type `t` may run, one per
atom (each must be a class that has it: `nil` has no methods). -/
def Program.resolve (P : Program) (t : Ty) (m : String) : Option (List Method) :=
  t.mapM fun
    -- `Object` holds the value classes' values too, which have no
    -- methods in v1.
    | .cls c => if c == 0 then none else P.lookup c m
    | _ => none

/-- Narrowing a path (design §2.1): `p` holds `t` where the test is
true. An empty type means control does not get there. -/
def narrow (Γ : Env) (p : Path) (t : Ty) : Option Env :=
  if t.isEmpty then none else some (Γ.set p t)

/-- The table of design §2.1 for one test of a path holding `t`. -/
def isATrue (ct : ClassTable) (t : Ty) (a : Atom) : Ty :=
  t.filter (·.le ct a) ++ (if t.any (fun b => a.le ct b && a != b) then [a] else [])

def isAFalse (ct : ClassTable) (t : Ty) (a : Atom) : Ty :=
  t.filter fun b => !(b.le ct a)

/-- `test` gives the types where it is true and false; a test of an
expression that is not a path narrows nothing. -/
def testOut (c : Ctx) (e : Expr) (Γ : Env) (tyT tyF : Ty → Ty) : Out :=
  match e.path?.bind fun p => (c.pathTy Γ p).map (p, ·) with
  | some (p, t) => ⟨[.bool], some Γ, narrow Γ p (tyT t), narrow Γ p (tyF t)⟩
  | none => Out.plain [.bool] Γ

/-- The truthy and falsy sides of a read holding `u` (design §2.1). -/
def truthyTy (u : Ty) : Ty := u.remove .nil

/-- The falsy values a type holds: `nil` and `false` where it holds
them (`Object` does, as every value class). -/
def falsyTy (ct : ClassTable) (u : Ty) : Ty := [.nil, .bool].filter fun a => Ty.le ct [a] u

/-- The `nil` a type holds, if it does. -/
def nilTy (ct : ClassTable) (u : Ty) : Ty := [Atom.nil].filter fun a => Ty.le ct [a] u

/-- Whether `==` against `nil`, `true` or `false` may narrow what `e`
reads in `Δ`: only a value no subclass can redefine `==` for. -/
def finalRead (c : Ctx) (Δ : Env) (e : Expr) : Bool :=
  (e.path?.bind (c.pathTy Δ)).all Ty.allFinal

/-- The block's starting environment: what it may assign un-narrowed,
its parameters given. -/
def blockEnv (c : Ctx) (Δ : Env) (ps : List String) (sig : BlockSig) (body : Expr) : Env :=
  (ps.zip sig.params).foldl (fun g (x, t) => g.set (.local x) t) (c.reset Δ (ps ++ body.assigned))

/-- The block's parameters are its method's locals, declared at least
as wide as what `yield` gives. -/
def blockParamsOk (c : Ctx) (ps : List String) (sig : BlockSig) : Bool :=
  ps.length == sig.params.length &&
  (ps.zip sig.params).all fun (x, t) => match c.decl x with
    | some d => t.le c.ct d
    | none => false

/-- The argument types fit the method's parameters. -/
def argsOk (c : Ctx) (tys : List Ty) (mt : Method) : Bool :=
  tys.length == mt.params.length && (tys.zip mt.params).all fun (t, (_, u)) => t.le c.ct u

mutual

/-- `check c Γ e`: `e` checked where `Γ` holds; `none` if it is rejected. -/
def check (c : Ctx) (Γ : Env) : Expr → Option Out
  | .nil => some (.plain [.nil] Γ)
  | .tru | .fls => some (.plain [.bool] Γ)
  | .int _ => some (.plain [.int] Γ)
  | .str _ => some (.plain [.str] Γ)
  | .var x t => do
    -- The annotation: at least what the local holds here.
    let u ← Γ.get (.local x)
    guard (u.le c.ct t)
    some ⟨t, some Γ, narrow Γ (.local x) (truthyTy u),
      narrow Γ (.local x) (falsyTy c.ct u)⟩
  | .field f t => do
    let fd ← c.field? f
    if fd.var then
      guard (fd.ty.le c.ct t)
      some (.plain t Γ)
    else
      let u := (Γ.get (.field f)).getD fd.ty
      guard (u.le c.ct t)
      some ⟨t, some Γ, narrow Γ (.field f) (truthyTy u),
        narrow Γ (.field f) (falsyTy c.ct u)⟩
  | .assign x e => do
    let o ← check c Γ e
    let d ← c.decl x
    guard (o.ty.le c.ct d)
    match o.out with
    | none => some .dead
    | some Δ => some (.plain o.ty (Δ.set (.local x) o.ty))
  | .setField f e => do
    let fd ← c.field? f
    guard fd.var
    let o ← check c Γ e
    guard (o.ty.le c.ct fd.ty)
    match o.out with
    | none => some .dead
    | some Δ => some (.plain o.ty Δ)
  | .self => some (.plain [.cls c.meth.owner] Γ)
  | .new k args => do
    guard (k < c.ct.length)
    match checkArgs c Γ args with
    | none => none
    | some .dead => some .dead
    | some (.live tys Δ) =>
      let fs := c.ct.allFields k
      guard (tys.length == fs.length && (tys.zip fs).all fun (t, f) => t.le c.ct f.ty)
      some (.plain [.cls k] Δ)
  | .call r m args => do
    let o ← check c Γ r
    match o.out with
    | none => some .dead
    | some Δ =>
      match checkArgs c Δ args with
      | none => none
      | some .dead => some .dead
      | some (.live tys Δ') =>
        let ms ← c.prog.resolve o.ty m
        guard (ms.all fun mt => mt.block.isNone && argsOk c tys mt)
        some (.plain (ms.flatMap (·.ret)) Δ')
  | .callBlk r m args ps body => do
    let o ← check c Γ r
    match o.out with
    | none => some .dead
    | some Δ =>
      match checkArgs c Δ args with
      | none => none
      | some .dead => some .dead
      | some (.live tys Δ') =>
        let ms ← c.prog.resolve o.ty m
        let mt ← ms.head?
        let sig ← mt.block
        guard (ms.all fun mt' => mt'.block == some sig && argsOk c tys mt')
        guard (blockParamsOk c ps sig)
        -- The block runs 0 or more times, during the call: its body starts
        -- with what it assigns un-narrowed, its parameters given.
        let ob ← check { c with inBlock := true } (blockEnv c Δ' ps sig body) body
        guard (ob.ty.le c.ct sig.ret)
        some (.plain (ms.flatMap (·.ret)) (match ob.out with
          | some Γb => Δ'.join Γb
          | none => Δ'))
  | .yield args => do
    let sig ← c.meth.block
    match checkArgs c Γ args with
    | none => none
    | some .dead => some .dead
    | some (.live tys Δ) =>
      guard (tys.length == sig.params.length &&
        (tys.zip sig.params).all fun (t, u) => t.le c.ct u)
      some (.plain sig.ret Δ)
  | .prim _ args params ret => do
    match checkArgs c Γ args with
    | none => none
    | some .dead => some .dead
    | some (.live tys Δ) =>
      guard (tys.length == params.length &&
        (tys.zip params).all fun (t, u) => t.le c.ct u)
      some (.plain ret Δ)
  | .seq a b => do
    let oa ← check c Γ a
    match oa.out with
    | none => some .dead
    | some Δ => check c Δ b
  | .ite cnd t e => do
    let oc ← check c Γ cnd
    let ot ← checkBranch c oc.tt t
    let oe ← checkBranch c oc.ff e
    some ⟨ot.ty ++ oe.ty, ojoin ot.out oe.out, ojoin ot.tt oe.tt, ojoin ot.ff oe.ff⟩
  | .while cnd b => do
    -- Each pass starts with what the loop assigns un-narrowed (docs/02
    -- §6): the body must end with at least that.
    let Γ0 := c.reset Γ (Expr.assigned (.while cnd b))
    let oc ← check c Γ0 cnd
    match oc.tt with
    | none => some { Out.plain [.nil] Γ with out := oc.ff, tt := oc.ff, ff := oc.ff }
    | some Δ =>
      let ob ← check c Δ b
      guard (ob.out.all (·.implies c.ct Γ0))
      some ⟨[.nil], oc.ff, oc.ff, oc.ff⟩
  | .ret e => do
    guard (!c.inBlock)
    let o ← check c Γ e
    guard (o.ty.le c.ct c.meth.ret)
    some .dead
  | .raise => some .dead
  | .isNil e => do
    let o ← check c Γ e
    match o.out with
    | none => some .dead
    | some Δ => some (testOut c e Δ (nilTy c.ct) (·.remove .nil))
  | .isA e a => do
    let o ← check c Γ e
    match o.out with
    | none => some .dead
    | some Δ => some (testOut c e Δ (isATrue c.ct · a) (isAFalse c.ct · a))
  | .eqNil e => do
    let o ← check c Γ e
    match o.out with
    | none => some .dead
    | some Δ =>
      -- Only a value no subclass can redefine `==` for narrows (09b19e3).
      some (testOut c e Δ (fun t => if finalRead c Δ e then t.keep [.nil] else t)
        (fun t => if finalRead c Δ e then t.remove .nil else t))
  | .neNil e => do
    let o ← check c Γ e
    match o.out with
    | none => some .dead
    | some Δ =>
      some (testOut c e Δ (fun t => if finalRead c Δ e then t.remove .nil else t)
        (fun t => if finalRead c Δ e then t.keep [.nil] else t))
  | .eqTrue e | .eqFalse e => do
    let o ← check c Γ e
    match o.out with
    | none => some .dead
    | some Δ =>
      some (testOut c e Δ (fun t => if finalRead c Δ e then t.keep [.bool] else t) id)
  | .and a b => do
    let oa ← check c Γ a
    let ob ← checkBranch c oa.tt b
    some ⟨oa.ty ++ ob.ty, ojoin oa.ff ob.out, ob.tt, ojoin oa.ff ob.ff⟩
  | .or a b => do
    let oa ← check c Γ a
    let ob ← checkBranch c oa.ff b
    some ⟨oa.ty ++ ob.ty, ojoin oa.tt ob.out, ojoin oa.tt ob.tt, ob.ff⟩
  | .not a => do
    let oa ← check c Γ a
    some ⟨[.bool], oa.out, oa.ff, oa.tt⟩

/-- Code reached where `Γ` holds, or (`none`) not at all: dead code is
not checked. -/
def checkBranch (c : Ctx) : Option Env → Expr → Option Out
  | some Γ, e => check c Γ e
  | none, _ => some .dead

/-- The arguments, left to right. -/
def checkArgs (c : Ctx) (Γ : Env) : List Expr → Option ArgsOut
  | [] => some (.live [] Γ)
  | e :: es => do
    let o ← check c Γ e
    match o.out with
    | none => some .dead
    | some Δ =>
      match checkArgs c Δ es with
      | none => none
      | some .dead => some .dead
      | some (.live tys Δ') => some (.live (o.ty :: tys) Δ')

end

end QuarzCore
