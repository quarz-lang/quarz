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
    | some u => u.le ct [] t
    | none => false

/-- After `ensure`: the locals in `xs` (what it assigns) as `Δe` (its end)
has them, the rest as `Δ`. -/
def takeFrom (Δ Δe : Env) (xs : List String) : Env :=
  Δ.filterMap fun (p, t) => match p with
    | .local x => if x ∈ xs then (Δe.get p).map (p, ·) else some (p, t)
    | .field _ => some (p, t)

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
  /-- A field's default: the object may not be used at all (docs/01 §3). -/
  inDefault : Bool
  deriving Inhabited

namespace Ctx

def ct (c : Ctx) : ClassTable := c.prog.classes

/-- The bounds of the parameters of the method's class: what a value of
one of them is (`T <: X`), where values flow (arguments, results,
assignments). Narrowing compares without them. -/
def bounds (c : Ctx) : List Ty := c.ct.boundsOf c.meth.owner

/-- `Σ(x)`: a local's declared type. -/
def decl (c : Ctx) (x : String) : Option Ty := (c.meth.locals.find? (·.1 == x)).map (·.2)

/-- The class's own parameters, as its body sees `self`'s arguments. -/
def selfArgs (c : Ctx) : List Ty := c.ct.selfArgs c.meth.owner

/-- The type of `self`. -/
def selfTy (c : Ctx) : Ty := [.cls c.meth.owner c.selfArgs]

/-- The fields of `self`, their types as the class's body sees them. -/
def fields (c : Ctx) : List Field := c.ct.allFieldsAt c.meth.owner c.selfArgs

def field? (c : Ctx) (f : String) : Option Field := c.ct.fieldAt? c.meth.owner c.selfArgs f

/-- What a path holds in `Γ`: a local only once assigned; an immutable
field its narrowed or declared type. -/
def pathTy (c : Ctx) (Γ : Env) : Path → Option Ty
  | .local x => Γ.get (.local x)
  | .field f => match c.field? f with
    | some fd => if fd.var then none else some ((Γ.get (.field f)).getD fd.ty)
    | none => none

end Ctx

namespace Ctx

/-- Code of an `initialize` (or a field's default): the object may not
be complete yet. -/
def inInit (c : Ctx) : Bool := c.meth.name == "initialize"

/-- Every field of `self` holds a value (has an entry in `Γ`, inside an
`initialize`): the object may be used. -/
def allSet (c : Ctx) (Γ : Env) : Bool :=
  c.fields.all fun f => (Γ.get (.field f.name)).isSome

/-- Before `super` into class `d`: every field holds a value but the
inherited ones to assign (the class's own assigned, docs/01 §3; those
with a default or that admit `nil` hold one from the start). -/
def preSuper (c : Ctx) (d : Nat) (Γ : Env) : Bool :=
  c.fields.all fun f =>
    ((c.ct.allFields d).any (·.name == f.name) && f.required c.ct) ||
      (Γ.get (.field f.name)).isSome

/-- Where `super` into class `d` may be: in `initialize` itself (not a
block, not a default), `d` the superclass, the class's own fields
assigned first (`preSuper`). -/
def superOk (c : Ctx) (d : Nat) (Γ : Env) : Bool :=
  c.inInit && !c.inBlock && !c.inDefault &&
    (c.ct[c.meth.owner]?).bind (·.super) == some d && c.preSuper d Γ

/-- After `super`: every field holds a value of its declared type (the
superclass's `initialize` assigned the inherited ones, and may have
assigned any, as far as the rules say). -/
def afterSuper (c : Ctx) (Δ : Env) : Env :=
  c.fields.foldl (fun Δ f => Δ.set (.field f.name) f.ty) Δ

/-- The arguments the superclass `d` gets from this class's body. -/
def superArgs (c : Ctx) (d : Nat) : List Ty :=
  (c.ct.ancestorArgs c.meth.owner c.selfArgs d).getD []

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
  | .setField _ e | .ret e | .raise e | .isNil e | .isA e _ | .eqNil e | .neNil e
  | .eqTrue e | .eqFalse e | .not e => e.assigned
  | .new _ _ args | .superInit _ args | .yield args | .prim _ args _ _ => assignedArgs args
  | .call r _ args => r.assigned ++ assignedArgs args
  | .callBlk r _ args ps b => r.assigned ++ assignedArgs args ++ ps ++ b.assigned
  | .seq a b | .while a b | .and a b | .or a b => a.assigned ++ b.assigned
  | .ite c t e => c.assigned ++ t.assigned ++ e.assigned
  | .rescue b x h els => b.assigned ++ x :: h.assigned ++ els.assigned
  | .ensure b e => b.assigned ++ e.assigned
  -- (Making a lambda assigns nothing; running one, only its own locals.)
  | .callProc f args => f.assigned ++ assignedArgs args
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

/-- A block's signature with the parameters it names substituted. -/
def BlockSig.subst (as : List Ty) (sig : BlockSig) : BlockSig :=
  ⟨sig.params.map (·.subst as), sig.ret.subst as⟩

/-- What a method may run a block with (`sig`), given the signature the
block was checked against (`sig'`): the values it gives are of the
block's parameters' types, and what the block gives back is of the
result it takes. -/
def BlockSig.le (ct : ClassTable) (sig sig' : BlockSig) : Prop :=
  sig.params.length = sig'.params.length ∧
  (∀ (i : Nat) (t t' : Ty), sig.params[i]? = some t → sig'.params[i]? = some t' → t.le ct [] t' = true) ∧
  sig'.ret.le ct [] sig.ret = true

/-- `BlockSig.le` on a method's optional block. -/
def BlockSig.optLe (ct : ClassTable) : Option BlockSig → Option BlockSig → Prop
  | none, none => True
  | some a, some b => BlockSig.le ct a b
  | _, _ => False

/-- A method's signature with its owner's parameters substituted (as a
receiver of class `c` given `as` sees it). -/
def Method.inst (mt : Method) (as : List Ty) : Method :=
  { mt with
    params := mt.params.map fun (x, t) => (x, t.subst as),
    ret := mt.ret.subst as,
    block := mt.block.map (BlockSig.subst as) }

/-- The method `m` run on an instance of `c` given `as`, as that
receiver sees its signature. -/
def Program.lookupAt (P : Program) (c : Nat) (as : List Ty) (m : String) : Option Method :=
  (P.lookup c m).bind fun mt => (P.classes.ancestorArgs c as mt.owner).map mt.inst

/-- A type with each parameter replaced by its bound's atoms (in `κ`):
what a value of it is, for finding the methods a call may run. -/
def Ty.expand (κ : List Ty) (t : Ty) : Ty := t.flatMap fun a => match a with
  | .param i => Ty.boundOf κ i
  | a => [a]

/-- The methods a call of `m` on a receiver of type `t` may run, one per
atom (each must be a class that has it: `nil` has no methods). -/
def Program.resolve (P : Program) (κ : List Ty) (t : Ty) (m : String) : Option (List Method) :=
  -- `initialize` runs from `new` only: called again, it would assign a
  -- made object's immutable fields.
  if m == "initialize" then none else
  -- A parameter's methods are its bound's (`T <: Shape`).
  (Ty.expand κ t).mapM fun
    -- `Object` holds the value classes' values too, which have no
    -- methods in v1.
    -- A procedures' class has none either (its values are procedures).
    | .cls c as => if c == 0 || P.classes.kindOf c == .proc then none else P.lookupAt c as m
    | _ => none

/-- Narrowing a path (design §2.1): `p` holds `t` where the test is
true. An empty type means control does not get there. -/
def narrow (Γ : Env) (p : Path) (t : Ty) : Option Env :=
  if t.isEmpty then none else some (Γ.set p t)

/-- The class of an atom's values, if it is a class. -/
def Atom.classOf : Atom → Option Nat
  | .cls c _ => some c
  | _ => none

/-- `a`'s class and `b`'s are related, one below the other (the arguments
aside: what the run-time test sees). -/
def Atom.classRelated (ct : ClassTable) (a b : Atom) : Bool :=
  match a.classOf, b.classOf with
  | some c, some d => ct.subclass c d || ct.subclass d c
  | _, _ => false

/-- The variants of enum `e`: the classes it is the superclass of. -/
def ClassTable.variantsOf (ct : ClassTable) (e : Nat) : List Nat :=
  (List.range ct.length).filter fun i => ((ct[i]?).bind (·.super)) == some e

/-- A type with each `enum` (without arguments) replaced by its variants:
what a value of it is, as no object is of an `enum` itself. -/
def Ty.expandEnums (ct : ClassTable) (t : Ty) : Ty := t.flatMap fun a => match a with
  | .cls c [] => if ct.kindOf c == .enumC then (ct.variantsOf c).map (.cls · []) else [a]
  | a => [a]

/-- `is_a?` false: the atoms not below the class, an `enum` as its
variants (so that a `case/in` covering them leaves nothing). -/
def isAFalse (ct : ClassTable) (t : Ty) (a : Atom) : Ty :=
  (Ty.expandEnums ct t).filter fun b => !(b.le ct [] a)

/-- A class without type arguments. -/
def Atom.bare : Atom → Bool
  | .cls _ [] => true
  | _ => false

/-- The table of design §2.1 for one test of a path holding `t`: the
atoms below `a` stay, and `a` itself comes in where `t` has an atom
above it, one of a class related to `a`'s (the arguments may be the
class's parameters, which the run-time class test does not see), or a
type parameter: the value is an `a`, whatever `T` is (unless that atom
is below `a` already, kept as it is). A related atom with closed
arguments does not bring in an `a` without arguments: a value of both
would make one below the other (`Box[String]` and `IntBox <
Box[Int]`). -/
def isATrueOn (ct : ClassTable) (t : Ty) (a : Atom) : Ty :=
  t.filter (·.le ct [] a) ++
    (if t.any (fun b => (a.le ct [] b && a != b) ||
        (((a.classRelated ct b && !(b.closed && a.bare)) || b.isParam) && !(b.le ct [] a)))
      then [a] else [])

/-- `is_a?` true, an `enum` as its variants (as on the false side, and as
the Rust checker's `split_by_type`). -/
def isATrue (ct : ClassTable) (t : Ty) (a : Atom) : Ty :=
  isATrueOn ct (Ty.expandEnums ct t) a

/-- A class test's atom: a class of the table given as many arguments as
it has parameters (or a value class). -/
def Atom.wf (ct : ClassTable) : Atom → Bool
  | .cls c args => match ct[c]? with
    | some k => args.length == k.params.length
    | none => false
  | .param _ => false
  | _ => true

/-- `C[Object, ...]`, every parameter of `C` covariant (or none): what
every instance of `C` is (docs/02 §7), so the run-time test of the class
alone checks it. -/
def objectArgs (ct : ClassTable) (c : Nat) (args : List Ty) : Bool :=
  args.length == (ct.variances c).length &&
  (args.zip (ct.variances c)).all fun (t, v) => t == [.cls 0 []] && v == .co

/-- Whether `is_a?(a)` can be checked at run time for a value of type `t`
(docs/02 §7): the run-time test sees the class only, so a class with
arguments is allowed when each atom of `t` that may pass it is already
of the class with those arguments (an atom of the class or a subclass
whose chain gives arguments below them), or every instance is
(`objectArgs`: `Object` arguments for covariant parameters, or a class
without parameters). -/
def verifiable (ct : ClassTable) (t : Ty) (a : Atom) : Bool :=
  match a with
  | .cls c args =>
    t.all fun b => match b with
      -- An atom of the class or a subclass: arguments below. One of a
      -- superclass (`Object` included) or a parameter: the arguments are
      -- not known at run time, so only arguments every instance has
      -- (`objectArgs`: a class without parameters, or `Object` for
      -- covariant ones). An unrelated class never passes the test.
      | .cls d bs => if ct.subclass d c then
          match ct.ancestorArgs d bs c with
          | some as' => argsLeWith (Atom.le ct []) (ct.variances c) as' args || objectArgs ct c args
          | none => false
        else objectArgs ct c args || !ct.subclass c d
      | .param _ => objectArgs ct c args
      | _ => true
  | _ => true

/-- `test` gives the types where it is true and false; a test of an
expression that is not a path narrows nothing. -/
def testOut (c : Ctx) (e : Expr) (Γ : Env) (tyT tyF : Ty → Ty) : Out :=
  match e.path?.bind fun p => (c.pathTy Γ p).map (p, ·) with
  | some (p, t) => ⟨[.bool], some Γ, narrow Γ p (tyT t), narrow Γ p (tyF t)⟩
  | none => Out.plain [.bool] Γ

/-- The truthy and falsy sides of a read holding `u` (design §2.1). A type
parameter stays on both sides: what it stands for may hold `nil` or
`false`. -/
def truthyTy (u : Ty) : Ty := u.remove .nil

/-- The falsy values a type holds: `nil` and `false` where it holds
them (`Object` does, as every value class), and its parameters. -/
def falsyTy (ct : ClassTable) (u : Ty) : Ty :=
  u.filter Atom.isParam ++ [.nil, .bool].filter fun a => Ty.le ct [] [a] u

/-- What a value of `u` found to be `nil` is: `nil`, if `u` holds it or
has a parameter (whose instantiation may). -/
def nilTy (ct : ClassTable) (u : Ty) : Ty :=
  if u.any Atom.isParam || Ty.le ct [] [.nil] u then [.nil] else []

/-- An atom whose values compare with `nil`, `true` and `false` by the
built-in `==`, and which nothing subclasses: a value class, or a `data`
type without type arguments that defines no `==` (docs/02 §6). -/
def Atom.finalIn (P : Program) : Atom → Bool
  | .cls c [] => (P.classes.kindOf c == .data || P.classes.kindOf c == .variant) &&
      (P.lookup c "==").isNone
  | a => a.final

def Ty.allFinalIn (P : Program) (t : Ty) : Bool := t.all (Atom.finalIn P)

/-- Whether `==` against `nil`, `true` or `false` may narrow what `e`
reads in `Δ`: only a value no subclass can redefine `==` for. -/
def finalRead (c : Ctx) (Δ : Env) (e : Expr) : Bool :=
  (e.path?.bind (c.pathTy Δ)).all (Ty.allFinalIn c.prog)

/-- The block's starting environment: what it may assign un-narrowed,
its parameters given. -/
def blockEnv (c : Ctx) (Δ : Env) (ps : List String) (sig : BlockSig) (body : Expr) : Env :=
  (ps.zip sig.params).foldl (fun g (x, t) => g.set (.local x) t) (c.reset Δ (ps ++ body.assigned))

/-- A lambda's own locals (parameters first): distinct, none a local of
the method; its body assigns only them (C0: no captured local). -/
def Ctx.lambdaOk (c : Ctx) (ps own : List (String × Ty)) (body : Expr) : Bool :=
  decide ((ps ++ own).map (·.1)).Nodup &&
  ((ps ++ own).all fun (x, _) => (c.meth.locals.find? (·.1 == x)).isNone) &&
  (body.assigned.all fun x => (ps ++ own).any (·.1 == x))

/-- A lambda's body is checked as a block of its method with the
lambda's parameters and own locals added, no block and no `return`. -/
def Ctx.lambdaCtx (c : Ctx) (ps own : List (String × Ty)) : Ctx :=
  { c with inBlock := true, meth := { c.meth with locals := ps ++ own ++ c.meth.locals, block := none } }

/-- The locals `Γ` has (assigned), each as declared. -/
def Ctx.declEnv (c : Ctx) (Γ : Env) : Env :=
  Γ.filterMap fun (p, _) => match p with
    | .local x => (c.decl x).map ((Path.local x), ·)
    | .field _ => none

/-- Where a lambda's body starts: the locals assigned where it is made,
as declared (R2a: it may run when they hold other values), no field
narrowed (read as declared), its parameters as declared. -/
def Ctx.lambdaEnv (c : Ctx) (Γ : Env) (ps : List (String × Ty)) : Env :=
  ps.foldl (fun g (x, t) => g.set (.local x) t) (c.declEnv Γ)

/-- The block's parameters are its method's locals, distinct, declared at
least as wide as what `yield` gives. -/
def blockParamsOk (c : Ctx) (ps : List String) (sig : BlockSig) : Bool :=
  ps.length == sig.params.length && decide ps.Nodup &&
  (ps.zip sig.params).all fun (x, t) => match c.decl x with
    | some d => t.le c.ct c.bounds d
    | none => false

/-- `k[targs]` is a class with as many parameters, each argument naming
only the class's own parameters (no bounds yet). -/
def Ctx.argsWf (c : Ctx) (k : Nat) (targs : List Ty) : Bool :=
  match c.ct[k]? with
  | some cl => targs.length == cl.params.length && Ty.argsParamsBelow c.selfArgs.length targs &&
      -- Each argument within its parameter's bound.
      (targs.zipIdx.all fun (t, i) => t.le c.ct c.bounds (Ty.boundOf cl.bounds i)) &&
      -- No object is of an `enum` itself, nor of a procedures' class.
      cl.kind != .enumC && cl.kind != .proc
  | none => false

/-- The argument types fit the method's parameters. -/
def argsOk (c : Ctx) (tys : List Ty) (mt : Method) : Bool :=
  tys.length == mt.params.length && (tys.zip mt.params).all fun (t, (_, u)) => t.le c.ct c.bounds u

mutual

/-- `check c Γ e`: `e` checked where `Γ` holds; `none` if it is rejected. -/
def check (c : Ctx) (Γ : Env) : Expr → Option Out
  | .nil => some (.plain [.nil] Γ)
  | .tru | .fls => some (.plain [.bool] Γ)
  | .int _ => some (.plain [.int] Γ)
  | .str _ => some (.plain [.str] Γ)
  | .flt _ => some (.plain [.float] Γ)
  | .var x t => do
    -- The annotation: at least what the local holds here.
    let u ← Γ.get (.local x)
    guard (u.le c.ct c.bounds t)
    some ⟨t, some Γ, narrow Γ (.local x) (truthyTy u),
      narrow Γ (.local x) (falsyTy c.ct u)⟩
  | .field f t => do
    let fd ← c.field? f
    -- In `initialize`, only a field already set (docs/01 §3).
    guard (!c.inInit || (Γ.get (.field f)).isSome)
    if fd.var then
      guard (fd.ty.le c.ct c.bounds t)
      some (.plain t Γ)
    else
      let u := (Γ.get (.field f)).getD fd.ty
      guard (u.le c.ct c.bounds t)
      some ⟨t, some Γ, narrow Γ (.field f) (truthyTy u),
        narrow Γ (.field f) (falsyTy c.ct u)⟩
  | .assign x e => do
    let o ← check c Γ e
    let d ← c.decl x
    guard (o.ty.le c.ct c.bounds d)
    match o.out with
    | none => some .dead
    | some Δ => some (.plain o.ty (Δ.set (.local x) o.ty))
  | .setField f e => do
    let fd ← c.field? f
    -- An immutable field only in `initialize` (not in a block of it).
    guard (fd.var || (c.inInit && !c.inBlock))
    let o ← check c Γ e
    guard (o.ty.le c.ct c.bounds fd.ty)
    match o.out with
    | none => some .dead
    | some Δ => some (.plain o.ty (if c.inInit then Δ.set (.field f) (if fd.var then fd.ty else o.ty)
        else Δ))
  | .self => do
    -- The object is used: in `initialize`, every field set; never in a
    -- default.
    guard (!c.inDefault && (!c.inInit || c.allSet Γ))
    some (.plain c.selfTy Γ)
  | .new k targs args => do
    guard (c.argsWf k targs)
    match checkArgs c Γ args with
    | none => none
    | some .dead => some .dead
    | some (.live tys Δ) =>
      -- Its `initialize`'s arguments (none without one), as the class
      -- given `targs` sees them.
      match c.prog.lookupAt k targs "initialize" with
      | some mt =>
        guard (mt.block.isNone && argsOk c tys mt)
        some (.plain [.cls k targs] Δ)
      | none =>
        guard tys.isEmpty
        some (.plain [.cls k targs] Δ)
  | .superInit d args => do
    guard (c.superOk d Γ)
    match checkArgs c Γ args with
    | none => none
    | some .dead => some .dead
    | some (.live tys Δ) =>
      match c.prog.lookupAt d (c.superArgs d) "initialize" with
      | some mt =>
        guard (mt.block.isNone && argsOk c tys mt)
        some (.plain [.nil] (c.afterSuper Δ))
      | none =>
        guard tys.isEmpty
        some (.plain [.nil] (c.afterSuper Δ))
  | .call r m args => do
    let o ← check c Γ r
    match o.out with
    | none => some .dead
    | some Δ =>
      match checkArgs c Δ args with
      | none => none
      | some .dead => some .dead
      | some (.live tys Δ') =>
        let ms ← c.prog.resolve c.bounds o.ty m
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
        let ms ← c.prog.resolve c.bounds o.ty m
        let mt ← ms.head?
        let sig ← mt.block
        guard (ms.all fun mt' => mt'.block == some sig && argsOk c tys mt')
        guard (blockParamsOk c ps sig)
        -- The block runs 0 or more times, during the call: its body starts
        -- with what it assigns un-narrowed, its parameters given.
        let ob ← check { c with inBlock := true } (blockEnv c Δ' ps sig body) body
        guard (ob.ty.le c.ct c.bounds sig.ret)
        -- After the call, what the block assigns un-narrowed: it may have
        -- stopped anywhere (an exception the method rescued), as the Rust
        -- checker has it.
        some (.plain (ms.flatMap (·.ret)) (c.reset Δ' (ps ++ body.assigned)))
  | .yield args => do
    let sig ← c.meth.block
    match checkArgs c Γ args with
    | none => none
    | some .dead => some .dead
    | some (.live tys Δ) =>
      guard (tys.length == sig.params.length &&
        (tys.zip sig.params).all fun (t, u) => t.le c.ct c.bounds u)
      some (.plain sig.ret Δ)
  | .prim _ args params ret => do
    match checkArgs c Γ args with
    | none => none
    | some .dead => some .dead
    | some (.live tys Δ) =>
      guard (tys.length == params.length &&
        (tys.zip params).all fun (t, u) => t.le c.ct c.bounds u)
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
    guard (o.ty.le c.ct c.bounds c.meth.ret)
    -- An `initialize` returns only once every field is set.
    guard (!c.inInit || (o.out.all (c.allSet ·)))
    some .dead
  | .raise e => do
    let o ← check c Γ e
    -- An exception: a value of the program's exception class.
    guard (o.ty.le c.ct c.bounds [.cls c.prog.exn []])
    some .dead
  | .lambda ps own ret body => do
    guard (!c.inInit && !c.inDefault)
    let k ← c.prog.procClass ps.length
    guard ((c.ct[k]?).map (·.params.length) == some (ps.length + 1))
    -- Its own locals (parameters first): distinct, none a local of the
    -- method; the body assigns only them (C0: no captured local).
    guard (c.lambdaOk ps own body)
    -- It may run any time later: the captured locals as declared (R2a),
    -- its parameters as declared; no block (`yield` is an error in it),
    -- no `return` (`inBlock`).
    let ob ← check (c.lambdaCtx ps own) (c.lambdaEnv Γ ps) body
    guard (ob.ty.le c.ct c.bounds ret)
    some (.plain [.cls k (ps.map (·.2) ++ [ret])] Γ)
  | .callProc f args => do
    let o ← check c Γ f
    match o.out with
    | none => some .dead
    | some Δ =>
      match checkArgs c Δ args with
      | none => none
      | some .dead => some .dead
      | some (.live tys Δ') =>
        -- A procedure of exactly that class: its parameters, its result.
        -- It writes none of this frame's locals.
        match o.ty with
        | [.cls k as] =>
          guard (c.prog.procClass (as.length - 1) == some k && as.length == tys.length + 1)
          guard ((tys.zip as).all fun (t, u) => t.le c.ct c.bounds u)
          some (.plain (as.getLast?.getD []) Δ')
        | _ => none
  | .rescue b x h els => do
    -- Not in `initialize` or a default (fields being set: design §12.6 Q3).
    guard (!c.inInit && !c.inDefault)
    guard (c.decl x == some [.cls c.prog.exn []])
    let ob ← check c Γ b
    let oe ← checkBranch c ob.out els
    -- The handler: raised anywhere in the body, so with what it assigns
    -- un-narrowed; the exception in `x`.
    let oh ← check c ((c.reset Γ b.assigned).set (.local x) [.cls c.prog.exn []]) h
    some ⟨oe.ty ++ oh.ty, ojoin oe.out oh.out, ojoin oe.tt oh.tt, ojoin oe.ff oh.ff⟩
  | .ensure b e => do
    guard (!c.inInit && !c.inDefault)
    let ob ← check c Γ b
    -- It runs however the body ends: with what the body assigns
    -- un-narrowed.
    let oe ← check c (c.reset Γ b.assigned) e
    match oe.out with
    | none => some .dead
    | some Δe =>
      let g := ob.out.map (·.takeFrom Δe e.assigned)
      some ⟨ob.ty, g, g, g⟩
  -- Only where control cannot get (a dead branch is not checked).
  | .absurd => none
  | .isNil e => do
    let o ← check c Γ e
    match o.out with
    | none => some .dead
    | some Δ => some (testOut c e Δ (nilTy c.ct) (·.remove .nil))
  | .isA e a => do
    let o ← check c Γ e
    match o.out with
    | none => some .dead
    | some Δ =>
      -- A class test checks the class only: its arguments must follow
      -- from the static type (docs/02 §7).
      guard (a.closed && a.wf c.ct && verifiable c.ct o.ty a)
      some (testOut c e Δ (isATrue c.ct · a) (isAFalse c.ct · a))
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
