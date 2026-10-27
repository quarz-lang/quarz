/-
QCore's semantics (design §3): a definitional interpreter with fuel
(Amin and Rompf, "Type Soundness Proofs with Definitional Interpreters",
POPL 2017). `eval n fr s e` runs `e` in frame `fr` on store `s` with `n`
steps of fuel; it gives a value, an exception being raised, a `return`
on its way to the method's end, `timeout` (out of fuel: a loop that does
not end) or `stuck`: what a type error would be, and what a checked
program must never do (Soundness.lean). Every recursive call takes one
less unit of fuel, so the recursion is structural.

Locals live in the store (`locs`) and frames map names to locations, so
that a block, which runs in the frame it is written in while the method
it is given to runs, assigns its method's locals there.
-/

import QuarzCore.Typing

namespace QuarzCore

inductive Value where
  | nil
  | bool (b : Bool)
  | int (n : Int)
  | str (s : String)
  /-- An object, by its index in the store's `objs`. -/
  | obj (l : Nat)
  deriving DecidableEq, Repr, Inhabited

def Value.truthy : Value → Bool
  | .nil | .bool false => false
  | _ => true

/-- An object: its class and its fields' values (`ClassTable.allFields`
order). -/
structure Obj where
  cls : Nat
  fields : List Value
  deriving Repr, Inhabited

structure Store where
  locs : List Value
  objs : List Obj
  deriving Repr, Inhabited

/-- An anonymous block, closed over the frame it is written in (the
names of that method's locals, `self`, and that method's own block, for
a `yield` in it), with its parameters and body. -/
inductive Closure where
  | mk (vars : List (String × Nat)) (self : Value) (outer : Option Closure)
      (params : List String) (body : Expr)
  deriving Repr, Inhabited

structure Frame where
  vars : List (String × Nat)
  self : Value
  blk : Option Closure
  deriving Repr, Inhabited

inductive Result where
  | ok (v : Value) (s : Store)
  | raised (s : Store)
  | returned (v : Value) (s : Store)
  | timeout
  | stuck
  deriving Repr, Inhabited

namespace Store

/-- A value's atom: its class (an object's is its run-time class). -/
def typeOf (s : Store) : Value → Option Atom
  | .nil => some .nil
  | .bool _ => some .bool
  | .int _ => some .int
  | .str _ => some .str
  | .obj l => (s.objs[l]?).map fun o => .cls o.cls

def hasType (ct : ClassTable) (s : Store) (v : Value) (t : Ty) : Bool :=
  match s.typeOf v with
  | some a => Ty.le ct [a] t
  | none => false

def setLoc (s : Store) (l : Nat) (v : Value) : Store := { s with locs := s.locs.set l v }

def setField (s : Store) (l i : Nat) (v : Value) : Store :=
  { s with objs := s.objs.modify l fun o => { o with fields := o.fields.set i v } }

/-- The names at consecutive locations from `base`. -/
def allocVars : Nat → List String → List (String × Nat)
  | _, [] => []
  | base, x :: xs => (x, base) :: allocVars (base + 1) xs

/-- Fresh locations, one per name, holding `nil`. -/
def alloc (s : Store) (names : List String) : Store × List (String × Nat) :=
  (⟨s.locs ++ names.map fun _ => .nil, s.objs⟩, allocVars s.locs.length names)

end Store

def lookupVar (vars : List (String × Nat)) (x : String) : Option Nat :=
  (vars.find? (·.1 == x)).map (·.2)

/-- Bind the values to the names' locations, in order. -/
def bindAll (s : Store) (vars : List (String × Nat)) : List String → List Value → Option Store
  | [], [] => some s
  | x :: xs, v :: vs => do
    let l ← lookupVar vars x
    bindAll (s.setLoc l v) vars xs vs
  | _, _ => none

/-- The index of field `f` in instances of `c`. -/
def fieldIndex (ct : ClassTable) (c : Nat) (f : String) : Option Nat :=
  (ct.allFields c).findIdx? (·.name == f)

/-- What `eval` gives on to the code after an expression that did not
end with a value (an exception, a `return`, no fuel left, stuck). -/
def Result.bind (r : Result) (k : Value → Store → Result) : Result :=
  match r with
  | .ok v s => k v s
  | .raised s => .raised s
  | .returned v s => .returned v s
  | .timeout => .timeout
  | .stuck => .stuck

/-- What the built-in methods (`Expr.prim`) give: a value of the type
asked for (Soundness.lean assumes no more), or `none`: an exception. The
fuel left is a seed for random tests. -/
abbrev Oracle := Nat → Store → Ty → Option Value

/-- The arguments' values, or how their evaluation ended. -/
inductive ArgsResult where
  | ok (vs : List Value) (s : Store)
  | other (r : Result)
  deriving Inhabited

mutual

def eval (P : Program) (orc : Oracle) : Nat → Frame → Store → Expr → Result
  | 0, _, _, _ => .timeout
  | n + 1, fr, s, e => match e with
    | .nil => .ok .nil s
    | .tru => .ok (.bool true) s
    | .fls => .ok (.bool false) s
    | .int k => .ok (.int k) s
    | .str t => .ok (.str t) s
    | .var x t =>
      match (lookupVar fr.vars x).bind (s.locs[·]?) with
      | some v => if s.hasType P.classes v t then .ok v s else .stuck
      | none => .stuck
    | .assign x e => (eval P orc n fr s e).bind fun v s =>
      match lookupVar fr.vars x with
      | some l => .ok v (s.setLoc l v)
      | none => .stuck
    | .field f t =>
      match fr.self with
      | .obj l => match s.objs[l]? with
        | some o => match (fieldIndex P.classes o.cls f).bind (o.fields[·]?) with
          | some v => if s.hasType P.classes v t then .ok v s else .stuck
          | none => .stuck
        | none => .stuck
      | _ => .stuck
    | .setField f e => (eval P orc n fr s e).bind fun v s =>
      match fr.self with
      | .obj l => match (s.objs[l]?).bind fun o => fieldIndex P.classes o.cls f with
        | some i => .ok v (s.setField l i v)
        | none => .stuck
      | _ => .stuck
    | .self => .ok fr.self s
    | .new k args => match evalArgs P orc n fr s args with
      | .other r => r
      | .ok vs s =>
        if vs.length == (P.classes.allFields k).length then
          .ok (.obj s.objs.length) { s with objs := s.objs ++ [⟨k, vs⟩] }
        else .stuck
    | .call r m args => (eval P orc n fr s r).bind fun v s =>
      match evalArgs P orc n fr s args with
      | .other r => r
      | .ok vs s => send P orc n s v m vs none
    | .callBlk r m args ps body => (eval P orc n fr s r).bind fun v s =>
      match evalArgs P orc n fr s args with
      | .other r => r
      | .ok vs s => send P orc n s v m vs (some (.mk fr.vars fr.self fr.blk ps body))
    | .yield args => match evalArgs P orc n fr s args with
      | .other r => r
      | .ok vs s => match fr.blk with
        | some clo => runBlock P orc n s clo vs
        | none => .stuck
    | .prim _ args _ ret => match evalArgs P orc n fr s args with
      | .other r => r
      | .ok _ s => match orc n s ret with
        | some v => .ok v s
        | none => .raised s
    | .seq a b => (eval P orc n fr s a).bind fun _ s => eval P orc n fr s b
    | .ite c t e => (eval P orc n fr s c).bind fun v s =>
      if v.truthy then eval P orc n fr s t else eval P orc n fr s e
    | .while c b => (eval P orc n fr s c).bind fun v s =>
      if v.truthy then (eval P orc n fr s b).bind fun _ s => eval P orc n fr s (.while c b)
      else .ok .nil s
    | .ret e => match eval P orc n fr s e with
      | .ok v s => .returned v s
      | r => r
    | .raise => .raised s
    | .isNil e => (eval P orc n fr s e).bind fun v s => .ok (.bool (v == .nil)) s
    | .isA e a => (eval P orc n fr s e).bind fun v s =>
      match s.typeOf v with
      | some u => .ok (.bool (u.le P.classes a)) s
      | none => .stuck
    | .eqNil e => (eval P orc n fr s e).bind fun v s => equal P orc n s v .nil
    | .neNil e => (eval P orc n fr s e).bind fun v s =>
      (equal P orc n s v .nil).bind fun r s => .ok (.bool (!r.truthy)) s
    | .eqTrue e => (eval P orc n fr s e).bind fun v s => equal P orc n s v (.bool true)
    | .eqFalse e => (eval P orc n fr s e).bind fun v s => equal P orc n s v (.bool false)
    | .and a b => (eval P orc n fr s a).bind fun v s =>
      if v.truthy then eval P orc n fr s b else .ok v s
    | .or a b => (eval P orc n fr s a).bind fun v s =>
      if v.truthy then .ok v s else eval P orc n fr s b
    | .not a => (eval P orc n fr s a).bind fun v s => .ok (.bool (!v.truthy)) s

/-- The arguments, left to right. -/
def evalArgs (P : Program) (orc : Oracle) : Nat → Frame → Store → List Expr → ArgsResult
  | _, _, s, [] => .ok [] s
  | 0, _, _, _ :: _ => .other .timeout
  | n + 1, fr, s, e :: es => match eval P orc n fr s e with
    | .ok v s => match evalArgs P orc n fr s es with
      | .ok vs s => .ok (v :: vs) s
      | .other r => .other r
    | r => .other r

/-- Call method `m` on `recv`: the one its run-time class has (a value
of a built-in class has none in v1). -/
def send (P : Program) (orc : Oracle) : Nat → Store → Value → String → List Value → Option Closure → Result
  | 0, _, _, _, _, _ => .timeout
  | n + 1, s, recv, m, vs, blk =>
    match recv with
    | .obj l => match (s.objs[l]?).bind fun o => P.lookup o.cls m with
      | some mt =>
        if vs.length != mt.params.length then .stuck else
        let (s, vars) := s.alloc (mt.locals.map (·.1))
        match bindAll s vars (mt.params.map (·.1)) vs with
        | some s => match eval P orc n ⟨vars, recv, blk⟩ s mt.body with
          | .ok v s | .returned v s => .ok v s
          | r => r
        | none => .stuck
      | none => .stuck
    | _ => .stuck

/-- Run a block with the values `yield` gives it. A `return` in a block
is not in v1. -/
def runBlock (P : Program) (orc : Oracle) : Nat → Store → Closure → List Value → Result
  | 0, _, _, _ => .timeout
  | n + 1, s, .mk vars self outer ps body, vs =>
    match bindAll s vars ps vs with
    | some s => match eval P orc n ⟨vars, self, outer⟩ s body with
      | .returned _ _ => .stuck
      | r => r
    | none => .stuck

/-- `v == w` against `nil`, `true` or `false`: an object whose class
defines `==` answers it (so a test of one tells nothing, 09b19e3);
otherwise it is identity. -/
def equal (P : Program) (orc : Oracle) : Nat → Store → Value → Value → Result
  | 0, _, _, _ => .timeout
  | n + 1, s, v, w =>
    match v with
    | .obj l => match (s.objs[l]?).bind fun o => P.lookup o.cls "==" with
      | some _ => send P orc n s v "==" [w] none
      | none => .ok (.bool false) s
    | _ => .ok (.bool (v == w)) s

end

/-- Run the program's top level. -/
def run (P : Program) (orc : Oracle) (fuel : Nat) : Result :=
  -- `self` is an instance of the top level's class (it has no fields).
  let (s, vars) := Store.alloc ⟨[], [⟨P.main.owner, []⟩]⟩ (P.main.locals.map (·.1))
  match eval P orc fuel ⟨vars, .obj 0, none⟩ s P.main.body with
  | .returned v s => .ok v s
  | r => r

end QuarzCore
