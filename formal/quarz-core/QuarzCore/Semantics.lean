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

An object records which of its fields are set: reading one that is not
is stuck, so that a field read before `initialize` assigns it is a run
the soundness theorem rules out.
-/

import QuarzCore.Typing

namespace QuarzCore

inductive Value where
  | nil
  | bool (b : Bool)
  | int (n : Int)
  | str (s : String)
  | flt (s : String)
  /-- An object, by its index in the store's `objs`. -/
  | obj (l : Nat)
  deriving DecidableEq, Repr, Inhabited

def Value.truthy : Value → Bool
  | .nil | .bool false => false
  | _ => true

/-- An object: its class with the type arguments it was made with (ghost:
nothing in the program reads them; the interpreter's checks and the
soundness invariants do), and its fields' values (`ClassTable.allFields`
order). -/
structure Obj where
  cls : Nat
  args : List Ty := []
  fields : List Value
  /-- Which fields hold a value: all once the object is made (a field
  with no default that admits `nil` holds it from the start, one with a
  default once that ran, the others once `initialize` assigned them). -/
  set : List Bool
  deriving Repr, Inhabited

structure Store where
  locs : List Value
  objs : List Obj
  deriving Repr, Inhabited

/-- An anonymous block, closed over the frame it is written in (the
names of that method's locals, `self`, and that method's own block, for
a `yield` in it), with its parameters and body. -/
inductive Closure where
  | mk (vars : List (String × Nat)) (self : Value) (selfArgs : List Ty) (outer : Option Closure)
      (params : List String) (body : Expr)
  deriving Repr, Inhabited

/-- A method's activation: its locals' locations, `self`, and the
arguments `self`'s class gives the method's owner (what the owner's
type parameters stand for here, closed), and the block it was given. -/
structure Frame where
  vars : List (String × Nat)
  self : Value
  selfArgs : List Ty := []
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

/-- A value's atom: its class (an object's is its run-time class). An
object still being made (a field not set yet) has none: no value of it
may go anywhere but its `initialize`'s `self`. -/
def typeOf (s : Store) : Value → Option Atom
  | .nil => some .nil
  | .bool _ => some .bool
  | .int _ => some .int
  | .str _ => some .str
  | .flt _ => some .float
  | .obj l => (s.objs[l]?).bind fun o => if o.set.all id then some (.cls o.cls o.args) else none

def hasType (ct : ClassTable) (s : Store) (v : Value) (t : Ty) : Bool :=
  match s.typeOf v with
  | some a => Ty.le ct [a] t
  | none => false

def setLoc (s : Store) (l : Nat) (v : Value) : Store := { s with locs := s.locs.set l v }

def setField (s : Store) (l i : Nat) (v : Value) : Store :=
  { s with objs := s.objs.modify l fun o => { o with fields := o.fields.set i v, set := o.set.set i true } }

/-- The names at consecutive locations from `base`. -/
def allocVars : Nat → List String → List (String × Nat)
  | _, [] => []
  | base, x :: xs => (x, base) :: allocVars (base + 1) xs

/-- Fresh locations, one per name, holding `nil`. -/
def alloc (s : Store) (names : List String) : Store × List (String × Nat) :=
  (⟨s.locs ++ names.map fun _ => .nil, s.objs⟩, allocVars s.locs.length names)

end Store

/-- The arguments object `l`'s class gives its ancestor `d` (the owner
of a method run on it): what `d`'s parameters stand for. -/
def Store.argsFor (s : Store) (ct : ClassTable) (l : Nat) (d : Nat) : List Ty :=
  ((s.objs[l]?).bind fun o => ct.ancestorArgs o.cls o.args d).getD []

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
    | .flt t => .ok (.flt t) s
    | .var x t =>
      match (lookupVar fr.vars x).bind (s.locs[·]?) with
      | some v => if s.hasType P.classes v (t.subst fr.selfArgs) then .ok v s else .stuck
      | none => .stuck
    | .assign x e => (eval P orc n fr s e).bind fun v s =>
      match lookupVar fr.vars x with
      | some l => .ok v (s.setLoc l v)
      | none => .stuck
    | .field f t =>
      match fr.self with
      | .obj l => match s.objs[l]? with
        | some o => match (fieldIndex P.classes o.cls f).bind fun i =>
            if o.set[i]? = some true then o.fields[i]? else none with
          | some v => if s.hasType P.classes v (t.subst fr.selfArgs) then .ok v s else .stuck
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
    | .new k targs args => match evalArgs P orc n fr s args with
      | .other r => r
      | .ok vs s => construct P orc n s k (Ty.substArgs fr.selfArgs targs) vs
    | .superInit d args => match evalArgs P orc n fr s args with
      | .other r => r
      | .ok vs s => match P.lookup d "initialize" with
        | some mt =>
          if vs.length != mt.params.length then .stuck else
          let (s, vars) := s.alloc (mt.locals.map (·.1))
          match fr.self, bindAll s vars (mt.params.map (·.1)) vs with
          | .obj l, some s =>
            match eval P orc n ⟨vars, fr.self, s.argsFor P.classes l mt.owner, none⟩ s mt.body with
            | .ok _ s | .returned _ s => .ok .nil s
            | r => r
          | _, _ => .stuck
        | none => if vs.isEmpty then .ok .nil s else .stuck
    | .call r m args => (eval P orc n fr s r).bind fun v s =>
      match evalArgs P orc n fr s args with
      | .other r => r
      | .ok vs s => send P orc n s v m vs none
    | .callBlk r m args ps body => (eval P orc n fr s r).bind fun v s =>
      match evalArgs P orc n fr s args with
      | .other r => r
      | .ok vs s => send P orc n s v m vs (some (.mk fr.vars fr.self fr.selfArgs fr.blk ps body))
    | .yield args => match evalArgs P orc n fr s args with
      | .other r => r
      | .ok vs s => match fr.blk with
        | some clo => runBlock P orc n s clo vs
        | none => .stuck
    | .prim _ args _ ret => match evalArgs P orc n fr s args with
      | .other r => r
      | .ok _ s => match orc n s (ret.subst fr.selfArgs) with
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
    -- A class test sees the class, not the arguments (erased).
    | .isA e a => (eval P orc n fr s e).bind fun v s =>
      match s.typeOf v, a with
      | some (.cls c _), .cls d _ => .ok (.bool (P.classes.subclass c d)) s
      | some u, _ => .ok (.bool (u.le P.classes a)) s
      | none, _ => .stuck
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
        | some s =>
          match eval P orc n ⟨vars, recv, s.argsFor P.classes l mt.owner, blk⟩ s mt.body with
          | .ok v s | .returned v s => .ok v s
          | r => r
        | none => .stuck
      | none => .stuck
    | _ => .stuck

/-- Run a block with the values `yield` gives it. A `return` in a block
is not in v1. -/
def runBlock (P : Program) (orc : Oracle) : Nat → Store → Closure → List Value → Result
  | 0, _, _, _ => .timeout
  | n + 1, s, .mk vars self selfArgs outer ps body, vs =>
    match bindAll s vars ps vs with
    | some s => match eval P orc n ⟨vars, self, selfArgs, outer⟩ s body with
      | .returned _ _ => .stuck
      | r => r
    | none => .stuck

/-- `C[targs].new(args)`: a new object of `C` given `targs` (closed), its
fields' defaults run in order, then its class's `initialize` (a field
that admits `nil` and has no default holds it from the start; the
others are set by their default or by `initialize`). -/
def construct (P : Program) (orc : Oracle) : Nat → Store → Nat → List Ty → List Value → Result
  | 0, _, _, _, _ => .timeout
  | n + 1, s, k, targs, vs =>
    let fs := P.classes.allFieldsAt k targs
    let l := s.objs.length
    let s := { s with objs := s.objs ++ [⟨k, targs, fs.map fun _ => .nil,
      fs.map fun f => f.default.isNone && Ty.le P.classes [.nil] f.ty⟩] }
    match runDefaults P orc n s l fs.zipIdx with
    | .ok _ s => match P.lookup k "initialize" with
      | some mt =>
        if vs.length != mt.params.length then .stuck else
        let (s, vars) := s.alloc (mt.locals.map (·.1))
        match bindAll s vars (mt.params.map (·.1)) vs with
        | some s =>
          match eval P orc n ⟨vars, .obj l, s.argsFor P.classes l mt.owner, none⟩ s mt.body with
          | .ok _ s | .returned _ s => .ok (.obj l) s
          | r => r
        | none => .stuck
      | none => if vs.isEmpty then .ok (.obj l) s else .stuck
    | .returned _ _ => .stuck
    | r => r

/-- The defaults of the fields `fs` (with their indices) of object `l`,
in order, each run with `self` the object. -/
def runDefaults (P : Program) (orc : Oracle) : Nat → Store → Nat → List (Field × Nat) → Result
  | _, s, _, [] => .ok .nil s
  | 0, _, _, _ :: _ => .timeout
  | n + 1, s, l, (f, i) :: rest => match f.default with
    | none => runDefaults P orc n s l rest
    | some d => match P.defaults[d]? with
      | some e => (eval P orc n ⟨[], .obj l, s.argsFor P.classes l (((s.objs[l]?).map (·.cls)).getD 0), none⟩ s e).bind fun v s =>
        runDefaults P orc n (s.setField l i v) l rest
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
  let (s, vars) := Store.alloc ⟨[], [⟨P.main.owner, [], [], []⟩]⟩ (P.main.locals.map (·.1))
  match eval P orc fuel ⟨vars, .obj 0, [], none⟩ s P.main.body with
  | .returned v s => .ok v s
  | r => r

end QuarzCore
