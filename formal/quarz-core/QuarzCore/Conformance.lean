/-
The differential test (design §5): a program the Rust checker accepted,
as `quarz check --tree` prints it, turned into a QCore program with the
types the Rust checker gave its reads as annotations, and checked by
the model. A program outside QCore's range is reported as such; one in
it that the model rejects is a disagreement to look at (the Rust checker
narrowing further than the rules allow, or the model being stricter).

What maps: user classes (subclasses of `Object`, their fields), the
top level and its methods (the file's main class is `Object` here), and
the methods' bodies: literals, locals and fields read and assigned,
`self`, calls (of a user method, a call; of a built-in one, or an
interpolation, a `prim` with the types the methods table declares),
`yield` and blocks, `if`, `while`, `return`, `raise`, `nil?`, `is_a?`,
`==`/`!=` against `nil`/`true`/`false`, `&&`, `||`, `!`, `Float` literals,
constants (not narrowed: a read of one is a value of its type, its
initializer checked as a method of the top level's class), `new` with
the fields' defaults and `initialize` (its `@x` parameters assigning
their fields first). A local's declared type is its first assignment's,
as the Rust checker's. Anything else puts the program out of range: so
do a node checked with different types (`varied_types`), a default with
locals, a `new` whose `initialize` (the Rust checker's choice among the
ancestors' overloads) is not the nearest one (`Program.lookup`), `super`
outside `initialize` or with a block, and required files. `super(args)`
in `initialize` is `superInit`, a bare `super` passing the parameters.
-/

import Lean.Data.Json
import QuarzCore.Program

namespace QuarzCore.Conformance

open Lean (Json)

abbrev M := Except String

def field (j : Json) (k : String) : M Json := j.getObjVal? k
def str (j : Json) : M String := j.getStr?
def nat (j : Json) : M Nat := j.getNat?
def arr (j : Json) : M (Array Json) := j.getArr?

/-- An enum variant in serde's external tagging: `"Nil"` or `{"Local":
"x"}`. -/
def variant (j : Json) : M (String × Json) :=
  match j with
  | .str s => pure (s, .null)
  | .obj kvs => match kvs.toList with
    | [(k, v)] => pure (k, v)
    | _ => throw "not a variant"
  | _ => throw "not a variant"

/-- What is known of the Rust program: its classes by Rust id. -/
structure Tables where
  /-- Rust class id ↦ (name, kind, file, superclass id, fields). -/
  classes : Array Json
  methods : Array Json
  defs : Array Json
  nodeTypes : Json
  varied : Array Json
  calls : Json
  constTargets : Json
  consts : Array Json
  /-- The QCore class of each user class (by Rust id), class 0 being
  `Object` (and the files' main classes). -/
  qclass : Nat → Option Nat
  objectId : Nat
  kernelId : Nat
  /-- A class type parameter's id ↦ (its class's Rust id, its position),
  from the classes' `type_params`. -/
  classParam : Nat → Option (Nat × Nat)
  /-- A narrowed parameter's id (`T & C`) ↦ its bounds. -/
  narrowed : Nat → Option (Array Json)
  /-- The id `Self` goes by. -/
  selfParam : Nat
  /-- The built-in exception classes (`Exception` and below it): classes
  of the model without fields, their methods built-in calls. -/
  excIds : List Nat := []
  /-- An op-assignment's target's current type, by node (`x += e`). -/
  opTargets : Json := Json.null
  /-- A block's declared result type (`do |x| -> T ... end`), by the node
  of the call it is given to. -/
  blockResults : Json := Json.null
  /-- The program's overloaded method names, each with its signatures
  (`Tables.sigKey`), in the order first met. -/
  overloads : List (String × List String) := []
  /-- The extensions (the prelude's and the program's), with their
  targets. -/
  extensions : Array Json := #[]

def Tables.cls (T : Tables) (id : Nat) : M Json := do
  match T.classes.find? fun c => (c.getObjValAs? Nat "id").toOption == some id with
  | some c => pure c
  | none => throw s!"class {id}"

def Tables.className (T : Tables) (id : Nat) : M String := do
  str (← field (← T.cls id) "name")

/-- The most parameters a procedure type of the model has here (its
classes `Proc0` to `Proc{procMax}`). -/
def procMax : Nat := 7

/-- The model's class of arrays (`Array[out T]`, a built-in generic class:
design §14), right after the procedures' classes. -/
def arrIdx : Nat := 3 + procMax

/-- `Array`'s Rust id and its parameter's. -/
def Tables.arrayInfo (T : Tables) : M (Nat × Nat) := do
  let some c := T.classes.find? fun c => (c.getObjValAs? String "name").toOption == some "Array"
    | throw "no Array"
  let [p] := (← arr (← field c "type_params")).toList | throw "Array's parameters"
  pure (← nat (← field c "id"), ← nat (← field p "id"))

/-- `ProcN[in A1, .., in An, out R]` (design §13.7). -/
def procClassOf (n : Nat) : Class :=
  ⟨s!"Proc{n}", some 0, [], List.replicate n .contra ++ [.co], [], [], .proc⟩

/-- A Rust type as atoms. A user class comes with its arguments; a class
type parameter is `.param i` (the position in its class: the body of
another class never names it, the checker having substituted); a
parameter a class test made (`T & C`) is the class it was narrowed to
(a larger type than the Rust checker's, so a weaker annotation: sound);
method and extension type parameters, and `Self`, are out of range. -/
partial def Tables.tyIn (T : Tables) (env : List (Nat × Ty)) (j : Json) : M Ty := do
  match ← str (← field j "t") with
  | "nothing" => pure []
  -- `-> Void`: the body's value is discarded and the result is nil.
  | "void" => pure [.nil]
  | "union" => do
    let ms ← arr (← field j "members")
    ms.toList.flatMapM (T.tyIn env)
  | "class" =>
    let id ← nat (← field j "id")
    let args ← arr (← field j "args")
    match ← T.className id with
    | "Nil" => if args.isEmpty then pure [.nil] else throw "a generic type"
    | "Bool" => if args.isEmpty then pure [.bool] else throw "a generic type"
    | "Int" => if args.isEmpty then pure [.int] else throw "a generic type"
    | "String" => if args.isEmpty then pure [.str] else throw "a generic type"
    | "Float" => if args.isEmpty then pure [.float] else throw "a generic type"
    | _ => match T.qclass id with
      | some k => pure [.cls k (← args.toList.mapM (T.tyIn env))]
      | none => throw s!"type {← T.className id}"
  | "param" =>
    let id ← nat (← field j "id")
    if let some t := (env.find? (·.1 == id)).map (·.2) then return t
    if id == T.selfParam then throw "a Self type"
    match T.classParam id with
    | some (cid, i) =>
      unless (T.qclass cid).any (· ≥ 2) do throw "a type parameter of a class out of range"
      pure [.param i]
    | none => match T.narrowed id with
      | some bounds =>
        -- `T & C`: the `C`.
        let cs ← bounds.toList.filterM fun b => do pure ((← str (← field b "t")) != "param")
        match cs with
        | [c] => T.tyIn env c
        | _ => throw "a narrowed type parameter without a class"
      | none => throw "a method or extension type parameter"
  -- `Type[T]` (a class as a value of its type): no class objects here.
  | "type_of" => throw "a Type[T] type"
  -- A procedure type: `ProcN[params, result]` (design §13.7), the model's
  -- classes 2 to 2 + `procMax`.
  | "proc" =>
    unless (← field j "recv") == .null do throw "a procedure type with a receiver"
    -- A shareable one captures by value (docs/02 §9): not the model's.
    if (← field j "shareable") == .bool true then throw "a shareable procedure type"
    let ps ← (← arr (← field j "params")).toList.mapM (T.tyIn env)
    unless ps.length ≤ procMax do throw "a procedure type of many parameters"
    pure [.cls (2 + ps.length) (ps ++ [← T.tyIn env (← field j "ret")])]
  | t => throw s!"a {t} type"

def Tables.ty (T : Tables) (j : Json) : M Ty := T.tyIn [] j

/-- A built-in method's owner's parameters on a receiver of Rust type
`rj` (one class): the class's own (its arguments), or those of a module
it includes (`Enumerable[T]`, `Comparable[T]`), as its include gives
them; and `Self`, the receiver's type. `none` when the owner is neither. -/
def Tables.receiverEnv (T : Tables) (rj : Json) (owner : Nat) : M (Option (List (Nat × Ty))) := do
  unless (← str (← field rj "t")) == "class" do return none
  let cid ← nat (← field rj "id")
  let c ← T.cls cid
  let ps ← (← arr (← field c "type_params")).toList.mapM fun q => do nat (← field q "id")
  let args ← (← arr (← field rj "args")).toList.mapM T.ty
  let base : List (Nat × Ty) := ps.zip args
  let me : List (Nat × Ty) := [(T.selfParam, ← T.ty rj)]
  -- (Up the superclass chain, each class's arguments through the one
  -- below: the first class or include of the owner, as the checker's
  -- linearization finds a class's own includes before its superclass's.)
  let mut c := c
  let mut cid := cid
  let mut base := base
  for _ in [0:T.classes.size] do
    if cid == owner then return some (base ++ me)
    for inc in (← arr (← field c "includes")) do
      if (← nat (← field inc "id")) == owner then
        let iargs ← (← arr (← field inc "args")).toList.mapM (T.tyIn base)
        let ips ← (← arr (← field (← T.cls owner) "type_params")).toList.mapM fun q => do nat (← field q "id")
        return some (ips.zip iargs ++ me)
    match ← field c "superclass" with
    | .null => return none
    | sj =>
      let sargs ← (← arr (← field sj "args")).toList.mapM (T.tyIn base)
      cid ← nat (← field sj "id")
      c ← T.cls cid
      let sps ← (← arr (← field c "type_params")).toList.mapM fun q => do nat (← field q "id")
      base := sps.zip sargs
  pure none

/-- The names a module declares, its prelude extensions' included (always
active: `minmax` on `Enumerable`). -/
def Tables.moduleNames (T : Tables) (mid : Nat) : M (List String) := do
  let own ← (← arr (← field (← T.cls mid) "method_names")).toList.mapM fun x => str x
  let mut out := own
  for e in T.extensions do
    if (← nat (← field e "target")) == mid then
      out := out ++ (← (← arr (← field e "method_names")).toList.mapM fun x => str x)
  pure out

/-- Whether a program's method (`m'`, of a class that includes the module
`mid`, directly or through a superclass) has the signature the module
declares for its name, with the module's parameters and `Self` as the
class sees them: a module's body calls it by that signature. -/
def Tables.matchesModule (T : Tables) (mid : Nat) (m' : Json) : M Bool := do
  let n ← str (← field m' "name")
  let o ← nat (← field m' "owner")
  unless (← arr (← field (← T.cls o) "type_params")).isEmpty do return false
  let some m0 ← T.methods.findM? (fun m0 => do
      pure ((← nat (← field m0 "owner")) == mid && (← str (← field m0 "name")) == n)) | return false
  let some env ← T.receiverEnv (Json.mkObj [("t", "class"), ("id", o), ("args", Json.arr #[])]) mid
    | return false
  let same (a b : Json) : M Bool := do
    match ← str (← field a "t"), ← str (← field b "t") with
    | "proc", "proc" =>
      let pa ← arr (← field a "params")
      let pb ← arr (← field b "params")
      unless pa.size == pb.size do return false
      for (x, y) in pa.toList.zip pb.toList do
        unless (← T.tyIn env x) == (← T.tyIn [] y) do return false
      pure ((← T.tyIn env (← field a "ret")) == (← T.tyIn [] (← field b "ret")))
    | _, _ => pure ((← T.tyIn env a) == (← T.tyIn [] b))
  let p0 := (← arr (← field m0 "params")).toList
  let p1 := (← arr (← field m' "params")).toList
  unless p0.length == p1.length do return false
  for (x, y) in p0.zip p1 do
    unless (← field x "kind") == (← field y "kind") do return false
    unless ← same (← field x "type") (← field y "type") do return false
  match ← field m0 "block", ← field m' "block" with
  | .null, .null => pure ()
  | .null, _ | _, .null => return false
  | b0, b1 => unless ← same (← field b0 "type") (← field b1 "type") do return false
  same (← field m0 "ret") (← field m' "ret")

/-- The type parameters a declared type (`j`) binds against a type (`t`),
added to `env`: what a call's result type tells of the method's
instantiation. -/
partial def Tables.solve (T : Tables) (env : List (Nat × Ty)) (j : Json) (t : Ty) :
    M (List (Nat × Ty)) := do
  match ← str (← field j "t") with
  | "param" =>
    let id ← nat (← field j "id")
    if env.any (·.1 == id) then pure env else pure (env ++ [(id, t)])
  | "class" =>
    match t with
    | [.cls _ as] =>
      let args ← arr (← field j "args")
      if args.size == as.length then
        (args.toList.zip as).foldlM (fun env (a, u) => T.solve env a u) env
      else pure env
    | _ => pure env
  | _ => pure env

/-- A Rust class type as a QCore class with its arguments. -/
def Tables.tyClass (T : Tables) (j : Json) : M (Nat × List Ty) := do
  match ← T.ty j with
  | [.cls k as] => pure (k, as)
  | _ => throw "a class type"

/-- A built-in method's parameter or result: a type QCore has no atoms
for (a type parameter, a generic class) is any value here. -/
def Tables.tyOrTop (T : Tables) (j : Json) (env : List (Nat × Ty) := []) : M Ty :=
  match T.tyIn env j with
  | .ok t => pure t
  | .error _ => pure [.nil, .bool, .int, .str, .cls 0 []]

def Tables.nodeTy (T : Tables) (id : Nat) : M Ty := do
  if T.varied.contains (.num id) then throw s!"node {id} checked with different types"
  match T.nodeTypes.getObjVal? (toString id) with
  | .ok t => T.ty t
  | .error _ => throw s!"node {id} has no type"

def Tables.method (T : Tables) (id : Nat) : M Json := do
  match T.methods.find? fun m => (m.getObjValAs? Nat "id").toOption == some id with
  | some m => pure m
  | none => throw s!"method {id}"

/-- A method's signature: its parameters' kinds and types, and its
block's type (names aside). -/
def sigKey (m : Json) : M String := do
  let ps ← (← arr (← field m "params")).toList.mapM fun p => do
    pure ((← field p "kind").compress ++ ":" ++ (← field p "type").compress)
  let b ← match ← field m "block" with
    | .null => pure "none"
    | b => pure (← field b "type").compress
  pure (",".intercalate ps ++ "|" ++ b)

/-- The model's name of a program's method: an overloaded one's name and
signature (`name#k`), as the runtime dispatches by signature (docs/05:
a subclass overriding one overload leaves the others to the
superclass's), so an override, of the same signature, has the same name.
The checker's choice among overloads is taken as given (the call's
method), the model checks the chosen signature. -/
def Tables.modelName (T : Tables) (m : Json) : M String := do
  let name ← str (← field m "name")
  match T.overloads.find? (·.1 == name) with
  | none => pure name
  | some (_, keys) =>
    if (← str (← field m "synth")) != "None" then throw s!"an overloaded accessor {name}"
    let key ← sigKey m
    -- (A signature naming a type parameter may equal another once
    -- substituted.)
    if (key.splitOn "\"t\":\"param\"").length > 1 then
      throw s!"an overload of {name} of a generic signature"
    match keys.idxOf? key with
    | some i => pure s!"{name}#{i}"
    | none => throw s!"an overload of {name} not the program's"

/-- The `initialize` the model's `new` of Rust class `id` runs: the
nearest one, in the class or a superclass (`Program.lookup`), by Rust
method id. -/
partial def Tables.nearestInit (T : Tables) (id : Nat) : M (Option Nat) := do
  let own := T.methods.find? fun m =>
    (m.getObjValAs? Nat "owner").toOption == some id &&
    (m.getObjValAs? String "name").toOption == some "initialize" &&
    (m.getObjVal? "singleton").toOption != some (.bool true)
  match own with
  | some m => pure (m.getObjValAs? Nat "id").toOption
  | none => match ← field (← T.cls id) "superclass" with
    | .null => pure none
    | t => T.nearestInit (← nat (← field t "id"))

/-- A class's Rust id by its name. -/
def Tables.classId (T : Tables) (n : String) : M (Option Nat) := do
  match T.classes.find? fun c => (c.getObjValAs? String "name").toOption == some n with
  | some c => pure (some (← nat (← field c "id")))
  | none => pure none

/-- Whether `new` of class `id` runs a built-in exception's `initialize`. -/
def Tables.excInit (T : Tables) (id : Nat) : M Bool := do
  match ← T.nearestInit id with
  | none => pure false
  | some mid =>
    let m ← T.method mid
    pure (T.excIds.contains (← nat (← field m "owner")))

/-- Whether an exception of class `id` made by the run time (`raise K`,
`raise K, m`, which run neither `initialize` nor the fields' defaults) is
what the model takes it for: no class from `id` up to the built-in ones
declares a field or an `initialize`. -/
partial def Tables.excPlain (T : Tables) (id : Nat) : M Bool := do
  if T.excIds.contains id then return true
  let c ← T.cls id
  unless (← arr (← field c "fields")).isEmpty do return false
  if T.methods.any (fun m => (m.getObjValAs? Nat "owner").toOption == some id &&
      (m.getObjValAs? String "name").toOption == some "initialize") then return false
  match ← field c "superclass" with
  | .null => pure false
  | sj => T.excPlain (← nat (← field sj "id"))

/-- The locals assigned so far, with their declared types. -/
abbrev Locals := List (String × Ty)

def addLocal (ls : Locals) (x : String) (t : Ty) : Locals :=
  -- The first assignment declares it (docs/02 §6).
  if ls.any (·.1 == x) then ls else ls ++ [(x, t)]

/-- Where a body is converted: whether it is top-level code (the top
level, or a method of its class), and for an `initialize`, its
parameters and its class's superclass (`super`). -/
structure Where where
  top : Bool
  init : Option (List (String × Ty) × Nat) := none
  /-- The Rust id of the method's class (for its fields). -/
  rcls : Option Nat := none
  /-- In a `rescue` clause: the local holding the exception (a bare
  `raise` raises it again), and the flag a `retry` sets. -/
  exc : Option String := none
  retryFlag : Option String := none
  /-- In a lambda: the locals of the code around it (the method's, the
  enclosing lambdas' and blocks'), which it captures. -/
  captured : Locals := []
  /-- In a method with a named block parameter: it, a procedure (its
  `yield` calls it). -/
  blkProc : Option (String × Ty) := none
  /-- In a `rescue` clause: its variable, a local of its own (quarz#126),
  by the model's name for it. -/
  renames : List (String × String) := []
  /-- The names of the scopes around the current one (the method's
  locals around a block, a lambda, a `case/in` arm or a `rescue` clause):
  a declaration (`y: T = e`, `y := e`) of one of them hides it. -/
  outer : List String := []
  /-- Whether the statements being converted are a scope's own (not an
  `if`'s or a `while`'s inside it). -/
  scopeTop : Bool := false
  /-- Whether the current scope is a block's, a lambda's, an arm's or a
  `rescue` clause's (not the method's). -/
  inner : Bool := false

/-- Converting a body, with the locals so far. -/
abbrev CM := ReaderT Where (StateT Locals M)

/-- The model's name of a local: a `rescue` clause's variable is its own. -/
def localName (x : String) : CM String := do
  pure (((← read).renames.find? (·.1 == x)).map (·.2) |>.getD x)

/-- A block's body, given the result type it declares (`block_results`)
for the call `id`, as a `def`'s return type: the body at most `T`, the
block giving `T`; `-> Void` discards the value. -/
def Tables.declaredResult (T : Tables) (id : Nat) (bd : Expr) : M Expr := do
  match T.blockResults.getObjVal? (toString id) with
  | .error _ => pure bd
  | .ok tj =>
    if (tj.getObjValAs? String "t").toOption == some "void" then return .seq bd .nil
    let t ← T.ty tj
    pure (.prim "blockResult" [bd] [t] t)

/-- A scope's body (a block's, a lambda's, a `case/in` arm's, a `rescue`
clause's): the names around it are outer, its statements its own. -/
def inScope {α} (k : CM α) : CM α := do
  let names := (← get).map (·.1) ++ (← read).renames.map (·.1)
  withReader (fun w => { w with outer := names ++ w.outer, scopeTop := true, inner := true }) k

/-- A block's or a lambda's body: its parameters hide a `rescue`
clause's variable of their names. -/
def hidingParams {α} (ps : List String) (k : CM α) : CM α :=
  withReader (fun w => { w with renames := w.renames.filter fun (x, _) => !ps.contains x }) (inScope k)

def positional (a : Json) : M Json := do
  match ← variant a with
  | ("Positional", e) => pure e
  | (k, _) => throw s!"a {k} argument"

/-- Whether an expression has a `return` (in a block of it too). -/
partial def hasRet : Expr → Bool
  | .ret _ => true
  | .assign _ e | .setField _ e | .raise e | .isNil e | .isA e _ | .eqNil e | .neNil e | .eqTrue e
  | .eqFalse e | .not e => hasRet e
  | .new _ _ as | .superInit _ as | .yield as | .prim _ as _ _ => as.any hasRet
  | .call r _ as => hasRet r || as.any hasRet
  | .callBlk r _ as _ b => hasRet r || as.any hasRet || hasRet b
  | .seq a b | .while a b | .and a b | .or a b => hasRet a || hasRet b
  | .ite c t e => hasRet c || hasRet t || hasRet e
  | .rescue b _ h e => hasRet b || hasRet h || hasRet e
  | .lambda _ _ _ b => hasRet b
  | .callProc f as => hasRet f || as.any hasRet
  | .ensure b e => hasRet b || hasRet e
  | _ => false

/-- Whether an expression tests or loops (what may narrow a path). -/
partial def narrows : Expr → Bool
  | .ite .. | .while .. | .isNil _ | .isA .. | .eqNil _ | .neNil _ | .eqTrue _ | .eqFalse _
  | .and .. | .or .. | .not _ => true
  | .assign _ e | .setField _ e | .ret e | .raise e => narrows e
  | .new _ _ as | .superInit _ as | .yield as | .prim _ as _ _ => as.any narrows
  | .call r _ as => narrows r || as.any narrows
  | .callBlk r _ as _ b => narrows r || as.any narrows || narrows b
  | .seq a b => narrows a || narrows b
  | .rescue .. | .ensure .. => true
  | .lambda _ _ _ b => narrows b
  | .callProc f as => narrows f || as.any narrows
  | _ => false

/-! ### Locals the model and the Rust checker see differently -/

/-- What the walk of a method's body (`daWalk`) knows: the locals
assigned on every path so far (none: control does not get here). -/
abbrev LM := M

structure DA where
  out : Option (List String)
  tt : Option (List String)
  ff : Option (List String)

def DA.plain (s : Option (List String)) : DA := ⟨s, s, s⟩

def daJoin : Option (List String) → Option (List String) → Option (List String)
  | none, b => b
  | a, none => a
  | some a, some b => some (a.filter (b.contains ·))

/-- Out of range: a read of a local not assigned on every path before it
(the Rust checker reads it as `T?`, the model's environment has no entry
for it). The walk knows no narrowing, so it walks the branches a test
makes dead too: stricter than the model there. -/
partial def daWalk (inBlk : List String) (s : Option (List String)) (e : Expr) : LM DA := do
  let some S := s | return DA.plain none
  let seqArgs (S : List String) (as : List Expr) : LM (Option (List String)) :=
    as.foldlM (fun acc a => do match acc with
      | none => pure none
      | some S => pure (← daWalk inBlk (some S) a).out) (some S)
  match e with
  | .var x _ =>
    unless S.contains x do throw s!"a read of {x}, not assigned on every path before it"
    pure (.plain s)
  | .assign x v =>
    let r ← daWalk inBlk s v
    pure (.plain (r.out.map (fun S => if S.contains x then S else x :: S)))
  | .setField _ v | .isNil v | .isA v _ | .eqNil v | .neNil v | .eqTrue v | .eqFalse v =>
    pure (.plain (← daWalk inBlk s v).out)
  | .ret v | .raise v => let _ ← daWalk inBlk s v; pure (.plain none)
  -- A lambda: its body where it may run (the locals assigned here, its
  -- parameters); making it assigns nothing.
  | .lambda ps _ _ b =>
    let _ ← daWalk inBlk (some (S ++ ps.map (·.1))) b
    pure (.plain s)
  | .callProc f as =>
    match (← daWalk inBlk s f).out with
    | none => pure (.plain none)
    | some S => pure (.plain (← seqArgs S as))
  | .rescue b x h els =>
    let rb ← daWalk inBlk s b
    let re ← daWalk inBlk rb.out els
    -- The handler: what held before the body, and the exception.
    let rh ← daWalk inBlk (some (x :: S)) h
    pure (.plain (daJoin re.out rh.out))
  | .ensure b e =>
    let rb ← daWalk inBlk s b
    let re ← daWalk inBlk (some S) e
    let ea := e.assigned
    pure (.plain (match rb.out, re.out with
      | some Sb, some Se => some (Sb.filter fun x => !ea.contains x || Se.contains x)
      | _, _ => none))
  | .absurd => pure (.plain none)
  | .new _ _ as | .superInit _ as | .yield as | .prim _ as _ _ => pure (.plain (← seqArgs S as))
  | .call r _ as =>
    match (← daWalk inBlk s r).out with
    | none => pure (.plain none)
    | some S => pure (.plain (← seqArgs S as))
  | .callBlk r _ as ps b =>
    let some S ← (do match (← daWalk inBlk s r).out with
        | none => pure none
        | some S => seqArgs S as) | pure (.plain none)
    let _ ← daWalk inBlk (some (S ++ ps)) b
    pure (.plain (some S))
  | .seq a b =>
    let ra ← daWalk inBlk s a
    daWalk inBlk ra.out b
  | .ite c t f =>
    let rc ← daWalk inBlk s c
    let rt ← daWalk inBlk rc.tt t
    let rf ← daWalk inBlk rc.ff f
    pure (.plain (daJoin rt.out rf.out))
  | .while c b =>
    let rc ← daWalk inBlk s c
    let _ ← daWalk inBlk rc.tt b
    pure (.plain rc.ff)
  | .and a b =>
    let ra ← daWalk inBlk s a
    let rb ← daWalk inBlk ra.tt b
    pure ⟨daJoin ra.ff rb.out, rb.tt, daJoin ra.ff rb.ff⟩
  | .or a b =>
    let ra ← daWalk inBlk s a
    let rb ← daWalk inBlk ra.ff b
    pure ⟨daJoin ra.tt rb.out, daJoin ra.tt rb.tt, rb.ff⟩
  | .not a =>
    let ra ← daWalk inBlk s a
    pure ⟨ra.out, ra.ff, ra.tt⟩
  | _ => pure (.plain s)

/-- The names of a method by where the Rust checker declares them, in
source order: the method's (`method`: its parameters and the names it
assigns first), the blocks' own (assigned first in a block), and block
parameters; `cur` the names the enclosing blocks declare. -/
structure Scopes where
  method : List String
  blockLocals : List String := []
  params : List String := []
  cur : List String := []
  /-- The names lambdas declare (their own): another lambda may use them
  again, the method or a block not. -/
  lambdaLocals : List String := []

/-- Out of range: a name that is two locals for the Rust checker and one
for the model, which declares a name once per method (docs/02 §6: a
local first assigned in a block is the block's own; a block parameter
is the block's and hides an outer name). Dead code counts: the model
declares a name where it is first written. -/
partial def scopeWalk (inBlock : Bool) (e : Expr) : StateT Scopes M Unit := do
  let walk := scopeWalk inBlock
  match e with
  | .assign x v =>
    walk v
    let st ← get
    if st.method.contains x || st.cur.contains x then return
    if st.blockLocals.contains x || st.params.contains x || st.lambdaLocals.contains x then
      throw s!"{x}: two locals for the Rust checker (a block's own, and another)"
    if inBlock then set { st with blockLocals := st.blockLocals ++ [x], cur := st.cur ++ [x] }
    else set { st with method := st.method ++ [x] }
  | .callBlk r _ as ps b =>
    walk r; for a in as do walk a
    let st ← get
    for p in ps do
      if st.method.contains p || st.cur.contains p || st.blockLocals.contains p then
        throw s!"{p}: a block parameter named like another local"
    set { st with params := st.params ++ ps, cur := st.cur ++ ps }
    scopeWalk true b
    modify fun st' => { st' with cur := st.cur }
  | .setField _ v | .isNil v | .isA v _ | .eqNil v | .neNil v | .eqTrue v | .eqFalse v | .ret v
  | .raise v | .not v => walk v
  | .new _ _ as | .superInit _ as | .yield as | .prim _ as _ _ => for a in as do walk a
  | .call r _ as => walk r; for a in as do walk a
  | .seq a b | .while a b | .and a b | .or a b => walk a; walk b
  | .ite c t f => walk c; walk t; walk f
  | .lambda ps own _ b =>
    -- Its body, a scope of its own as a method's (from its parameters); its
    -- names, a local of the method (or a block) of the same name is
    -- another (out of range, as a block's own); another lambda may use them.
    let st ← get
    let mine := (ps ++ own).map (·.1)
    for x in mine do
      if st.method.contains x || st.cur.contains x || st.blockLocals.contains x || st.params.contains x then
        throw s!"{x}: a lambda's own local named like another"
    -- (A block's own local or parameter out of scope here, the block
    -- closed, is another local for the Rust checker: out of range if the
    -- body assigns it.)
    let closed := (st.blockLocals ++ st.params).filter fun x => !st.cur.contains x && !st.method.contains x
    let ((), inner) ← (scopeWalk false b).run
      { method := ps.map (·.1), blockLocals := closed, lambdaLocals := st.lambdaLocals }
    set { st with lambdaLocals := (st.lambdaLocals ++ mine ++ inner.lambdaLocals).eraseDups }
  | .callProc f as => walk f; for a in as do walk a
  | .rescue b x h els =>
    walk b
    -- (A clause's variable is a local of its own, named apart.)
    walk (.assign x .nil); walk h; walk els
  | .ensure b e => walk b; walk e
  | _ => pure ()

def localsInRange (params : List String) (body : Expr) : M Unit := do
  let _ ← daWalk [] (some params) body
  let _ ← (scopeWalk false body).run { method := params }

/-- What a `case/in` or a match on an open type raises when nothing
matches: a `NoMatchingPatternError` (made by the run time: opaque). -/
def noMatchE (T : Tables) : M Expr := do
  let some cid ← T.classId "NoMatchingPatternError" | throw "no NoMatchingPatternError"
  let some q := T.qclass cid | throw "NoMatchingPatternError out of range"
  pure (.raise (.prim "new" [] [] [.cls q []]))

/-! ### Patterns (docs/01 §11) as tests -/

/-- A pattern compiled against a subject, matching and binding in the
order the compiled program does (a binding is made when it is reached,
and kept if a later part fails): `test`, which makes the bindings
before its last class or value test (none: it matches every value),
then `post`, the bindings after it, made once it matched; the names it
binds with their declared types; the temporaries it assigns; and what a
capture of it gets (Rust's narrowed type). -/
structure PatC where
  test : Option Expr
  post : Expr
  names : List (String × Ty)
  tmps : List (String × Ty)
  yes : Ty

/-- An expression's assignments renamed (a pattern's test and
assignments: the bindings made before a later part's test are in it). -/
def renameAssigns (r : String → String) : Expr → Expr
  | .assign x e => .assign (r x) (renameAssigns r e)
  | .seq a b => .seq (renameAssigns r a) (renameAssigns r b)
  | .and a b => .and (renameAssigns r a) (renameAssigns r b)
  | .or a b => .or (renameAssigns r a) (renameAssigns r b)
  | .not a => .not (renameAssigns r a)
  | .ite c t e => .ite (renameAssigns r c) (renameAssigns r t) (renameAssigns r e)
  | e => e

/-- The names a pattern binds, renamed (`m`), in its assignments too. -/
def PatC.rename (c : PatC) (m : List (String × String)) : PatC :=
  let r (x : String) : String := ((m.find? (·.1 == x)).map (·.2)).getD x
  let names := c.names.map fun (x, t) => (r x, t)
  { c with test := c.test.map (renameAssigns r), post := renameAssigns r c.post, names := names }

/-- `x` then `y`, as one match: `x`'s bindings after its test come before
`y`'s test. -/
def PatC.conj (x y : Option Expr × Expr) : Option Expr × Expr :=
  match y.1 with
  | none => (x.1, .seq x.2 y.2)
  | some t2 =>
    let t2 := Expr.seq x.2 t2
    (some (match x.1 with | some t1 => .and t1 t2 | none => t2), y.2)

/-- A test (none: always true) as an expression. -/
def PatC.testOr (t : Option Expr) : Expr := t.getD .tru

/-- Rust's subclass relation, by class ids. -/
def rsub (T : Tables) (c d : Nat) : M Bool := do
  let mut x := c
  for _ in [0:T.classes.size + 1] do
    if x == d then return true
    match ← field (← T.cls x) "superclass" with
    | .null => return false
    | sj => x ← nat (← field sj "id")
  pure false

/-- The variants of an enum (by Rust ids). -/
def variantsOf (T : Tables) (cid : Nat) : M (List Json) :=
  T.classes.toList.filterM fun d => do
    match ← field d "superclass" with
    | .null => pure false
    | s => pure ((← nat (← field s "id")) == cid && (← str (← field d "kind")) == "Variant")

def patMembers (st : Json) : M (List Json) := do
  match ← str (← field st "t") with
  | "union" => pure (← arr (← field st "members")).toList
  | _ => pure [st]

/-- A class by its name, as a pattern names it. -/
def classNamed (T : Tables) (full : String) : M Json := do
  let cands ← T.classes.toList.filterM fun c => do
    let n ← str (← field c "name")
    pure (n == full || n.endsWith ("::" ++ full))
  let [c] := cands | throw s!"pattern class {full}"
  pure c

def classAtom (T : Tables) (cid : Nat) : M Atom := do
  match ← T.ty (Json.mkObj [("t", "class"), ("id", cid), ("args", Json.arr #[])]) with
  | [a] => pure a
  | _ => throw s!"pattern class {cid}"

/-- A pattern's class (its Rust id and atom), by its name. -/
def patClass (T : Tables) (names : Json) : M (Nat × Atom) := do
  let ns ← (← arr (← field names "names")).toList.mapM str
  let c ← classNamed T ("::".intercalate ns)
  let cid ← nat (← field c "id")
  unless (← arr (← field c "type_params")).isEmpty do throw "a pattern of a generic class"
  if (← str (← field c "kind")) == "Enum" then throw "a pattern of an enum"
  pure (cid, ← classAtom T cid)

/-- What a match by the classes `targets` narrows `st` to (Rust's
`split_by_type`, enums as their variants): a member below a target
stays, a target below a member comes in. -/
def splitYes (T : Tables) (st : Json) (targets : List (Nat × Option Atom)) : M Ty := do
  let ms ← patMembers st
  let expanded ← ms.flatMapM fun m => do
    if (← str (← field m "t")) != "class" then return [m]
    let c ← T.cls (← nat (← field m "id"))
    if (← str (← field c "kind")) != "Enum" then return [m]
    (← variantsOf T (← nat (← field c "id"))).mapM fun d => do
      pure (Json.mkObj [("t", "class"), ("id", ← nat (← field d "id")), ("args", Json.arr #[])])
  let mut out : Ty := []
  for m in expanded do
    match ← str (← field m "t") with
    | "class" =>
      let mid ← nat (← field m "id")
      if ← targets.anyM fun (pid, _) => rsub T mid pid then out := out ++ (← T.ty m)
      else
        for (pid, a) in targets do
          if ← rsub T pid mid then
            -- Rust adds the class only when it is below the member with its
            -- arguments (`IntBox` for `Box[Int]`, not `Box[String]`): out of
            -- range rather than followed through the chain's arguments.
            unless (← arr (← field m "args")).isEmpty do throw "a capture on a generic member"
            let some a := a | throw s!"type {← str (← field (← T.cls pid) "name")}"
            out := out ++ [a]
    | t => throw s!"a pattern on a {t} subject"
  pure out.eraseDups

/-- A built-in class's Rust id, by name. -/
def builtinId (T : Tables) (n : String) : M (Option Nat) := do
  match ← T.classes.toList.findM? fun c => do pure ((← str (← field c "name")) == n) with
  | some c => pure (some (← nat (← field c "id")))
  | none => pure none

/-- Whether a field's pattern matches every value of the field's declared
type (Rust's `field_pattern_irrefutable`). -/
partial def irrefutable (T : Tables) (p : Json) (fty : Json) : M Bool := do
  let (k, v) ← variant (← field p "kind")
  match k with
  | "Bind" => pure true
  | "Capture" => match (← arr v).toList with
    | [inner, _] => irrefutable T inner fty
    | _ => pure false
  | "Const" =>
    if (← str (← field fty "t")) != "class" then return false
    let (pid, _) ← patClass T v
    rsub T (← nat (← field fty "id")) pid
  | _ => pure false

mutual

/-- Pattern `p` against the subject `rd` (read at a type) of Rust type
`st` (`stTy` in the model); `base` names its temporaries. `trusted`: the
value is known to be of the pattern's class (a field pattern Rust counts
as irrefutable), so a class test tests nothing. -/
partial def compilePat (T : Tables) (base : String) (rd : Ty → Expr) (st : Json) (stTy : Ty)
    (p : Json) (trusted : Bool := false) : M PatC := do
  let (k, v) ← variant (← field p "kind")
  match k with
  | "Bind" =>
    let x ← str v
    if x == "_" then pure ⟨none, .nil, [], [], stTy⟩
    else pure ⟨none, .assign x (rd stTy), [(x, stTy)], [], stTy⟩
  | "Capture" =>
    let [inner, x] := (← arr v).toList | throw "a capture"
    let x ← str x
    let c ← compilePat T base rd st stTy inner trusted
    let (test, post) := PatC.conj (c.test, c.post) (none, .assign x (rd c.yes))
    pure ⟨test, post, c.names ++ [(x, c.yes)], c.tmps, c.yes⟩
  | "Alt" =>
    let cs ← (List.range (← arr v).size).zip (← arr v).toList |>.mapM fun (i, q) =>
      compilePat T s!"{base}|{i}" rd st stTy q
    unless cs.all (·.names.isEmpty) do throw "a binding in an alternative"
    let yes := (cs.flatMap (·.yes)).eraseDups
    -- (An alternative binds nothing: its `post` assigns temporaries only.)
    if cs.any (·.test.isNone) then return ⟨none, .nil, [], cs.flatMap (·.tmps), yes⟩
    match cs.filterMap (·.test) with
    | t :: ts => pure ⟨some (ts.foldl .or t), .nil, [], cs.flatMap (·.tmps), yes⟩
    | [] => throw "an empty alternative"
  | "Value" =>
    let r := rd stTy
    let some intId ← builtinId T "Int" | throw "no Int"
    let some floatId ← builtinId T "Float" | throw "no Float"
    let num : M PatC := do
      -- Rust's `numeric_widen`: another numeric class's equal number
      -- matches too (docs/02 §6); the model's test of equality is opaque.
      let some integerId ← builtinId T "Integer" | throw "no Integer"
      let yes ← splitYes T st [(intId, some .int), (integerId, none), (floatId, some .float)]
      pure ⟨some (.and (.or (.isA r .int) (.isA r .float)) (.prim "===" [] [] [.bool])), .nil, [], [], yes⟩
    match ← variant (← field v "kind") with
    -- (A literal pattern compares structurally, no `==` of the subject's:
    -- the tests that narrow whatever the subject's type.)
    | ("Nil", _) =>
      let some nilId ← builtinId T "Nil" | throw "no Nil"
      pure ⟨some (.isNil r), .nil, [], [], ← splitYes T st [(nilId, some .nil)]⟩
    | ("True", _) =>
      let some bid ← builtinId T "Bool" | throw "no Bool"
      pure ⟨some (.and (.isA r .bool) (.eqTrue (rd [.bool]))), .nil, [], [],
        ← splitYes T st [(bid, some .bool)]⟩
    | ("False", _) =>
      let some bid ← builtinId T "Bool" | throw "no Bool"
      pure ⟨some (.and (.isA r .bool) (.eqFalse (rd [.bool]))), .nil, [], [],
        ← splitYes T st [(bid, some .bool)]⟩
    | ("Int", _) => num
    | ("Float", _) => num
    | ("Str", parts) =>
      unless (← (← arr parts).toList.allM fun q => do pure ((← variant q).1 == "Lit")) do
        throw "an interpolated string pattern"
      let some sid ← builtinId T "String" | throw "no String"
      pure ⟨some (.and (.isA r .str) (.prim "===" [] [] [.bool])), .nil, [], [],
        ← splitYes T st [(sid, some .str)]⟩
    | (k, _) => throw s!"a {k} value pattern"
  | "Const" =>
    let (pid, a) ← patClass T v
    let yes ← splitYes T st [(pid, some a)]
    -- A dead arm: Rust declares the pattern's class (`dead_arm_type`).
    let yes := if yes.isEmpty then [a] else yes
    if trusted then pure ⟨none, .nil, [], [], yes⟩
    else pure ⟨some (.isA (rd stTy) a), .nil, [], [], yes⟩
  | "ConstArray" =>
    let [path, ap] := (← arr v).toList | throw "a ConstArray"
    unless (← arr (← field ap "post")).isEmpty && (← field ap "rest") == .null do
      throw "a rest in a field pattern"
    let pats := (← arr (← field ap "pre")).toList
    fieldsPat T base rd st stTy path trusted fun fields => do
      unless fields.length == pats.length do throw "a field pattern of another arity"
      pure (fields.zip pats |>.map fun (f, q) => (f, q, false))
  | "ConstHash" =>
    let [path, hp] := (← arr v).toList | throw "a ConstHash"
    unless (← field hp "rest") == .null do throw "a rest in a field pattern"
    let pairs := (← arr (← field hp "pairs")).toList
    fieldsPat T base rd st stTy path trusted fun fields => pairs.mapM fun pr => do
      let key ← str (← field pr "key")
      let some f ← fields.findM? fun f => do pure ((← str (← field f "name")) == key)
        | throw s!"no field {key}"
      let q ← match ← field pr "pattern" with
        | .null => pure (Json.mkObj [("kind", Json.mkObj [("Bind", key)])])
        | q => pure q
      pure (f, q, true)
  | k => throw s!"a {k} pattern"

/-- `C(...)`: a class test, then each field (in the pattern's order, as
the compiled program reads them) read into a temporary of its declared
type and matched; a named field's pattern Rust counts as irrefutable
tests no class. -/
partial def fieldsPat (T : Tables) (base : String) (rd : Ty → Expr) (st : Json) (stTy : Ty)
    (path : Json) (trusted : Bool) (pick : List Json → M (List (Json × Json × Bool))) : M PatC := do
  let (pid, a) ← patClass T path
  let cj ← T.cls pid
  let kind ← str (← field cj "kind")
  unless kind == "Data" || kind == "Variant" do throw "a field pattern on a class"
  let fields := (← arr (← field cj "fields")).toList
  -- The compiled program reads the fields themselves: a method of the
  -- class (or above) named like one, other than its reader, is out of
  -- range (the model reads through the method).
  for f in fields do
    let fname ← str (← field f "name")
    if ← T.methods.anyM fun m => do
        if (← str (← field m "name")) != fname || (← field m "singleton") == .bool true then return false
        if !(← rsub T pid (← nat (← field m "owner"))) then return false
        pure ((← str (← field m "synth")) != s!"FieldGet(\"{fname}\")") then
      throw s!"a field pattern on a class defining {fname}"
  let yes ← splitYes T st [(pid, some a)]
  let mut acc : Option Expr × Expr := (if trusted then none else some (.isA (rd stTy) a), .nil)
  let mut names : List (String × Ty) := []
  let mut tmps : List (String × Ty) := []
  let mut i := 0
  for (f, q, byType) in ← pick fields do
    let fname ← str (← field f "name")
    let ftyJ ← field f "type"
    let fty ← T.ty ftyJ
    let tmp := s!"{base}.{i}"
    i := i + 1
    let irr ← if byType then irrefutable T q ftyJ else pure false
    let c ← compilePat T tmp (fun t => .var tmp t) ftyJ fty q irr
    if T.overloads.any (·.1 == fname) then throw s!"a field pattern reading an overloaded {fname}"
    acc := PatC.conj acc (none, .assign tmp (.call (rd [a]) fname []))
    acc := PatC.conj acc (c.test, c.post)
    names := names ++ c.names
    tmps := tmps ++ [(tmp, fty)] ++ c.tmps
  pure ⟨acc.1, acc.2, names, tmps, if yes.isEmpty then [a] else yes⟩

end


mutual

partial def expr (T : Tables) (e : Json) : CM Expr := do
  let id ← nat (← field e "id")
  let (k, v) ← variant (← field e "kind")
  match k with
  | "Nil" => pure .nil
  | "True" => pure .tru
  | "False" => pure .fls
  | "SelfRef" => pure .self
  | "Float" => pure (.flt v.compress)
  -- A constant: not narrowed (docs/02 §6), a value of its own type. The
  -- type the Rust checker gave the read must be that one.
  | "Const" =>
    let target ← match T.constTargets.getObjVal? (toString id) with
      | .ok t => pure t
      | .error _ => throw "a constant read not resolved"
    -- A variant without data: its value (a new one each time: the model's
    -- equality of variants is their class's).
    if (← str (← field target "t")) == "variant" then
      let some q := T.qclass (← nat (← field target "id")) | throw "a variant out of range"
      return .new q [] []
    unless (← str (← field target "t")) == "const" do throw "a class as a value"
    let cid ← nat (← field target "id")
    let some k := T.consts.find? fun k => (k.getObjValAs? Nat "id").toOption == some cid
      | throw "a constant of another file"
    let declared ← field k "type"
    unless (← field T.nodeTypes (toString id)) == declared do
      throw s!"disagree: constant read {id} not of the constant's type"
    pure (.prim "const" [] [] (← T.ty declared))
  | "Int" =>
    let n ← match (← field v "value") with
      | .num n => pure n.mantissa
      | _ => throw "a big integer"
    -- An integer literal where a `Float` is expected is one (docs/02 §5).
    if (← T.nodeTy id) == [.float] then pure (.flt s!"{n}.0") else pure (.int n)
  | "Str" =>
    let parts ← arr v
    let interps ← parts.toList.filterMapM fun p => do
      match ← variant p with
      | ("Interp", x) => pure (some x)
      | _ => pure none
    if interps.isEmpty then pure (.str "") else
    -- An interpolation: `to_s` of each piece, a built-in here.
    let args ← interps.mapM (expr T)
    let tys ← interps.mapM fun x => do T.nodeTy (← nat (← field x "id"))
    pure (.prim "interpolate" args tys [.str])
  | "Local" => pure (.var (← localName (← str v)) (← T.nodeTy id))
  | "IVar" =>
    -- A field a built-in exception class declares (`@message`): not one
    -- of the model's.
    if let some rc := (← read).rcls then
      let f ← str v
      let mut c := rc
      for _ in [0:T.classes.size] do
        if T.excIds.contains c then throw "a field of a built-in exception class"
        let cj ← T.cls c
        if ← (← arr (← field cj "fields")).anyM (fun fj => do pure ((← str (← field fj "name")) == f)) then break
        match ← field cj "superclass" with
        | .null => break
        | sj => c ← nat (← field sj "id")
    pure (.field (← str v) (← T.nodeTy id))
  | "Assign" =>
    let value ← expr T (← field v "value")
    let vt ← T.nodeTy (← nat (← field (← field v "value") "id"))
    match ← variant (← field v "target") with
    | ("Local", l) =>
      let x ← localName (← str (← field l "name"))
      modify (addLocal · x vt)
      pure (.assign x value)
    | ("IVar", f) => pure (.setField (← str f) value)
    | (t, _) => throw s!"assigning a {t}"
  -- `x op= e` (a local, or a field of `self`): `x = x op e`, the read of
  -- `x` at the type the checker gave its current value. `||=`, `&&=` with
  -- the model's `||`, `&&`; another operator the method the checker
  -- resolved, a built-in one a built-in call.
  -- `y: T = e`, `y := e` (docs/01 §10), not hiding an outer `y` (`body`
  -- converts the ones that do, at a scope's top): a local of its
  -- declared type.
  | "TypedDecl" =>
    let y ← str (← field v "name")
    if (← read).inner || (← read).outer.contains y then
      throw "a declaration of a block's, an arm's or a clause's own inside an if, a loop or a guard"
    let value ← expr T (← field v "value")
    let y ← localName y
    modify (addLocal · y (← T.nodeTy id))
    pure (.assign y value)
  | "OpAssign" =>
    let (tk, tv) ← variant (← field v "target")
    -- The target: a local, or a field of `self`, read at the type the
    -- checker gave its current value (`op_targets`), assigned as the
    -- model's `setField` checks.
    let cur ← match T.opTargets.getObjVal? (toString id) with
      | .ok t => T.ty t
      | .error _ => throw "an op-assign's target not typed"
    if T.varied.contains (.num id) then throw s!"node {id} checked with different types"
    let (rd, wr) ← match tk with
      | "Local" =>
        let x ← localName (← str (← field tv "name"))
        unless (← get).any (·.1 == x) do throw "an op-assign to a local not yet assigned"
        pure (Expr.var x cur, Expr.assign x)
      | "IVar" =>
        let f ← str tv
        if (← read).rcls.isNone then throw "an op-assign to a field outside a class"
        pure (Expr.field f cur, Expr.setField f)
      | _ => throw s!"an op-assign to a {tk}"
    let d := cur
    let value ← expr T (← field v "value")
    let op ← str (← field v "op")
    -- (A class may define `||`, `&&`: a call, which the model's are not.)
    if op == "OrOr" || op == "AndAnd" then
      if ← T.methods.anyM (fun m => do
          let n ← str (← field m "name")
          pure ((n == "||" || n == "&&") && (← field m "native") != .bool true)) then
        throw "an op-assign with a program's || or &&"
    match op with
    | "OrOr" => pure (wr (.or rd value))
    | "AndAnd" => pure (wr (.and rd value))
    | _ =>
      let target ← match T.calls.getObjVal? (toString id) with
        | .ok t => pure t
        | .error _ => throw "an op-assign not resolved"
      unless (← str (← field target "t")) == "method" do throw "an op-assign not to a method"
      let m ← T.method (← nat (← field target "method"))
      let name ← str (← field m "name")
      let mname ← T.modelName m
      if (← field m "native") == .bool true then
        if (← nat (← field m "owner")) == (← T.arrayInfo).1 then throw "an op-assign of an array"
        unless (← arr (← field m "type_params")).isEmpty do throw "an op-assign of a generic method"
        let [p] := (← arr (← field m "params")).toList | throw "an op-assign's parameters"
        unless (← str (← field p "kind")) == "Positional" do throw "an op-assign's parameters"
        pure (wr (.prim name [rd, value] [d, ← T.tyOrTop (← field p "type")] (← T.tyOrTop (← field m "ret"))))
      else pure (wr (.call rd mname [value]))
  | "And" => match v with
    | .arr #[a, b] => pure (.and (← expr T a) (← expr T b))
    | _ => throw "And"
  | "Or" => match v with
    | .arr #[a, b] => pure (.or (← expr T a) (← expr T b))
    | _ => throw "Or"
  | "Not" =>
    -- A class may define `!` (a call, which the model's `!` is not).
    if (← T.nodeTy (← nat (← field v "id"))).any (fun a => match a with | .cls .. => true | _ => false) then
      throw "a ! of an object"
    pure (.not (← expr T v))
  | "If" =>
    let c ← expr T (← field v "cond")
    let t ← body T (← arr (← field v "then"))
    let e ← match ← field v "els" with
      | .null => pure .nil
      | els => body T (← arr els)
    pure (.ite c t e)
  | "While" =>
    if (← field v "do_while") == .bool true then throw "a do-while loop"
    let c ← expr T (← field v "cond")
    let c := if (← field v "negate") == .bool true then .not c else c
    pure (.while c (← body T (← arr (← field v "body"))))
  | "Return" => match v with
    | .null => pure (.ret .nil)
    | x => pure (.ret (← expr T x))
  | "Seq" => body T (← arr v)
  -- An array literal: a built-in call making one (design §14), its
  -- elements of the element type the checker gave it.
  | "Array" =>
    let es ← (← arr v).toList.mapM fun a => do expr T (← positional a)
    match ← T.nodeTy id with
    | [.cls k [e]] =>
      unless k == arrIdx do throw "an array literal's type"
      pure (.prim "array" es (es.map fun _ => e) [.cls k [e]])
    | _ => throw "an array literal's type"
  | "Yield" =>
    let as ← (← arr v).toList.mapM fun a => do expr T (← positional a)
    match (← read).blkProc with
    | some (b, t) => pure (.callProc (.var b t) as)
    | none => pure (.yield as)
  | "Call" => call T id v
  | "Super" =>
    -- `super` in `initialize`, into the superclass's.
    unless (← field v "block") == .null do throw "a block given to super"
    let some (params, d) := (← read).init | throw "super outside initialize"
    if let some rc := (← read).rcls then
      if let some sj := ((← T.cls rc).getObjVal? "superclass").toOption then
        if sj != .null then
          if ← T.excInit (← nat (← field sj "id")) then
            throw "super into a built-in exception's initialize"
    let args ← match ← field v "args" with
      -- A bare `super` passes the method's arguments.
      | .null => pure (params.map fun (x, t) => Expr.var x t)
      | a => (← arr a).toList.mapM fun a => do expr T (← positional a)
    return .superInit d args
  | "CaseIn" => caseIn T id v
  | "Begin" => beginE T id v false
  -- A lambda (design §13.8, §13.10): its body with its own locals (its
  -- parameters, and the names first assigned in it); it may assign the
  -- locals around it.
  | "Lambda" =>
    let pj ← field T.nodeTypes (toString id)
    unless (← str (← field pj "t")) == "proc" do throw "a lambda not of a procedure type"
    unless (← field pj "recv") == .null do throw "a lambda with a receiver"
    if (← field pj "shareable") == .bool true then throw "a shareable lambda"
    let pts ← (← arr (← field pj "params")).toList.mapM fun t => (T.ty t : M Ty)
    let rj ← field pj "ret"
    let void := (← str (← field rj "t")) == "void"
    let ret ← T.ty rj
    let names ← (← arr (← field (← field v "params") "list")).toList.mapM fun p => do
      unless (← str (← field p "kind")) == "Positional" do throw "a lambda parameter not positional"
      unless (← field p "default") == .null do throw "a lambda parameter with a default"
      str (← field p "name")
    unless names.length == pts.length do throw "a lambda's parameters"
    lambdaOf T names pts ret void (← arr (← field v "body"))
  | "Retry" =>
    let some f := (← read).retryFlag | throw "a retry outside a rescue clause"
    pure (.assign f .tru)
  | "MatchPattern" => matchPattern T id v
  | k => throw s!"a {k} expression"

partial def body (T : Tables) (es : Array Json) : CM Expr := do
  let top := (← read).scopeTop
  -- A statement (not the body's value): a `begin` whose `rescue` retries
  -- is in range there (a loop, its value unused). (Within it, nested
  -- bodies are not the scope's own.)
  let stmt (x : Json) (last : Bool) : CM Expr := withReader (fun w => { w with scopeTop := false }) do
    match ← variant (← field x "kind") with
    | ("Begin", v) => if last then expr T x else beginE T (← nat (← field x "id")) v true
    | _ => expr T x
  match es.toList with
  | [] => pure .nil
  | e :: rest =>
    -- A declaration (`y: T = e`, `y := e`) at the top of a scope within
    -- the method (hiding an outer `y` or not, it is the scope's own): a new
    -- local for the rest of the scope (its value read before, so
    -- `y := y + 1` reads the outer one).
    if top then
      if let .ok ("TypedDecl", v) := variant (← field e "kind") then
        let y ← str (← field v "name")
        if (← read).inner || (← read).outer.contains y then
          let id ← nat (← field e "id")
          let value ← withReader (fun w => { w with scopeTop := false }) (expr T (← field v "value"))
          let fresh := s!"{y}#d{id}"
          modify (addLocal · fresh (← T.nodeTy id))
          let decl := Expr.assign fresh value
          if rest.isEmpty then return .seq decl (.var fresh (← T.nodeTy id))
          let more ← withReader (fun w => { w with renames := (y, fresh) :: w.renames })
            (body T rest.toArray)
          return .seq decl more
    let n := rest.length
    let first ← stmt e (n == 0)
    -- (After a statement, the rest at the scope's top again.)
    if top then
      if rest.isEmpty then return first
      return .seq first (← body T rest.toArray)
    (rest.zipIdx).foldlM (fun acc (x, i) => do pure (.seq acc (← stmt x (i + 1 == n)))) first

/-- Whether a body (in a `rescue` clause) has `retry` only where it ends
the clause: its last statement, or the last of an `if`'s branches there. -/
partial def retryTail (es : List Json) : M Bool := do
  let mentions (j : Json) : Bool := (j.compress.splitOn "\"Retry\"").length > 1
  match es.reverse with
  | [] => pure true
  | last :: before =>
    if before.any mentions then return false
    match ← variant (← field last "kind") with
    | ("Retry", _) => pure true
    | ("If", v) =>
      let t ← retryTail (← arr (← field v "then")).toList
      let e ← match ← field v "els" with
        | .null => pure true
        | els => retryTail (← arr els).toList
      pure (t && e && !mentions (← field v "cond"))
    | _ => pure !(mentions last)

/-- `begin body rescue C => e; h ... else els ensure ens end` (docs/01
§12). Each clause a class test of the exception (held in a local no
program can spell), the last raising it again; the body's value, without
`else`, held in a local too. A `retry` (in a statement, at the end of a
clause) makes it a loop: a flag the clause sets, the body run again
while it is set; `ensure` outside the loop. -/
partial def beginE (T : Tables) (id : Nat) (v : Json) (stmt : Bool) : CM Expr := do
  let w ← read
  if w.init.isSome then throw "a begin in initialize"
  if w.rcls.isNone && !w.top then throw "a begin in a default"
  let rescues := (← arr (← field v "rescues")).toList
  let bodyJ := (← arr (← field v "body"))
  let bd ← body T bodyJ
  -- (The rest in source order, as the Rust checker declares locals:
  -- the clauses, then `else`, then `ensure`.)
  let elseBody : CM (Option Expr) := do
    match ← field v "else_body" with
    | .null => pure none
    | e => pure (some (← body T (← arr e)))
  let some eid ← T.classId "Exception" | throw "no Exception"
  let some excQ := T.qclass eid | throw "Exception out of range"
  let excTy : Ty := [.cls excQ []]
  let retries : Bool := rescues.any fun r => match (r.getObjVal? "body").toOption with
    | some b => decide ((b.compress.splitOn "\"Retry\"").length > 1)
    | none => false
  if retries && !stmt then throw "a begin that retries used as a value"
  let core ← if rescues.isEmpty then do
      unless (← field v "else_body") == .null do throw "else without rescue"
      pure bd
    else do
      let tmp := s!"rescue#{id}"
      modify (addLocal · tmp excTy)
      let flag := s!"retry#{id}"
      if retries then modify (addLocal · flag [.bool])
      let clauseAtoms (r : Json) : CM Ty := do
        match (← arr (← field r "classes")).toList with
          | [] =>
            let some sid ← T.classId "StandardError" | throw "no StandardError"
            let some q := T.qclass sid | throw "StandardError out of range"
            pure [Atom.cls q []]
          | cs => cs.mapM fun c => do
            let (k, n) ← variant (← field c "kind")
            unless k == "Named" do throw s!"a {k} rescue class"
            unless (← arr (← field n "args")).isEmpty do throw "a generic rescue class"
            let ns ← (← arr (← field (← field n "path") "names")).toList.mapM fun j => (str j : CM String)
            -- By its full name only (the tree has not the class Rust
            -- resolved: a name in a module, or a type alias, would be
            -- another class).
            let full := "::".intercalate ns
            let some cid ← T.classId full | throw s!"a rescue class by a partial name {full}"
            let cj ← T.cls cid
            let some q := T.qclass (← nat (← field cj "id")) | throw "a rescue class out of range"
            pure (Atom.cls q [])
      -- A clause's variable: a local of the clause (quarz#126), fresh,
      -- shadowing one outside, unseen after it.
      let clauses ← rescues.zipIdx.mapM fun (r, ci) => do
        let atoms ← clauseAtoms r
        let stmts := (← arr (← field r "body")).toList
        if retries then
          unless ← retryTail stmts do throw "a retry not at the end of its clause"
          if stmts.any (fun j => (j.compress.splitOn "\"Begin\"").length > 1) then
            throw "a begin in a clause that retries"
        let var ← match ← field r "var" with
          | .null => pure none
          | x => do
            let x ← str x
            let xr := s!"{x}#r{id}.{ci}"
            modify (addLocal · xr atoms)
            pure (some (x, xr))
        let rf := if retries then some flag else none
        let hb ← withReader (fun w => { w with exc := some tmp, retryFlag := rf, renames := var.toList ++ w.renames })
          (inScope (body T (← arr (← field r "body"))))
        let hb := match var with
          | none => hb
          | some (_, xr) => Expr.seq (.assign xr (.var tmp atoms)) hb
        pure (atoms, hb)
      let handler := clauses.foldr (fun (atoms, hb) rest =>
        match atoms.map (fun a => Expr.isA (.var tmp excTy) a) with
        | t :: ts => Expr.ite (ts.foldl .or t) hb rest
        | [] => rest) (.raise (.var tmp excTy))
      let node ← match ← elseBody with
        | some e => pure (Expr.rescue bd tmp handler e)
        | none =>
          let tv := s!"begin#{id}"
          let bty ← match bodyJ.back? with
            | some last => T.nodeTy (← nat (← field last "id"))
            | none => pure [.nil]
          modify (addLocal · tv bty)
          pure (Expr.rescue (.assign tv bd) tmp handler (.var tv bty))
      if retries then
        pure (Expr.seq (.assign flag .tru) (.while (.var flag [.bool]) (.seq (.assign flag .fls) node)))
      else pure node
  match ← field v "ensure" with
  | .null => pure core
  | e => pure (.ensure core (← body T (← arr e)))

/-- Where a `case` or a match reads its subject: a path the model narrows
(a local, an immutable field of `self`), or a local it is held in
(evaluated once, as Rust does). -/
partial def subject (T : Tables) (tmp : String) (subjJ : Json) (stTy : Ty) :
    CM (Expr × (Ty → Expr) × Option String) := do
  -- Whether a field of the method's class (or one above) is `var`: the
  -- model narrows only immutable ones.
  let fieldVar (f : String) : CM Bool := do
    let some rc := (← read).rcls | pure true
    let mut c := rc
    for _ in [0:T.classes.size] do
      let cj ← T.cls c
      for fj in (← arr (← field cj "fields")) do
        if (← str (← field fj "name")) == f then return (← field fj "var") == .bool true
      match ← field cj "superclass" with
      | .null => return true
      | sj => c ← nat (← field sj "id")
    pure true
  let tmpRoute : CM (Expr × (Ty → Expr) × Option String) := do
    let e ← expr T subjJ
    modify (addLocal · tmp stTy)
    pure (Expr.assign tmp e, fun t => Expr.var tmp t, none)
  match ← variant (← field subjJ "kind") with
  | ("Local", x) => do let x ← localName (← str x); pure (Expr.nil, fun t => Expr.var x t, some x)
  | ("IVar", f) => do
    let f ← str f
    -- (`@f`: a field, which only `initialize` may assign.)
    if ← fieldVar f then tmpRoute else pure (Expr.nil, fun t => Expr.field f t, some s!"@{f}")
  | _ => tmpRoute

/-- Declare what a compiled pattern assigns: its temporaries, and the
names it binds unless declared before (`before`). -/
partial def declarePat (before : Locals) (c : PatC) : CM Unit := do
  for (x, t) in c.tmps do modify (addLocal · x t)
  for (x, t) in c.names do
    unless before.any (·.1 == x) do modify (addLocal · x t)

/-- `case subject in arms else els` (docs/01 §11) as tests (`compilePat`):
an arm's pattern a test on the subject and assignments, its guard after
them; without `else`, a closed type (variants, `data`, `nil`, `Bool`, or
more than one member) must be covered (`absurd`, docs/02 §6), an open
one raises `NoMatchingPatternError`. -/
partial def caseIn (T : Tables) (id : Nat) (v : Json) : CM Expr := do
  let subjJ ← field v "subject"
  let st ← field T.nodeTypes (toString (← nat (← field subjJ "id")))
  let stTy ← T.ty st
  let before ← get
  -- A name no program can spell.
  let (pre, rd, subjLocal) ← subject T s!"case#{id}" subjJ stTy
  let armsJ := (← arr (← field v "arms")).toList
  -- An arm's names are its own (docs/01 §11): fresh, shadowing an outer
  -- local, gone after the arm; its guard and body a scope.
  let arms ← (List.range armsJ.length).zip armsJ |>.mapM fun (i, arm) => do
    let c ← compilePat T s!"case#{id}#{i}" rd st stTy (← field arm "pattern")
    let m := c.names.map fun (x, _) => (x, s!"{x}#p{id}.{i}")
    let c := c.rename m
    for (x, t) in c.names do modify (addLocal · x t)
    withReader (fun w => { w with renames := m ++ w.renames }) (inScope do
      let guard ← match ← field arm "guard" with
        | .null => pure none
        | g =>
          let e ← withReader (fun w => { w with scopeTop := false }) (expr T (← field g "cond"))
          pure (some (if (← field g "negate") == .bool true then Expr.not e else e))
      let bd ← body T (← arr (← field arm "body"))
      pure (c, guard, bd))
  -- The subject is read again by each test (the path the model narrows),
  -- where the program reads it once: out of range when a pattern or a
  -- guard may assign it.
  if let some x := subjLocal then
    if arms.any (fun (_, g, _) => (g.map (·.assigned.contains x)).getD false) then
      throw "a case whose guard assigns its subject"
    if x.startsWith "@" && (← read).init.isSome && arms.any (fun (_, g, _) => g.isSome) then
      throw "a case on a field with a guard in initialize"
  for (c, _, _) in arms do declarePat before c
  let els ← match ← field v "els" with
    | .null => pure none
    | e => pure (some (← body T (← arr e)))
  -- Closed as the Rust checker has it (`is_closed_type` for each member,
  -- or more than one member once enums are expanded).
  let members ← patMembers st
  let closedOne (m : Json) : M (Bool × Nat) := do
    match ← str (← field m "t") with
    | "class" =>
      let c ← T.cls (← nat (← field m "id"))
      let kind ← str (← field c "kind")
      let name ← str (← field c "name")
      let n ← if kind == "Enum" then do pure (← variantsOf T (← nat (← field c "id"))).length
        else pure 1
      pure (kind == "Data" || kind == "Variant" || kind == "Enum" || name == "Nil" || name == "Bool", n)
    | _ => pure (false, 1)
  let infos : List (Bool × Nat) ← members.mapM fun m => (closedOne m : CM (Bool × Nat))
  let closed := infos.all (fun i => i.1) || (infos.map (fun i => i.2)).sum > 1
  let nm ← noMatchE T
  let last := match els with
    | some e => e
    | none => if closed then .absurd else nm
  let chain := arms.foldr (fun (c, guard, bd) rest =>
    match guard with
    | some g => Expr.ite (PatC.testOr (PatC.conj (c.test, c.post) (some g, .nil)).1) bd rest
    | none => match c.test with
      | some t => .ite t (.seq c.post bd) rest
      | none => .seq c.post bd) last
  return .seq pre chain

/-- `value => pattern` (raises when it does not match) and `value in
pattern` (a `Bool`, the bindings made where it is true). -/
partial def matchPattern (T : Tables) (id : Nat) (v : Json) : CM Expr := do
  let valJ ← field v "value"
  let st ← field T.nodeTypes (toString (← nat (← field valJ "id")))
  let stTy ← T.ty st
  let before ← get
  let (pre, rd, subjLocal) ← subject T s!"match#{id}" valJ stTy
  let c ← compilePat T s!"match#{id}#0" rd st stTy (← field v "pattern")
  -- It binds into the enclosing scope once it matched whole (docs/01
  -- §11): into temporaries while it tests, then the names (a name a
  -- `rescue` clause or an arm has is theirs).
  let tmpOf (x : String) : String := s!"{x}#m{id}"
  let real ← c.names.mapM fun (x, t) => do pure (x, ← localName x, t)
  let c := c.rename (c.names.map fun (x, _) => (x, tmpOf x))
  -- (`v in p` rebinding a local: its false side keeps the local as it
  -- was, which the model's `&&` cannot say.)
  if (← field v "raises") != .bool true && real.any (fun (_, r, _) => before.any (·.1 == r)) then
    throw "an in rebinding a local"
  let c := { c with
    post := real.foldl (fun acc (x, r, t) => Expr.seq acc (.assign r (.var (tmpOf x) t))) c.post,
    tmps := c.tmps ++ c.names,
    names := real.map fun (_, r, t) => (r, t) }
  if let some x := subjLocal then
    if c.names.any (·.1 == x) then throw "a match whose pattern assigns its subject"
  declarePat before c
  if (← field v "raises") == .bool true then
    let nm ← noMatchE T
    return .seq pre (match c.test with
      | some t => .ite t (.seq c.post .nil) nm
      | none => .seq c.post .nil)
  else
    -- (`in`'s value: its bindings after the test made where it is true,
    -- as an `&&`; the model's `true` keeps the false side alive, which
    -- only makes it stricter.)
    return .seq pre (match c.test with
      | some t => .and t (.seq c.post .tru)
      | none => .seq c.post .tru)

partial def call (T : Tables) (id : Nat) (c : Json) : CM Expr := do
  let name ← str (← field c "name")
  let recvJ ← field c "recv"
  -- (`x&.m`: nil when `x` is, not the model's call.)
  if (c.getObjVal? "safe_nav").toOption == some (.bool true) then throw "a safe navigation call"
  -- `x.m!` that the checker resolved to `m` (docs/01 §10): `x = x.m`.
  if name.endsWith "!" then
    if let .ok t := T.calls.getObjVal? (toString id) then
      if (t.getObjValAs? String "t").toOption == some "method" then
        let m ← T.method (← nat (← field t "method"))
        let base := String.ofList (name.toList.dropLast)
        if (← str (← field m "name")) == base then
          if recvJ == .null then throw "a bang sugar without a receiver"
          let (k, x) ← variant (← field recvJ "kind")
          unless k == "Local" do throw "a bang sugar on a receiver not a local"
          let x ← localName (← str x)
          return .assign x (← call T id (c.setObjVal! "name" (Json.str base)))
  -- (`&p`: a procedure given as the block.)
  let mut args : List Json := []
  let mut bpass : Option Json := none
  for a in (← arr (← field c "args")) do
    match ← variant a with
    | ("BlockPass", e) => bpass := some e
    | _ => args := args ++ [← positional a]
  let blk ← field c "block"
  -- (The receiver of `new`, a class, is not an expression here.)
  let isNew := match T.calls.getObjVal? (toString id) with
    | .ok t => (t.getObjValAs? String "t").toOption == some "constructor"
    | .error _ => false
  let recv : Option Expr ← match recvJ with
    | .null => pure none
    | r => if isNew then pure none else pure (some (← expr T r))
  let target ← match T.calls.getObjVal? (toString id) with
    | .ok t => pure t
    | .error _ => throw s!"call {name} not resolved"
  -- `&p` reaches a program's method only (below).
  if bpass.isSome then
    if (← str (← field target "t")) != "method" || ["nil?", "==", "!=", "is_a?"].contains name then
      throw "a block pass to a built-in"
  let lit (a : Json) : M String := do pure (← variant (← field a "kind")).1
  -- A data-less variant as a value (compared below).
  let isVariant (a : Json) : M Bool := do
    unless (← lit a) == "Const" do return false
    match T.constTargets.getObjVal? (toString (← nat (← field a "id"))) with
    | .ok t => pure ((← str (← field t "t")) == "variant")
    | .error _ => pure false
  -- `x == V` (`V == x`, `!=`) with a variant without data: as Rust
  -- narrows it (`equality_facts`), `x.is_a?(V)`, the variant having one
  -- value. A program's own `==` or `!=` keeps it out of range.
  if (name == "==" || name == "!=") && recvJ != .null then
    if let [a] := args then
      let other ← if ← isVariant a then pure (some (recvJ, a))
        else if ← isVariant recvJ then pure (some (a, recvJ)) else pure none
      if let some (x, vj) := other then
        if ← T.methods.anyM (fun m => do
            let n ← str (← field m "name")
            pure ((n == "==" || n == "!=") && (← field m "native") != .bool true)) then
          throw "a comparison with a variant value and a user-defined =="
        let target ← match T.constTargets.getObjVal? (toString (← nat (← field vj "id"))) with
          | .ok t => pure t
          | .error _ => throw "a constant read not resolved"
        let some q := T.qclass (← nat (← field target "id")) | throw "a variant out of range"
        let test := Expr.isA (← expr T x) (.cls q [])
        return if name == "==" then test else .not test
  -- The tests: forms of their own (design §1.3).
  match name, recv, args, blk with
  | "nil?", some r, [], .null => return .isNil r
  | "==", some r, [a], .null =>
    match ← lit a with
    | "Nil" => return .eqNil r
    | "True" => return .eqTrue r
    | "False" => return .eqFalse r
    | _ => pure ()
  | "!=", some r, [a], .null =>
    -- The model's `!=` is `!(==)`; a program's own `!=` (a `data` type may
    -- define one) is out of range.
    -- (The call resolves to `Object#!=` on an `X?`: look for any.)
    if ← T.methods.anyM (fun m => do
        pure ((← str (← field m "name")) == "!=" && (← field m "native") != .bool true)) then
      throw "a user-defined !="
    match ← lit a with
    | "Nil" => return .neNil r
    | "True" => return .not (.eqTrue r)
    | "False" => return .not (.eqFalse r)
    | _ => pure ()
  | _, _, _, _ => pure ()
  match ← str (← field target "t") with
  | "is_a" =>
    let some r := recv | throw "is_a? without a receiver"
    match ← T.ty (← field target "type") with
    | [.cls k as] =>
      -- (The Rust checker tests an array's elements: docs/02 §7.)
      if k == arrIdx then throw "is_a? of an array type"
      return .isA r (.cls k as)
    | [a] => return .isA r a
    | _ => throw "is_a? of a union"
  -- `raise` (docs/01 §12): an exception, a class (made without a
  -- message, or with the second argument), a string (a `RuntimeError`);
  -- bare in a `rescue` clause, the exception being handled.
  | "raise" =>
    let excAtom (cid : Nat) : M Atom := do
      match T.qclass cid with
      | some q => pure (.cls q [])
      | none => throw s!"raise of {← T.className cid}"
    let made (cid : Nat) (as : List Expr) : CM Expr := do
      -- The run time makes it with its fields `nil`, no `initialize` run.
      unless ← T.excPlain cid do throw "raise of an exception class with fields or initialize"
      pure (.prim "new" as (as.map fun _ => [.nil, .bool, .int, .str, .cls 0 []]) [← excAtom cid])
    match args with
    | [] =>
      let some x := (← read).exc | throw "a bare raise outside rescue"
      let some eid ← T.classId "Exception" | throw "no Exception"
      return .raise (.var x [← excAtom eid])
    | [a] =>
      let aty ← field T.nodeTypes (toString (← nat (← field a "id")))
      match ← str (← field aty "t") with
      | "class_object" =>
        unless (← variant (← field a "kind")).1 == "Const" do throw "raise of a class value"
        let target ← match T.constTargets.getObjVal? (toString (← nat (← field a "id"))) with
          | .ok t => pure t
          | .error _ => throw "a constant read not resolved"
        unless (← str (← field target "t")) == "class" do throw "raise of a class value"
        return .raise (← made (← nat (← field target "id")) [])
      | _ =>
        match ← T.ty aty with
        | [.str] =>
          let some rid ← T.classId "RuntimeError" | throw "no RuntimeError"
          return .raise (← made rid [← expr T a])
        | _ => return .raise (← expr T a)
    | [k, msg] =>
      unless (← variant (← field k "kind")).1 == "Const" do throw "raise of a class value"
      let target ← match T.constTargets.getObjVal? (toString (← nat (← field k "id"))) with
        | .ok t => pure t
        | .error _ => throw "a constant read not resolved"
      unless (← str (← field target "t")) == "class" do throw "raise of a class value"
      return .raise (← made (← nat (← field target "id")) [← expr T msg])
    | _ => throw "raise with more arguments"
  -- `f.call(args)` (`f.(args)`, `f[args]`): a procedure run.
  | "proc_call" =>
    unless blk == .null do throw "a block given to a procedure"
    let some r := recv | throw "a procedure call without a receiver"
    return .callProc r (← args.mapM (expr T))
  | "constructor" =>
    -- `C.new(args)`: the fields' defaults, then `initialize`.
    unless blk == .null do throw "a block given to new"
    let k ← nat (← field target "class")
    let some q := T.qclass k | throw s!"new of {← T.className k}"
    -- An exception made: what the built-in `initialize` gives, opaque.
    if ← T.excInit k then
      unless ← T.excPlain k do throw "new of an exception class with fields"
      return .prim "new" (← args.mapM (expr T)) (← args.mapM fun _ => pure [.nil, .bool, .int, .str, .cls 0 []])
        [.cls q []]
    -- The Rust checker picks among the ancestors' overloads: in range
    -- only where it picks the one the model's `new` runs.
    let init := match ← field target "init" with
      | .null => none
      | j => j.getNat?.toOption
    unless init == (← T.nearestInit k) do throw "a new taking an initialize further up"
    -- The type arguments the checker gave the object (one type across
    -- the passes, as `nodeTy` asks).
    if T.varied.contains (.num id) then throw s!"node {id} checked with different types"
    let (q', targs) ← T.tyClass (← field T.nodeTypes (toString id))
    unless q' == q do throw "a new of another class than its type"
    return .new q targs (← args.mapM (expr T))
  | "method" =>
    let m ← T.method (← nat (← field target "method"))
    let native := (← field m "native") == .bool true
    -- On an array: `Array`'s methods and those of the modules it includes
    -- (`Enumerable[T]`), native or written in Quarz, are built-in calls
    -- typed by their declarations (the prelude's bodies are the Rust
    -- checker's to check, not the model's); `Object`'s are out of range.
    let onArray (rt : Ty) : Bool := rt.any fun a => match a with | .cls k _ => k == arrIdx | _ => false
    -- (An extension's method: which extension applies, and its own
    -- parameters, are stage 6's.)
    if (← field m "extension") != .null then throw s!"an extension's method {name}"
    -- The receiver's view of the method's owner (its parameters, `Self`).
    let recvEnv : Option (List (Nat × Ty)) ← match (recvJ.getObjVal? "id").toOption with
      | none => pure none
      | some rid => do
        match T.nodeTypes.getObjVal? (toString (← nat rid)) with
        | .ok rj => T.receiverEnv rj (← nat (← field m "owner"))
        | .error _ => pure none
    let arrayEnv : Option (List (Nat × Ty)) ← match (recvJ.getObjVal? "id").toOption with
      | none => pure none
      | some rj => do
        let rt ← T.nodeTy (← nat rj)
        if !onArray rt then pure none else
        match rt, recvEnv with
        | [.cls _ [_]], some env =>
          -- (Array's own methods, or its includes': not `Object`'s.)
          let owner ← nat (← field m "owner")
          let (aid, _) ← T.arrayInfo
          let incs ← (← arr (← field (← T.cls aid) "includes")).toList.mapM fun i => do nat (← field i "id")
          unless owner == aid || incs.contains owner do throw s!"an array's method {name} of another class"
          pure (some env)
        | [.cls _ [_]], none => throw s!"an array's method {name} of another class"
        | _, _ => throw "an array method on a union"
    let synth ← str (← field m "synth")
    let as ← args.mapM (expr T)
    -- An accessor `attr_*` makes is a method of the model (`accessor`).
    let owner ← nat (← field m "owner")
    let accessor := (synth.startsWith "FieldGet(" || synth.startsWith "FieldSet(") &&
      (T.qclass owner).any (· ≥ 2) && !T.excIds.contains owner
    -- A method of a module the prelude declares (`Comparable`,
    -- `Enumerable`), which a program's class includes: a built-in call, its
    -- module's parameters and `Self` through the receiver's class.
    let ownerJ ← T.cls owner
    let preludeModule := (← str (← field ownerJ "kind")) == "Module" && (T.qclass owner).isNone
    let preludeModule := preludeModule && owner != T.kernelId
    if preludeModule && recvEnv.isNone then
      throw s!"a method {name} of a module, its receiver's view unknown"
    -- (A built-in call does not dispatch: a program's method of the name,
    -- which a subclass's object would run instead, puts it out of range.)
    if preludeModule then
      let rcid ← match (recvJ.getObjVal? "id").toOption with
        | none => throw s!"a module's method {name} on self"
        | some rid => do
          let rj ← field T.nodeTypes (toString (← nat rid))
          unless (← str (← field rj "t")) == "class" do throw s!"a module's method {name} on a union"
          nat (← field rj "id")
      -- A program's class related to the receiver's (above it: the
      -- module may hide its method, or an abstract stub may hide it;
      -- below: a subclass's object would run its own) defining the name,
      -- or overloading a name the module declares (its body may call it):
      -- the built-in call does not dispatch as Quarz does.
      let modNames ← T.moduleNames owner
      let related ← T.methods.toList.filterM fun m' => do
        let o ← nat (← field m' "owner")
        if (T.qclass o).isNone then return false
        pure ((← rsub T o rcid) || (← rsub T rcid o))
      -- (A related class including the module again, with other
      -- arguments, sees it otherwise than the receiver's, whose view
      -- types the module's body.)
      let includers ← T.classes.toList.filterM fun c => do
        let cid ← nat (← field c "id")
        if (T.qclass cid).isNone then return false
        unless (← rsub T cid rcid) || (← rsub T rcid cid) do return false
        (← arr (← field c "includes")).toList.anyM fun i => do pure ((← nat (← field i "id")) == owner)
      if includers.length > 1 then throw s!"a module's method {name}, its module included twice"
      for m' in related do
        let n' ← str (← field m' "name")
        if n' == name then throw s!"a module's method {name} a program's class defines"
        if modNames.contains n' then
          let ok ← try T.matchesModule owner m' catch _ => pure false
          unless ok do throw s!"a module's method {name}: a program's {n'} of another signature than its module's"
      -- (A program's extension may add an include the tree does not show.)
      let preludeFile ← nat (← field (← T.cls (← T.arrayInfo).1) "file")
      if ← (T.extensions.toList.anyM fun e => do pure ((← nat (← field e "file")) != preludeFile)) then
        throw s!"a module's method {name} with a program's extension"
    if (native || synth != "None" || T.excIds.contains owner || arrayEnv.isSome || preludeModule) && !accessor then
      -- A built-in method: its declared types. On the implicit receiver,
      -- it takes `self` (it may read its fields), but a `Kernel`
      -- function.
      if bpass.isSome then throw s!"a block pass to built-in {name}"
      -- A block given to it (design §14): scoped as a block here, made a
      -- loop running it any number of times by `unblock`.
      let withBlock (env : List (Nat × Ty)) (e : Expr) : CM Expr := do
        if blk == .null then return e
        let .prim _ pargs pparams pret := e | throw "a built-in call"
        let ty ← match ← field m "block" with
          | .null => throw s!"a block given to built-in {name} that takes none"
          | sig =>
            -- (One it keeps, `at_exit`'s, runs later: not a loop.)
            match ← field sig "name" with
            | .null | .str "&" => field sig "type"
            | _ => throw s!"a block kept by built-in {name}"
        unless (← str (← field ty "t")) == "proc" do throw "a block type"
        -- (A block with a receiver of its own, `Self.() -> R`: `self` is not
        -- the enclosing one.)
        unless (← field ty "recv") == .null do throw s!"a block of built-in {name} with a receiver"
        let tys ← (← arr (← field ty "params")).toList.mapM fun t => (T.tyIn env t : M Ty)
        unless tys.all Ty.closed do throw s!"a block of built-in {name} of an open type"
        let rj ← field ty "ret"
        let sret ← T.tyIn env rj
        unless sret.closed do throw s!"a block of built-in {name} of an open type"
        let pjs := (← arr (← field (← field blk "params") "list")).toList
        let ps ← pjs.mapM fun p => do
          unless (← str (← field p "kind")) == "Positional" do throw "a block parameter not positional"
          str (← field p "name")
        unless ps.length == tys.length do throw s!"a block of built-in {name}'s parameters"
        -- (An annotated parameter is declared by its annotation, which the
        -- tree keeps unresolved: out of range.)
        for ((x, t), pj) in (ps.zip tys).zip pjs do
          unless (pj.getObjVal? "ty").toOption.getD .null == .null do
            throw "an annotated block parameter"
          if (← get).any (fun (y, u) => y == x && u != t) then
            throw s!"block parameter {x} of two types"
          modify (addLocal · x t)
        let bd ← T.declaredResult id (← hidingParams ps (body T (← arr (← field blk "body"))))
        if hasRet bd then throw "a return in a block"
        let bd := if (← str (← field rj "t")) == "void" then Expr.seq bd .nil else bd
        return .callBlk (.prim ("#builtin " ++ name) pargs pparams pret) name [.prim "#sig" [] tys sret] ps bd
      -- A rest parameter (`*args`) takes as many arguments as are given,
      -- each of its element type.
      -- Otherwise the positional parameters the call fills; those it
      -- leaves, and keyword ones, must have defaults.
      let ps := (← arr (← field m "params")).toList
      -- An array's method: its declared types, the receiver's element type
      -- for `Array`'s parameter, the method's own from the call's result
      -- type (the checker's instantiation).
      if let some env0 := arrayEnv then
        let some r := recv | throw "an array method without a receiver"
        let rt ← T.nodeTy (← nat (← field recvJ "id"))
        let env ← T.solve env0 (← field m "ret") (← T.nodeTy id)
        -- (A lower bound, `U >: T`, widens what the checker chose: a
        -- result it narrowed below the bound disagrees.)
        let mut env := env
        for tp in (← arr (← field m "type_params")) do
          let tid ← nat (← field tp "id")
          let some u := (env.find? (·.1 == tid)).map (·.2) | throw "a method type parameter not in the result"
          unless (← arr (← field tp "bounds")).isEmpty do throw "a bounded method type parameter"
          match ← field tp "lower" with
          | .null => pure ()
          | lj =>
            let lo ← T.tyIn env lj
            env := env.map fun (i, t) => if i == tid then (i, t ++ lo.filter (!t.contains ·)) else (i, t)
        if ← ps.anyM (fun p => do pure ((← str (← field p "kind")) != "Positional")) then
          throw "an array method's parameters"
        let rest := ps.drop as.length
        for p in rest do
          unless (← field p "default") == .bool true do throw "a built-in call leaving a parameter"
        let params ← (ps.take as.length).mapM fun p => do T.tyIn env (← field p "type")
        return ← withBlock env (.prim name (r :: as) (rt :: params) (← T.tyIn env (← field m "ret")))
      -- (A generic one's type parameters: what the call's result type
      -- says, where it says it; a lower bound widens it.)
      let tps ← arr (← field m "type_params")
      let env0 := recvEnv.getD []
      let env ← if tps.isEmpty then pure env0 else do
        let env ← match T.nodeTy id with
          | .ok rt => T.solve env0 (← field m "ret") rt
          | .error _ => pure env0
        let mut env := env
        for tp in tps do
          let tid ← nat (← field tp "id")
          if env.any (·.1 == tid) then
            match ← field tp "lower" with
            | .null => pure ()
            | lj =>
              let lo ← T.tyOrTop lj env
              env := env.map fun (i, t) => if i == tid then (i, t ++ lo.filter (!t.contains ·)) else (i, t)
        pure env
      let params ← if ← ps.anyM (fun p => do pure ((← str (← field p "kind")) == "Rest")) then
          match ps with
          | [p] => do
            -- (Its declared type, `Array[E]`: each argument an `E`.)
            let t ← match ← T.tyOrTop (← field p "type") env with
              | [.cls k [e]] => pure (if k == arrIdx then e else [.cls k [e]])
              | t => pure t
            pure (as.map fun _ => t)
          | _ => throw "a rest parameter with others"
        else do
          let pos ← ps.filterM fun p => do pure ((← str (← field p "kind")) == "Positional")
          let rest := ps.filter fun p => !(pos.take as.length).contains p
          for p in rest do
            unless (← field p "default") == .bool true do throw "a built-in call leaving a parameter"
          (pos.take as.length).mapM fun p => do T.tyOrTop (← field p "type") env
      let ret ← T.tyOrTop (← field m "ret") env
      let (rs, rps) ← match recv with
        | some r => do
          let rt ← T.nodeTy (← nat (← field recvJ "id"))
          pure ([r], [rt])
        | none =>
          if (← nat (← field m "owner")) == T.kernelId then pure ([], [])
          else pure ([.self], [[.cls 0 []]])
      return ← withBlock env (.prim name (rs ++ as) (rps ++ params) ret)
    -- (A program's method: by its model name, an overload's its own; on
    -- a union, the members' overloads may differ.)
    let rawName := name
    let name ← T.modelName m
    if name != rawName then
      if let some rj := (recvJ.getObjVal? "id").toOption then
        if (← T.nodeTy (← nat rj)).length > 1 then throw s!"an overload of {rawName} on a union receiver"
    if recv.isNone && T.qclass (← nat (← field m "owner")) == some 1 && !(← read).top then
      throw "a top-level method called from a class"
    let r := recv.getD .self
    -- A named block parameter: the method takes a procedure (its last
    -- parameter), the block given made a lambda.
    -- (Of a union, the classes' methods may differ in whether they keep
    -- the block: out of range when a method of the name keeps it.)
    if blk != .null || bpass.isSome then
      if let some rj := (recvJ.getObjVal? "id").toOption then
        let classes := (← T.nodeTy (← nat rj)).filter fun a => match a with | .cls .. => true | _ => false
        let keeps ← T.methods.anyM fun m' => do
          if (← str (← field m' "name")) != rawName then return false
          match ← field m' "block" with
          | .null => pure false
          | b => pure (match ← field b "name" with | .null | .str "&" => false | _ => true)
        if classes.length > 1 && keeps then throw "a block given to a union receiver"
    let named ← match ← field m "block" with
      | .null => pure false
      | sig => do match ← field sig "name" with
        | .null | .str "&" => pure false
        | _ => pure true
    if let some e := bpass then
      unless blk == .null do throw "a block and a block pass"
      let pe ← expr T e
      if named then return .call r name (as ++ [pe])
      -- Into an anonymous block: a block calling it, the procedure read
      -- once, before the call (the receiver and the arguments plain, so
      -- the order does not matter).
      let plain : Expr → Bool := fun x => match x with
        | .var .. | .self | .nil | .tru | .fls | .int _ | .str _ | .flt _ => true
        | _ => false
      unless plain r && as.all plain do throw "a block pass after a call"
      unless (match pe with | .var .. => true | _ => false) do throw "a block pass of an expression"
      let sig ← field m "block"
      let ty ← field sig "type"
      unless (← str (← field ty "t")) == "proc" do throw "a block type"
      let tys ← (← arr (← field ty "params")).toList.mapM fun t => (T.ty t : M Ty)
      unless tys.all Ty.closed do throw "a block pass to a generic method"
      let void := (← str (← field (← field ty "ret") "t")) == "void"
      let pt ← T.nodeTy (← nat (← field e "id"))
      let tmp := s!"&{id}"
      let ps := (List.range tys.length).map fun i => s!"&{id}.{i}"
      modify (addLocal · tmp pt)
      for (x, t) in ps.zip tys do modify (addLocal · x t)
      let run := Expr.callProc (.var tmp pt) ((ps.zip tys).map fun (x, t) => .var x t)
      return .seq (.assign tmp pe) (.callBlk r name as ps (if void then .seq run .nil else run))
    match blk with
    | .null => return .call r name as
    | b =>
      if named then
        let ps ← (← arr (← field (← field b "params") "list")).toList.mapM fun p => do
          str (← field p "name")
        let ty ← field (← field m "block") "type"
        let tys ← (← arr (← field ty "params")).toList.mapM fun t => (T.ty t : M Ty)
        unless tys.all Ty.closed do throw "a kept block of a generic method"
        unless ps.length == tys.length do throw "a block's parameters"
        let rj ← field ty "ret"
        unless (← T.ty rj).closed do throw "a kept block of a generic method"
        let lam ← lambdaOf T ps tys (← T.ty rj) ((← str (← field rj "t")) == "void") (← arr (← field b "body"))
          (some id)
        return .call r name (as ++ [lam])
      let ps ← (← arr (← field (← field b "params") "list")).toList.mapM fun p => do
        str (← field p "name")
      -- The block's parameters, as the method's block declares them.
      let sig ← match ← field m "block" with
        | .null => throw "a block given to a method that takes none"
        | s => pure s
      match ← str (← field (← field sig "type") "t") with
      | "proc" =>
        let tys ← (← arr (← field (← field sig "type") "params")).toList.mapM fun t => (T.ty t : M Ty)
        -- Types naming the method's class's parameters, as the receiver
        -- sees them: its own arguments when it is of that class (another
        -- class's view, through the chain, is out of range here).
        let tys ← if tys.all Ty.closed then pure tys else do
          let some rj := recvJ.getObjVal? "id" |>.toOption
            | throw "a block of a generic method on self"
          let rt ← T.nodeTy (← nat rj)
          let owner := T.qclass (← nat (← field m "owner"))
          match rt with
          | [.cls k as] =>
            unless owner == some k do throw "a block of a generic method through a subclass"
            pure (tys.map (Ty.subst as))
          | _ => throw "a block of a generic method on a union"
        -- A parameter named like a local of another type (another
        -- block's parameter: one local for the model).
        for (x, t) in ps.zip tys do
          if (← get).any (fun (y, u) => y == x && u != t) then
            throw s!"block parameter {x} of two types"
          modify (addLocal · x t)
      | _ => throw "a block type"
      let bd ← T.declaredResult id (← hidingParams ps (body T (← arr (← field b "body"))))
      -- A `return` from a block is not in v1.
      if hasRet bd then throw "a return in a block"
      -- `-> Void`: its value discarded, nil.
      let void := match (← field sig "type").getObjVal? "ret" with
        | .ok rj => (rj.getObjValAs? String "t").toOption == some "void"
        | .error _ => false
      return .callBlk r name as ps (if void then .seq bd .nil else bd)
  | t => throw s!"a {t} call"


/-- A lambda of parameters `names` of types `pts`, giving `ret` (`void`:
`-> Void`), of body `bodyJ` (a block given to a method that may keep it
too: design §13.10). -/
partial def lambdaOf (T : Tables) (names : List String) (pts : List Ty) (ret : Ty) (void : Bool)
    (bodyJ : Array Json) (call : Option Nat := none) : CM Expr := do
  let w ← read
  if w.init.isSome then throw "a lambda in initialize"
  if w.rcls.isNone && !w.top then throw "a lambda in a default"
  let outer ← get
  let around := (outer ++ w.captured).filter fun (x, _) => !names.contains x
  -- Its parameters, then the locals around it (it may assign them: C1),
  -- then its own (first assigned in it).
  set ((names.zip pts ++ around : Locals))
  let bd ← withReader (fun w => { w with exc := none, retryFlag := none, captured := around })
    (hidingParams names (body T bodyJ))
  let bd ← match call with
    | some id => T.declaredResult id bd
    | none => pure bd
  let mine ← get
  set outer
  let own := mine.drop (names.length + around.length)
  let mine := names.zip pts ++ own
  if hasRet bd then throw "a return in a lambda"
  -- Its body reads the method's locals and `self`'s fields as declared
  -- (R2a): a read the Rust checker narrows further is out of range.
  let narrower (decl t : Ty) : Bool := !(decl.all fun a => t.contains a)
  let fieldDecl (f : String) : CM (Option Ty) := do
    let some rc := (← read).rcls | pure none
    let mut c := rc
    for _ in [0:T.classes.size] do
      let cj ← T.cls c
      for fj in (← arr (← field cj "fields")) do
        if (← str (← field fj "name")) == f then return some (← T.ty (← field fj "type"))
      match ← field cj "superclass" with
      | .null => return none
      | sj => c ← nat (← field sj "id")
    pure none
  let rec reads : Expr → List (Bool × String × Ty)
    | .var x t => [(true, x, t)]
    | .field f t => [(false, f, t)]
    | .assign _ e | .setField _ e | .ret e | .raise e | .isNil e | .isA e _ | .eqNil e | .neNil e
    | .eqTrue e | .eqFalse e | .not e => reads e
    | .new _ _ as | .superInit _ as | .yield as | .prim _ as _ _ => as.flatMap reads
    | .call r _ as | .callProc r as => reads r ++ as.flatMap reads
    | .callBlk r _ as _ b => reads r ++ as.flatMap reads ++ reads b
    | .seq a b | .while a b | .and a b | .or a b | .ensure a b => reads a ++ reads b
    | .ite c t e => reads c ++ reads t ++ reads e
    | .rescue b _ h e => reads b ++ reads h ++ reads e
    | .lambda _ _ _ b => reads b
    | _ => []
  -- (A test in the body narrows there: the model does too; a local as a
  -- condition, its truthiness tested.)
  let cond : Expr → List String := fun e => match e with
    | .var x _ => [x]
    | _ => []
  let rec tested : Expr → List String
    | .isNil (.var x _) | .isA (.var x _) _ | .eqNil (.var x _) | .neNil (.var x _)
    | .eqTrue (.var x _) | .eqFalse (.var x _) => [x]
    | .assign _ e | .setField _ e | .ret e | .raise e | .isNil e | .isA e _ | .eqNil e | .neNil e
    | .eqTrue e | .eqFalse e => tested e
    | .new _ _ as | .superInit _ as | .yield as | .prim _ as _ _ => as.flatMap tested
    | .call r _ as | .callProc r as => tested r ++ as.flatMap tested
    | .callBlk r _ as _ b => tested r ++ as.flatMap tested ++ tested b
    | .seq a b | .ensure a b => tested a ++ tested b
    | .while c b | .and c b | .or c b => cond c ++ tested c ++ tested b
    | .ite c t e => cond c ++ tested c ++ tested t ++ tested e
    | .not c => cond c ++ tested c
    | .rescue b _ h e => tested b ++ tested h ++ tested e
    | .lambda _ _ _ b => tested b
    | _ => []
  let tested := tested bd
  for (isLocal, x, t) in reads bd do
    if isLocal then
      if let some (_, d) := around.find? (·.1 == x) then
        if !mine.any (·.1 == x) && !tested.contains x && narrower d t then
          throw s!"a lambda reading {x} narrower than declared"
    else
      if let some d ← fieldDecl x then
        if narrower d t then throw s!"a lambda reading @{x} narrower than declared"
  -- `-> Void`: its value discarded, nil.
  let bd := if void then Expr.seq bd .nil else bd
  pure (.lambda (names.zip pts) own ret bd)

end

/-- The method an `attr_reader` or `attr_writer` makes, of QCore class
`owner`. -/
def accessor (T : Tables) (owner : Nat) (m : Json) : M (Option Method) := do
  let synth ← str (← field m "synth")
  let name ← str (← field m "name")
  let fieldOf (pre : String) : String := String.ofList ((synth.toList.drop pre.length).dropLast.dropLast)
  -- (Other generated methods, `with` and `to_h`, are built-in calls.)
  unless synth.startsWith "Field" || synth == "DataInit" do return none
  let ret ← T.ty (← field m "ret")
  if synth.startsWith "FieldGet(\"" then
    pure (some ⟨owner, name, [], ret, none, [], .field (fieldOf "FieldGet(\"") ret⟩)
  else if synth.startsWith "FieldSet(\"" then
    let [p] := (← arr (← field m "params")).toList | throw "a writer's parameters"
    let t ← T.ty (← field p "type")
    pure (some ⟨owner, name, [("v", t)], ret, none, [("v", t)],
      .setField (fieldOf "FieldSet(\"") (.var "v" t)⟩)
  else if synth == "DataInit" then
    -- A `data` type's `initialize`: each field from the parameter of its
    -- name, in order.
    let ps ← (← arr (← field m "params")).toList.mapM fun p => do
      if (← field p "default") == .bool true then throw "a data field with a default"
      pure (← str (← field p "name"), ← T.ty (← field p "type"))
    let bd := ps.foldr (fun (x, t) acc => .seq (.setField x (.var x t)) acc) .nil
    pure (some ⟨owner, name, ps, [.nil], none, ps, bd⟩)
  else pure none

/-- A Rust method as a QCore one. -/
def method (T : Tables) (owner : Nat) (m : Json) (d : Json) : M Method := do
  if (← field m "singleton") == .bool true then throw "a class method"
  unless (← arr (← field m "type_params")).isEmpty do throw "a method type parameter"
  unless (← field m "extension") == .null do throw "an extension's method"
  -- The Rust variance check skips private methods (docs/02 §3), the
  -- model's checks every one: a private method of a class with a variant
  -- parameter is out of range.
  if (← field d "visibility") == .str "Private" then
    let tps ← arr (← field (← T.cls (← nat (← field m "owner"))) "type_params")
    if ← tps.anyM (fun p => do pure ((← str (← field p "variance")) != "Invariant")) then
      throw "a private method of a variant class"
  let name ← T.modelName m
  let params ← (← arr (← field m "params")).toList.mapM fun p => do
    if (← str (← field p "kind")) != "Positional" then throw "a parameter not positional"
    if (← field p "default") == .bool true then throw "a parameter with a default"
    pure (← str (← field p "name"), ← T.ty (← field p "type"))
  -- A method a `static` statement generated (docs/14 §5): its body is a
  -- block of the `static def` that made it, not in the tree.
  if (← field m "generated") == .bool true then throw "a generated method"
  let ret ← T.ty (← field m "ret")
  if (← field m "block_optional") == .bool true then throw "an optional block"
  let (block, bproc) ← match ← field m "block" with
    | .null => pure (none, none)
    | b => do
      let t ← field b "type"
      unless (← str (← field t "t")) == "proc" do throw "a block type"
      match ← field b "name" with
      | .null | .str "&" =>
        let ps ← (← arr (← field t "params")).toList.mapM T.ty
        pure (some ⟨ps, ← T.ty (← field t "ret")⟩, none)
      | .str n =>
        -- A named block, which the method may keep: its last parameter,
        -- a procedure (design §13.10).
        if name == "initialize" then throw "a named block parameter of initialize"
        pure (none, some (n, ← T.ty t))
      | _ => throw "a block parameter's name"
  let params := params ++ bproc.toList
  -- (In `initialize`, the superclass, for `super`.)
  let init ← if name != "initialize" then pure none else do
    let sup ← match ← field (← T.cls (← nat (← field m "owner"))) "superclass" with
      | .null => pure 0
      | t => pure (← T.tyClass t).1
    pure (some (params, sup))
  let w : Where := ⟨owner == 1, init, some (← nat (← field m "owner")), none, none, [], bproc, [], [], true, false⟩
  let (bd, ls) ← ((body T (← arr (← field d "body"))).run w).run params
  -- (`yield` runs the block given, whatever the parameter holds later.)
  if let some (n, _) := bproc then
    if (bd.assigned ++ bd.procAssigned).contains n then throw "a named block parameter assigned"
  -- The model narrows without the bounds (a test of a `T <: Shape` value
  -- keeps `T` where the Rust checker may not): a method of a class with a
  -- bounded parameter that tests or loops is out of range.
  let tps ← arr (← field (← T.cls (← nat (← field m "owner"))) "type_params")
  if narrows bd then
    if ← tps.anyM (fun p => do pure !(← arr (← field p "bounds")).isEmpty) then
      throw "a test in a class with a bounded parameter"
  -- `def initialize(@x: T)`: the field assigned from the parameter first.
  let ivars ← (← arr (← field m "params")).toList.filterMapM fun p => do
    if (← field p "assigns_ivar") == .bool true then
      pure (some (← str (← field p "name"), ← T.ty (← field p "type")))
    else pure none
  let bd := ivars.foldr (fun (x, t) b => .seq (.setField x (.var x t)) b) bd
  pure ⟨owner, name, params, ret, block, ls, bd⟩

/-- A block given to a built-in method (`callBlk` of a `#builtin` call,
scoped as a block: design §14), made a loop: the call first (its result
held), then the block's body run any number of times, its parameters
any values of their types, its value at most the block's result type.
New locals (the results held) go to the method, or to the lambda the
call is in. -/
partial def unblockExpr : Expr → StateM (Nat × List (String × Ty)) Expr
  | .callBlk r m as ps b => do
    match r, as with
    | .prim n pargs pparams pret, [.prim "#sig" [] tys sret] =>
      if n.startsWith "#builtin " then
        let pargs ← pargs.mapM unblockExpr
        let b ← unblockExpr b
        let (i, ls) ← get
        let tmp := s!"&b{i}"
        set (i + 1, ls ++ [(tmp, pret)])
        let run := (ps.zip tys).foldr (fun (x, t) acc => Expr.seq (.assign x (.prim "arg" [] [] t)) acc)
          (Expr.prim "result" [b] [sret] [.nil])
        return .seq (.assign tmp (.prim m pargs pparams pret))
          (.seq (.while (.prim "again" [] [] [.bool]) run) (.var tmp pret))
      else pure ()
    | _, _ => pure ()
    return .callBlk (← unblockExpr r) m (← as.mapM unblockExpr) ps (← unblockExpr b)
  | .lambda ps own ret b => do
    let (i, ls) ← get
    set (i, ([] : List (String × Ty)))
    let b ← unblockExpr b
    let (i', inner) ← get
    set (i', ls)
    return .lambda ps (own ++ inner) ret b
  | .assign x e => return .assign x (← unblockExpr e)
  | .setField f e => return .setField f (← unblockExpr e)
  | .new c ts as => return .new c ts (← as.mapM unblockExpr)
  | .superInit d as => return .superInit d (← as.mapM unblockExpr)
  | .call r m as => return .call (← unblockExpr r) m (← as.mapM unblockExpr)
  | .yield as => return .yield (← as.mapM unblockExpr)
  | .prim n as ps t => return .prim n (← as.mapM unblockExpr) ps t
  | .seq a b => return .seq (← unblockExpr a) (← unblockExpr b)
  | .ite c t e => return .ite (← unblockExpr c) (← unblockExpr t) (← unblockExpr e)
  | .while c b => return .while (← unblockExpr c) (← unblockExpr b)
  | .ret e => return .ret (← unblockExpr e)
  | .raise e => return .raise (← unblockExpr e)
  | .rescue b x h e => return .rescue (← unblockExpr b) x (← unblockExpr h) (← unblockExpr e)
  | .ensure b e => return .ensure (← unblockExpr b) (← unblockExpr e)
  | .callProc f as => return .callProc (← unblockExpr f) (← as.mapM unblockExpr)
  | .isNil e => return .isNil (← unblockExpr e)
  | .isA e a => return .isA (← unblockExpr e) a
  | .eqNil e => return .eqNil (← unblockExpr e)
  | .neNil e => return .neNil (← unblockExpr e)
  | .eqTrue e => return .eqTrue (← unblockExpr e)
  | .eqFalse e => return .eqFalse (← unblockExpr e)
  | .and a b => return .and (← unblockExpr a) (← unblockExpr b)
  | .or a b => return .or (← unblockExpr a) (← unblockExpr b)
  | .not a => return .not (← unblockExpr a)
  | e => return e

/-- A method with its blocks given to built-in methods made loops. -/
def methodUnblock (mt : Method) : Method :=
  let (b, (_, ls)) := (unblockExpr mt.body).run (0, [])
  { mt with body := b, locals := mt.locals ++ ls }

/-- The QCore program of a tree. -/
def program (j : Json) : M Program := do
  let classes ← arr (← field j "classes")
  let units ← arr (← field j "units")
  let files ← units.toList.mapM fun u => do nat (← field u "file")
  let mainClasses ← units.toList.mapM fun u => do nat (← field u "main_class")
  let some objectJ := classes.find? fun c => (c.getObjValAs? String "name").toOption == some "Object"
    | throw "no Object"
  let objectId ← nat (← field objectJ "id")
  let some kernelJ := classes.find? fun c => (c.getObjValAs? String "name").toOption == some "Kernel"
    | throw "no Kernel"
  let kernelId ← nat (← field kernelJ "id")
  -- The user classes, in Rust id order (a superclass is declared first).
  let user ← classes.toList.filterM fun c => do
    let kind ← str (← field c "kind")
    pure (files.contains (← nat (← field c "file")) &&
      (kind == "Class" || kind == "Data" || kind == "Enum" || kind == "Variant") &&
      !mainClasses.contains (← nat (← field c "id")))
  -- The built-in exception classes: `Exception` and the classes below it
  -- outside the program's files (in Rust id order: a superclass first).
  let some excJ := classes.find? fun c => (c.getObjValAs? String "name").toOption == some "Exception"
    | throw "no Exception"
  let excRoot ← nat (← field excJ "id")
  let below (c : Json) : M Bool := do
    let mut x ← nat (← field c "id")
    for _ in [0:classes.size + 1] do
      if x == excRoot then return true
      match ← field (← match classes.find? fun d => (d.getObjValAs? Nat "id").toOption == some x with
          | some d => pure d | none => throw "class") "superclass" with
      | .null => return false
      | sj => x ← nat (← field sj "id")
    pure false
  let excs ← classes.toList.filterM fun c => do
    pure (!files.contains (← nat (← field c "file")) && (← below c))
  let excIds ← excs.mapM fun c => do nat (← field c "id")
  let userIds := excIds ++ (← user.mapM fun c => do nat (← field c "id"))
  -- `Object` is 0, the files' main classes (the top level and its
  -- methods) 1, the user classes from 2.
  let arrayId ← match classes.find? fun c => (c.getObjValAs? String "name").toOption == some "Array" with
    | some c => nat (← field c "id")
    | none => throw "no Array"
  let qclass : Nat → Option Nat := fun id =>
    if id == objectId then some 0
    else if mainClasses.contains id then some 1
    else if id == arrayId then some arrIdx
    else (userIds.idxOf? id).map (· + 4 + procMax)
  unless units.size == 1 do throw "a required file"
  let fdefs ← arr (← field j "field_defaults")
  -- The classes' type parameters by id, and the narrowed ones.
  let classParams ← classes.toList.flatMapM fun c => do
    let cid ← nat (← field c "id")
    (← arr (← field c "type_params")).toList.zipIdx.mapM fun (p, i) => do
      pure (← nat (← field p "id"), (cid, i))
  let narrowedList ← (← arr (← field j "narrowed_params")).toList.mapM fun p => do
    pure (← nat (← field p "id"), ← arr (← field p "bounds"))
  let selfParam ← nat (← field j "self_param")
  let T : Tables := ⟨classes, ← arr (← field j "methods"), ← arr (← field j "definitions"),
    ← field j "node_types", ← arr (← field j "varied_types"), ← field j "calls",
    (← field j "const_targets"), (← arr (← field j "consts")), qclass, objectId, kernelId,
    fun id => (classParams.find? (·.1 == id)).map (·.2),
    fun id => (narrowedList.find? (·.1 == id)).map (·.2), selfParam, excIds,
    (j.getObjVal? "op_targets").toOption.getD Json.null,
    (j.getObjVal? "block_results").toOption.getD Json.null, [], ← arr (← field j "extensions")⟩
  -- The program's overloaded names (but `initialize`, which `new` and
  -- `super` take the nearest of).
  let mine ← (← arr (← field j "methods")).toList.filterM fun m => do
    pure (files.contains (← nat (← field m "file")))
  let mut overloads : List (String × List String) := []
  for m in mine do
    let n ← str (← field m "name")
    if n == "initialize" then continue
    let key ← sigKey m
    overloads := match overloads.find? (·.1 == n) with
      | some (_, ks) => if ks.contains key then overloads
          else overloads.map fun (n', ks') => if n' == n then (n', ks' ++ [key]) else (n', ks')
      | none => overloads ++ [(n, [key])]
  let T := { T with overloads := overloads.filter fun (_, ks) => ks.length > 1 }
  -- (The runtime dispatches without the block's type: overloads of one
  -- class differing in their block only are out of range.)
  for a in mine do
    for b in mine do
      let n ← str (← field a "name")
      if n == "initialize" || n != (← str (← field b "name")) then continue
      let ka ← sigKey a
      let kb ← sigKey b
      if ka != kb && (← nat (← field a "owner")) == (← nat (← field b "owner")) &&
          (ka.splitOn "|").head? == (kb.splitOn "|").head? then
        throw s!"overloads of {n} differing in their block only"
  let excClasses ← excs.mapM fun c => do
    let sup ← match ← field c "superclass" with
      | .null => pure 0
      | t => pure (← T.tyClass t).1
    pure (⟨← str (← field c "name"), some sup, [], [], [], [], .cls⟩ : Class)
  let qclasses ← user.mapM fun c => do
    -- A module the program declares is not the model's (stage 6a-2); one of
    -- the prelude's, its methods are built-in calls.
    for inc in (← arr (← field c "includes")) do
      let mid ← nat (← field inc "id")
      if files.contains (← nat (← field (← T.cls mid) "file")) then
        throw "an include of a program's module"
      -- (The module's methods come before the superclass's: a program
      -- superclass's method of one's name, which a call resolved to the
      -- superclass would run in the model, is out of range.)
      let modNames ← T.moduleNames mid
      let cid ← nat (← field c "id")
      for m in (← arr (← field j "methods")).toList do
        let o ← nat (← field m "owner")
        if o != cid && files.contains (← nat (← field m "file")) && (← rsub T cid o) &&
            modNames.contains (← str (← field m "name")) then
          throw "an include hiding a superclass's method"
    let sup ← match ← field c "superclass" with
      | .null => pure (0, [])
      | t => T.tyClass t
    -- The model's range: a superclass's arguments take no arguments
    -- themselves (`Box[T]`, `Box[Int?]`, not `Box[Box[T]]`).
    unless sup.2.all (fun t => t.all fun a => a.isParam || decide (a.depth ≤ 1)) do
      throw "a superclass argument with arguments"
    let cid ← nat (← field c "id")
    -- The type parameters: their variances and bounds (one bound, closed,
    -- of atoms taking no arguments: `T <: Shape`; `T <: Comparable[T]`
    -- and `T <: A & B` are out of range).
    let pbs ← (← arr (← field c "type_params")).toList.mapM fun p => do
      let bound ← match (← arr (← field p "bounds")).toList with
        | [] => pure [Atom.cls 0 []]
        | [b] =>
          let t ← T.ty b
          unless t.all (fun a => a.closed && decide (a.depth ≤ 1)) do throw "a bound with arguments"
          pure t
        | _ => throw "a type parameter with several bounds"
      let v ← match ← str (← field p "variance") with
        | "Covariant" => pure Variance.co
        | "Contravariant" => pure Variance.contra
        | "Invariant" => pure Variance.inv
        | v => throw s!"a {v} type parameter"
      pure (v, bound)
    let params := pbs.map (·.1)
    let fields ← (← arr (← field c "fields")).toList.mapM fun f => do
      let name ← str (← field f "name")
      -- Its default, by its place in `field_defaults`.
      let d := fdefs.toList.findIdx? fun e =>
        (e.getObjValAs? Nat "class").toOption == some cid &&
        (e.getObjValAs? String "field").toOption == some name
      pure (⟨name, ← T.ty (← field f "type"), (← field f "var") == .bool true, d⟩ : Field)
    -- A `data` type (docs/01 §4): final; its generated methods below.
    let kind ← match ← str (← field c "kind") with
      | "Data" =>
        unless params.isEmpty do throw "a generic data type"
        pure ClassKind.data
      | "Enum" =>
        unless params.isEmpty do throw "a generic enum"
        pure ClassKind.enumC
      | "Variant" =>
        unless params.isEmpty do throw "a generic enum"
        pure ClassKind.variant
      | _ => pure ClassKind.cls
    pure (⟨← str (← field c "name"), some sup.1, fields, params, sup.2, pbs.map (·.2), kind⟩ : Class)
  let methods ← T.defs.toList.filterMapM fun d => do
    let m ← T.method (← nat (← field d "method"))
    match ← field d "def" with
    | .null => pure none
    | def_ =>
      match qclass (← nat (← field m "owner")) with
      | some owner => pure (some (← method T owner m def_))
      | none => throw "a method of a class out of range"
  -- Each constant's initializer, checked as a method of the top level's
  -- class giving the constant's type.
  let consts ← (← arr (← field j "consts")).toList.mapM fun k => do
    -- A class's constant is checked with that class as `self`: not here.
    unless (← field k "owner") == .null do throw "a class constant"
    let ty ← match ← field k "type" with
      | .null => throw "a constant of no type"
      | t => T.ty t
    match ← field k "value" with
    | .null => throw "a constant with no initializer"
    | v =>
      let (bd, ls) ← ((expr T v).run ⟨true, none, none, none, none, [], none, [], [], false, false⟩).run []
      pure (⟨1, "const " ++ (← str (← field k "name")), [], ty, none, ls, bd⟩ : Method)
  let some mainUnit := units.back? | throw "no unit"
  let (mainBody, mainLocals) ← ((body T (← arr (← field mainUnit "body"))).run ⟨true, none, none, none, none, [], none, [], [], true, false⟩).run []
  let all : Ty := [.nil, .bool, .int, .str, .cls 0 []]
  -- A default that tests or loops, with a bounded parameter anywhere (it
  -- is checked in each inheriting class): out of range, as in `method`.
  let bounded ← user.anyM fun c => do
    (← arr (← field c "type_params")).anyM fun p => do pure !(← arr (← field p "bounds")).isEmpty
  let defaults ← fdefs.toList.mapM fun e => do
    let (x, ls) ← ((expr T (← field e "value")).run ⟨false, none, none, none, none, [], none, [], [], false, false⟩).run []
    unless ls.isEmpty do throw "a field default with locals"
    if bounded && narrows x then throw "a test in a default with a bounded parameter"
    pure x
  -- The user classes' accessors.
  let accessors ← (← arr (← field j "methods")).toList.filterMapM fun m => do
    let o ← nat (← field m "owner")
    match qclass o with
    | some q => if q ≥ 2 && !excIds.contains o then accessor T q m else pure none
    | none => pure none
  let own := methods ++ accessors
  let P : Program := ⟨⟨"Object", none, [], [], [], [], .cls⟩ :: ⟨"<main>", some 0, [], [], [], [], .cls⟩ ::
      ((List.range (procMax + 1)).map procClassOf ++ [⟨"Array", some 0, [], [.co], [], [], .builtin⟩] ++
        excClasses ++ qclasses),
    own ++ consts,
    ⟨1, "<main>", [], all, none, mainLocals, mainBody⟩, defaults⟩
  for m in P.main :: P.methods do localsInRange (m.params.map (·.1)) m.body
  -- The runtime takes a subclass's method for an override of an
  -- ancestor's of other parameters when it accepts them (as many, the
  -- same kinds, each at least the ancestor's; a block or none, whatever
  -- its type): such a pair of other signatures, which the model calls
  -- apart, is out of range.
  for a in mine do
    for b in mine do
      let n ← str (← field a "name")
      if n == "initialize" || n != (← str (← field b "name")) then continue
      if (← sigKey a) == (← sigKey b) then continue
      let ao ← nat (← field a "owner")
      let bo ← nat (← field b "owner")
      unless ao != bo && (← rsub T ao bo) do continue
      let pa := (← arr (← field a "params")).toList
      let pb := (← arr (← field b "params")).toList
      let blocks := ((← field a "block") == .null) == ((← field b "block") == .null)
      let kinds ← (pa.zip pb).allM fun (x, y) => do
        pure ((← field x "kind") == (← field y "kind"))
      if pa.length == pb.length && blocks && kinds then
        let accepts ← (pa.zip pb).allM fun (x, y) => do
          match T.ty (← field x "type"), T.ty (← field y "type") with
          | .ok tx, .ok ty => pure (Ty.le P.classes [] ty tx)
          | _, _ => pure true
        if accepts then throw s!"overloads of {n}: an override of other parameters"
  let mainU := methodUnblock P.main
  let methodsU := P.methods.map methodUnblock
  -- (A default has no locals: one holding a built-in call's result is out
  -- of range.)
  let defaultsU ← P.defaults.mapM fun d => do
    let (d', (_, ls)) := (unblockExpr d).run (0, [])
    unless ls.isEmpty do throw "a block given to a built-in in a field default"
    pure d'
  let P : Program := ⟨P.classes, methodsU, mainU, defaultsU⟩
  -- Two methods of one name in a class, or in a class and its ancestor
  -- with other parameters or block, are overloads (one signature twice in
  -- a class is a Rust error): the Rust checker picks the one that fits,
  -- `Program.lookup` the nearest. Out of range. (Not `initialize`, which
  -- no call dispatches on: `super` takes the nearest above in both, and
  -- a `new` taking another than the model's is out of range there.)
  for a in own do
    for b in own do
      -- (An overload's own name differs: two methods of one model name
      -- are an override, of one signature.)
      if a.name == b.name && a.name != "initialize" && a.owner != b.owner &&
          P.classes.subclass a.owner b.owner &&
          (a.params.map (·.2) != b.params.map (·.2) || a.block != b.block) then
        throw s!"overloads of {a.name}"
    if (own.filter fun m => m.owner == a.owner && m.name == a.name).length > 1 then
      throw s!"overloads of {a.name}"
  pure P

end QuarzCore.Conformance
