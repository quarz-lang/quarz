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
locals, an `initialize` under fields it must leave to `super`, and
required files.
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

def Tables.cls (T : Tables) (id : Nat) : M Json := do
  match T.classes.find? fun c => (c.getObjValAs? Nat "id").toOption == some id with
  | some c => pure c
  | none => throw s!"class {id}"

def Tables.className (T : Tables) (id : Nat) : M String := do
  str (← field (← T.cls id) "name")

/-- A Rust type as atoms. -/
partial def Tables.ty (T : Tables) (j : Json) : M Ty := do
  match ← str (← field j "t") with
  | "nothing" => pure []
  | "union" => do
    let ms ← arr (← field j "members")
    ms.toList.flatMapM T.ty
  | "class" =>
    let id ← nat (← field j "id")
    let args ← arr (← field j "args")
    unless args.isEmpty do throw "a generic type"
    match ← T.className id with
    | "Nil" => pure [.nil]
    | "Bool" => pure [.bool]
    | "Int" => pure [.int]
    | "String" => pure [.str]
    | "Float" => pure [.float]
    | _ => match T.qclass id with
      | some k => pure [.cls k]
      | none => throw s!"type {← T.className id}"
  | t => throw s!"a {t} type"

/-- A built-in method's parameter or result: a type QCore has no atoms
for (a type parameter, a generic class) is any value here. -/
def Tables.tyOrTop (T : Tables) (j : Json) : M Ty :=
  match T.ty j with
  | .ok t => pure t
  | .error _ => pure [.nil, .bool, .int, .str, .cls 0]

def Tables.nodeTy (T : Tables) (id : Nat) : M Ty := do
  if T.varied.contains (.num id) then throw s!"node {id} checked with different types"
  match T.nodeTypes.getObjVal? (toString id) with
  | .ok t => T.ty t
  | .error _ => throw s!"node {id} has no type"

def Tables.method (T : Tables) (id : Nat) : M Json := do
  match T.methods.find? fun m => (m.getObjValAs? Nat "id").toOption == some id with
  | some m => pure m
  | none => throw s!"method {id}"

/-- The locals assigned so far, with their declared types. -/
abbrev Locals := List (String × Ty)

def addLocal (ls : Locals) (x : String) (t : Ty) : Locals :=
  -- The first assignment declares it (docs/02 §6).
  if ls.any (·.1 == x) then ls else ls ++ [(x, t)]

/-- Converting a body: whether it is top-level code (the top level, or a
method of its class), and the locals so far. -/
abbrev CM := ReaderT Bool (StateT Locals M)

def positional (a : Json) : M Json := do
  match ← variant a with
  | ("Positional", e) => pure e
  | (k, _) => throw s!"a {k} argument"

/-- Whether an expression has a `return` (in a block of it too). -/
partial def hasRet : Expr → Bool
  | .ret _ => true
  | .assign _ e | .setField _ e | .isNil e | .isA e _ | .eqNil e | .neNil e | .eqTrue e
  | .eqFalse e | .not e => hasRet e
  | .new _ as | .yield as | .prim _ as _ _ => as.any hasRet
  | .call r _ as => hasRet r || as.any hasRet
  | .callBlk r _ as _ b => hasRet r || as.any hasRet || hasRet b
  | .seq a b | .while a b | .and a b | .or a b => hasRet a || hasRet b
  | .ite c t e => hasRet c || hasRet t || hasRet e
  | _ => false

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
    unless (← str (← field target "t")) == "const" do throw "a class as a value"
    let cid ← nat (← field target "id")
    let some k := T.consts.find? fun k => (k.getObjValAs? Nat "id").toOption == some cid
      | throw "a constant of another file"
    let declared ← field k "type"
    unless (← field T.nodeTypes (toString id)) == declared do
      throw s!"disagree: constant read {id} not of the constant's type"
    pure (.prim "const" [] [] (← T.ty declared))
  | "Int" => pure (.int (← match (← field v "value") with
      | .num n => pure n.mantissa
      | _ => throw "a big integer"))
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
  | "Local" => pure (.var (← str v) (← T.nodeTy id))
  | "IVar" => pure (.field (← str v) (← T.nodeTy id))
  | "Assign" =>
    let value ← expr T (← field v "value")
    let vt ← T.nodeTy (← nat (← field (← field v "value") "id"))
    match ← variant (← field v "target") with
    | ("Local", l) =>
      let x ← str (← field l "name")
      modify (addLocal · x vt)
      pure (.assign x value)
    | ("IVar", f) => pure (.setField (← str f) value)
    | (t, _) => throw s!"assigning a {t}"
  | "And" => match v with
    | .arr #[a, b] => pure (.and (← expr T a) (← expr T b))
    | _ => throw "And"
  | "Or" => match v with
    | .arr #[a, b] => pure (.or (← expr T a) (← expr T b))
    | _ => throw "Or"
  | "Not" => pure (.not (← expr T v))
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
  | "Yield" => pure (.yield (← (← arr v).toList.mapM fun a => do expr T (← positional a)))
  | "Call" => call T id v
  | k => throw s!"a {k} expression"

partial def body (T : Tables) (es : Array Json) : CM Expr := do
  match es.toList with
  | [] => pure .nil
  | e :: es => es.foldlM (fun acc x => do pure (.seq acc (← expr T x))) (← expr T e)

partial def call (T : Tables) (id : Nat) (c : Json) : CM Expr := do
  let name ← str (← field c "name")
  let recvJ ← field c "recv"
  let args ← (← arr (← field c "args")).toList.mapM fun a => (positional a : CM Json)
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
  let lit (a : Json) : M String := do pure (← variant (← field a "kind")).1
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
    if (← lit a) == "Nil" then return .neNil r
  | _, _, _, _ => pure ()
  match ← str (← field target "t") with
  | "is_a" =>
    let some r := recv | throw "is_a? without a receiver"
    match ← T.ty (← field target "type") with
    | [a] => return .isA r a
    | _ => throw "is_a? of a union"
  | "raise" => return .raise
  | "constructor" =>
    -- `C.new(args)`: the fields' defaults, then `initialize`.
    unless blk == .null do throw "a block given to new"
    let k ← nat (← field target "class")
    let some q := T.qclass k | throw s!"new of {← T.className k}"
    return .new q (← args.mapM (expr T))
  | "method" =>
    let m ← T.method (← nat (← field target "method"))
    let native := (← field m "native") == .bool true
    let synth ← str (← field m "synth")
    let as ← args.mapM (expr T)
    -- An accessor `attr_*` makes is a method of the model (`accessor`).
    let accessor := (synth.startsWith "FieldGet(" || synth.startsWith "FieldSet(") &&
      (T.qclass (← nat (← field m "owner"))).any (· ≥ 2)
    if (native || synth != "None") && !accessor then
      -- A built-in method: its declared types. On the implicit receiver,
      -- it takes `self` (it may read its fields), but a `Kernel`
      -- function.
      unless blk == .null do throw s!"a block given to built-in {name}"
      let params ← (← arr (← field m "params")).toList.mapM fun p => do T.tyOrTop (← field p "type")
      let ret ← T.tyOrTop (← field m "ret")
      let (rs, rps) ← match recv with
        | some r => do
          let rt ← T.nodeTy (← nat (← field recvJ "id"))
          pure ([r], [rt])
        | none =>
          if (← nat (← field m "owner")) == T.kernelId then pure ([], [])
          else pure ([.self], [[.cls 0]])
      return .prim name (rs ++ as) (rps ++ params) ret
    if recv.isNone && T.qclass (← nat (← field m "owner")) == some 1 && !(← read) then
      throw "a top-level method called from a class"
    let r := recv.getD .self
    match blk with
    | .null => return .call r name as
    | b =>
      let ps ← (← arr (← field (← field b "params") "list")).toList.mapM fun p => do
        str (← field p "name")
      -- The block's parameters, as the method's block declares them.
      let sig ← match ← field m "block" with
        | .null => throw "a block given to a method that takes none"
        | s => pure s
      match ← str (← field (← field sig "type") "t") with
      | "proc" =>
        let tys ← (← arr (← field (← field sig "type") "params")).toList.mapM fun t => (T.ty t : M Ty)
        for (x, t) in ps.zip tys do modify (addLocal · x t)
      | _ => throw "a block type"
      let bd ← body T (← arr (← field b "body"))
      -- A `return` from a block is not in v1.
      if hasRet bd then throw "a return in a block"
      return .callBlk r name as ps bd
  | t => throw s!"a {t} call"

end

/-- The method an `attr_reader` or `attr_writer` makes, of QCore class
`owner`. -/
def accessor (T : Tables) (owner : Nat) (m : Json) : M (Option Method) := do
  let synth ← str (← field m "synth")
  let name ← str (← field m "name")
  let fieldOf (pre : String) : String := String.ofList ((synth.toList.drop pre.length).dropLast.dropLast)
  let ret ← T.ty (← field m "ret")
  if synth.startsWith "FieldGet(\"" then
    pure (some ⟨owner, name, [], ret, none, [], .field (fieldOf "FieldGet(\"") ret⟩)
  else if synth.startsWith "FieldSet(\"" then
    let [p] := (← arr (← field m "params")).toList | throw "a writer's parameters"
    let t ← T.ty (← field p "type")
    pure (some ⟨owner, name, [("v", t)], ret, none, [("v", t)],
      .setField (fieldOf "FieldSet(\"") (.var "v" t)⟩)
  else pure none

/-- A Rust method as a QCore one. -/
def method (T : Tables) (owner : Nat) (m : Json) (d : Json) : M Method := do
  if (← field m "singleton") == .bool true then throw "a class method"
  let name ← str (← field m "name")
  let params ← (← arr (← field m "params")).toList.mapM fun p => do
    if (← str (← field p "kind")) != "Positional" then throw "a parameter not positional"
    if (← field p "default") == .bool true then throw "a parameter with a default"
    pure (← str (← field p "name"), ← T.ty (← field p "type"))
  let ret ← T.ty (← field m "ret")
  if (← field m "block_optional") == .bool true then throw "an optional block"
  let block ← match ← field m "block" with
    | .null => pure none
    | b => do
      let t ← field b "type"
      unless (← str (← field t "t")) == "proc" do throw "a block type"
      let ps ← (← arr (← field t "params")).toList.mapM T.ty
      pure (some ⟨ps, ← T.ty (← field t "ret")⟩)
  let (bd, ls) ← ((body T (← arr (← field d "body"))).run (owner == 1)).run params
  -- `def initialize(@x: T)`: the field assigned from the parameter first.
  let ivars ← (← arr (← field m "params")).toList.filterMapM fun p => do
    if (← field p "assigns_ivar") == .bool true then
      pure (some (← str (← field p "name"), ← T.ty (← field p "type")))
    else pure none
  let bd := ivars.foldr (fun (x, t) b => .seq (.setField x (.var x t)) b) bd
  pure ⟨owner, name, params, ret, block, ls, bd⟩

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
    pure (files.contains (← nat (← field c "file")) && (← str (← field c "kind")) == "Class" &&
      !mainClasses.contains (← nat (← field c "id")))
  let userIds ← user.mapM fun c => do nat (← field c "id")
  -- `Object` is 0, the files' main classes (the top level and its
  -- methods) 1, the user classes from 2.
  let qclass : Nat → Option Nat := fun id =>
    if id == objectId then some 0
    else if mainClasses.contains id then some 1
    else (userIds.idxOf? id).map (· + 2)
  unless units.size == 1 do throw "a required file"
  let fdefs ← arr (← field j "field_defaults")
  let T : Tables := ⟨classes, ← arr (← field j "methods"), ← arr (← field j "definitions"),
    ← field j "node_types", ← arr (← field j "varied_types"), ← field j "calls",
    (← field j "const_targets"), (← arr (← field j "consts")), qclass, objectId, kernelId⟩
  let qclasses ← user.mapM fun c => do
    -- An included module's methods are not the model's.
    unless (← arr (← field c "includes")).isEmpty do throw "an include"
    let sup ← match ← field c "superclass" with
      | .null => pure 0
      | t => match ← T.ty t with
        | [.cls k] => pure k
        | _ => throw "a superclass"
    let cid ← nat (← field c "id")
    let fields ← (← arr (← field c "fields")).toList.mapM fun f => do
      let name ← str (← field f "name")
      -- Its default, by its place in `field_defaults`.
      let d := fdefs.toList.findIdx? fun e =>
        (e.getObjValAs? Nat "class").toOption == some cid &&
        (e.getObjValAs? String "field").toOption == some name
      pure (⟨name, ← T.ty (← field f "type"), (← field f "var") == .bool true, d⟩ : Field)
    pure (⟨← str (← field c "name"), some sup, fields⟩ : Class)
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
      let (bd, ls) ← ((expr T v).run true).run []
      pure (⟨1, "const " ++ (← str (← field k "name")), [], ty, none, ls, bd⟩ : Method)
  let some mainUnit := units.back? | throw "no unit"
  let (mainBody, mainLocals) ← ((body T (← arr (← field mainUnit "body"))).run true).run []
  let all : Ty := [.nil, .bool, .int, .str, .cls 0]
  let defaults ← fdefs.toList.mapM fun e => do
    let (x, ls) ← ((expr T (← field e "value")).run false).run []
    unless ls.isEmpty do throw "a field default with locals"
    pure x
  -- The user classes' accessors.
  let accessors ← (← arr (← field j "methods")).toList.filterMapM fun m => do
    match qclass (← nat (← field m "owner")) with
    | some q => if q ≥ 2 then accessor T q m else pure none
    | none => pure none
  let own := methods ++ accessors
  let P : Program := ⟨⟨"Object", none, []⟩ :: ⟨"<main>", some 0, []⟩ :: qclasses,
    own ++ consts,
    ⟨1, "<main>", [], all, none, mainLocals, mainBody⟩, defaults⟩
  -- Two methods of one name in a class, or in a class and its ancestor
  -- with other parameters or block, are overloads (one signature twice in
  -- a class is a Rust error): the Rust checker picks the one that fits,
  -- `Program.lookup` the nearest. Out of range.
  for a in own do
    for b in own do
      if a.name == b.name && a.owner != b.owner && P.classes.subclass a.owner b.owner &&
          (a.params.map (·.2) != b.params.map (·.2) || a.block != b.block) then
        throw s!"overloads of {a.name}"
    if (own.filter fun m => m.owner == a.owner && m.name == a.name).length > 1 then
      throw s!"overloads of {a.name}"
  -- An `initialize` with fields to assign above it needs `super`: not yet.
  unless (List.range P.classes.length).all (fun k => !P.ownInit k ||
      !((match (P.classes[k]?).bind (·.super) with
        | some d => P.classes.allFields d
        | none => []).any (·.required P.classes))) do
    throw "an initialize under fields it must leave to super"
  pure P

end QuarzCore.Conformance
