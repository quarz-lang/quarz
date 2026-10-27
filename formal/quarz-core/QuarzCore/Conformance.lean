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
`==`/`!=` against `nil`/`true`/`false`, `&&`, `||`, `!`. A local's
declared type is its first assignment's, as the Rust checker's. Anything
else puts the program out of range: so do a node checked with different
types (`varied_types`), constants, field defaults, and required files.
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
  /-- The QCore class of each user class (by Rust id), class 0 being
  `Object` (and the files' main classes). -/
  qclass : Nat → Option Nat
  objectId : Nat

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

mutual

partial def expr (T : Tables) (e : Json) : CM Expr := do
  let id ← nat (← field e "id")
  let (k, v) ← variant (← field e "kind")
  match k with
  | "Nil" => pure .nil
  | "True" => pure .tru
  | "False" => pure .fls
  | "SelfRef" => pure .self
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
    -- `C.new(args)`: opaque (`initialize` assigns immutable fields, which
    -- v1 does not model), giving a `C`.
    unless blk == .null do throw "a block given to new"
    let k ← nat (← field target "class")
    let some q := T.qclass k | throw s!"new of {← T.className k}"
    let as ← args.mapM (expr T)
    let params ← match ← field target "init" with
      | .null => pure []
      | i => do
        let m ← T.method (← nat i)
        (← arr (← field m "params")).toList.mapM fun p => do T.ty (← field p "type")
    return .prim "new" as params [.cls q]
  | "method" =>
    let m ← T.method (← nat (← field target "method"))
    let native := (← field m "native") == .bool true
    let synth ← str (← field m "synth")
    let as ← args.mapM (expr T)
    if native || synth != "None" then
      -- A built-in method: its declared types.
      unless blk == .null do throw s!"a block given to built-in {name}"
      let params ← (← arr (← field m "params")).toList.mapM fun p => do T.tyOrTop (← field p "type")
      let ret ← T.tyOrTop (← field m "ret")
      let (rs, rps) ← match recv with
        | some r => do
          let rt ← T.nodeTy (← nat (← field recvJ "id"))
          pure ([r], [rt])
        | none => pure ([], [])
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
      return .callBlk r name as ps bd
  | t => throw s!"a {t} call"

end

/-- A Rust method as a QCore one. -/
def method (T : Tables) (owner : Nat) (m : Json) (d : Json) : M Method := do
  let name ← str (← field m "name")
  let params ← (← arr (← field m "params")).toList.mapM fun p => do
    if (← str (← field p "kind")) != "Positional" then throw "a parameter not positional"
    pure (← str (← field p "name"), ← T.ty (← field p "type"))
  let ret ← T.ty (← field m "ret")
  let block ← match ← field m "block" with
    | .null => pure none
    | b => do
      let t ← field b "type"
      unless (← str (← field t "t")) == "proc" do throw "a block type"
      let ps ← (← arr (← field t "params")).toList.mapM T.ty
      pure (some ⟨ps, ← T.ty (← field t "ret")⟩)
  let (bd, ls) ← ((body T (← arr (← field d "body"))).run (owner == 1)).run params
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
  unless (← arr (← field j "consts")).isEmpty do throw "a constant"
  unless (← arr (← field j "field_defaults")).isEmpty do throw "a field default"
  let T : Tables := ⟨classes, ← arr (← field j "methods"), ← arr (← field j "definitions"),
    ← field j "node_types", ← arr (← field j "varied_types"), ← field j "calls", qclass, objectId⟩
  let qclasses ← user.mapM fun c => do
    let sup ← match ← field c "superclass" with
      | .null => pure 0
      | t => match ← T.ty t with
        | [.cls k] => pure k
        | _ => throw "a superclass"
    let fields ← (← arr (← field c "fields")).toList.mapM fun f => do
      pure (⟨← str (← field f "name"), ← T.ty (← field f "type"), (← field f "var") == .bool true⟩ : Field)
    pure (⟨← str (← field c "name"), some sup, fields⟩ : Class)
  let methods ← T.defs.toList.filterMapM fun d => do
    let m ← T.method (← nat (← field d "method"))
    match ← field d "def" with
    | .null => pure none
    | _ => if (← str (← field m "name")) == "initialize" then pure none else
    match ← field d "def" with
    | .null => pure none
    | def_ =>
      match qclass (← nat (← field m "owner")) with
      | some owner => pure (some (← method T owner m def_))
      | none => throw "a method of a class out of range"
  let some mainUnit := units.back? | throw "no unit"
  let (mainBody, mainLocals) ← ((body T (← arr (← field mainUnit "body"))).run true).run []
  let all : Ty := [.nil, .bool, .int, .str, .cls 0]
  pure ⟨⟨"Object", none, []⟩ :: ⟨"<main>", some 0, []⟩ :: qclasses, methods,
    ⟨1, "<main>", [], all, none, mainLocals, mainBody⟩⟩

end QuarzCore.Conformance
