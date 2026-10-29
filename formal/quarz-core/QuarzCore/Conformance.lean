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

def Tables.cls (T : Tables) (id : Nat) : M Json := do
  match T.classes.find? fun c => (c.getObjValAs? Nat "id").toOption == some id with
  | some c => pure c
  | none => throw s!"class {id}"

def Tables.className (T : Tables) (id : Nat) : M String := do
  str (← field (← T.cls id) "name")

/-- A Rust type as atoms. A user class comes with its arguments; a class
type parameter is `.param i` (the position in its class: the body of
another class never names it, the checker having substituted); a
parameter a class test made (`T & C`) is the class it was narrowed to
(a larger type than the Rust checker's, so a weaker annotation: sound);
method and extension type parameters, and `Self`, are out of range. -/
partial def Tables.ty (T : Tables) (j : Json) : M Ty := do
  match ← str (← field j "t") with
  | "nothing" => pure []
  -- `-> Void`: the body's value is discarded and the result is nil.
  | "void" => pure [.nil]
  | "union" => do
    let ms ← arr (← field j "members")
    ms.toList.flatMapM T.ty
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
      | some k => pure [.cls k (← args.toList.mapM T.ty)]
      | none => throw s!"type {← T.className id}"
  | "param" =>
    let id ← nat (← field j "id")
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
        | [c] => T.ty c
        | _ => throw "a narrowed type parameter without a class"
      | none => throw "a method or extension type parameter"
  -- `Type[T]` (a class as a value of its type): no class objects here.
  | "type_of" => throw "a Type[T] type"
  | t => throw s!"a {t} type"

/-- A Rust class type as a QCore class with its arguments. -/
def Tables.tyClass (T : Tables) (j : Json) : M (Nat × List Ty) := do
  match ← T.ty j with
  | [.cls k as] => pure (k, as)
  | _ => throw "a class type"

/-- A built-in method's parameter or result: a type QCore has no atoms
for (a type parameter, a generic class) is any value here. -/
def Tables.tyOrTop (T : Tables) (j : Json) : M Ty :=
  match T.ty j with
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

/-- Converting a body, with the locals so far. -/
abbrev CM := ReaderT Where (StateT Locals M)

def positional (a : Json) : M Json := do
  match ← variant a with
  | ("Positional", e) => pure e
  | (k, _) => throw s!"a {k} argument"

/-- Whether an expression has a `return` (in a block of it too). -/
partial def hasRet : Expr → Bool
  | .ret _ => true
  | .assign _ e | .setField _ e | .isNil e | .isA e _ | .eqNil e | .neNil e | .eqTrue e
  | .eqFalse e | .not e => hasRet e
  | .new _ _ as | .superInit _ as | .yield as | .prim _ as _ _ => as.any hasRet
  | .call r _ as => hasRet r || as.any hasRet
  | .callBlk r _ as _ b => hasRet r || as.any hasRet || hasRet b
  | .seq a b | .while a b | .and a b | .or a b => hasRet a || hasRet b
  | .ite c t e => hasRet c || hasRet t || hasRet e
  | _ => false

/-- Whether an expression tests or loops (what may narrow a path). -/
partial def narrows : Expr → Bool
  | .ite .. | .while .. | .isNil _ | .isA .. | .eqNil _ | .neNil _ | .eqTrue _ | .eqFalse _
  | .and .. | .or .. | .not _ => true
  | .assign _ e | .setField _ e | .ret e => narrows e
  | .new _ _ as | .superInit _ as | .yield as | .prim _ as _ _ => as.any narrows
  | .call r _ as => narrows r || as.any narrows
  | .callBlk r _ as _ b => narrows r || as.any narrows || narrows b
  | .seq a b => narrows a || narrows b
  | _ => false

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
  | "Super" =>
    -- `super` in `initialize`, into the superclass's.
    unless (← field v "block") == .null do throw "a block given to super"
    let some (params, d) := (← read).init | throw "super outside initialize"
    let args ← match ← field v "args" with
      -- A bare `super` passes the method's arguments.
      | .null => pure (params.map fun (x, t) => Expr.var x t)
      | a => (← arr a).toList.mapM fun a => do expr T (← positional a)
    return .superInit d args
  | "CaseIn" => caseIn T id v
  | "MatchPattern" => matchPattern T id v
  | k => throw s!"a {k} expression"

partial def body (T : Tables) (es : Array Json) : CM Expr := do
  match es.toList with
  | [] => pure .nil
  | e :: es => es.foldlM (fun acc x => do pure (.seq acc (← expr T x))) (← expr T e)

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
  | ("Local", x) => do let x ← str x; pure (Expr.nil, fun t => Expr.var x t, some x)
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
  let arms ← (List.range armsJ.length).zip armsJ |>.mapM fun (i, arm) => do
    let c ← compilePat T s!"case#{id}#{i}" rd st stTy (← field arm "pattern")
    let guard ← match ← field arm "guard" with
      | .null => pure none
      | g =>
        let e ← expr T (← field g "cond")
        pure (some (if (← field g "negate") == .bool true then Expr.not e else e))
    let bd ← body T (← arr (← field arm "body"))
    pure (c, guard, bd)
  -- The subject is read again by each test (the path the model narrows),
  -- where the program reads it once: out of range when a pattern or a
  -- guard may assign it.
  if let some x := subjLocal then
    if arms.any (fun (c, g, _) => c.names.any (·.1 == x) || (g.map (·.assigned.contains x)).getD false) then
      throw "a case whose pattern or guard assigns its subject"
    if x.startsWith "@" && (← read).init.isSome && arms.any (fun (_, g, _) => g.isSome) then
      throw "a case on a field with a guard in initialize"
  -- Rust declares a bound name afresh in each arm (after the `case`, the
  -- name is the last arm's): one bound in two arms, or assigned in the
  -- `case` besides, is out of range.
  let binds := arms.flatMap fun (c, _, _) => c.names.map (·.1)
  let mid ← get
  for x in binds do
    unless before.any (·.1 == x) do
      if (binds.filter (· == x)).length > 1 || mid.any (·.1 == x) then
        throw "a name bound in a case arm and assigned in another"
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
  let last := match els with
    | some e => e
    | none => if closed then .absurd else .raise
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
  if let some x := subjLocal then
    if c.names.any (·.1 == x) then throw "a match whose pattern assigns its subject"
  declarePat before c
  if (← field v "raises") == .bool true then
    return .seq pre (match c.test with
      | some t => .ite t (.seq c.post .nil) .raise
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
      -- A rest parameter (`*args`) takes as many arguments as are given
      -- (any value: its declared `Array[E]` is no type of the model's).
      -- Otherwise the positional parameters the call fills; those it
      -- leaves, and keyword ones, must have defaults.
      let ps := (← arr (← field m "params")).toList
      let params ← if ← ps.anyM (fun p => do pure ((← str (← field p "kind")) == "Rest")) then
          match ps with
          | [p] => do let t ← T.tyOrTop (← field p "type"); pure (as.map fun _ => t)
          | _ => throw "a rest parameter with others"
        else do
          let pos ← ps.filterM fun p => do pure ((← str (← field p "kind")) == "Positional")
          let rest := ps.filter fun p => !(pos.take as.length).contains p
          for p in rest do
            unless (← field p "default") == .bool true do throw "a built-in call leaving a parameter"
          (pos.take as.length).mapM fun p => do T.tyOrTop (← field p "type")
      let ret ← T.tyOrTop (← field m "ret")
      let (rs, rps) ← match recv with
        | some r => do
          let rt ← T.nodeTy (← nat (← field recvJ "id"))
          pure ([r], [rt])
        | none =>
          if (← nat (← field m "owner")) == T.kernelId then pure ([], [])
          else pure ([.self], [[.cls 0 []]])
      return .prim name (rs ++ as) (rps ++ params) ret
    if recv.isNone && T.qclass (← nat (← field m "owner")) == some 1 && !(← read).top then
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
  let name ← str (← field m "name")
  let params ← (← arr (← field m "params")).toList.mapM fun p => do
    if (← str (← field p "kind")) != "Positional" then throw "a parameter not positional"
    if (← field p "default") == .bool true then throw "a parameter with a default"
    pure (← str (← field p "name"), ← T.ty (← field p "type"))
  -- A method a `static` statement generated (docs/14 §5): its body is a
  -- block of the `static def` that made it, not in the tree.
  if (← field m "generated") == .bool true then throw "a generated method"
  let ret ← T.ty (← field m "ret")
  if (← field m "block_optional") == .bool true then throw "an optional block"
  let block ← match ← field m "block" with
    | .null => pure none
    | b => do
      let t ← field b "type"
      unless (← str (← field t "t")) == "proc" do throw "a block type"
      let ps ← (← arr (← field t "params")).toList.mapM T.ty
      pure (some ⟨ps, ← T.ty (← field t "ret")⟩)
  -- (In `initialize`, the superclass, for `super`.)
  let init ← if name != "initialize" then pure none else do
    let sup ← match ← field (← T.cls (← nat (← field m "owner"))) "superclass" with
      | .null => pure 0
      | t => pure (← T.tyClass t).1
    pure (some (params, sup))
  let w : Where := ⟨owner == 1, init, some (← nat (← field m "owner"))⟩
  let (bd, ls) ← ((body T (← arr (← field d "body"))).run w).run params
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
  let userIds ← user.mapM fun c => do nat (← field c "id")
  -- `Object` is 0, the files' main classes (the top level and its
  -- methods) 1, the user classes from 2.
  let qclass : Nat → Option Nat := fun id =>
    if id == objectId then some 0
    else if mainClasses.contains id then some 1
    else (userIds.idxOf? id).map (· + 2)
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
    fun id => (narrowedList.find? (·.1 == id)).map (·.2), selfParam⟩
  let qclasses ← user.mapM fun c => do
    -- An included module's methods are not the model's.
    unless (← arr (← field c "includes")).isEmpty do throw "an include"
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
      let (bd, ls) ← ((expr T v).run ⟨true, none, none⟩).run []
      pure (⟨1, "const " ++ (← str (← field k "name")), [], ty, none, ls, bd⟩ : Method)
  let some mainUnit := units.back? | throw "no unit"
  let (mainBody, mainLocals) ← ((body T (← arr (← field mainUnit "body"))).run ⟨true, none, none⟩).run []
  let all : Ty := [.nil, .bool, .int, .str, .cls 0 []]
  -- A default that tests or loops, with a bounded parameter anywhere (it
  -- is checked in each inheriting class): out of range, as in `method`.
  let bounded ← user.anyM fun c => do
    (← arr (← field c "type_params")).anyM fun p => do pure !(← arr (← field p "bounds")).isEmpty
  let defaults ← fdefs.toList.mapM fun e => do
    let (x, ls) ← ((expr T (← field e "value")).run ⟨false, none, none⟩).run []
    unless ls.isEmpty do throw "a field default with locals"
    if bounded && narrows x then throw "a test in a default with a bounded parameter"
    pure x
  -- The user classes' accessors.
  let accessors ← (← arr (← field j "methods")).toList.filterMapM fun m => do
    match qclass (← nat (← field m "owner")) with
    | some q => if q ≥ 2 then accessor T q m else pure none
    | none => pure none
  let own := methods ++ accessors
  let P : Program := ⟨⟨"Object", none, [], [], [], [], .cls⟩ :: ⟨"<main>", some 0, [], [], [], [], .cls⟩ :: qclasses,
    own ++ consts,
    ⟨1, "<main>", [], all, none, mainLocals, mainBody⟩, defaults⟩
  -- Two methods of one name in a class, or in a class and its ancestor
  -- with other parameters or block, are overloads (one signature twice in
  -- a class is a Rust error): the Rust checker picks the one that fits,
  -- `Program.lookup` the nearest. Out of range. (Not `initialize`, which
  -- no call dispatches on: `super` takes the nearest above in both, and
  -- a `new` taking another than the model's is out of range there.)
  for a in own do
    for b in own do
      if a.name == b.name && a.name != "initialize" && a.owner != b.owner &&
          P.classes.subclass a.owner b.owner &&
          (a.params.map (·.2) != b.params.map (·.2) || a.block != b.block) then
        throw s!"overloads of {a.name}"
    if (own.filter fun m => m.owner == a.owner && m.name == a.name).length > 1 then
      throw s!"overloads of {a.name}"
  pure P

end QuarzCore.Conformance
