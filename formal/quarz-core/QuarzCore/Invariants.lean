/-
What a checked program's run keeps (design §4), for the soundness proof
(Soundness.lean):

- `WfStore`: every object's fields hold values of their declared types;
  `Λ`, a ghost, gives each location the declared type of the local it is
  for.
- `Ext W`: from one store to a later one, every location either keeps its
  value or, if it is in `W` (what may be written there), gets a value of
  its declared type; objects keep their classes and immutable fields.
- `Sat c Γ fr s`: the narrowing environment holds in frame `fr` (each
  local there holds a value of its narrowed and of its declared type,
  each immutable field of `self` one of its narrowed type).
- `FrameOK`: the frame's locals are where `Λ` says, `self` is of the
  method's class, and its block (`ClosureOK`) is as it was checked.
- `ClosureOK`: an anonymous block, its body checked from the block's
  environment, and two facts about its frame: what held at the call,
  with what the block assigns un-narrowed (`R`: kept while the method
  called runs, the block writing only what it assigns, with values of
  their declared types), and what holds after the call (`J`: the call's
  environment joined with the body's end; restored each time the block
  ends).

Frames' locations do not overlap: a block's frame is older than the
frame of the method it is given to, and its locations are below.
-/

import QuarzCore.Typed
import QuarzCore.Semantics
import QuarzCore.TypeLemmas

namespace QuarzCore

variable (P : Program)

def Store.hasTy (s : Store) (v : Value) (t : Ty) : Prop := s.hasType P.classes v t = true

structure WfStore (Λ : List Ty) (s : Store) : Prop where
  len : Λ.length = s.locs.length
  objs : ∀ (l : Nat) (o : Obj), s.objs[l]? = some o →
    o.cls < P.classes.length ∧
    o.fields.length = (P.classes.allFields o.cls).length ∧
    ∀ (i : Nat) (v : Value) (f : Field), o.fields[i]? = some v → (P.classes.allFields o.cls)[i]? = some f →
      s.hasTy P v f.ty

structure Ext (W : Nat → Prop) (Λ Λ' : List Ty) (s s' : Store) : Prop where
  tys : Λ <+: Λ'
  locs : ∀ (l : Nat) (v : Value), s.locs[l]? = some v → ∃ v' : Value, s'.locs[l]? = some v' ∧
    (v' = v ∨ (W l ∧ ∃ t, Λ[l]? = some t ∧ s'.hasTy P v' t))
  objs : ∀ (l : Nat) (o : Obj), s.objs[l]? = some o → ∃ o' : Obj, s'.objs[l]? = some o' ∧ o'.cls = o.cls ∧
    ∀ (i : Nat) (f : Field), (P.classes.allFields o.cls)[i]? = some f → f.var = false → o'.fields[i]? = o.fields[i]?

/-- What a path holds in frame `fr` of a method checked in `c`. -/
def PathHolds (c : Ctx) (fr : Frame) (s : Store) : Path → Ty → Prop
  | .local x, t => ∃ l v d, lookupVar fr.vars x = some l ∧ s.locs[l]? = some v ∧
      c.decl x = some d ∧ s.hasTy P v t ∧ s.hasTy P v d
  | .field f, t => ∃ l o fd i v, fr.self = .obj l ∧ s.objs[l]? = some o ∧ c.field? f = some fd ∧
      fd.var = false ∧ fieldIndex P.classes o.cls f = some i ∧
      (P.classes.allFields o.cls)[i]? = some fd ∧ o.fields[i]? = some v ∧ s.hasTy P v t

def Sat (c : Ctx) (Γ : Env) (fr : Frame) (s : Store) : Prop :=
  ∀ p t, Γ.get p = some t → PathHolds P c fr s p t

/-- The locations a frame's locals are at. -/
def frameLocs (vars : List (String × Nat)) (l : Nat) : Prop := ∃ x, (x, l) ∈ vars

/-- The locations of the locals `xs` of a frame. -/
def frameW (vars : List (String × Nat)) (xs : List String) (l : Nat) : Prop :=
  ∃ x ∈ xs, lookupVar vars x = some l

/-- What running a block (and the blocks it was given) may write: in each
block's frame, the locals it assigns and its parameters. -/
def blkW : Option Closure → Nat → Prop
  | none, _ => False
  | some (.mk vars _ outer ps body), l => frameW vars (ps ++ body.assigned) l ∨ blkW outer l

/-- The locations of the frames of a block chain. -/
def chainLocs : Option Closure → Nat → Prop
  | none, _ => False
  | some (.mk vars _ outer _ _), l => frameLocs vars l ∨ chainLocs outer l

/-- What evaluating `e` in frame `fr` may write: the locals `e` assigns,
and what the frame's block may. -/
def evalW (fr : Frame) (e : Expr) (l : Nat) : Prop := frameW fr.vars e.assigned l ∨ blkW fr.blk l

/-- A frame of a method checked in `c`, its block aside. -/
structure FrameCore (c : Ctx) (Λ : List Ty) (vars : List (String × Nat)) (me : Value)
    (s : Store) : Prop where
  decls : ∀ x d, c.decl x = some d → ∃ l, lookupVar vars x = some l ∧ Λ[l]? = some d
  inj : ∀ x y l, lookupVar vars x = some l → lookupVar vars y = some l → x = y
  inStore : ∀ x l, (x, l) ∈ vars → l < s.locs.length
  self : s.hasTy P me [.cls c.meth.owner]
  selfObj : ∃ l, me = .obj l

def ClosureOK (Λ : List Ty) (s : Store) : Closure → BlockSig → Prop
  | .mk vars self outer ps body, sig => ∃ (c : Ctx) (Δ : Env) (ob : Out),
      c.prog = P ∧
      FrameCore P c Λ vars self s ∧
      -- What this block's method takes, as checked.
      (∀ sig', c.meth.block = some sig' → match outer with
        | some clo => ClosureOK Λ s clo sig'
        | none => False) ∧
      -- This frame's locations are above those of the frames below it.
      (∀ l l', frameLocs vars l → chainLocs outer l' → l' < l) ∧
      blockParamsOk c ps sig = true ∧
      Typed { c with inBlock := true } (blockEnv c Δ ps sig body) body ob ∧
      ob.ty.le c.ct sig.ret = true ∧
      Sat P c (c.reset Δ (ps ++ body.assigned)) ⟨vars, self, outer⟩ s ∧
      Sat P c (match ob.out with
        | some Γb => Δ.join Γb
        | none => Δ) ⟨vars, self, outer⟩ s

/-- A block as checked in context `c`, its call's environment `Δ`, its
body checked as `ob` (what `ClosureOK` says there is). -/
def ClosureAt (Λ : List Ty) (s : Store) (c : Ctx) (Δ : Env) (ob : Out) : Closure → BlockSig → Prop
  | .mk vars self outer ps body, sig =>
      c.prog = P ∧
      FrameCore P c Λ vars self s ∧
      (∀ sig', c.meth.block = some sig' → match outer with
        | some clo => ClosureOK P Λ s clo sig'
        | none => False) ∧
      (∀ l l', frameLocs vars l → chainLocs outer l' → l' < l) ∧
      blockParamsOk c ps sig = true ∧
      Typed { c with inBlock := true } (blockEnv c Δ ps sig body) body ob ∧
      ob.ty.le c.ct sig.ret = true ∧
      Sat P c (c.reset Δ (ps ++ body.assigned)) ⟨vars, self, outer⟩ s ∧
      Sat P c (match ob.out with
        | some Γb => Δ.join Γb
        | none => Δ) ⟨vars, self, outer⟩ s

theorem closureOK_iff {Λ : List Ty} {s : Store} {clo : Closure} {sig : BlockSig} :
    ClosureOK P Λ s clo sig ↔ ∃ c Δ ob, ClosureAt P Λ s c Δ ob clo sig := by
  cases clo; unfold ClosureOK ClosureAt; rfl

structure FrameOK (c : Ctx) (Λ : List Ty) (fr : Frame) (s : Store) : Prop where
  core : FrameCore P c Λ fr.vars fr.self s
  blk : ∀ sig, c.meth.block = some sig → ∃ clo, fr.blk = some clo ∧ ClosureOK P Λ s clo sig
  above : ∀ l l', frameLocs fr.vars l → chainLocs fr.blk l' → l' < l
  chainIn : ∀ l, chainLocs fr.blk l → l < s.locs.length

/-- The built-in methods answer with values of the types asked for. -/
def OracleOK (orc : Oracle) : Prop := ∀ n s t v, orc n s t = some v → s.hasTy P v t

/-- A checked program's methods, as the soundness proof uses them. -/
structure WfProg : Prop where
  classes : WfClasses P.classes
  methods : ∀ mt ∈ P.methods, P.wfMethod mt = true ∧
    ∃ o, Typed ⟨P, mt, false⟩ (mt.params.map fun (x, t) => (.local x, t)) mt.body o ∧
      (o.out = none ∨ o.ty.le P.classes mt.ret = true)

/-- Where an environment holds after an expression, if control gets there. -/
def OutOK (c : Ctx) (g : Option Env) (fr : Frame) (s : Store) : Prop :=
  ∃ Γ, g = some Γ ∧ Sat P c Γ fr s

/-- What evaluating an expression checked as `o` in context `c`, frame
`fr`, may give: never stuck; a value of its type, with the environments
after it holding (where its value is truthy and falsy too); a `return`
of the method's result type (not in a block); an exception (which ends
the run: v1 has no `rescue`). The store grows as `Ext` allows, the frame
stays as checked. -/
def Post (c : Ctx) (o : Out) (fr : Frame) (Λ : List Ty) (s : Store) (W : Nat → Prop) :
    Result → Prop
  | .stuck => False
  | .timeout => True
  | .ok v s' => ∃ Λ', WfStore P Λ' s' ∧ Ext P W Λ Λ' s s' ∧ FrameOK P c Λ' fr s' ∧
      s'.hasTy P v o.ty ∧ OutOK P c o.out fr s' ∧
      (v.truthy = true → OutOK P c o.tt fr s') ∧ (v.truthy = false → OutOK P c o.ff fr s')
  | .returned v s' => ∃ Λ', WfStore P Λ' s' ∧ Ext P W Λ Λ' s s' ∧ FrameOK P c Λ' fr s' ∧
      s'.hasTy P v c.meth.ret ∧ c.inBlock = false
  -- No `rescue` in v1: an exception ends the run.
  | .raised _ => True

end QuarzCore
