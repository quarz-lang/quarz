/-
What a checked program's run keeps (design §4), for the soundness proof
(Soundness.lean):

- `WfStore`: every object's fields that are set hold values of their
  declared types; `Λ`, a ghost, gives each location the declared type of
  the local it is for.
- `Ext W Wo`: from one store to a later one, every location either keeps
  its value or, if it is in `W` (what may be written there), gets a value
  of its declared type; objects keep their classes and the fields set,
  and, but for those in `Wo` (the object an `initialize` running there
  makes), their immutable fields.
- `Sat c Γ fr s`: the narrowing environment holds in frame `fr` (each
  local there holds a value of its narrowed and of its declared type;
  each field of `self` there is set, an immutable one holding a value of
  its narrowed type).
- `FrameOK`: the frame's locals are where `Λ` says, `self` is of the
  method's class (in `initialize`, maybe not made yet: its fields the
  method's class does not have set), and its block chain (`ChainAt`) is
  as it was checked.
- `ChainAt`: each anonymous block of the chain, its body checked from the
  block's environment, and two facts about its frame: what held at the call,
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
    o.set.length = o.fields.length ∧
    ∀ (i : Nat) (v : Value) (f : Field), o.set[i]? = some true → o.fields[i]? = some v →
      (P.classes.allFields o.cls)[i]? = some f → s.hasTy P v f.ty

/-- Objects keep their classes and the fields set. -/
def ObjsGrow (s s' : Store) : Prop :=
  ∀ (l : Nat) (o : Obj), s.objs[l]? = some o → ∃ o' : Obj, s'.objs[l]? = some o' ∧ o'.cls = o.cls ∧
    o'.set.length = o.set.length ∧ ∀ i : Nat, o.set[i]? = some true → o'.set[i]? = some true

structure Ext (W Wo : Nat → Prop) (Λ Λ' : List Ty) (s s' : Store) : Prop where
  tys : Λ <+: Λ'
  locs : ∀ (l : Nat) (v : Value), s.locs[l]? = some v → ∃ v' : Value, s'.locs[l]? = some v' ∧
    (v' = v ∨ (W l ∧ ∃ t, Λ[l]? = some t ∧ s'.hasTy P v' t))
  grow : ObjsGrow s s'
  imm : ∀ (l : Nat) (o o' : Obj), s.objs[l]? = some o → s'.objs[l]? = some o' → ¬ Wo l →
    ∀ (i : Nat) (f : Field), (P.classes.allFields o.cls)[i]? = some f → f.var = false →
      o'.fields[i]? = o.fields[i]?

/-- What a path holds in frame `fr` of a method checked in `c`. -/
def PathHolds (c : Ctx) (fr : Frame) (s : Store) : Path → Ty → Prop
  | .local x, t => ∃ l v d, lookupVar fr.vars x = some l ∧ s.locs[l]? = some v ∧
      c.decl x = some d ∧ s.hasTy P v t ∧ s.hasTy P v d
  | .field f, t => ∃ l o fd i, fr.self = .obj l ∧ s.objs[l]? = some o ∧ c.field? f = some fd ∧
      fieldIndex P.classes o.cls f = some i ∧ (P.classes.allFields o.cls)[i]? = some fd ∧
      o.set[i]? = some true ∧ (fd.var = false → ∃ v, o.fields[i]? = some v ∧ s.hasTy P v t)

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

/-- The `self` of an `initialize` (or a field's default) of class `k`: an
object of `k` or a subclass, which may not be made yet, its fields `k`
does not have set (a subclass with fields to assign defines its own
`initialize`). -/
def InitSelf (k : Nat) (me : Value) (s : Store) : Prop :=
  ∃ l o, me = .obj l ∧ s.objs[l]? = some o ∧ k ∈ P.classes.ancestors o.cls ∧
    ∀ i, (P.classes.allFields k).length ≤ i → i < o.set.length → o.set[i]? = some true

/-- What an expression evaluated in frame `fr` may assign immutable
fields of: in `initialize` (not in a block), `self`'s. -/
def initW (c : Ctx) (fr : Frame) (l : Nat) : Prop :=
  c.inInit = true ∧ c.inBlock = false ∧ fr.self = .obj l

/-- A frame of a method checked in `c`, its block aside. -/
structure FrameCore (c : Ctx) (Λ : List Ty) (vars : List (String × Nat)) (me : Value)
    (s : Store) : Prop where
  decls : ∀ x d, c.decl x = some d → ∃ l, lookupVar vars x = some l ∧ Λ[l]? = some d
  inj : ∀ x y l, lookupVar vars x = some l → lookupVar vars y = some l → x = y
  inStore : ∀ x l, (x, l) ∈ vars → l < s.locs.length
  self : c.inInit = false → s.hasTy P me [.cls c.meth.owner]
  selfInit : c.inInit = true → InitSelf P c.meth.owner me s
  selfObj : ∃ l, me = .obj l

/-- A frame's block chain as it was checked: for each block (innermost
first) the context it was written in, the environment at its call and
its body's `Out` (`ws`), which stay the same while the block lives. A
block's own method takes the next block of the chain. -/
def ChainAt (Λ : List Ty) (s : Store) : List (Ctx × Env × Out) → Option Closure →
    Option BlockSig → Prop
  | [], none, none => True
  | (c, Δ, ob) :: ws, some (.mk vars self outer ps body), some sig =>
      c.prog = P ∧
      FrameCore P c Λ vars self s ∧
      ChainAt Λ s ws outer c.meth.block ∧
      (∀ l l', frameLocs vars l → chainLocs outer l' → l' < l) ∧
      blockParamsOk c ps sig = true ∧
      Typed { c with inBlock := true } (blockEnv c Δ ps sig body) body ob ∧
      ob.ty.le c.ct sig.ret = true ∧
      Sat P c (c.reset Δ (ps ++ body.assigned)) ⟨vars, self, outer⟩ s ∧
      Sat P c (match ob.out with
        | some Γb => Δ.join Γb
        | none => Δ) ⟨vars, self, outer⟩ s
  | _, _, _ => False

structure FrameOK (c : Ctx) (Λ : List Ty) (fr : Frame) (s : Store) (ws : List (Ctx × Env × Out)) :
    Prop where
  core : FrameCore P c Λ fr.vars fr.self s
  chain : ChainAt P Λ s ws fr.blk c.meth.block
  above : ∀ l l', frameLocs fr.vars l → chainLocs fr.blk l' → l' < l
  chainIn : ∀ l, chainLocs fr.blk l → l < s.locs.length
  /-- `initialize` (`new` gives it no block). -/
  initBlk : c.inInit = true → c.inBlock = false → fr.blk = none

/-- The built-in methods answer with values of the types asked for. -/
def OracleOK (orc : Oracle) : Prop := ∀ n s t v, orc n s t = some v → s.hasTy P v t

/-- A checked program's methods, as the soundness proof uses them. -/
structure WfProg : Prop where
  classes : WfClasses P.classes
  methods : ∀ mt ∈ P.methods, P.wfMethod mt = true ∧
    ∃ o, Typed ⟨P, mt, false⟩ (mt.params.map (fun (x, t) => (.local x, t)) ++
        (if mt.name == "initialize" then Program.heldEnv P.classes (P.classes.allFields mt.owner) else []))
      mt.body o ∧
      (mt.name ≠ "initialize" → o.out = none ∨ o.ty.le P.classes mt.ret = true) ∧
      (mt.name = "initialize" → o.out.all (Ctx.allSet ⟨P, mt, false⟩ ·) = true)
  inits : ∀ k, k < P.classes.length → P.wfInit k = true
  defaults : ∀ k, k < P.classes.length → ∀ j f d, (P.classes.allFields k)[j]? = some f →
    f.default = some d → ∃ e o, P.defaults[d]? = some e ∧
      Typed (P.defaultCtx k f.ty) (Program.heldEnv P.classes ((P.classes.allFields k).take j)) e o ∧
      o.ty.le P.classes f.ty = true

/-- Where an environment holds after an expression, if control gets there. -/
def OutOK (c : Ctx) (g : Option Env) (fr : Frame) (s : Store) : Prop :=
  ∃ Γ, g = some Γ ∧ Sat P c Γ fr s

/-- What evaluating an expression checked as `o` in context `c`, frame
`fr`, may give: never stuck; a value of its type, with the environments
after it holding (where its value is truthy and falsy too); a `return`
of the method's result type (not in a block; in `initialize`, with the
object made); an exception (which ends
the run: v1 has no `rescue`). The store grows as `Ext` allows, the frame
stays as checked. -/
def Post (c : Ctx) (o : Out) (fr : Frame) (ws : List (Ctx × Env × Out)) (Λ : List Ty) (s : Store)
    (W : Nat → Prop) : Result → Prop
  | .stuck => False
  | .timeout => True
  | .ok v s' => ∃ Λ', WfStore P Λ' s' ∧ Ext P W (initW c fr) Λ Λ' s s' ∧ FrameOK P c Λ' fr s' ws ∧
      s'.hasTy P v o.ty ∧ OutOK P c o.out fr s' ∧
      (v.truthy = true → OutOK P c o.tt fr s') ∧ (v.truthy = false → OutOK P c o.ff fr s')
  | .returned v s' => ∃ Λ', WfStore P Λ' s' ∧ Ext P W (initW c fr) Λ Λ' s s' ∧ FrameOK P c Λ' fr s' ws ∧
      s'.hasTy P v c.meth.ret ∧ c.inBlock = false ∧
      -- An `initialize` returns once its object is made.
      (c.inInit = true → (s'.typeOf fr.self).isSome)
  -- No `rescue` in v1: an exception ends the run.
  | .raised _ => True

end QuarzCore
