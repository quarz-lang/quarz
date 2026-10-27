/-
What the soundness theorem (Soundness.lean) says of each of the
interpreter's functions, and lemmas to chain them.
-/

import QuarzCore.StableLemmas
import QuarzCore.InheritLemmas

set_option linter.deprecated false

namespace QuarzCore

variable (P : Program) (orc : Oracle)

/-- Values of the types, in order. -/
def AllTy (s : Store) : List Value → List Ty → Prop
  | [], [] => True
  | v :: vs, t :: ts => s.hasTy P v t ∧ AllTy s vs ts
  | _, _ => False

/-- What the arguments' evaluation gives. -/
def ArgsPost (c : Ctx) (ao : ArgsOut) (fr : Frame) (ws : List (Ctx × Env × Out)) (Λ : List Ty)
    (s : Store) (W : Nat → Prop) : ArgsResult → Prop
  | .ok vs s' => ∃ tys Δ, ao = .live tys Δ ∧ ∃ Λ', WfStore P Λ' s' ∧ Ext P W (initW c fr) Λ Λ' s s' ∧
      FrameOK P c Λ' fr s' ws ∧ Sat P c Δ fr s' ∧ AllTy P s' vs tys
  | .other .stuck => False
  | .other (.ok _ _) => False
  | .other (.returned v s') => ∃ Λ', WfStore P Λ' s' ∧ Ext P W (initW c fr) Λ Λ' s s' ∧
      FrameOK P c Λ' fr s' ws ∧ s'.hasTy P v c.meth.ret ∧ c.inBlock = false ∧
      (c.inInit = true → (s'.typeOf fr.self).isSome)
  | .other _ => True

/-- The writes of evaluating `es` in `fr`. -/
def evalWs (fr : Frame) (es : List Expr) (l : Nat) : Prop :=
  (∃ e ∈ es, frameW fr.vars e.assigned l) ∨ blkW fr.blk l

def EvalGood (n : Nat) : Prop :=
  ∀ (c : Ctx) (Γ : Env) (e : Expr) (o : Out) (fr : Frame) (s : Store) (Λ : List Ty)
    (ws : List (Ctx × Env × Out)),
    c.prog = P → Typed c Γ e o → WfStore P Λ s → FrameOK P c Λ fr s ws → Sat P c Γ fr s →
    Post P c o fr ws Λ s (evalW fr e) (eval P orc n fr s e)

def ArgsGood (n : Nat) : Prop :=
  ∀ (c : Ctx) (Γ : Env) (es : List Expr) (ao : ArgsOut) (fr : Frame) (s : Store) (Λ : List Ty)
    (ws : List (Ctx × Env × Out)),
    c.prog = P → TypedArgs c Γ es ao → WfStore P Λ s → FrameOK P c Λ fr s ws → Sat P c Γ fr s →
    ArgsPost P c ao fr ws Λ s (evalWs fr es) (evalArgs P orc n fr s es)

/-- A block given to a method that takes `sig`, as it was checked (`ws`:
its chain's witnesses), its chain in the store. -/
def BlkGiven (Λ : List Ty) (s : Store) (ws : List (Ctx × Env × Out)) (sig : Option BlockSig)
    (blk : Option Closure) : Prop :=
  ChainAt P Λ s ws blk sig ∧ ∀ l, chainLocs blk l → l < s.locs.length

/-- What a call gives: never stuck; a value of the method's result type,
the store grown as the block's writes allow, the block as it was. -/
def SendPost (ret : Ty) (sig : Option BlockSig) (blk : Option Closure) (w : List (Ctx × Env × Out))
    (Λ : List Ty) (s : Store) : Result → Prop
  | .ok v s' => ∃ Λ', WfStore P Λ' s' ∧ Ext P (blkW blk) (fun _ => False) Λ Λ' s s' ∧ s'.hasTy P v ret ∧
      BlkGiven P Λ' s' w sig blk
  | .stuck | .returned _ _ => False
  | _ => True

def SendGood (n : Nat) : Prop :=
  ∀ (s : Store) (Λ : List Ty) (recv : Value) (k : Nat) (m : String) (mt : Method)
    (vs : List Value) (blk : Option Closure) (w : List (Ctx × Env × Out)),
    WfStore P Λ s → (∃ l o, recv = .obj l ∧ s.objs[l]? = some o ∧ k ∈ P.classes.ancestors o.cls) →
    s.hasTy P recv [.cls k] → m ≠ "initialize" → P.lookup k m = some mt →
    AllTy P s vs (mt.params.map (·.2)) →
    BlkGiven P Λ s w mt.block blk →
    SendPost P mt.ret mt.block blk w Λ s (send P orc n s recv m vs blk)

def BlockGood (n : Nat) : Prop :=
  ∀ (s : Store) (Λ : List Ty) (clo : Closure) (sig : BlockSig) (vs : List Value)
    (w : List (Ctx × Env × Out)),
    WfStore P Λ s → BlkGiven P Λ s w (some sig) (some clo) →
    AllTy P s vs sig.params →
    SendPost P sig.ret (some sig) (some clo) w Λ s (runBlock P orc n s clo vs)

/-- `v == w` (`w` nil, true or false): never stuck, a boolean or what a
user `==` gives (a boolean, `wfMethod`), no local written. -/
def EqualGood (n : Nat) : Prop :=
  ∀ (s : Store) (Λ : List Ty) (v w : Value) (t : Ty),
    WfStore P Λ s → s.hasTy P v t → (w = .nil ∨ w = .bool true ∨ w = .bool false) →
    SendPost P [.bool] none none [] Λ s (equal P orc n s v w)

/-- What `C.new(args)` gives: never stuck; an instance of `C`, no
location written, no object there before changed but as `Ext` allows. -/
def ConstructPost (k : Nat) (Λ : List Ty) (s : Store) : Result → Prop
  | .ok v s' => ∃ Λ', WfStore P Λ' s' ∧ Ext P (fun _ => False) (fun _ => False) Λ Λ' s s' ∧
      s'.hasTy P v [.cls k]
  | .stuck | .returned _ _ => False
  | _ => True

def ConstructGood (n : Nat) : Prop :=
  ∀ (s : Store) (Λ : List Ty) (k : Nat) (vs : List Value),
    WfStore P Λ s → k < P.classes.length →
    (∀ mi, P.lookup k "initialize" = some mi → mi.block = none ∧ AllTy P s vs (mi.params.map (·.2))) →
    (P.lookup k "initialize" = none → vs = []) →
    ConstructPost P k Λ s (construct P orc n s k vs)

structure Good (n : Nat) : Prop where
  eval : EvalGood P orc n
  args : ArgsGood P orc n
  send : SendGood P orc n
  block : BlockGood P orc n
  equal : EqualGood P orc n
  construct : ConstructGood P orc n

variable {P}

theorem Post.extend {c : Ctx} {o : Out} {fr : Frame} {ws : List (Ctx × Env × Out)} {Λ Λ1 : List Ty}
    {s s1 : Store}
    {W1 W2 W : Nat → Prop} {r : Result} (h : Post P c o fr ws Λ1 s1 W2 r)
    (he : Ext P W1 (initW c fr) Λ Λ1 s s1) (hw : WfStore P Λ s) (h1 : ∀ l, W1 l → W l)
    (h2 : ∀ l, W2 l → W l) : Post P c o fr ws Λ s W r := by
  cases r with
  | ok v s' =>
    obtain ⟨Λ', a, e, f, g, i, j, k⟩ := h
    exact ⟨Λ', a, (he.trans e hw).mono (fun l hl => hl.elim (h1 l) (h2 l)) (fun l hl => hl.elim id id),
      f, g, i, j, k⟩
  | returned v s' =>
    obtain ⟨Λ', a, e, f, g, i⟩ := h
    exact ⟨Λ', a, (he.trans e hw).mono (fun l hl => hl.elim (h1 l) (h2 l)) (fun l hl => hl.elim id id),
      f, g, i⟩
  | raised => trivial
  | timeout => trivial
  | stuck => exact h

/-- Chaining: what comes after an expression that ended with a value. -/
theorem Post.bind {c : Ctx} {o o' : Out} {fr : Frame} {ws : List (Ctx × Env × Out)} {Λ : List Ty}
    {s : Store}
    {W W' : Nat → Prop} {r : Result} {k : Value → Store → Result}
    (h : Post P c o fr ws Λ s W r) (hW : ∀ l, W l → W' l)
    (hk : ∀ v s1 Λ1, WfStore P Λ1 s1 → Ext P W (initW c fr) Λ Λ1 s s1 → FrameOK P c Λ1 fr s1 ws →
      s1.hasTy P v o.ty → OutOK P c o.out fr s1 →
      (v.truthy = true → OutOK P c o.tt fr s1) → (v.truthy = false → OutOK P c o.ff fr s1) →
      Post P c o' fr ws Λ s W' (k v s1)) :
    Post P c o' fr ws Λ s W' (r.bind k) := by
  cases r with
  | ok v s1 =>
    obtain ⟨Λ1, a, e, f, g, i, j, k'⟩ := h
    exact hk v s1 Λ1 a e f g i j k'
  | returned v s' =>
    obtain ⟨Λ', a, e, f, g, i⟩ := h
    exact ⟨Λ', a, e.mono hW (fun _ h => h), f, g, i⟩
  | raised => trivial
  | timeout => trivial
  | stuck => exact h

/-- `Post.bind`, the continuation also told which result it follows. -/
theorem Post.bindEq {c : Ctx} {o o' : Out} {fr : Frame} {ws : List (Ctx × Env × Out)} {Λ : List Ty}
    {s : Store}
    {W W' : Nat → Prop} {r : Result} {k : Value → Store → Result}
    (h : Post P c o fr ws Λ s W r) (hW : ∀ l, W l → W' l)
    (hk : ∀ v s1 Λ1, r = .ok v s1 → WfStore P Λ1 s1 → Ext P W (initW c fr) Λ Λ1 s s1 →
      FrameOK P c Λ1 fr s1 ws →
      s1.hasTy P v o.ty → OutOK P c o.out fr s1 →
      (v.truthy = true → OutOK P c o.tt fr s1) → (v.truthy = false → OutOK P c o.ff fr s1) →
      Post P c o' fr ws Λ s W' (k v s1)) :
    Post P c o' fr ws Λ s W' (r.bind k) := by
  cases r with
  | ok v s1 =>
    obtain ⟨Λ1, a, e, f, g, i, j, k'⟩ := h
    exact hk v s1 Λ1 rfl a e f g i j k'
  | returned v s' =>
    obtain ⟨Λ', a, e, f, g, i⟩ := h
    exact ⟨Λ', a, e.mono hW (fun _ h => h), f, g, i⟩
  | raised => trivial
  | timeout => trivial
  | stuck => exact h

end QuarzCore
