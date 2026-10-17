import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Basic.Countable.Defs
import Mathlib.Basic.Countable.Basic
import PvsNP.TuringMachine
import PvsNP.Complexity
import PvsNP.OracleVerifiers
import PvsNP.Enumeration

/-!
# Space-bounded simulation, PSPACE, and query kinds for BGS collapse
-/

namespace PvsNP

open Polynomial Function

def Cfg.space {Q Γ : Type} (c : Cfg Q Γ) : ℕ :=
  c.left.length + 1 + c.right.length

def configCount (k m S : ℕ) : ℕ :=
  k * (S + 1) * (m + 1) ^ S + 1

def TM.runInSpace {Q Γ : Type} [DecidableEq Q] (M : TM Q Γ) (S : ℕ) :
    ℕ → Cfg Q Γ → Option (Cfg Q Γ)
  | 0, c => if c.space ≤ S then some c else none
  | t + 1, c =>
      if c.space ≤ S then
        if M.halted c then some c
        else M.runInSpace S t (M.step c)
      else none

theorem TM.runInSpace_eq_run {Q Γ : Type} [DecidableEq Q]
    (M : TM Q Γ) (S t : ℕ) (c : Cfg Q Γ)
    (h : ∀ i ≤ t, (M.run i c).space ≤ S) :
    M.runInSpace S t c = some (M.run t c) := by
  induction t generalizing c with
  | zero =>
    have hs : c.space ≤ S := by simpa [TM.run] using h 0 (by omega)
    simp [TM.runInSpace, TM.run, hs]
  | succ t ih =>
    have hs0 : c.space ≤ S := by simpa [TM.run] using h 0 (by omega)
    by_cases hh : M.halted c
    · have hr : M.run (t + 1) c = c := TM.run_of_halted M hh (t + 1)
      simp [TM.runInSpace, hs0, hh, hr]
    · have hstep : ∀ i ≤ t, (M.run i (M.step c)).space ≤ S := by
        intro i hi
        simpa [TM.run] using h (i + 1) (Nat.succ_le_succ hi)
      simp only [TM.runInSpace, hs0, hh, ↓reduceIte]
      simpa [TM.run] using ih (M.step c) hstep

def TM.acceptsInSpaceBound {Q Γ : Type} [DecidableEq Q]
    (M : TM Q Γ) (x : List Bool) (S tmax : ℕ) : Bool :=
  match M.runInSpace S tmax (M.init x) with
  | none => false
  | some c => decide (c.state = M.accept)

def acceptsInSpace {k m : ℕ} (M : TM (Fin k) (Fin m)) (x : List Bool) (S : ℕ) : Bool :=
  M.acceptsInSpaceBound x S (configCount k m S)

abbrev TMData (k m : ℕ) :=
  Fin k × Fin k × Fin k × Fin m × (Bool → Fin m) × (Fin k → Fin m → Fin k × Fin m × Dir)

def TM.ofData {k m : ℕ} (d : TMData k m) : TM (Fin k) (Fin m) where
  start := d.1; accept := d.2.1; reject := d.2.2.1
  blank := d.2.2.2.1; inp := d.2.2.2.2.1; δ := d.2.2.2.2.2

def TM.toData {k m : ℕ} (M : TM (Fin k) (Fin m)) : TMData k m :=
  (M.start, M.accept, M.reject, M.blank, M.inp, M.δ)

structure SpaceDecider where
  k : ℕ
  m : ℕ
  M : TM (Fin k) (Fin m)
  d : ℕ

instance (k m : ℕ) : Fintype (TM (Fin k) (Fin m)) := by
  let e : TM (Fin k) (Fin m) ≃ TMData k m :=
  { toFun := TM.toData, invFun := TM.ofData, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  exact Fintype.ofEquiv (TMData k m) e.symm

instance (k m : ℕ) : Countable (TM (Fin k) (Fin m)) := inferInstance

instance : Countable SpaceDecider := by
  let φ : SpaceDecider ≃ (Σ k : ℕ, Σ m : ℕ, TM (Fin k) (Fin m) × ℕ) :=
  { toFun := fun s => ⟨s.k, s.m, (s.M, s.d)⟩
    invFun := fun ⟨k, m, Md⟩ => ⟨k, m, Md.1, Md.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have : Countable (Σ k : ℕ, Σ m : ℕ, TM (Fin k) (Fin m) × ℕ) := inferInstance
  exact Countable.of_equiv _ φ.symm

instance : Nonempty SpaceDecider :=
  ⟨{ k := 1, m := 1
     M := TM.ofData (0, 0, 0, 0, fun _ => 0, fun _ _ => (0, 0, Dir.stay))
     d := 0 }⟩

noncomputable def enumSpaceDecider : ℕ → SpaceDecider :=
  Classical.choose (exists_surjective_nat SpaceDecider)

theorem enumSpaceDecider_surjective : Surjective enumSpaceDecider :=
  Classical.choose_spec (exists_surjective_nat SpaceDecider)

def tagEncode (i : ℕ) (x : List Bool) : List Bool :=
  List.replicate i true ++ [false, true] ++ x

theorem tagEncode_injective {i i' : ℕ} {x x' : List Bool}
    (h : tagEncode i x = tagEncode i' x') : i = i' ∧ x = x' := by
  unfold tagEncode at h
  induction i generalizing i' with
  | zero =>
    cases i' with
    | zero => simp_all
    | succ j => simp [List.replicate_succ] at h
  | succ i ih =>
    cases i' with
    | zero => simp [List.replicate_succ] at h
    | succ j =>
      simp only [List.replicate_succ, List.cons_append] at h
      obtain ⟨-, htail⟩ := List.cons_eq_cons.mp h
      obtain ⟨hij, hx⟩ := ih htail
      exact ⟨by omega, hx⟩

def PSPACE : Set Language :=
  {L | ∃ s : SpaceDecider,
    ∀ x, x ∈ L ↔ acceptsInSpace s.M x (x.length ^ s.d + s.d) = true}

def spaceLang (i : ℕ) : Language :=
  {x | acceptsInSpace (enumSpaceDecider i).M x
    (x.length ^ (enumSpaceDecider i).d + (enumSpaceDecider i).d) = true}

/-! ## Query kinds -/

inductive QueryKind where
  | fin : ℕ → QueryKind
  | relative : ℕ → QueryKind
  | slice : ℕ → ℕ[X] → QueryKind

instance : Countable QueryKind := by
  let φ : QueryKind ≃ ℕ ⊕ ℕ ⊕ (ℕ × ℕ[X]) :=
  { toFun := fun
      | .fin i => Sum.inl i
      | .relative j => Sum.inr (Sum.inl j)
      | .slice j q => Sum.inr (Sum.inr (j, q))
    invFun := fun
      | Sum.inl i => .fin i
      | Sum.inr (Sum.inl j) => .relative j
      | Sum.inr (Sum.inr (j, q)) => .slice j q
    left_inv := fun c => by cases c <;> rfl
    right_inv := fun s => by rcases s with _ | _ | ⟨_, _⟩ <;> rfl }
  exact Countable.of_equiv _ φ.symm

instance : Nonempty QueryKind := ⟨.fin 0⟩

noncomputable def enumQueryKind : ℕ → QueryKind :=
  Classical.choose (exists_surjective_nat QueryKind)

theorem enumQueryKind_surjective : Surjective enumQueryKind :=
  Classical.choose_spec (exists_surjective_nat QueryKind)

/-- Evaluate a query kind against oracle `O`. -/
noncomputable def QueryKind.eval (O : List Bool → Bool) : QueryKind → List Bool → Bool
  | .fin k, x =>
      decide (acceptsInSpace (enumSpaceDecider k).M x
        (x.length ^ (enumSpaceDecider k).d + (enumSpaceDecider k).d) = true)
  | .relative j, x =>
      let d := enumDecider j
      decide ((d.M.orun O (d.p.eval x.length) (d.M.oinit x)).cfg.state = d.M.accept)
  | .slice j q, x =>
      let d := enumDecider j
      @decide (∃ y : List Bool, y.length = q.eval x.length ∧
        (d.M.orun O (d.p.eval y.length) (d.M.oinit y)).cfg.state = d.M.accept)
        (Classical.propDecidable _)

/-- Space-only oracle (`enumSpaceDecider` tags). -/
noncomputable def upspaceOracle : List Bool → Bool := fun w =>
  @decide (∃ i : ℕ, ∃ x : List Bool, w = tagEncode i x ∧
      acceptsInSpace (enumSpaceDecider i).M x
        (x.length ^ (enumSpaceDecider i).d + (enumSpaceDecider i).d) = true)
    (Classical.propDecidable _)

theorem upspaceOracle_tag_iff (i : ℕ) (x : List Bool) :
    upspaceOracle (tagEncode i x) = true ↔
      acceptsInSpace (enumSpaceDecider i).M x
        (x.length ^ (enumSpaceDecider i).d + (enumSpaceDecider i).d) = true := by
  classical
  constructor
  · intro h
    have hex : ∃ i' x', tagEncode i x = tagEncode i' x' ∧
        acceptsInSpace (enumSpaceDecider i').M x'
          (x'.length ^ (enumSpaceDecider i').d + (enumSpaceDecider i').d) = true :=
      of_decide_eq_true (by simpa [upspaceOracle] using h)
    obtain ⟨i', x', heq, hacc⟩ := hex
    obtain ⟨rfl, rfl⟩ := tagEncode_injective heq
    exact hacc
  · intro hacc
    exact decide_eq_true ⟨i, x, rfl, hacc⟩

theorem spaceLang_iff_oracle (i : ℕ) (x : List Bool) :
    x ∈ spaceLang i ↔ upspaceOracle (tagEncode i x) = true := by
  simp [spaceLang, upspaceOracle_tag_iff]

/-- Tag-then-copy OTM. -/
def tagQueryOTM (i : ℕ) : OTM (Fin (i + 6)) Γ₃ where
  start := ⟨0, by omega⟩
  accept := ⟨i + 4, by omega⟩
  reject := ⟨i + 5, by omega⟩
  blank := 0
  inp := encBit
  ask := ⟨i + 3, by omega⟩
  yes := ⟨i + 4, by omega⟩
  no := ⟨i + 5, by omega⟩
  wr := fun q g =>
    if q.val < i then some true
    else if q.val = i then some false
    else if q.val = i + 1 then some true
    else if q.val = i + 2 ∧ g ≠ 0 then some (toBit g)
    else none
  δ := fun q g =>
    if h : q.val < i then
      (⟨q.val + 1, by omega⟩, g, Dir.stay)
    else if h : q.val = i then
      (⟨i + 1, by omega⟩, g, Dir.stay)
    else if h : q.val = i + 1 then
      (⟨i + 2, by omega⟩, g, Dir.stay)
    else if h : q.val = i + 2 then
      if g = 0 then (⟨i + 3, by omega⟩, 0, Dir.stay)
      else (⟨i + 2, by omega⟩, g, Dir.right)
    else (q, g, Dir.stay)

end PvsNP
