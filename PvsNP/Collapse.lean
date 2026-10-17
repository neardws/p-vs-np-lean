import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import PvsNP.Verifier
import PvsNP.SpaceSim

/-!
# Baker–Gill–Solovay collapse

For the classical raw-slice `OracleNP = OracleP ∪ OracleNPRawSlice`, the constant-true
oracle collapses: every raw slice is the universal language, which is in `OracleP`.
-/

namespace PvsNP

open Polynomial Function

/-- Length-symmetric languages. -/
def LengthSymmetric (L : Language) : Prop :=
  ∀ x y : List Bool, x.length = y.length → (x ∈ L ↔ y ∈ L)

/-! ## Trivial accept-all machine -/

/-- Two-state OTM already in the accept state on every input (0 steps). -/
def acceptAllOTM : OTM (Fin 2) (Fin 1) where
  start := 0
  accept := 0
  reject := 1
  blank := 0
  inp := fun _ => 0
  ask := 1
  yes := 0
  no := 1
  wr := fun _ _ => none
  δ := fun q g => (q, g, Dir.stay)

theorem acceptAllOTM_decides (A : List Bool → Bool) :
    ODecidesInTime acceptAllOTM A Set.univ (fun _ => 0) := by
  intro x
  cases x with
  | nil =>
    constructor
    · simp [OTM.orun, OTM.oinit, TM.init, TM.halted, acceptAllOTM]
    · simp [OTM.orun, OTM.oinit, TM.init, acceptAllOTM]
  | cons b bs =>
    constructor
    · simp [OTM.orun, OTM.oinit, TM.init, TM.halted, acceptAllOTM]
    · simp [OTM.orun, OTM.oinit, TM.init, acceptAllOTM]

theorem univ_mem_OracleP (A : List Bool → Bool) : (Set.univ : Language) ∈ OracleP A := by
  refine ⟨2, 1, acceptAllOTM, 0, ?_⟩
  intro x
  simpa [eval_zero] using acceptAllOTM_decides A x

/-- Constant-true oracle. -/
def trivialOracle : List Bool → Bool := fun _ => true

theorem rawSlice_trivial_eq_univ {L : Language} {q : ℕ[X]}
    (hq : ∀ x, x ∈ L ↔ ∃ y : List Bool, y.length = q.eval x.length ∧ trivialOracle y = true) :
    L = (Set.univ : Language) := by
  ext x
  constructor
  · intro _; trivial
  · intro _
    exact (hq x).2 ⟨List.replicate (q.eval x.length) true, by simp [List.length_replicate], rfl⟩

theorem OracleNPRawSlice_trivial_subset_OracleP :
    OracleNPRawSlice trivialOracle ⊆ OracleP trivialOracle := by
  intro L ⟨q, hq⟩
  rw [rawSlice_trivial_eq_univ hq]
  exact univ_mem_OracleP trivialOracle

/-- **Baker–Gill–Solovay collapse** (raw-slice `OracleNP`). -/
theorem bgs_collapse : ∃ A, OracleP A = OracleNP A := by
  refine ⟨trivialOracle, ?_⟩
  ext L
  constructor
  · intro h; exact OracleP_subset_OracleNP trivialOracle h
  · intro h
    rcases h with hP | hS
    · exact hP
    · exact OracleNPRawSlice_trivial_subset_OracleP hS

theorem OracleNPSlice.lengthSymmetric {A : List Bool → Bool} {L : Language}
    (h : L ∈ OracleNPSlice A) : LengthSymmetric L := by
  obtain ⟨W, _, q, hq⟩ := h
  intro x y hlen
  constructor
  · intro hx; exact (hq y).2 (by simpa [hlen] using (hq x).1 hx)
  · intro hy; exact (hq x).2 (by simpa [hlen] using (hq y).1 hy)

theorem not_lengthSymmetric_singleton_false :
    ¬ LengthSymmetric ({[false]} : Language) := by
  intro h
  have := (h [false] [true] (by rfl)).mp rfl
  simp at this

end PvsNP
