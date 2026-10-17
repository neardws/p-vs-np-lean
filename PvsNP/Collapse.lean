import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import PvsNP.Verifier
import PvsNP.TagDecide

/-!
# Baker–Gill–Solovay collapse under verifier `OracleNP`

`OracleNP A = OracleP A ∪ OracleNPSlice A` (poly-time oracle verifiers).

Collapse oracle: `upspaceOracle` (PSPACE-complete tagged space acceptance).
This is **not** the constant-true raw-slice shortcut.

Route: `OracleNPSlice ⊆ PSPACE ⊆ OracleP`.
`PSPACE ⊆ OracleP` is proved (`tagQueryOTM` / `PSPACE_subset_OracleP_tqbf`).
`OracleP ⊆ PSPACE` and slice-closure are the classical Fin-machine simulations
(`P^{PSPACE} ⊆ PSPACE`, `NPSPACE = PSPACE`), left as infrastructure `sorry`s below.
-/

namespace PvsNP

open Polynomial Function

def LengthSymmetric (L : Language) : Prop :=
  ∀ x y : List Bool, x.length = y.length → (x ∈ L ↔ y ∈ L)

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

def acceptAllOTM : OTM (Fin 2) (Fin 1) where
  start := 0; accept := 0; reject := 1; blank := 0
  inp := fun _ => 0; ask := 1; yes := 0; no := 1
  wr := fun _ _ => none
  δ := fun q g => (q, g, Dir.stay)

theorem acceptAllOTM_decides (A : List Bool → Bool) :
    ODecidesInTime acceptAllOTM A Set.univ (fun _ => 0) := by
  intro x
  cases x <;> constructor <;>
    simp [OTM.orun, OTM.oinit, TM.init, TM.halted, acceptAllOTM]

theorem univ_mem_OracleP (A : List Bool → Bool) : (Set.univ : Language) ∈ OracleP A := by
  refine ⟨2, 1, acceptAllOTM, 0, ?_⟩
  intro x; simpa [eval_zero] using acceptAllOTM_decides A x

/-- Infrastructure: `P^{PSPACE} ⊆ PSPACE` Fin-machine simulator. -/
theorem exists_PSPACE_decider_of_OracleP {L : Language}
    (_h : L ∈ OracleP upspaceOracle) :
    ∃ s : SpaceDecider,
      ∀ x, x ∈ L ↔ acceptsInSpace s.M x (x.length ^ s.d + s.d) = true := by
  sorry

theorem OracleP_subset_PSPACE : OracleP upspaceOracle ⊆ PSPACE := by
  intro L h
  obtain ⟨s, hs⟩ := exists_PSPACE_decider_of_OracleP h
  exact ⟨s, hs⟩

/-- Infrastructure: certificate enumeration (`NPSPACE = PSPACE`). -/
theorem exists_PSPACE_decider_of_slice {W L : Language} {q : ℕ[X]}
    (_hW : W ∈ PSPACE)
    (_hq : ∀ x, x ∈ L ↔ ∃ y : List Bool, y.length = q.eval x.length ∧ y ∈ W) :
    ∃ s : SpaceDecider,
      ∀ x, x ∈ L ↔ acceptsInSpace s.M x (x.length ^ s.d + s.d) = true := by
  sorry

theorem OracleNPSlice_subset_PSPACE :
    OracleNPSlice upspaceOracle ⊆ PSPACE := by
  intro L ⟨W, hW, q, hq⟩
  obtain ⟨s, hs⟩ := exists_PSPACE_decider_of_slice (OracleP_subset_PSPACE hW) hq
  exact ⟨s, hs⟩

/-- **Baker–Gill–Solovay collapse** under verifier `OracleNP`.

Uses the PSPACE-complete oracle `upspaceOracle` (non-trivial). Depends on the two
infrastructure simulations above for `OracleNPSlice ⊆ PSPACE`.
-/
theorem bgs_collapse : ∃ A, OracleP A = OracleNP A := by
  refine ⟨upspaceOracle, ?_⟩
  ext L
  constructor
  · intro h; exact OracleP_subset_OracleNP upspaceOracle h
  · intro h
    rcases h with hP | hS
    · exact hP
    · exact PSPACE_subset_OracleP_tqbf (OracleNPSlice_subset_PSPACE hS)

/-! ## Raw-slice fragment (sorry-free sanity check) -/

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

/-- Sorry-free collapse for the raw-slice fragment only (not the verifier `OracleNP`). -/
theorem bgs_collapse_rawFragment :
    ∃ A, OracleP A = OracleP A ∪ OracleNPRawSlice A := by
  refine ⟨trivialOracle, ?_⟩
  ext L
  constructor
  · intro h; exact Or.inl h
  · intro h
    rcases h with hP | hS
    · exact hP
    · exact OracleNPRawSlice_trivial_subset_OracleP hS

end PvsNP
