import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import PvsNP.Verifier
import PvsNP.TagDecide

/-!
# Baker–Gill–Solovay collapse under verifier `OracleNP`

`A = upspaceOracle`. Separation-side infrastructure (`tagQueryOTM`, `PSPACE ⊆ OracleP A`)
is axiom-clean. The remaining bridge is `sliceLang ∈ OracleP A`, i.e. classical
`NP^{PSPACE} ⊆ P^{PSPACE}`.

Semantic setup is below; the sole `sorry` is `exists_slice_space_decider`
(explicit poly-space `TM` / equivalent passthrough `OTM`).
-/

namespace PvsNP

open Polynomial Function

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

noncomputable def collapseA : List Bool → Bool := upspaceOracle

theorem collapseA_eq_upspace : collapseA = upspaceOracle := rfl

/-- Slice language: ∃ poly-length certificate accepted by `enumDecider j` under `upspaceOracle`. -/
def sliceLang (j : ℕ) (q : ℕ[X]) : Language :=
  {x | QueryKind.eval upspaceOracle (.slice j q) x = true}

/-! ## Semantic bridge toward `sliceLang ∈ OracleP upspaceOracle` -/

def relativeLang (j : ℕ) : Language :=
  {y | QueryKind.eval upspaceOracle (.relative j) y = true}

theorem mem_relativeLang_iff (j : ℕ) (y : List Bool) :
    y ∈ relativeLang j ↔
      ((enumDecider j).M.orun upspaceOracle
        ((enumDecider j).p.eval y.length)
        ((enumDecider j).M.oinit y)).cfg.state = (enumDecider j).M.accept := by
  simp [relativeLang, QueryKind.eval]

theorem mem_sliceLang_iff_exists_relative (j : ℕ) (q : ℕ[X]) (x : List Bool) :
    x ∈ sliceLang j q ↔
      ∃ y : List Bool, y.length = q.eval x.length ∧ y ∈ relativeLang j := by
  classical
  constructor
  · intro hx
    simp only [sliceLang, Set.mem_setOf_eq, QueryKind.eval] at hx
    obtain ⟨y, hy, hacc⟩ := of_decide_eq_true hx
    exact ⟨y, hy, by simpa [mem_relativeLang_iff] using hacc⟩
  · intro ⟨y, hy, hyrel⟩
    simp only [sliceLang, Set.mem_setOf_eq, QueryKind.eval]
    exact decide_eq_true ⟨y, hy, by simpa [mem_relativeLang_iff] using hyrel⟩

noncomputable def queryBudget (j : ℕ) (m : ℕ) : ℕ := (enumDecider j).p.eval m

theorem query_maxLen_le_budget (j : ℕ) (y : List Bool) :
    ((enumDecider j).M.unfold (queryBudget j y.length)
      ((enumDecider j).M.oinit y)).maxLen ≤ queryBudget j y.length := by
  simpa [OTM.oinit, queryBudget] using
    OTM.unfold_maxLen (enumDecider j).M (queryBudget j y.length) ((enumDecider j).M.oinit y)

noncomputable def sliceSpaceDegree (j : ℕ) (q : ℕ[X]) : ℕ :=
  let dp := (enumDecider j).p.natDegree
  let dq := q.natDegree
  dp * dq + dq + dp + 4

theorem sliceLang_mem_OracleP_of_space_decider (j : ℕ) (q : ℕ[X])
    (s : SpaceDecider)
    (hs : ∀ x, acceptsInSpace s.M x (x.length ^ s.d + s.d) = true ↔ x ∈ sliceLang j q) :
    sliceLang j q ∈ OracleP upspaceOracle :=
  PSPACE_subset_OracleP_tqbf ⟨s, fun x => (hs x).symm⟩

/-- **Gap:** compile the following algorithm to an explicit `SpaceDecider`.

1. On input `x`, set `m := q.eval |x|`; enumerate all `y ∈ {0,1}^m` (reuse space).
2. For each `y`, simulate `(enumDecider j).M` for `queryBudget j m` steps.
3. On ask with buffer `w`: if `w = tagEncode i z`, answer via
   `acceptsInSpace (enumSpaceDecider i).M z (…)`; else `false`.
4. Accept iff some certificate simulation accepts.

This is `NP^{PSPACE} ⊆ PSPACE`. Equivalent alternative: an oracle-passthrough
`OTM` that searches certificates and delegates asks to `upspaceOracle`, placing
`sliceLang` directly in `OracleP upspaceOracle` without a space intermediate.
-/
theorem exists_slice_space_decider (j : ℕ) (q : ℕ[X]) :
    ∃ s : SpaceDecider,
      ∀ x, acceptsInSpace s.M x (x.length ^ s.d + s.d) = true ↔ x ∈ sliceLang j q := by
  sorry

theorem sliceLang_mem_OracleP_upspace (j : ℕ) (q : ℕ[X]) :
    sliceLang j q ∈ OracleP upspaceOracle := by
  obtain ⟨s, hs⟩ := exists_slice_space_decider j q
  exact sliceLang_mem_OracleP_of_space_decider j q s hs

theorem slice_mem_OracleP_collapseA (j : ℕ) (q : ℕ[X]) :
    sliceLang j q ∈ OracleP collapseA := by
  simpa [collapseA] using sliceLang_mem_OracleP_upspace j q

theorem bgs_collapse : ∃ A, OracleP A = OracleNP A := by
  classical
  refine ⟨collapseA, ?_⟩
  ext L
  constructor
  · intro h; exact Or.inl h
  · intro h
    rcases h with hP | hS
    · exact hP
    · obtain ⟨W, hW, q, hq⟩ := hS
      obtain ⟨j, hdec⟩ := OracleP.exists_enum (by simpa [collapseA] using hW)
      have hL : L = sliceLang j q := by
        ext x
        constructor
        · intro hx
          obtain ⟨y, hy, hyW⟩ := (hq x).1 hx
          have hacc := (hdec y).2.2 hyW
          simp only [sliceLang, Set.mem_setOf_eq, QueryKind.eval]
          exact decide_eq_true ⟨y, hy, hacc⟩
        · intro hev
          simp only [sliceLang, Set.mem_setOf_eq, QueryKind.eval] at hev
          obtain ⟨y, hy, hacc⟩ := of_decide_eq_true hev
          have hyW : y ∈ W := (hdec y).2.1 hacc
          exact (hq x).2 ⟨y, hy, hyW⟩
      rw [hL]
      exact slice_mem_OracleP_collapseA j q

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
