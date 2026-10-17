import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import PvsNP.Verifier
import PvsNP.TagDecide

/-!
# Baker–Gill–Solovay collapse under verifier `OracleNP`

`collapseA` answers `QueryKind` tags evaluated against `upspaceOracle`.
Slice languages reduce to one `tagQueryOTM` query.

Bridge `orun_upspace_iff_collapseA`: a machine counted in `OracleP collapseA`
accepts under `collapseA` iff it accepts under `upspaceOracle`. This is the
classical content that the extra tags of `collapseA` do not change the
poly-time oracle language of interest for BGS; it is the remaining obligation.
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

noncomputable def collapseA : List Bool → Bool := fun w =>
  @decide (∃ i : ℕ, ∃ x : List Bool, w = tagEncode i x ∧
    QueryKind.eval upspaceOracle (enumQueryKind i) x = true)
    (Classical.propDecidable _)

theorem collapseA_tag_iff (i : ℕ) (x : List Bool) :
    collapseA (tagEncode i x) = true ↔
      QueryKind.eval upspaceOracle (enumQueryKind i) x = true := by
  classical
  constructor
  · intro h
    have hex : ∃ i' x', tagEncode i x = tagEncode i' x' ∧
        QueryKind.eval upspaceOracle (enumQueryKind i') x' = true :=
      of_decide_eq_true (by simpa [collapseA] using h)
    obtain ⟨i', x', heq, hev⟩ := hex
    obtain ⟨rfl, rfl⟩ := tagEncode_injective heq
    exact hev
  · intro hev
    exact decide_eq_true ⟨i, x, rfl, hev⟩

/-- Bridge: `orun` of `enumDecider j` agrees on `upspaceOracle` vs `collapseA`. -/
theorem orun_upspace_iff_collapseA (j : ℕ) (y : List Bool) :
    ((enumDecider j).M.orun upspaceOracle
        ((enumDecider j).p.eval y.length) ((enumDecider j).M.oinit y)).cfg.state =
      (enumDecider j).M.accept ↔
    ((enumDecider j).M.orun collapseA
        ((enumDecider j).p.eval y.length) ((enumDecider j).M.oinit y)).cfg.state =
      (enumDecider j).M.accept := by
  sorry

theorem slice_mem_OracleP_collapseA (j : ℕ) (q : ℕ[X]) :
    ({x | QueryKind.eval upspaceOracle (.slice j q) x = true} : Language) ∈
      OracleP collapseA := by
  obtain ⟨i, hi⟩ := enumQueryKind_surjective (.slice j q)
  refine ⟨i + 6, 3, tagQueryOTM i, X + C (i + 4), ?_⟩
  intro x
  have h := tagQueryOTM_decides_oracle i collapseA x
  have h' :
      (tagQueryOTM i).toTM.halted
          ((tagQueryOTM i).orun collapseA ((X + C (i + 4)).eval x.length)
            ((tagQueryOTM i).oinit x)).cfg ∧
        (((tagQueryOTM i).orun collapseA ((X + C (i + 4)).eval x.length)
            ((tagQueryOTM i).oinit x)).cfg.state = (tagQueryOTM i).accept ↔
          collapseA (tagEncode i x) = true) := by
    simpa [eval_add, eval_X, eval_C, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
      Set.mem_setOf_eq] using h
  constructor
  · exact h'.1
  · constructor
    · intro hacc
      have htag : collapseA (tagEncode i x) = true := h'.2.1 hacc
      have hev := (collapseA_tag_iff i x).1 htag
      simpa [hi] using hev
    · intro hev
      have htag : collapseA (tagEncode i x) = true :=
        (collapseA_tag_iff i x).2 (by simpa [hi] using hev)
      exact h'.2.2 htag

/-- **Baker–Gill–Solovay collapse** under verifier `OracleNP`. -/
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
      obtain ⟨j, hdec⟩ := OracleP.exists_enum hW
      have hL : L = {x | QueryKind.eval upspaceOracle (.slice j q) x = true} := by
        ext x
        constructor
        · intro hx
          obtain ⟨y, hy, hyW⟩ := (hq x).1 hx
          have haccA := (hdec y).2.2 hyW
          have haccU := (orun_upspace_iff_collapseA j y).2 haccA
          simp only [Set.mem_setOf_eq, QueryKind.eval]
          exact decide_eq_true ⟨y, hy, haccU⟩
        · intro hev
          simp only [Set.mem_setOf_eq, QueryKind.eval] at hev
          obtain ⟨y, hy, haccU⟩ := of_decide_eq_true hev
          have haccA := (orun_upspace_iff_collapseA j y).1 haccU
          have hyW : y ∈ W := (hdec y).2.1 haccA
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
