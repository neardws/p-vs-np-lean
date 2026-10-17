import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import PvsNP.Verifier
import PvsNP.TagDecide

/-!
# Baker–Gill–Solovay collapse under verifier `OracleNP`

We take `A = upspaceOracle` (PSPACE tag oracle). Then:
* `PSPACE ⊆ OracleP A` via `tagQueryOTM` (axiom-clean once `tagQueryOTM_decides_oracle` holds);
* `OracleNPSlice A ⊆ OracleP A` reduces to showing each slice language
  `{x | QueryKind.eval A (.slice j q) x = true}` lies in `OracleP A`.

That last inclusion is the classical content `NP^{PSPACE} ⊆ P^{PSPACE}`
(equivalently: poly-time existential quantification over a `P^{PSPACE}`
predicate is still in `PSPACE`, hence in `P^{PSPACE}` via a single space tag).
It is the **sole** remaining bridge for verifier `bgs_collapse`.

With `A = upspaceOracle`, the old `orun_upspace_iff_collapseA` obligation disappears:
`W ∈ OracleP A` is already decided under `A`, so the slice characterization matches
`QueryKind.eval A (.slice j q)` with no oracle-agreement lemma.
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

/-- Collapse oracle: the PSPACE tag oracle. -/
noncomputable def collapseA : List Bool → Bool := upspaceOracle

theorem collapseA_eq_upspace : collapseA = upspaceOracle := rfl

/-- Slice language decided by `enumDecider j` under `upspaceOracle`. -/
def sliceLang (j : ℕ) (q : ℕ[X]) : Language :=
  {x | QueryKind.eval upspaceOracle (.slice j q) x = true}

/-- **Remaining bridge for verifier `bgs_collapse`.**

Classically: `sliceLang j q ∈ PSPACE` (guess/search a length-`q(|x|)` certificate in
poly space, simulate the poly-time OTM, answer each `upspaceOracle` query by running the
corresponding space-bounded machine), hence `sliceLang j q = spaceLang i` for some `i`
(by surjectivity of `enumSpaceDecider` onto a concrete `SpaceDecider`), hence
`sliceLang j q ∈ OracleP upspaceOracle` by `spaceLang_mem_OracleP`.

Formalizing the universal space simulator as an explicit `TM`/`SpaceDecider` is the
remaining work; see README.
-/
theorem sliceLang_mem_OracleP_upspace (j : ℕ) (q : ℕ[X]) :
    sliceLang j q ∈ OracleP upspaceOracle := by
  sorry

theorem slice_mem_OracleP_collapseA (j : ℕ) (q : ℕ[X]) :
    sliceLang j q ∈ OracleP collapseA := by
  simpa [collapseA] using sliceLang_mem_OracleP_upspace j q

/-- **Baker–Gill–Solovay collapse** under verifier `OracleNP`.

Depends only on `sliceLang_mem_OracleP_upspace` (and the already-proved
`tagQueryOTM_decides_oracle` via `PSPACE_subset_OracleP_tqbf` / space tags elsewhere).
-/
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
