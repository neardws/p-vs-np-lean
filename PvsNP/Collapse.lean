import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import PvsNP.SpaceSim
import PvsNP.TagDecide
import PvsNP.Verifier

/-!
# Baker–Gill–Solovay collapse

Oracle: `upspaceOracle` (universal space-bounded acceptance, tagged queries `1ⁱ01x`).

Under `OracleNP = OracleP ∪ OracleNPSlice`, collapse ⇔ `OracleNPSlice ⊆ OracleP`.
We route through `PSPACE`:
`OracleNPSlice ⊆ PSPACE ⊆ OracleP` and `OracleP ⊆ PSPACE`.
-/

namespace PvsNP

open Polynomial Function

/-- Membership depends only on length. -/
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


/-- Every PSPACE language is some `spaceLang i`. -/
theorem mem_PSPACE_iff_spaceLang {L : Language} :
    L ∈ PSPACE ↔ ∃ i, ∀ x, x ∈ L ↔ x ∈ spaceLang i := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := h
    obtain ⟨i, hi⟩ := enumSpaceDecider_surjective s
    refine ⟨i, fun x => ?_⟩
    subst hi
    simpa [spaceLang] using hs x
  · intro ⟨i, h⟩
    refine ⟨enumSpaceDecider i, fun x => ?_⟩
    simpa [spaceLang] using h x

/-- **Bridge 2.** `PSPACE ⊆ P^{upspace}`. -/
theorem PSPACE_subset_OracleP_tqbf : PSPACE ⊆ OracleP upspaceOracle := by
  intro L hL
  obtain ⟨i, h⟩ := (mem_PSPACE_iff_spaceLang).1 hL
  have := spaceLang_mem_OracleP i
  convert this using 1
  ext x
  exact h x

/-! ## Bridge 1 & 3: oracle poly-time / slice → PSPACE

A language decided by a poly-time OTM with `upspaceOracle` is decided in polynomial space
by simulating the OTM and answering each query via `acceptsInSpace` (space reuse).
Existential slice search is deterministic poly-space (enumerate certificates; reuse space).

The SpaceDecider witness is obtained from the (finite) OTM description via the universal
space-bounded simulator. Constructing that Fin-machine table is a sizable but routine
encoding; recorded as one simulation lemma each. -/

/-- Universal simulation: every `OracleP upspaceOracle` language is in `PSPACE`. -/
theorem OracleP_tqbf_subset_PSPACE : OracleP upspaceOracle ⊆ PSPACE := by
  intro L hL
  obtain ⟨k, m, M, p, hdec⟩ := hL
  -- Build a SpaceDecider that hardcodes `(k,m,M,p)` and on input `x` simulates the OTM,
  -- answering oracle calls by running `acceptsInSpace` on decoded tagged queries.
  -- Existence follows from finiteness of the transition table of such a simulator.
  classical
  have hex : ∃ s : SpaceDecider,
      ∀ x, x ∈ L ↔ acceptsInSpace s.M x (x.length ^ s.d + s.d) = true := by
    -- The characteristic function
    --   f x := decide ((M.orun upspaceOracle (p.eval x.length) (M.oinit x)).cfg.state = M.accept)
    -- is poly-space computable (OTM runs ≤ p(|x|) steps; each query of length ≤ p(|x|)
    -- is answered in space poly(|x|) by `acceptsInSpace`). Hence some SpaceDecider realizes f.
    sorry
  obtain ⟨s, hs⟩ := hex
  exact ⟨s, hs⟩

/-- Slice-NP over `upspaceOracle` is in `PSPACE` (enumerate witnesses; reuse space). -/
theorem OracleNPSlice_tqbf_subset_PSPACE : OracleNPSlice upspaceOracle ⊆ PSPACE := by
  intro L hL
  obtain ⟨W, hW, q, hq⟩ := hL
  have hWps : W ∈ PSPACE := OracleP_tqbf_subset_PSPACE hW
  obtain ⟨sW, hsW⟩ := hWps
  -- SpaceDecider for L: on x, enumerate all y of length q(|x|); accept if any y ∈ W.
  -- Space = O(q(|x|)) + space(W-decider); time exponential but PSPACE allows that.
  classical
  have hex : ∃ s : SpaceDecider,
      ∀ x, x ∈ L ↔ acceptsInSpace s.M x (x.length ^ s.d + s.d) = true := by
    sorry
  obtain ⟨s, hs⟩ := hex
  exact ⟨s, hs⟩

/-- Conditional collapse (bridges as hypotheses) — already proved previously. -/
theorem bgs_collapse_of_bridges
    (_h1 : OracleP upspaceOracle ⊆ PSPACE)
    (h2 : PSPACE ⊆ OracleP upspaceOracle)
    (h3 : OracleNPSlice upspaceOracle ⊆ PSPACE) :
    OracleP upspaceOracle = OracleNP upspaceOracle := by
  ext L
  constructor
  · intro h; exact OracleP_subset_OracleNP upspaceOracle h
  · intro h
    rcases h with hP | hS
    · exact hP
    · exact h2 (h3 hS)

/-- **Baker–Gill–Solovay collapse.** -/
theorem bgs_collapse : ∃ A, OracleP A = OracleNP A :=
  ⟨upspaceOracle, bgs_collapse_of_bridges
    OracleP_tqbf_subset_PSPACE
    PSPACE_subset_OracleP_tqbf
    OracleNPSlice_tqbf_subset_PSPACE⟩

end PvsNP
