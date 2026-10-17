import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import PvsNP.OracleVerifiers
import PvsNP.Verifier

/-!
# Collapse scaffolding: toward `∃ A, P^A = NP^A`

Classical route: take a PSPACE-complete oracle `A` (TQBF). Then `P^A = NP^A = PSPACE`.

Under `OracleNP A = OracleP A ∪ OracleNPSlice A`, collapse ⇔ `OracleNPSlice A ⊆ OracleP A`.
-/

namespace PvsNP

open Polynomial

/-- Membership depends only on length. -/
def LengthSymmetric (L : Language) : Prop :=
  ∀ x y : List Bool, x.length = y.length → (x ∈ L ↔ y ∈ L)

theorem OracleNPSlice.lengthSymmetric {A : List Bool → Bool} {L : Language}
    (h : L ∈ OracleNPSlice A) : LengthSymmetric L := by
  obtain ⟨W, _, q, hq⟩ := h
  intro x y hlen
  constructor
  · intro hx
    exact (hq y).2 (by simpa [hlen] using (hq x).1 hx)
  · intro hy
    exact (hq x).2 (by simpa [hlen] using (hq y).1 hy)

theorem not_lengthSymmetric_singleton_false :
    ¬ LengthSymmetric ({[false]} : Language) := by
  intro h
  have := (h [false] [true] (by rfl)).mp rfl
  simp at this

/-- Cells touched by a configuration (left + head + right). -/
def Cfg.space {Q Γ : Type} (c : Cfg Q Γ) : ℕ :=
  c.left.length + 1 + c.right.length

/-- `M` decides `L` using at most `S(|x|)` tape cells on every input. -/
def SpaceDecides {Q Γ : Type} [DecidableEq Q] (M : TM Q Γ) (L : Language) (S : ℕ → ℕ) : Prop :=
  ∃ T : ℕ → ℕ, DecidesInTime M L T ∧
    ∀ x t, t ≤ T x.length → (M.run t (M.init x)).space ≤ S x.length

/-- The class **PSPACE**. -/
def PSPACE : Set Language :=
  {L | ∃ (Q Γ : Type) (_ : Fintype Q) (_ : DecidableEq Q) (_ : Fintype Γ) (M : TM Q Γ) (k : ℕ),
    SpaceDecides M L (fun n => n ^ k + k)}

/-- Stand-in shape for a PSPACE-complete language. Real TQBF needs quantifier alternation;
the encoding/completeness proof is **pending**. -/
def TQBF : Language := SAT

/-- Characteristic function of `TQBF`. -/
noncomputable def tqbfOracle : List Bool → Bool :=
  fun w => @decide (w ∈ TQBF) (Classical.propDecidable _)

/-- **Pending.** Poly-time oracle machines with a PSPACE oracle are in PSPACE. -/
theorem OracleP_tqbf_subset_PSPACE : OracleP tqbfOracle ⊆ PSPACE := by
  sorry

/-- **Pending.** PSPACE-completeness of TQBF ⇒ `PSPACE ⊆ P^{TQBF}`. -/
theorem PSPACE_subset_OracleP_tqbf : PSPACE ⊆ OracleP tqbfOracle := by
  sorry

/-- **Pending.** Slice-NP over a PSPACE oracle is in PSPACE (NPSPACE = PSPACE). -/
theorem OracleNPSlice_tqbf_subset_PSPACE : OracleNPSlice tqbfOracle ⊆ PSPACE := by
  sorry

/-- Collapse once the three PSPACE bridge lemmas are proved. -/
theorem bgs_collapse_of_bridges
    (_h1 : OracleP tqbfOracle ⊆ PSPACE)
    (h2 : PSPACE ⊆ OracleP tqbfOracle)
    (h3 : OracleNPSlice tqbfOracle ⊆ PSPACE) :
    OracleP tqbfOracle = OracleNP tqbfOracle := by
  ext L
  constructor
  · intro h; exact OracleP_subset_OracleNP tqbfOracle h
  · intro h
    rcases h with hP | hS
    · exact hP
    · exact h2 (h3 hS)

end PvsNP
