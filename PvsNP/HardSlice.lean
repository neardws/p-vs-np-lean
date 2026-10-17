import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import PvsNP.TagDecide

/-!
# Hard-slice oracle + kind-language membership

`hardSliceOracle` answers `tagEncode i x` by `QueryKind.eval upspaceOracle`.
`kindLang` / `upSliceLang` therefore lie in `OracleP hardSliceOracle`.

Closing verifier `bgs_collapse` still needs either a `SpaceDecider` for
`NP^{PSPACE} ⊆ PSPACE` or a length-WF pad-tag OTM (`satTagOTM`); see Collapse/README.
-/

namespace PvsNP

open Polynomial Function

noncomputable def encodeKind (κ : QueryKind) : ℕ :=
  Classical.choose (enumQueryKind_surjective κ)

theorem encodeKind_spec (κ : QueryKind) :
    enumQueryKind (encodeKind κ) = κ :=
  Classical.choose_spec (enumQueryKind_surjective κ)

noncomputable def hardSliceOracle : List Bool → Bool := fun w =>
  @decide (∃ i : ℕ, ∃ x : List Bool,
      w = tagEncode i x ∧ QueryKind.eval upspaceOracle (enumQueryKind i) x = true)
    (Classical.propDecidable _)

theorem hardSliceOracle_tagEncode (i : ℕ) (x : List Bool) :
    hardSliceOracle (tagEncode i x) = true ↔
      QueryKind.eval upspaceOracle (enumQueryKind i) x = true := by
  classical
  constructor
  · intro h
    obtain ⟨i', x', heq, hacc⟩ := of_decide_eq_true (by simpa [hardSliceOracle] using h)
    obtain ⟨rfl, rfl⟩ := tagEncode_injective heq
    exact hacc
  · intro h
    exact decide_eq_true ⟨i, x, rfl, h⟩

def kindLang (κ : QueryKind) : Language :=
  {x | QueryKind.eval upspaceOracle κ x = true}

theorem kindLang_mem_OracleP_hardSlice (κ : QueryKind) :
    kindLang κ ∈ OracleP hardSliceOracle := by
  refine ⟨encodeKind κ + 6, 3, tagQueryOTM (encodeKind κ),
    X + C (encodeKind κ + 4), ?_⟩
  intro x
  have hκ : enumQueryKind (encodeKind κ) = κ := encodeKind_spec κ
  have : ODecidesInTime (tagQueryOTM (encodeKind κ)) hardSliceOracle (kindLang κ)
      (fun n => encodeKind κ + n + 4) := by
    intro y
    have hy := tagQueryOTM_decides_oracle (encodeKind κ) hardSliceOracle y
    constructor
    · exact hy.1
    · constructor
      · intro hacc
        have htag : hardSliceOracle (tagEncode (encodeKind κ) y) = true := by
          simpa [Set.mem_ofPred_eq] using hy.2.1 hacc
        have : QueryKind.eval upspaceOracle κ y = true := by
          simpa [hκ] using (hardSliceOracle_tagEncode _ _).1 htag
        simpa [kindLang] using this
      · intro hyL
        have : QueryKind.eval upspaceOracle κ y = true := by simpa [kindLang] using hyL
        have htag : hardSliceOracle (tagEncode (encodeKind κ) y) = true :=
          (hardSliceOracle_tagEncode _ _).2 (by simpa [hκ] using this)
        exact hy.2.2 (by simpa [Set.mem_ofPred_eq] using htag)
  simpa [eval_add, eval_X, eval_C, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    using this x

def upSliceLang (j : ℕ) (q : ℕ[X]) : Language :=
  {x | QueryKind.eval upspaceOracle (.slice j q) x = true}

theorem upSliceLang_mem_OracleP_hardSlice (j : ℕ) (q : ℕ[X]) :
    upSliceLang j q ∈ OracleP hardSliceOracle := by
  simpa [upSliceLang, kindLang] using kindLang_mem_OracleP_hardSlice (.slice j q)

end PvsNP
