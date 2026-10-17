import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import PvsNP.Enumeration
import PvsNP.OracleVerifiers

/-!
# Baker–Gill–Solovay separation

Under `OracleNP = OracleP ∪ OracleNPRawSlice`, the classical test language sits in
`OracleNPRawSlice` and the existing diagonalization shows it lies outside `OracleP`.
-/

namespace PvsNP

open Polynomial Function

def unary (n : ℕ) : List Bool := List.replicate n true
@[simp] theorem unary_length (n : ℕ) : (unary n).length = n := List.length_replicate

/-- The BGS test language is the raw slice with `q = X`. -/
theorem testLang_mem_OracleNPRawSlice (B : List Bool → Bool) :
    testLang B ∈ OracleNPRawSlice B := by
  refine ⟨X, ?_⟩
  intro x
  simp [testLang, eval_X]

/-- Still in the stronger slice form via `queryLang ∈ OracleP`. -/
theorem testLang_mem_OracleNPSlice (B : List Bool → Bool) :
    testLang B ∈ OracleNPSlice B := by
  refine ⟨queryLang B, queryLang_mem_OracleP B, X, ?_⟩
  intro x
  simp [testLang, queryLang, eval_X]

theorem testLang_mem_OracleNP (B : List Bool → Bool) :
    testLang B ∈ OracleNP B :=
  Or.inr (testLang_mem_OracleNPRawSlice B)

theorem unfold_decides_testLang {k m : ℕ} {M : OTM (Fin k) (Fin m)}
    {B : List Bool → Bool} {p : ℕ[X]}
    (hdec : ODecidesInTime M B (testLang B) (fun n => p.eval n)) (n : ℕ) :
    (M.unfold (p.eval n) (M.oinit (unary n))).eval B = true ↔
      ∃ y : List Bool, y.length = n ∧ B y = true := by
  have h := hdec (unary n)
  simp only [unary_length] at h
  have heval := OTM.unfold_eval M B (p.eval n) (M.oinit (unary n))
  constructor
  · intro heq
    rw [heval, decide_eq_true_eq] at heq
    exact by simpa [testLang, unary_length] using (h.2.1 heq)
  · intro hy
    have hin : unary n ∈ testLang B := by simpa [testLang, unary_length] using hy
    rw [heval, decide_eq_true_eq]
    exact h.2.2 hin

noncomputable def bgsOracle : List Bool → Bool :=
  Classical.choose (exists_oracle_diag enumTree enumTree_depth_lt_two_pow)

theorem bgsOracle_spec :
    ∀ i, ∃ n, ((enumTree i n).eval bgsOracle = true ↔
      ¬ ∃ y : List Bool, y.length = n ∧ bgsOracle y = true) :=
  Classical.choose_spec (exists_oracle_diag enumTree enumTree_depth_lt_two_pow)

theorem testLang_not_mem_OracleP_bgs : testLang bgsOracle ∉ OracleP bgsOracle := by
  intro hmem
  obtain ⟨i, hdec⟩ := OracleP.exists_enum hmem
  obtain ⟨n, hn⟩ := bgsOracle_spec i
  change ((enumDecider i).M.unfold ((enumDecider i).p.eval n)
      ((enumDecider i).M.oinit (unary n))).eval bgsOracle = true ↔
      ¬ ∃ y : List Bool, y.length = n ∧ bgsOracle y = true at hn
  have hiff := unfold_decides_testLang hdec n
  by_cases h : ∃ y : List Bool, y.length = n ∧ bgsOracle y = true
  · exact (hn.1 (hiff.2 h)) h
  · exact (fun ht => h (hiff.1 ht)) (hn.2 h)

/-- **Baker–Gill–Solovay (1975), separation.** -/
theorem bgs_separation : ∃ B, OracleP B ≠ OracleNP B := by
  refine ⟨bgsOracle, fun hEq => ?_⟩
  have hin : testLang bgsOracle ∈ OracleNP bgsOracle := testLang_mem_OracleNP _
  rw [← hEq] at hin
  exact testLang_not_mem_OracleP_bgs hin

/-- Relativized `P ⊆ NP`: `OracleP A ⊆ OracleNP A` by construction of the union. -/
theorem OracleP_subset_OracleNP (A : List Bool → Bool) : OracleP A ⊆ OracleNP A :=
  fun _ h => Or.inl h

end PvsNP
