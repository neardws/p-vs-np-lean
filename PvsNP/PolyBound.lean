import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# Polynomials grow slower than exponentials

Every polynomial `p : ℕ[X]` satisfies `p(n) < 2ⁿ` for infinitely many `n`.
-/

namespace PvsNP

open Polynomial Filter Topology

/-- `c · n^d < 2^n` for all sufficiently large `n`. -/
theorem exists_forall_mul_pow_lt_two_pow (c d : ℕ) :
    ∃ N, ∀ n ≥ N, c * n ^ d < 2 ^ n := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt d (r := (2 : ℝ)) (by norm_num)
  have hc : Tendsto (fun n : ℕ => (c : ℝ) * ((n : ℝ) ^ d / (2 : ℝ) ^ n)) atTop (nhds 0) := by
    simpa using h.const_mul (c : ℝ)
  rw [Metric.tendsto_atTop] at hc
  obtain ⟨N, hN⟩ := hc 1 (by norm_num)
  refine ⟨N, fun n hn => ?_⟩
  have habs : dist ((c : ℝ) * ((n : ℝ) ^ d / (2 : ℝ) ^ n)) 0 < 1 := hN n hn
  rw [Real.dist_eq, sub_zero] at habs
  have hnonneg : (0 : ℝ) ≤ (c : ℝ) * ((n : ℝ) ^ d / (2 : ℝ) ^ n) := by positivity
  have hre : (c : ℝ) * ((n : ℝ) ^ d / (2 : ℝ) ^ n) < 1 := by rwa [abs_of_nonneg hnonneg] at habs
  have hpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have : (c : ℝ) * (n : ℝ) ^ d < (2 : ℝ) ^ n := by
    rw [← div_lt_one hpos]; convert hre using 1; ring
  exact_mod_cast this

/-- `p.eval n ≤ (∑ coeffs) · n^{deg}` for `n ≥ 1`. -/
lemma eval_le_sum_mul_pow (p : ℕ[X]) {n : ℕ} (hn : 1 ≤ n) :
    p.eval n ≤ p.sum (fun _ a => a) * n ^ p.natDegree := by
  classical
  rw [eval_eq_sum, Polynomial.sum_def, Polynomial.sum_def]
  calc ∑ e ∈ p.support, p.coeff e * n ^ e
      ≤ ∑ e ∈ p.support, p.coeff e * n ^ p.natDegree := by
        apply Finset.sum_le_sum; intro e he
        exact Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right hn (Polynomial.le_natDegree_of_mem_supp e he))
    _ = (∑ e ∈ p.support, p.coeff e) * n ^ p.natDegree := by rw [← Finset.sum_mul]
    _ = p.sum (fun _ a => a) * n ^ p.natDegree := by simp [Polynomial.sum_def]

/-- Every polynomial `p : ℕ[X]` satisfies `p(n) < 2ⁿ` for infinitely many `n`. -/
theorem poly_lt_two_pow_infinitely_often (p : ℕ[X]) :
    ∀ N, ∃ n ≥ N, p.eval n < 2 ^ n := by
  classical
  intro N
  let c := p.sum fun _ a => a
  let d := p.natDegree
  obtain ⟨M, hM⟩ := exists_forall_mul_pow_lt_two_pow c d
  refine ⟨max (max N M) 1, ?_, ?_⟩
  · omega
  · exact lt_of_le_of_lt (eval_le_sum_mul_pow p (by omega)) (hM _ (by omega))

end PvsNP
