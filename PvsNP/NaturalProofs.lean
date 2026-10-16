import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import PvsNP.Complexity

/-!
# Natural proofs (Razborov–Rudich 1997)

This file is the natural-proofs-barrier layer of the project. It defines Boolean circuits,
`P/poly`, combinatorial properties of Boolean functions and the three Razborov–Rudich
conditions, and states the barrier theorem.

* A **combinatorial property** `C` is a family `C n ⊆ {f : {0,1}ⁿ → {0,1}}`.
* **Constructivity**: membership `f ∈ C n` is decidable in time polynomial in the truth-table
  length `2ⁿ`, i.e. the language of truth tables of members is in `P`.
* **Largeness**: `|C n| ≥ 2^{-c n} · 2^{2ⁿ}` for some `c` and all large `n`.
* **Usefulness against P/poly**: every sequence `f` with `f n ∈ C n` for infinitely many `n`
  is not in `P/poly`.
* The **barrier theorem** (natural + useful against P/poly ⇒ no secure PRFs) is recorded as the
  proposition `RazborovRudichStatement`, parameterised by the still-undefined notion of PRF
  security; its proof is pending.
-/

namespace PvsNP.Natural

/-- Boolean functions on `n` bits. -/
abbrev BoolFn (n : ℕ) := (Fin n → Bool) → Bool

/-- De Morgan circuits (formulas with sharing omitted; size counts gates). -/
inductive Circuit (n : ℕ)
  | var (i : Fin n)
  | const (b : Bool)
  | not (c : Circuit n)
  | and (c d : Circuit n)
  | or (c d : Circuit n)

namespace Circuit
/-- Evaluation. -/
def eval {n : ℕ} : Circuit n → BoolFn n
  | var i, x => x i
  | const b, _ => b
  | not c, x => !(c.eval x)
  | and c d, x => c.eval x && d.eval x
  | or c d, x => c.eval x || d.eval x
/-- Size = number of nodes. -/
def size {n : ℕ} : Circuit n → ℕ
  | var _ => 1
  | const _ => 1
  | not c => c.size + 1
  | and c d => c.size + d.size + 1
  | or c d => c.size + d.size + 1
end Circuit

/-- `f n` has a circuit of size at most `s`. -/
def HasCircuitOfSize {n : ℕ} (f : BoolFn n) (s : ℕ) : Prop :=
  ∃ c : Circuit n, c.size ≤ s ∧ c.eval = f

/-- A family of Boolean functions, one for each input length. -/
abbrev BoolSeq := (n : ℕ) → BoolFn n

/-- `P/poly` (circuit-size version): some polynomial bound works for all `n`. -/
def PPoly : Set BoolSeq := {f | ∃ k : ℕ, ∀ n, HasCircuitOfSize (f n) (n ^ k + k)}

/-- A combinatorial property of Boolean functions. -/
abbrev Property := (n : ℕ) → Set (BoolFn n)

/-- Truth table of `f` as a binary string of length `2ⁿ` (lexicographic order on inputs). -/
noncomputable def truthTable {n : ℕ} (f : BoolFn n) : List Bool :=
  (List.finRange (2 ^ n)).map fun j => f (fun i => Nat.testBit j.val i.val)

/-- **Constructivity**: membership is in `P` as a function of the truth table. -/
def Constructive (C : Property) : Prop :=
  ∃ L ∈ P, ∀ n (f : BoolFn n), truthTable f ∈ L ↔ f ∈ C n

open Classical in
/-- **Largeness**: `|C n| · 2^{c n} ≥ 2^{2ⁿ}` for all large `n`. -/
def Large (C : Property) : Prop :=
  ∃ c n₀ : ℕ, ∀ n ≥ n₀, 2 ^ (2 ^ n) ≤ (Finset.univ.filter (· ∈ C n)).card * 2 ^ (c * n)

/-- **Usefulness against P/poly**. -/
def UsefulAgainstPPoly (C : Property) : Prop :=
  ∀ f : BoolSeq, (∀ N, ∃ n ≥ N, f n ∈ C n) → f ∉ PPoly

/-- A natural property useful against P/poly. -/
def NaturalAgainstPPoly (C : Property) : Prop :=
  Constructive C ∧ Large C ∧ UsefulAgainstPPoly C

/-- The *shape* of the Razborov–Rudich barrier theorem, parameterised by the proposition
`PRFsExist` ("pseudorandom function families secure against P/poly adversaries exist").
A concrete definition of `PRFsExist` (keyed families computable in polynomial time,
indistinguishability by polynomial-size oracle circuits with advantage `≥ 1/poly`) and the proof
of `RazborovRudichStatement PRFsExist` for it are **pending**. We deliberately do not state the
theorem for an arbitrary `Prop`, since that would be false. -/
def RazborovRudichStatement (PRFsExist : Prop) : Prop :=
  ∀ C : Property, NaturalAgainstPPoly C → ¬ PRFsExist

/-! ## Proved basic lemmas -/

/-- Largeness is monotone. -/
theorem Large.mono {C D : Property} (h : ∀ n, C n ⊆ D n) (hC : Large C) : Large D := by
  classical
  obtain ⟨c, n₀, hc⟩ := hC
  refine ⟨c, n₀, fun n hn => le_trans (hc n hn) ?_⟩
  apply Nat.mul_le_mul_right
  apply Finset.card_le_card
  intro f; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact fun hf => h n hf

/-- The trivial property (all functions) is large. -/
theorem large_univ : Large (fun _ => Set.univ) := by
  classical
  refine ⟨0, 0, fun n _ => ?_⟩
  simp [Fintype.card_bool, Fintype.card_fin]

/-- Usefulness is antitone: a sub-property of a useful property is useful. -/
theorem UsefulAgainstPPoly.anti {C D : Property} (h : ∀ n, C n ⊆ D n)
    (hD : UsefulAgainstPPoly D) : UsefulAgainstPPoly C := by
  intro f hf
  apply hD f
  intro N; obtain ⟨n, hn, hfn⟩ := hf N; exact ⟨n, hn, h n hfn⟩

/-- A useful property cannot contain the constant-false function at infinitely many lengths
(constant functions have size-1 circuits). -/
theorem UsefulAgainstPPoly.not_const {C : Property} (hC : UsefulAgainstPPoly C) :
    ¬ ∀ N, ∃ n ≥ N, (fun _ => false) ∈ C n := by
  intro h
  apply hC (fun _ _ => false) h
  refine ⟨1, fun n => ⟨.const false, ?_, rfl⟩⟩
  simp [Circuit.size]

/-- The trivial property is not useful against P/poly. -/
theorem not_useful_univ : ¬ UsefulAgainstPPoly (fun _ => Set.univ) := fun h =>
  h.not_const (fun N => ⟨N, le_refl _, Set.mem_univ _⟩)

end PvsNP.Natural
