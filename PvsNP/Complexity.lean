import Mathlib.Algebra.Polynomial.Eval.Defs
import PvsNP.TuringMachine

/-!
# Polynomial time, P, NP, coNP and SAT

This file sits on top of `PvsNP.TuringMachine` and defines the classical (unrelativized)
complexity classes used in the statement of the P vs NP problem (`PvsNP.Main`).

* `DecidesInTime M L T` : on every input `x`, `M` halts within `T |x|` steps and accepts iff
  `x ∈ L`.
* `P` : languages decided by some finite-state, finite-alphabet machine in time bounded by a
  polynomial `p : ℕ[X]`.
* `NP` : verifier definition. `L ∈ NP` iff there are `V ∈ P` and a polynomial `q` with
  `x ∈ L ↔ ∃ y, |y| ≤ q(|x|) ∧ pair x y ∈ V`, where `pair` is a fixed injective,
  linear-size pairing of binary strings.
* `coNP` : complements of NP languages.
* `SAT` : binary encodings of satisfiable CNF formulas.
-/

namespace PvsNP

open Polynomial

/-- `M` decides `L` with running time bounded by `T`. -/
def DecidesInTime {Q Γ : Type} [DecidableEq Q] (M : TM Q Γ) (L : Language) (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool, M.haltsWithin x (T x.length) ∧ (M.acceptsAt x (T x.length) ↔ x ∈ L)

/-- Polynomial-time decidability. -/
def PolyTimeDecides {Q Γ : Type} [DecidableEq Q] (M : TM Q Γ) (L : Language) : Prop :=
  ∃ p : ℕ[X], DecidesInTime M L (fun n => p.eval n)

/-- The class **P**. Machines must have finitely many states and tape symbols. -/
def P : Set Language :=
  {L | ∃ (Q Γ : Type) (_ : Fintype Q) (_ : DecidableEq Q) (_ : Fintype Γ) (M : TM Q Γ),
    PolyTimeDecides M L}

/-- Self-delimiting pairing: each bit of `x` is doubled, then the separator `01`, then `y`. -/
def pair (x y : List Bool) : List Bool :=
  (x.flatMap fun b => [b, b]) ++ [false, true] ++ y

/-- The class **NP**, verifier definition. -/
def NP : Set Language :=
  {L | ∃ V ∈ P, ∃ q : ℕ[X], ∀ x, x ∈ L ↔ ∃ y : List Bool, y.length ≤ q.eval x.length ∧ pair x y ∈ V}

/-- The class **coNP**. -/
def coNP : Set Language := {L | Lᶜ ∈ NP}

/-! ## SAT -/

/-- A literal: variable index and polarity (`true` = positive). -/
abbrev Literal := ℕ × Bool
/-- A clause is a disjunction of literals. -/
abbrev Clause := List Literal
/-- A CNF formula is a conjunction of clauses. -/
abbrev CNF := List Clause

/-- Literal evaluation. -/
def Literal.eval (σ : ℕ → Bool) (l : Literal) : Bool := σ l.1 == l.2
/-- Clause evaluation. -/
def Clause.eval (σ : ℕ → Bool) (c : Clause) : Bool := c.any (Literal.eval σ)
/-- CNF evaluation. -/
def CNF.eval (σ : ℕ → Bool) (φ : CNF) : Bool := φ.all (Clause.eval σ)
/-- Satisfiability. -/
def CNF.Satisfiable (φ : CNF) : Prop := ∃ σ : ℕ → Bool, φ.eval σ = true

/-- Unary-free binary encoding of naturals: each bit doubled, terminated by `01`. -/
def encNat (n : ℕ) : List Bool := pair (Nat.bits n) []

/-- Encoding of a literal, clause and formula into binary strings. Separators use the pair
`10`, which cannot occur at an even position inside a doubled-bit block. -/
def encLit (l : Literal) : List Bool := encNat l.1 ++ [l.2, l.2]
def encClause (c : Clause) : List Bool := (c.flatMap encLit) ++ [true, false]
def encCNF (φ : CNF) : List Bool := (φ.flatMap encClause) ++ [true, false]

/-- The language **SAT**. -/
def SAT : Language := {w | ∃ φ : CNF, encCNF φ = w ∧ φ.Satisfiable}

/-- A basic sanity lemma: the empty formula is satisfiable, so `encCNF [] ∈ SAT`. -/
theorem encCNF_nil_mem_SAT : encCNF [] ∈ SAT :=
  ⟨[], rfl, ⟨fun _ => true, rfl⟩⟩

/-- A formula containing the empty clause is unsatisfiable. -/
theorem not_satisfiable_of_nil_mem {φ : CNF} (h : [] ∈ φ) : ¬ φ.Satisfiable := by
  rintro ⟨σ, hσ⟩
  simp only [CNF.eval, List.all_eq_true] at hσ
  simpa [Clause.eval] using hσ [] h

/-- coNP is exactly the set of complements of NP languages (definitional unfolding). -/
theorem mem_coNP_iff (L : Language) : L ∈ coNP ↔ Lᶜ ∈ NP := Iff.rfl

/-- **P ⊆ NP.** Pending: needs a TM that decodes `pair x y` and simulates the P-machine on `x`,
ignoring the certificate (or using an empty certificate with `q = 0`). -/
theorem P_subset_NP : P ⊆ NP := by
  sorry

end PvsNP
