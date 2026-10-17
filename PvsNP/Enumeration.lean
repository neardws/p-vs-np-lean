import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import Mathlib.Basic.Countable.Defs
import PvsNP.PolyBound
import PvsNP.Relativization

/-!
# Countable enumeration of oracle machines

Every language in `OracleP A` is decided by some machine in the enumeration `enumDecider`.
-/

namespace PvsNP

open Polynomial Function

/-- Flat encoding of an `OTM (Fin k) (Fin m)`. -/
abbrev OTMData (k m : ℕ) :=
  Fin k × Fin k × Fin k × Fin m × (Bool → Fin m) ×
  (Fin k → Fin m → Fin k × Fin m × Dir) ×
  Fin k × Fin k × Fin k × (Fin k → Fin m → Option Bool)

def OTM.ofData {k m : ℕ} (d : OTMData k m) : OTM (Fin k) (Fin m) where
  start := d.1
  accept := d.2.1
  reject := d.2.2.1
  blank := d.2.2.2.1
  inp := d.2.2.2.2.1
  δ := d.2.2.2.2.2.1
  ask := d.2.2.2.2.2.2.1
  yes := d.2.2.2.2.2.2.2.1
  no := d.2.2.2.2.2.2.2.2.1
  wr := d.2.2.2.2.2.2.2.2.2

def OTM.toData {k m : ℕ} (M : OTM (Fin k) (Fin m)) : OTMData k m :=
  (M.start, M.accept, M.reject, M.blank, M.inp, M.δ, M.ask, M.yes, M.no, M.wr)

def OTM.dataEquiv (k m : ℕ) : OTM (Fin k) (Fin m) ≃ OTMData k m where
  toFun := OTM.toData
  invFun := OTM.ofData
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

instance (k m : ℕ) : Fintype (OTM (Fin k) (Fin m)) :=
  Fintype.ofEquiv (OTMData k m) (OTM.dataEquiv k m).symm

instance (k m : ℕ) : Countable (OTM (Fin k) (Fin m)) := inferInstance

instance : Countable (AddMonoidAlgebra ℕ ℕ) :=
  Countable.of_equiv (ℕ →₀ ℕ) AddMonoidAlgebra.coeffAddEquiv.toEquiv.symm

instance : Countable ℕ[X] :=
  Countable.of_equiv (AddMonoidAlgebra ℕ ℕ) (toFinsuppIso ℕ).toEquiv.symm

/-- A poly-time oracle machine description. -/
structure OracleDecider where
  k : ℕ
  m : ℕ
  M : OTM (Fin k) (Fin m)
  p : ℕ[X]

instance : Countable OracleDecider := by
  let φ : OracleDecider ≃ (Σ k : ℕ, Σ m : ℕ, OTM (Fin k) (Fin m) × ℕ[X]) :=
  { toFun := fun d => ⟨d.k, d.m, (d.M, d.p)⟩
    invFun := fun ⟨k, m, Mp⟩ => ⟨k, m, Mp.1, Mp.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have : Countable (Σ k : ℕ, Σ m : ℕ, OTM (Fin k) (Fin m) × ℕ[X]) := inferInstance
  exact Countable.of_equiv _ φ.symm

instance : Nonempty OracleDecider :=
  ⟨{ k := 1, m := 1
     M := OTM.ofData (0, 0, 0, 0, fun _ => 0, fun _ _ => (0, 0, Dir.stay), 0, 0, 0, fun _ _ => none)
     p := 0 }⟩

/-- Surjective enumeration of all oracle deciders. -/
noncomputable def enumDecider : ℕ → OracleDecider :=
  Classical.choose (exists_surjective_nat OracleDecider)

theorem enumDecider_surjective : Surjective enumDecider :=
  Classical.choose_spec (exists_surjective_nat OracleDecider)

/-- Query tree of machine `i` on unary input `1ⁿ`. -/
noncomputable def enumTree (i n : ℕ) : QTree :=
  let d := enumDecider i
  d.M.unfold (d.p.eval n) (d.M.oinit (List.replicate n true))

theorem enumTree_depth_lt_two_pow (i : ℕ) :
    ∀ N, ∃ n ≥ N, (enumTree i n).depth < 2 ^ n := by
  intro N
  obtain ⟨n, hn, hlt⟩ := poly_lt_two_pow_infinitely_often (enumDecider i).p N
  refine ⟨n, hn, lt_of_le_of_lt ?_ hlt⟩
  exact OTM.unfold_depth _ _ _

/-- Every language in `OracleP A` is decided by some enumerated machine. -/
theorem OracleP.exists_enum {A : List Bool → Bool} {L : Language} (hL : L ∈ OracleP A) :
    ∃ i : ℕ, ODecidesInTime (enumDecider i).M A L (fun n => (enumDecider i).p.eval n) := by
  obtain ⟨k, m, M, p, hdec⟩ := hL
  obtain ⟨i, hi⟩ := enumDecider_surjective ⟨k, m, M, p⟩
  refine ⟨i, ?_⟩
  rw [hi]
  exact hdec

end PvsNP
