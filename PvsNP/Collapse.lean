import PvsNP.Relativization

/-!
# Length-symmetry of slice-`OracleNP`

Under the slice definition of `OracleNP`, every language in the class is length-symmetric.
Together with the observation that ordinary `P` contains non-length-symmetric languages,
this explains why classical BGS *collapse* needs a richer `OracleNP` (see README).
-/

namespace PvsNP

/-- Membership depends only on length. -/
def LengthSymmetric (L : Language) : Prop :=
  ∀ x y : List Bool, x.length = y.length → (x ∈ L ↔ y ∈ L)

theorem OracleNP.lengthSymmetric {A : List Bool → Bool} {L : Language}
    (h : L ∈ OracleNP A) : LengthSymmetric L := by
  obtain ⟨q, hq⟩ := h
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

end PvsNP
