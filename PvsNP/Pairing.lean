import PvsNP.Complexity

/-!
# Pairing lemmas

`pair x y = doubled x ++ [false, true] ++ y` where each bit of `x` is duplicated.
-/

namespace PvsNP

/-- The doubled encoding of `x`. -/
def doubled (x : List Bool) : List Bool :=
  x.flatMap fun b => [b, b]

theorem doubled_length (x : List Bool) : (doubled x).length = 2 * x.length := by
  induction x with
  | nil => rfl
  | cons b bs ih =>
    simp only [doubled, List.flatMap_cons, List.length_append, List.length_cons, List.length_nil]
    change 1 + 1 + (doubled bs).length = 2 * (bs.length + 1)
    rw [ih]; ring

theorem pair_eq (x y : List Bool) :
    pair x y = doubled x ++ [false, true] ++ y := rfl

theorem pair_length (x y : List Bool) :
    (pair x y).length = 2 * x.length + 2 + y.length := by
  simp [pair_eq, doubled_length, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem pair_append_y (x y : List Bool) :
    pair x y = (doubled x ++ [false, true]) ++ y := by
  rw [pair_eq, List.append_assoc]

theorem doubled_cons (b : Bool) (bs : List Bool) :
    doubled (b :: bs) = [b, b] ++ doubled bs := by
  simp [doubled]

/-- `pair` is injective. -/
theorem pair_injective {x y x' y' : List Bool} (h : pair x y = pair x' y') :
    x = x' ∧ y = y' := by
  induction x generalizing x' with
  | nil =>
    cases x' with
    | nil =>
      simp [pair_eq, doubled] at h
      exact ⟨rfl, h⟩
    | cons b bs =>
      cases b <;> simp [pair_eq, doubled] at h
  | cons b bs ih =>
    cases x' with
    | nil =>
      cases b <;> simp [pair_eq, doubled] at h
    | cons b' bs' =>
      have hb : b = b' := by
        cases b <;> cases b' <;> simp [pair_eq, doubled_cons] at h <;> simp_all
      subst b'
      have h2 : pair bs y = pair bs' y' := by
        cases b <;> simp [pair_eq, doubled_cons] at h ⊢ <;> exact h
      obtain ⟨hs, hy⟩ := ih h2
      exact ⟨congrArg (b :: ·) hs, hy⟩

end PvsNP
