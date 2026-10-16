import Mathlib.Data.Fintype.Card
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Fintype.BigOperators

/-!
# The combinatorial core of the Baker–Gill–Solovay oracle separation

This file is part of the relativization layer (`PvsNP.Relativization`). It proves, with no
`sorry`, the counting/diagonalization heart of the theorem "∃ B, P^B ≠ NP^B".

The model is the **query (decision-tree) model**: a deterministic oracle computation on a fixed
input is a finite tree `QTree` whose internal nodes ask the oracle about a string and branch on
the answer. Any oracle Turing machine running `t` steps on an input unfolds to such a tree of
depth `≤ t` whose queried strings have length `≤ t`; that unfolding lemma is the (pending)
bridge to the Turing-machine level (see README).

Main theorem `exists_oracle_diag`: for *any countable family* `M i n` of query trees (machine
`i` on input `1ⁿ`) such that each machine has, infinitely often, fewer than `2ⁿ` queries, there is
an oracle `B` such that no machine decides the unary test language
`L_B = {1ⁿ | ∃ y ∈ B, |y| = n}` — a language that is trivially in `NP^B`.
-/

namespace PvsNP

/-- An adaptive oracle query tree. -/
inductive QTree
  | ret (b : Bool)
  | ask (y : List Bool) (k : Bool → QTree)

namespace QTree

/-- Evaluate against an oracle. -/
def eval : QTree → (List Bool → Bool) → Bool
  | ret b, _ => b
  | ask y k, O => eval (k (O y)) O

/-- Strings actually queried on the path followed with oracle `O`. -/
def asked : QTree → (List Bool → Bool) → List (List Bool)
  | ret _, _ => []
  | ask y k, O => y :: asked (k (O y)) O

/-- Depth (worst-case number of queries). -/
def depth : QTree → ℕ
  | ret _ => 0
  | ask _ k => max (depth (k false)) (depth (k true)) + 1

/-- Maximum length of any string queried anywhere in the tree. -/
def maxLen : QTree → ℕ
  | ret _ => 0
  | ask y k => max y.length (max (maxLen (k false)) (maxLen (k true)))

theorem eval_congr (t : QTree) (O O' : List Bool → Bool) (h : ∀ y ∈ t.asked O, O y = O' y) :
    t.eval O = t.eval O' := by
  induction t with
  | ret b => rfl
  | ask y k ih =>
    simp only [asked, List.mem_cons] at h
    simp only [eval]
    rw [← h y (Or.inl rfl)]
    exact ih _ (fun z hz => h z (Or.inr hz))

theorem length_asked_le (t : QTree) (O : List Bool → Bool) : (t.asked O).length ≤ t.depth := by
  induction t with
  | ret b => simp [asked, depth]
  | ask y k ih =>
    simp only [asked, depth, List.length_cons]
    have := ih (O y)
    have hb : ∀ b, (k b).depth ≤ max (k false).depth (k true).depth := by
      intro b; cases b <;> simp
    have := hb (O y)
    omega

theorem length_le_maxLen (t : QTree) (O : List Bool → Bool) :
    ∀ y ∈ t.asked O, y.length ≤ t.maxLen := by
  induction t with
  | ret b => simp [asked]
  | ask y k ih =>
    intro z hz
    simp only [asked, List.mem_cons] at hz
    simp only [maxLen]
    rcases hz with rfl | hz
    · omega
    · have := ih (O y) z hz
      have hb : ∀ b, (k b).maxLen ≤ max (k false).maxLen (k true).maxLen := by
        intro b; cases b <;> simp
      have := hb (O y)
      omega

end QTree

/-- If fewer than `2ⁿ` strings are listed, some string of length `n` is missing. -/
theorem exists_length_not_mem (n : ℕ) (l : List (List Bool)) (hl : l.length < 2 ^ n) :
    ∃ y : List Bool, y.length = n ∧ y ∉ l := by
  by_contra hcon
  push Not at hcon
  have hinj : Set.InjOn (fun v : List.Vector Bool n => v.toList)
      (Finset.univ : Finset (List.Vector Bool n)) := by
    intro a _ b _ h; exact List.Vector.eq a b h
  have hmaps : ∀ v ∈ (Finset.univ : Finset (List.Vector Bool n)), v.toList ∈ l.toFinset := by
    intro v _; simpa using hcon v.toList v.toList_length
  have := Finset.card_le_card_of_injOn _ hmaps hinj
  simp only [Finset.card_univ, card_vector, Fintype.card_bool] at this
  have h2 := List.toFinset_card_le l
  omega

/-- The diagonalization state after a stage: a finite set of strings put into the oracle and a
length bound `N` below which the oracle is frozen. -/
structure DiagState where
  S : List (List Bool)
  N : ℕ

section Diag

variable (M : ℕ → ℕ → QTree) (hM : ∀ i N, ∃ n ≥ N, (M i n).depth < 2 ^ n)

/-- Oracle given by a finite list of strings. -/
noncomputable def listOracle (S : List (List Bool)) : List Bool → Bool :=
  fun y => @decide (y ∈ S) (Classical.propDecidable _)

/-- The input length chosen at stage `i`. -/
noncomputable def stageN (i : ℕ) (s : DiagState) : ℕ := Classical.choose (hM i s.N)

theorem stageN_ge (i : ℕ) (s : DiagState) : s.N ≤ stageN M hM i s :=
  (Classical.choose_spec (hM i s.N)).1

theorem stageN_depth (i : ℕ) (s : DiagState) :
    (M i (stageN M hM i s)).depth < 2 ^ stageN M hM i s :=
  (Classical.choose_spec (hM i s.N)).2

/-- A fresh string of the chosen length, not queried by machine `i`. -/
noncomputable def stageY (i : ℕ) (s : DiagState) : List Bool :=
  Classical.choose (exists_length_not_mem (stageN M hM i s)
    ((M i (stageN M hM i s)).asked (listOracle s.S))
    (lt_of_le_of_lt (QTree.length_asked_le _ _) (stageN_depth M hM i s)))

theorem stageY_spec (i : ℕ) (s : DiagState) :
    (stageY M hM i s).length = stageN M hM i s ∧
      stageY M hM i s ∉ (M i (stageN M hM i s)).asked (listOracle s.S) :=
  Classical.choose_spec (exists_length_not_mem (stageN M hM i s)
    ((M i (stageN M hM i s)).asked (listOracle s.S))
    (lt_of_le_of_lt (QTree.length_asked_le _ _) (stageN_depth M hM i s)))

/-- One stage of the construction for machine `i`. -/
noncomputable def diagStep (i : ℕ) (s : DiagState) : DiagState :=
  { S := if (M i (stageN M hM i s)).eval (listOracle s.S) then s.S else stageY M hM i s :: s.S
    N := max (stageN M hM i s + 1) ((M i (stageN M hM i s)).maxLen + 1) }

/-- The state after stages `0, …, k-1`. -/
noncomputable def diagState : ℕ → DiagState
  | 0 => ⟨[], 0⟩
  | k + 1 => diagStep M hM k (diagState k)

/-- The diagonal oracle. -/
noncomputable def diagOracle : List Bool → Bool :=
  fun y => @decide (∃ k, y ∈ (diagState M hM k).S) (Classical.propDecidable _)

theorem diagState_N_le (k : ℕ) : (diagState M hM k).N ≤ (diagState M hM (k+1)).N := by
  have := stageN_ge M hM k (diagState M hM k)
  simp only [diagState, diagStep]
  omega

theorem diagState_N_mono {j k : ℕ} (h : j ≤ k) : (diagState M hM j).N ≤ (diagState M hM k).N := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (diagState_N_le M hM _)

theorem mem_diagStep {i : ℕ} {s : DiagState} {y : List Bool} (h : y ∈ (diagStep M hM i s).S) :
    y ∈ s.S ∨ y = stageY M hM i s := by
  simp only [diagStep] at h
  split_ifs at h
  · exact Or.inl h
  · rcases List.mem_cons.mp h with h | h
    · exact Or.inr h
    · exact Or.inl h

/-- Invariant: all strings in stage `k` are shorter than `N_k`. -/
theorem diagState_len (k : ℕ) : ∀ y ∈ (diagState M hM k).S, y.length < (diagState M hM k).N := by
  induction k with
  | zero => simp [diagState]
  | succ k ih =>
    intro y hy
    have h1 := stageN_ge M hM k (diagState M hM k)
    have h2 := (stageY_spec M hM k (diagState M hM k)).1
    have hN : (diagState M hM (k+1)).N = max (stageN M hM k (diagState M hM k) + 1)
        ((M k (stageN M hM k (diagState M hM k))).maxLen + 1) := rfl
    rcases mem_diagStep M hM hy with hy | rfl
    · have := ih y hy; omega
    · omega

/-- Stages only grow. -/
theorem diagState_sub (k : ℕ) : ∀ y ∈ (diagState M hM k).S, y ∈ (diagState M hM (k+1)).S := by
  intro y hy
  show y ∈ (diagStep M hM k (diagState M hM k)).S
  simp only [diagStep]
  split_ifs <;> simp [hy]

/-- Short strings of a later stage were already present. -/
theorem diagState_frozen {j k : ℕ} (h : j ≤ k) :
    ∀ y ∈ (diagState M hM k).S, y.length < (diagState M hM j).N → y ∈ (diagState M hM j).S := by
  induction h with
  | refl => exact fun y hy _ => hy
  | @step k hjk ih =>
    intro y hy hlen
    apply ih y _ hlen
    rcases mem_diagStep M hM hy with hy | rfl
    · exact hy
    · exfalso
      have h1 := stageN_ge M hM k (diagState M hM k)
      have h2 := (stageY_spec M hM k (diagState M hM k)).1
      have := diagState_N_mono M hM hjk
      omega

theorem diagState_mono {j k : ℕ} (h : j ≤ k) :
    ∀ y ∈ (diagState M hM j).S, y ∈ (diagState M hM k).S := by
  induction h with
  | refl => exact fun y hy => hy
  | step _ ih => exact fun y hy => diagState_sub M hM _ y (ih y hy)

/-- The diagonal oracle agrees with stage `k` on strings shorter than `N_k`. -/
theorem diagOracle_eq (k : ℕ) (y : List Bool) (hy : y.length < (diagState M hM k).N) :
    diagOracle M hM y = listOracle (diagState M hM k).S y := by
  simp only [diagOracle, listOracle]
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨k', hk'⟩
    rcases le_total k k' with h | h
    · exact diagState_frozen M hM h y hk' hy
    · exact diagState_mono M hM h y hk'
  · exact fun h => ⟨k, h⟩

end Diag

/-- **Diagonalization theorem (query model).** For every countable family of query trees in
which each machine infinitely often makes fewer than `2ⁿ` queries, there is an oracle `B` such
that every machine `i` errs on some input `1ⁿ` for `L_B = {1ⁿ | ∃ y, |y| = n ∧ B y}`. -/
theorem exists_oracle_diag (M : ℕ → ℕ → QTree) (hM : ∀ i N, ∃ n ≥ N, (M i n).depth < 2 ^ n) :
    ∃ B : List Bool → Bool, ∀ i, ∃ n,
      ((M i n).eval B = true ↔ ¬ ∃ y : List Bool, y.length = n ∧ B y = true) := by
  refine ⟨diagOracle M hM, fun i => ?_⟩
  set s := diagState M hM i with hs
  set n := stageN M hM i s with hn_def
  have hy0s := stageY_spec M hM i s
  have hnge := stageN_ge M hM i s
  set O := listOracle s.S with hO
  refine ⟨n, ?_⟩
  have hN1 : (diagState M hM (i+1)).N = max (n + 1) ((M i n).maxLen + 1) := rfl
  have hS1 : (diagState M hM (i+1)).S = if (M i n).eval O then s.S else (stageY M hM i s) :: s.S := rfl
  have hagree : ∀ y : List Bool, y.length < max (n + 1) ((M i n).maxLen + 1) →
      diagOracle M hM y = listOracle (diagState M hM (i+1)).S y := by
    intro y hy; exact diagOracle_eq M hM (i+1) y (hN1 ▸ hy)
  have hnoS : ∀ y ∈ s.S, y.length ≠ n := by
    intro y hy; have := diagState_len M hM i y hy; change y.length < s.N at this; omega
  have heval : (M i n).eval (diagOracle M hM) = (M i n).eval O := by
    symm
    apply QTree.eval_congr
    intro y hy
    have hl := QTree.length_le_maxLen _ _ y hy
    rw [hagree y (by omega), hS1]
    split_ifs
    · rfl
    · have hne : y ≠ (stageY M hM i s) := fun h => hy0s.2 (by rw [← h]; exact hy)
      simp [hO, listOracle, hne]
  rw [heval]
  by_cases he : (M i n).eval O = true
  · simp only [he, true_iff]
    rintro ⟨y, hyl, hyB⟩
    rw [hagree y (by omega), hS1, if_pos he] at hyB
    exact hnoS y (by simpa [listOracle] using hyB) hyl
  · have he' : (M i n).eval O = false := by simpa using he
    rw [he']
    simp only [Bool.false_eq_true, false_iff, not_not]
    refine ⟨(stageY M hM i s), hy0s.1, ?_⟩
    rw [hagree (stageY M hM i s) (by omega), hS1, if_neg he]
    simp [listOracle]
