import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import PvsNP.SpaceSim

/-!
# Decision theorem for `tagQueryOTM`

Tag-writing phase (`tagWriting_orun`) is complete. Separator bits, copy loop, and ask
remain (same pattern as `queryCfg_step` / `queryOTM_decides`).
-/

namespace PvsNP

open Polynomial

def InputAtStart (i : ℕ) (x : List Bool) (c : Cfg (Fin (i + 6)) Γ₃) : Prop :=
  c.left = [] ∧
  ((x = [] ∧ c.head = 0 ∧ c.right = []) ∨
    (∃ r rs, x = r :: rs ∧ c.head = encBit r ∧ c.right = rs.map encBit))

theorem inputAtStart_oinit (i : ℕ) (x : List Bool) :
    InputAtStart i x ((tagQueryOTM i).oinit x).cfg := by
  cases x with
  | nil => simp [InputAtStart, OTM.oinit, TM.init, tagQueryOTM]
  | cons r rs => simp [InputAtStart, OTM.oinit, TM.init, tagQueryOTM]

def TagWriting (i t : ℕ) (x : List Bool) (c : OCfg (Fin (i + 6)) Γ₃) : Prop :=
  c.cfg.state.val = t ∧
  c.buf = List.replicate t true ∧
  InputAtStart i x c.cfg

theorem tagWriting_zero (i : ℕ) (x : List Bool) :
    TagWriting i 0 x ((tagQueryOTM i).oinit x) := by
  refine ⟨?_, rfl, inputAtStart_oinit i x⟩
  cases x <;> rfl

theorem replicate_concat_true (t : ℕ) :
    List.replicate t true ++ [true] = List.replicate (t + 1) true := by
  induction t with
  | zero => rfl
  | succ t ih => simp [List.replicate, ih]

theorem not_halted_of_val_lt {i : ℕ} {c : OCfg (Fin (i + 6)) Γ₃}
    (h : c.cfg.state.val < i + 4) :
    ¬ (tagQueryOTM i).toTM.halted c.cfg := by
  intro hh
  simp only [TM.halted, tagQueryOTM] at hh
  rcases hh with hv | hv
  · have := congrArg Fin.val hv; simp at this; omega
  · have := congrArg Fin.val hv; simp at this; omega

theorem tagWriting_step (i t : ℕ) (ht : t < i) (x : List Bool)
    (A : List Bool → Bool) (c : OCfg (Fin (i + 6)) Γ₃) (hc : TagWriting i t x c) :
    TagWriting i (t + 1) x ((tagQueryOTM i).ostep A c) := by
  obtain ⟨hst, hbuf, hinput⟩ := hc
  have hstFin : c.cfg.state = ⟨t, by omega⟩ := Fin.ext hst
  have hnh : ¬ (tagQueryOTM i).toTM.halted c.cfg := not_halted_of_val_lt (by omega)
  have hne : c.cfg.state ≠ (tagQueryOTM i).ask := by
    intro h; have hv := congrArg Fin.val h
    simp only [hst, tagQueryOTM] at hv; omega
  have hostep : (tagQueryOTM i).ostep A c = (tagQueryOTM i).plain c := by
    simp only [OTM.ostep, hnh, ↓reduceIte, hne, ↓reduceIte]
  rw [hostep]
  have hδ : (tagQueryOTM i).δ c.cfg.state c.cfg.head =
      (⟨t + 1, by omega⟩, c.cfg.head, Dir.stay) := by
    simp only [tagQueryOTM, hstFin, ht, ↓reduceDIte]
  have hwr : (tagQueryOTM i).wr c.cfg.state c.cfg.head = some true := by
    simp only [tagQueryOTM, hstFin, ht, ↓reduceIte]
  have hstep : (tagQueryOTM i).toTM.step c.cfg =
      ⟨⟨t + 1, by omega⟩, c.cfg.left, c.cfg.head, c.cfg.right⟩ := by
    simp only [TM.step, hnh, ↓reduceIte, hδ, TM.move]
  have hplain : (tagQueryOTM i).plain c =
      ⟨⟨⟨t + 1, by omega⟩, c.cfg.left, c.cfg.head, c.cfg.right⟩,
        List.replicate (t + 1) true⟩ := by
    simp only [OTM.plain, hstep, hwr, Option.toList_some, hbuf, replicate_concat_true]
  rw [hplain]; exact ⟨rfl, rfl, hinput⟩

theorem tagWriting_orun (i : ℕ) (A : List Bool → Bool) (x : List Bool) (t : ℕ) (ht : t ≤ i) :
    TagWriting i t x ((tagQueryOTM i).orun A t ((tagQueryOTM i).oinit x)) := by
  induction t with
  | zero => simpa [OTM.orun] using tagWriting_zero i x
  | succ t ih =>
    have hc := ih (Nat.le_of_succ_le ht)
    have hadd := OTM.orun_add (tagQueryOTM i) A t 1 ((tagQueryOTM i).oinit x)
    rw [hadd]; simp only [OTM.orun]
    exact tagWriting_step i t (by omega) x A _ hc

/-- After `i+2` steps: buffer = tag, tape = input.
**Remaining:** two separator writes from `tagWriting_orun i i` (same as `tagWriting_step`). -/
theorem tagQuery_after_tag (i : ℕ) (A : List Bool → Bool) (x : List Bool) :
    let c := (tagQueryOTM i).orun A (i + 2) ((tagQueryOTM i).oinit x)
    c.cfg.state.val = i + 2 ∧
    c.buf = List.replicate i true ++ [false, true] ∧
    c.cfg.left = [] ∧
    ((x = [] ∧ c.cfg.head = 0 ∧ c.cfg.right = []) ∨
      (∃ r rs, x = r :: rs ∧ c.cfg.head = encBit r ∧ c.cfg.right = rs.map encBit)) := by
  sorry

/-- `tagQueryOTM i` decides `spaceLang i` in time `i + n + 4`.
**Remaining:** `tagQuery_after_tag` + copy loop (`queryCfg_orun` style) + ask. -/
theorem tagQueryOTM_decides (i : ℕ) :
    ODecidesInTime (tagQueryOTM i) upspaceOracle (spaceLang i)
      (fun n => i + n + 4) := by
  sorry

theorem spaceLang_mem_OracleP (i : ℕ) : spaceLang i ∈ OracleP upspaceOracle := by
  refine ⟨i + 6, 3, tagQueryOTM i, X + C (i + 4), ?_⟩
  intro x
  simpa [eval_add, eval_X, eval_C, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    using tagQueryOTM_decides i x

theorem PSPACE_subset_OracleP_tqbf : PSPACE ⊆ OracleP upspaceOracle := by
  intro L hL
  obtain ⟨s, hs⟩ := hL
  obtain ⟨i, hi⟩ := enumSpaceDecider_surjective s
  have h := spaceLang_mem_OracleP i
  convert h using 1
  ext x
  subst hi
  simpa [spaceLang] using hs x

/-- **Simulation obligation:** universal space simulation of OTMs with `upspaceOracle`. -/
theorem OracleP_tqbf_subset_PSPACE : OracleP upspaceOracle ⊆ PSPACE := by
  intro L hL
  obtain ⟨k, m, M, p, hdec⟩ := hL
  classical
  have hex : ∃ s : SpaceDecider,
      ∀ x, x ∈ L ↔ acceptsInSpace s.M x (x.length ^ s.d + s.d) = true := by
    sorry
  obtain ⟨s, hs⟩ := hex
  exact ⟨s, hs⟩

/-- **Simulation obligation:** enumerate witnesses in poly space. -/
theorem OracleNPSlice_tqbf_subset_PSPACE : OracleNPSlice upspaceOracle ⊆ PSPACE := by
  intro L hL
  obtain ⟨W, hW, q, hq⟩ := hL
  have hWps : W ∈ PSPACE := OracleP_tqbf_subset_PSPACE hW
  obtain ⟨sW, hsW⟩ := hWps
  classical
  have hex : ∃ s : SpaceDecider,
      ∀ x, x ∈ L ↔ acceptsInSpace s.M x (x.length ^ s.d + s.d) = true := by
    sorry
  obtain ⟨s, hs⟩ := hex
  exact ⟨s, hs⟩

end PvsNP
