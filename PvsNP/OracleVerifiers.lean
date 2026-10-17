import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import PvsNP.Relativization

/-!
# Concrete oracle verifiers

`queryOTM` decides `queryLang A = { y | A y = true }` — fully proved.
-/

namespace PvsNP

open Polynomial

abbrev Γ₃ : Type := Fin 3

def encBit (b : Bool) : Γ₃ := if b then ⟨2, by decide⟩ else ⟨1, by decide⟩

@[simp] theorem encBit_ne_blank (b : Bool) : encBit b ≠ (0 : Γ₃) := by cases b <;> decide

def toBit (g : Γ₃) : Bool := decide (g = (⟨2, by decide⟩ : Γ₃))

@[simp] theorem toBit_encBit (b : Bool) : toBit (encBit b) = b := by cases b <;> rfl

theorem OTM.orun_add {Q Γ : Type} [DecidableEq Q] (M : OTM Q Γ) (O : List Bool → Bool)
    (m n : ℕ) (c : OCfg Q Γ) :
    M.orun O (m + n) c = M.orun O n (M.orun O m c) := by
  induction m generalizing c with
  | zero => simp [OTM.orun]
  | succ m ih => rw [Nat.succ_add]; simpa [OTM.orun] using ih _

def queryOTM : OTM (Fin 4) Γ₃ where
  start := 0
  accept := 2
  reject := 3
  blank := 0
  inp := encBit
  ask := 1
  yes := 2
  no := 3
  wr := fun q g => if q = 0 ∧ g ≠ 0 then some (toBit g) else none
  δ := fun q g =>
    if q = 0 then
      if g = 0 then (1, 0, Dir.stay) else (0, g, Dir.right)
    else (q, g, Dir.stay)

def queryLang (A : List Bool → Bool) : Language := {y | A y = true}

@[simp] theorem queryOTM_start : queryOTM.start = 0 := rfl
@[simp] theorem queryOTM_accept : queryOTM.accept = 2 := rfl
@[simp] theorem queryOTM_reject : queryOTM.reject = 3 := rfl
@[simp] theorem queryOTM_ask : queryOTM.ask = 1 := rfl
@[simp] theorem queryOTM_yes : queryOTM.yes = 2 := rfl
@[simp] theorem queryOTM_no : queryOTM.no = 3 := rfl
@[simp] theorem queryOTM_blank : queryOTM.blank = 0 := rfl

theorem queryOTM_δ_data (g : Γ₃) (hg : g ≠ 0) :
    queryOTM.δ 0 g = (0, g, Dir.right) := by
  simp [queryOTM, hg]

theorem queryOTM_δ_blank : queryOTM.δ 0 0 = (1, 0, Dir.stay) := by
  simp [queryOTM]

theorem queryOTM_wr_data (g : Γ₃) (hg : g ≠ 0) :
    queryOTM.wr 0 g = some (toBit g) := by
  simp [queryOTM, hg]

def QueryCfg (done rest : List Bool) (c : OCfg (Fin 4) Γ₃) : Prop :=
  c.cfg.state = 0 ∧
  c.buf = done ∧
  c.cfg.left = (done.map encBit).reverse ∧
  ((rest = [] ∧ c.cfg.head = 0 ∧ c.cfg.right = []) ∨
    (∃ r rs, rest = r :: rs ∧ c.cfg.head = encBit r ∧ c.cfg.right = rs.map encBit))

theorem queryCfg_init (y : List Bool) : QueryCfg [] y (queryOTM.oinit y) := by
  cases y with
  | nil =>
    change QueryCfg [] [] ⟨⟨0, [], 0, []⟩, []⟩
    simp [QueryCfg]
  | cons r rs =>
    change QueryCfg [] (r :: rs) ⟨⟨0, [], encBit r, rs.map encBit⟩, []⟩
    exact ⟨rfl, rfl, rfl, Or.inr ⟨r, rs, rfl, rfl, rfl⟩⟩

theorem queryCfg_step {done : List Bool} {r : Bool} {rs : List Bool} {c : OCfg (Fin 4) Γ₃}
    (hc : QueryCfg done (r :: rs) c) :
    QueryCfg (done ++ [r]) rs (queryOTM.plain c) := by
  obtain ⟨hst, hbuf, hleft, htape⟩ := hc
  rcases htape with ⟨hnil, _, _⟩ | ⟨r', rs', heq, hhead, hright⟩
  · cases hnil
  · obtain ⟨rfl, rfl⟩ := heq
    have hnh : ¬ queryOTM.toTM.halted c.cfg := by
      intro h; simp [TM.halted, hst] at h
    have hne : encBit r ≠ (0 : Γ₃) := encBit_ne_blank r
    have hstep : queryOTM.toTM.step c.cfg =
        queryOTM.toTM.move 0 c.cfg.left (encBit r) c.cfg.right Dir.right := by
      simp only [TM.step, hnh, ↓reduceIte, hst, hhead, queryOTM_δ_data (encBit r) hne]
    have hplain : queryOTM.plain c =
        ⟨queryOTM.toTM.move 0 c.cfg.left (encBit r) c.cfg.right Dir.right,
          done ++ [r]⟩ := by
      simp only [OTM.plain, hstep, hst, hhead, queryOTM_wr_data (encBit r) hne, toBit_encBit,
        Option.toList_some, hbuf]
    rw [hplain]
    cases rs with
    | nil =>
      simp [TM.move, hright, hleft, QueryCfg, List.map_append, List.reverse_append]
    | cons s ss =>
      simp [TM.move, hright, hleft, QueryCfg, List.map_append, List.reverse_append]

theorem queryCfg_orun (A : List Bool → Bool) (done rest : List Bool) (c : OCfg (Fin 4) Γ₃)
    (hc : QueryCfg done rest c) :
    QueryCfg (done ++ rest) [] (queryOTM.orun A rest.length c) := by
  induction rest generalizing done c with
  | nil => simpa [OTM.orun] using hc
  | cons r rs ih =>
    obtain ⟨hst, hbuf, hleft, htape⟩ := hc
    have hnh : ¬ queryOTM.toTM.halted c.cfg := by
      intro h; simp [TM.halted, hst] at h
    have hostep : queryOTM.ostep A c = queryOTM.plain c := by
      have hne : ¬ (c.cfg.state = 1) := by simp [hst]
      simp only [OTM.ostep, hnh, ↓reduceIte, queryOTM_ask, hne, ↓reduceIte]
    rw [List.length_cons, OTM.orun, hostep]
    have hc' : QueryCfg done (r :: rs) c := ⟨hst, hbuf, hleft, htape⟩
    simpa [List.append_assoc] using ih (done ++ [r]) _ (queryCfg_step hc')

theorem queryOTM_decides (A : List Bool → Bool) :
    ODecidesInTime queryOTM A (queryLang A) (fun n => n + 2) := by
  intro x
  have hc : QueryCfg x [] (queryOTM.orun A x.length (queryOTM.oinit x)) := by
    simpa using queryCfg_orun A [] x _ (queryCfg_init x)
  obtain ⟨hst, hbuf, _, htape⟩ := hc
  have hhead : (queryOTM.orun A x.length (queryOTM.oinit x)).cfg.head = 0 := by
    rcases htape with ⟨_, h, _⟩ | ⟨_,_,heq,_,_⟩
    · exact h
    · cases heq
  have hnh0 : ¬ queryOTM.toTM.halted
      (queryOTM.orun A x.length (queryOTM.oinit x)).cfg := by
    intro h; simp [TM.halted, hst] at h
  have h1 : queryOTM.ostep A (queryOTM.orun A x.length (queryOTM.oinit x)) =
      queryOTM.plain (queryOTM.orun A x.length (queryOTM.oinit x)) := by
    have hne : ¬ ((queryOTM.orun A x.length (queryOTM.oinit x)).cfg.state = 1) := by simp [hst]
    simp only [OTM.ostep, hnh0, ↓reduceIte, queryOTM_ask, hne, ↓reduceIte]
  have hask_state :
      (queryOTM.plain (queryOTM.orun A x.length (queryOTM.oinit x))).cfg.state = 1 := by
    have hstep : queryOTM.toTM.step (queryOTM.orun A x.length (queryOTM.oinit x)).cfg =
        queryOTM.toTM.move 1 (queryOTM.orun A x.length (queryOTM.oinit x)).cfg.left 0
          (queryOTM.orun A x.length (queryOTM.oinit x)).cfg.right Dir.stay := by
      simp only [TM.step, hnh0, ↓reduceIte, hst, hhead, queryOTM_δ_blank]
    simp only [OTM.plain, hstep, TM.move]
  have hask_buf :
      (queryOTM.plain (queryOTM.orun A x.length (queryOTM.oinit x))).buf = x := by
    have hwr : queryOTM.wr 0 0 = none := by simp [queryOTM]
    simp only [OTM.plain, TM.step, hnh0, ↓reduceIte, hst, hhead, queryOTM_δ_blank, TM.move,
      hwr, Option.toList_none, List.append_nil, hbuf]
  set cAsk := queryOTM.plain (queryOTM.orun A x.length (queryOTM.oinit x))
  have hnhA : ¬ queryOTM.toTM.halted cAsk.cfg := by
    intro h; simp [TM.halted, hask_state] at h
  have h2 : queryOTM.ostep A cAsk = queryOTM.answer cAsk (A x) := by
    simp only [OTM.ostep, hnhA, hask_state, queryOTM_ask, ↓reduceIte, hask_buf]
  have hfinal : queryOTM.orun A (x.length + 2) (queryOTM.oinit x) =
      queryOTM.answer cAsk (A x) := by
    rw [OTM.orun_add queryOTM A x.length 2, OTM.orun, h1, OTM.orun, h2]
    rfl
  constructor
  · -- halted
    rw [hfinal]
    cases hA : A x <;> simp [OTM.answer, TM.halted, hA]
  · -- accepts iff
    rw [hfinal]
    cases hA : A x <;> simp [OTM.answer, queryLang, hA]

theorem queryLang_mem_OracleP (A : List Bool → Bool) : queryLang A ∈ OracleP A := by
  refine ⟨4, 3, queryOTM, X + C 2, ?_⟩
  intro x
  simpa [eval_add, eval_X, eval_C] using queryOTM_decides A x

end PvsNP
