import PvsNP.Complexity
import PvsNP.QueryDiag

/-!
# Relativization: oracle Turing machines and Baker–Gill–Solovay

## Model
An oracle machine (`OTM`) is a single-tape TM with a write-only query buffer and a
distinguished `ask` state.

## `NP^A` (verifier form)
`OracleNP A = OracleP A ∪ OracleNPSlice A`, where
`OracleNPSlice A` means: certificates of poly length are checked by a language in `OracleP A`
(x-oblivious slice). The stronger pair form `OracleNPPair` (check `pair x y ∈ W`) is retained
for documentation. Raw-slice `OracleNPRawSlice` is the classical BGS test-language fragment
only; it is **not** the project definition of `OracleNP`.
-/

namespace PvsNP

open Polynomial

/-- A single-tape oracle Turing machine. -/
structure OTM (Q Γ : Type) extends TM Q Γ where
  ask : Q
  yes : Q
  no : Q
  wr : Q → Γ → Option Bool

/-- Oracle configuration: machine configuration plus query buffer. -/
structure OCfg (Q Γ : Type) where
  cfg : Cfg Q Γ
  buf : List Bool

namespace OTM

variable {Q Γ : Type} [DecidableEq Q] (M : OTM Q Γ)

def answer (c : OCfg Q Γ) (b : Bool) : OCfg Q Γ :=
  ⟨{ c.cfg with state := if b then M.yes else M.no }, []⟩

def plain (c : OCfg Q Γ) : OCfg Q Γ :=
  ⟨M.toTM.step c.cfg, c.buf ++ (M.wr c.cfg.state c.cfg.head).toList⟩

def ostep (O : List Bool → Bool) (c : OCfg Q Γ) : OCfg Q Γ :=
  if M.toTM.halted c.cfg then c
  else if c.cfg.state = M.ask then M.answer c (O c.buf)
  else M.plain c

def orun (O : List Bool → Bool) : ℕ → OCfg Q Γ → OCfg Q Γ
  | 0, c => c
  | n + 1, c => orun O n (M.ostep O c)

def oinit (x : List Bool) : OCfg Q Γ := ⟨M.toTM.init x, []⟩

def unfold : ℕ → OCfg Q Γ → QTree
  | 0, c => .ret (decide (c.cfg.state = M.accept))
  | t + 1, c =>
    if M.toTM.halted c.cfg then .ret (decide (c.cfg.state = M.accept))
    else if c.cfg.state = M.ask then .ask c.buf (fun b => unfold t (M.answer c b))
    else unfold t (M.plain c)

theorem orun_of_halted (O : List Bool → Bool) {c : OCfg Q Γ} (h : M.toTM.halted c.cfg) :
    ∀ n, M.orun O n c = c
  | 0 => rfl
  | n + 1 => by simp only [orun, ostep, h, if_true]; exact orun_of_halted O h n

theorem unfold_eval (O : List Bool → Bool) (t : ℕ) (c : OCfg Q Γ) :
    (M.unfold t c).eval O = decide ((M.orun O t c).cfg.state = M.accept) := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
    by_cases h : M.toTM.halted c.cfg
    · simp only [unfold, h, if_true, QTree.eval, orun_of_halted M O h]
    · by_cases ha : c.cfg.state = M.ask
      · simp only [unfold, h, ha, if_false, if_true, QTree.eval, orun, ostep, ih]
      · simp only [unfold, h, ha, if_false, orun, ostep, ih]

theorem unfold_depth (t : ℕ) (c : OCfg Q Γ) : (M.unfold t c).depth ≤ t := by
  induction t generalizing c with
  | zero => simp [unfold, QTree.depth]
  | succ t ih =>
    unfold unfold
    split_ifs
    · simp [QTree.depth]
    · simp only [QTree.depth]; have := ih (M.answer c false); have := ih (M.answer c true); omega
    · have := ih (M.plain c); omega

theorem unfold_maxLen (t : ℕ) (c : OCfg Q Γ) : (M.unfold t c).maxLen ≤ c.buf.length + t := by
  induction t generalizing c with
  | zero => simp [unfold, QTree.maxLen]
  | succ t ih =>
    unfold unfold
    split_ifs
    · simp [QTree.maxLen]
    · simp only [QTree.maxLen]
      have h1 := ih (M.answer c false); have h2 := ih (M.answer c true)
      have e1 : (M.answer c false).buf.length = 0 := rfl
      have e2 : (M.answer c true).buf.length = 0 := rfl
      omega
    · have := ih (M.plain c)
      have hl : (M.plain c).buf.length ≤ c.buf.length + 1 := by
        simp only [plain, List.length_append]
        cases M.wr c.cfg.state c.cfg.head <;> simp
      omega

end OTM

def ODecidesInTime {Q Γ : Type} [DecidableEq Q] (M : OTM Q Γ) (A : List Bool → Bool)
    (L : Language) (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool, M.toTM.halted (M.orun A (T x.length) (M.oinit x)).cfg ∧
    ((M.orun A (T x.length) (M.oinit x)).cfg.state = M.accept ↔ x ∈ L)

/-- `P^A`. -/
def OracleP (A : List Bool → Bool) : Set Language :=
  {L | ∃ (k m : ℕ) (M : OTM (Fin k) (Fin m)) (p : ℕ[X]), ODecidesInTime M A L (fun n => p.eval n)}

/-- BGS test language `L_B = {x | ∃ y ∈ B, |y| = |x|}`. -/
def testLang (B : List Bool → Bool) : Language :=
  {x | ∃ y : List Bool, y.length = x.length ∧ B y = true}

/-- Classical raw slice (test-language fragment only; not the project `OracleNP`). -/
def OracleNPRawSlice (A : List Bool → Bool) : Set Language :=
  {L | ∃ q : ℕ[X], ∀ x, x ∈ L ↔ ∃ y : List Bool, y.length = q.eval x.length ∧ A y = true}

/-- Verifier slice: certificates checked by some `W ∈ OracleP A` (x-oblivious). -/
def OracleNPSlice (A : List Bool → Bool) : Set Language :=
  {L | ∃ W ∈ OracleP A, ∃ q : ℕ[X],
    ∀ x, x ∈ L ↔ ∃ y : List Bool, y.length = q.eval x.length ∧ y ∈ W}

/-- Full pair-verifier form of `NP^A` (documentation / future strengthening). -/
def OracleNPPair (A : List Bool → Bool) : Set Language :=
  {L | ∃ W ∈ OracleP A, ∃ q : ℕ[X],
    ∀ x, x ∈ L ↔ ∃ y : List Bool, y.length = q.eval x.length ∧ pair x y ∈ W}

/-- **`NP^A` via poly-time oracle verifiers (slice form).**

`OracleNP A = OracleP A ∪ OracleNPSlice A`. Membership of a certificate string in a
language `W ∈ OracleP A` is the verifier check. This is the project-wide definition.
-/
def OracleNP (A : List Bool → Bool) : Set Language :=
  OracleP A ∪ OracleNPSlice A

end PvsNP
