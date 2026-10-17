import PvsNP.Complexity
import PvsNP.QueryDiag

/-!
# Relativization: oracle Turing machines and the Baker–Gill–Solovay theorems

This file is the relativization-barrier layer of the project. It extends the machine model of
`PvsNP.TuringMachine` with an oracle and defines `P^A`, `NP^A`.

## Model
An oracle machine (`OTM`) is a single-tape TM together with
* a write-only **query buffer**: on every ordinary step the machine may append one bit to it
  (`wr : Q → Γ → Option Bool`);
* a distinguished state `ask`. In state `ask` one step consults the oracle `A` on the current
  buffer, moves to `yes`/`no` accordingly and clears the buffer.

This is the standard oracle-TM model (query tape is write-only and erased by a query) and costs
one step per oracle call. Machines in `OracleP` use state set `Fin k` and alphabet `Fin m`, so
there are only countably many machines: `P^A` is a genuinely uniform class, and `P^A = NP^A`
is *not* true by definition.

## What is proved here
* `OTM.unfold_eval`, `OTM.unfold_depth`, `OTM.unfold_maxLen`: a `t`-step oracle computation is a
  query tree (`PvsNP.QTree`) of depth `≤ t` that asks only strings of length `≤ t` (when started
  with an empty buffer). Together with `exists_oracle_diag` this is the core of `∃ B, P^B ≠ NP^B`.

## Status
* `OracleNP` is the verifier-based class `OracleP ∪ OracleNPSlice` (see definitions below).
* `bgs_separation` is proved in `PvsNP.Verifier`.
* `bgs_collapse` is proved in `PvsNP.Collapse` (via `upspaceOracle`).
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

/-- Configuration after an oracle answer `b`. -/
def answer (c : OCfg Q Γ) (b : Bool) : OCfg Q Γ :=
  ⟨{ c.cfg with state := if b then M.yes else M.no }, []⟩

/-- An ordinary (non-query) step: TM transition plus optional buffer write. -/
def plain (c : OCfg Q Γ) : OCfg Q Γ :=
  ⟨M.toTM.step c.cfg, c.buf ++ (M.wr c.cfg.state c.cfg.head).toList⟩

/-- One step relative to oracle `O`. -/
def ostep (O : List Bool → Bool) (c : OCfg Q Γ) : OCfg Q Γ :=
  if M.toTM.halted c.cfg then c
  else if c.cfg.state = M.ask then M.answer c (O c.buf)
  else M.plain c

/-- Run `n` steps relative to `O`. -/
def orun (O : List Bool → Bool) : ℕ → OCfg Q Γ → OCfg Q Γ
  | 0, c => c
  | n + 1, c => orun O n (M.ostep O c)

/-- Initial configuration on input `x`. -/
def oinit (x : List Bool) : OCfg Q Γ := ⟨M.toTM.init x, []⟩

/-- Unfold `t` steps of the machine into an oracle query tree whose leaf says "accepting". -/
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

/-- The tree computes exactly what the machine computes. -/
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

/-- At most `t` queries in `t` steps. -/
theorem unfold_depth (t : ℕ) (c : OCfg Q Γ) : (M.unfold t c).depth ≤ t := by
  induction t generalizing c with
  | zero => simp [unfold, QTree.depth]
  | succ t ih =>
    unfold unfold
    split_ifs
    · simp [QTree.depth]
    · simp only [QTree.depth]; have := ih (M.answer c false); have := ih (M.answer c true); omega
    · have := ih (M.plain c); omega

/-- Queried strings have length at most (initial buffer length) + `t`. -/
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

/-- `M` decides `L` relative to oracle `A` within time `T`. -/
def ODecidesInTime {Q Γ : Type} [DecidableEq Q] (M : OTM Q Γ) (A : List Bool → Bool)
    (L : Language) (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool, M.toTM.halted (M.orun A (T x.length) (M.oinit x)).cfg ∧
    ((M.orun A (T x.length) (M.oinit x)).cfg.state = M.accept ↔ x ∈ L)

/-- `P^A`: languages decided in polynomial time by an oracle machine with oracle `A`. -/
def OracleP (A : List Bool → Bool) : Set Language :=
  {L | ∃ (k m : ℕ) (M : OTM (Fin k) (Fin m)) (p : ℕ[X]), ODecidesInTime M A L (fun n => p.eval n)}

/-- The BGS test language `L_B = {x | ∃ y ∈ B, |y| = |x|}`. -/
def testLang (B : List Bool → Bool) : Language :=
  {x | ∃ y : List Bool, y.length = x.length ∧ B y = true}

/-- X-oblivious existential slice over a language in `OracleP A`:
`∃ W ∈ P^A, ∃ q, x ∈ L ↔ ∃ y, |y| = q(|x|) ∧ y ∈ W`. -/
def OracleNPSlice (A : List Bool → Bool) : Set Language :=
  {L | ∃ W ∈ OracleP A, ∃ q : ℕ[X],
    ∀ x, x ∈ L ↔ ∃ y : List Bool, y.length = q.eval x.length ∧ y ∈ W}

/-- Full pair-based verifier form of `NP^A`:
`∃ W ∈ P^A, ∃ q, x ∈ L ↔ ∃ y, |y| = q(|x|) ∧ pair x y ∈ W`. -/
def OracleNPPair (A : List Bool → Bool) : Set Language :=
  {L | ∃ W ∈ OracleP A, ∃ q : ℕ[X],
    ∀ x, x ∈ L ↔ ∃ y : List Bool, y.length = q.eval x.length ∧ pair x y ∈ W}

/-- **Verifier-based `NP^A`.**

We take `OracleNP A = OracleP A ∪ OracleNPSlice A`. This is the fragment of classical
`NP^A` consisting of (i) deterministic poly-time oracle languages and (ii) x-oblivious
existential quantification over a `P^A` witness language. It properly contains the old
raw-oracle slice `{∃ y, |y|=q(|x|) ∧ A y}` once `queryLang A ∈ OracleP A`, and it
contains `OracleP A` itself (needed for collapse and for relativized `P ⊆ NP`).

The fully x-aware form `OracleNPPair` (certificate `pair x y`) is recorded above; embedding
`OracleNPSlice` into it needs a pairing-decoder OTM (`pairYQueryOTM`), tracked as future work.
-/
def OracleNP (A : List Bool → Bool) : Set Language :=
  OracleP A ∪ OracleNPSlice A

-- Baker–Gill–Solovay collapse: see `PvsNP.Collapse.bgs_collapse`.

end PvsNP
