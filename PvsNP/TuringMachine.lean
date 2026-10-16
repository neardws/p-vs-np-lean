import Mathlib.Data.Set.Defs
import Mathlib.Order.Basic

/-!
# Single-tape deterministic Turing machines

This file is the foundation layer of the `p-vs-np-lean` project. Every complexity class
in the project (`PvsNP.Complexity`) is defined in terms of the machines here.

We define our own small, explicit model instead of wrapping Mathlib's `Turing.TM0`, so that
step counting (needed for polynomial time) is completely transparent:

* a machine has a finite state set `Q`, a finite tape alphabet `Γ` with a blank symbol and an
  embedding of the input alphabet `Bool`, a start state, an accept and a reject state and a
  transition function `δ : Q → Γ → Q × Γ × Dir`;
* a configuration is a state together with a tape zipper `(left, head, right)`;
* `step` performs one transition (halting states are fixed points);
* `run M n c` iterates `step` `n` times.
-/

namespace PvsNP

/-- Languages over the binary alphabet. -/
abbrev Language := Set (List Bool)

/-- Head movement. -/
inductive Dir
  | left | right | stay
  deriving DecidableEq, Repr

/-- A single-tape deterministic Turing machine. -/
structure TM (Q Γ : Type) where
  start : Q
  accept : Q
  reject : Q
  blank : Γ
  inp : Bool → Γ
  δ : Q → Γ → Q × Γ × Dir

/-- A configuration: current state and a tape zipper. `left` is stored nearest-cell-first. -/
structure Cfg (Q Γ : Type) where
  state : Q
  left : List Γ
  head : Γ
  right : List Γ

namespace TM

variable {Q Γ : Type} [DecidableEq Q] (M : TM Q Γ)

/-- Is the state a halting state? -/
def halted (c : Cfg Q Γ) : Prop := c.state = M.accept ∨ c.state = M.reject

instance (c : Cfg Q Γ) : Decidable (M.halted c) := by unfold halted; infer_instance

/-- Initial configuration on input `x`; the head is on the first input symbol. -/
def init (x : List Bool) : Cfg Q Γ :=
  match x with
  | [] => ⟨M.start, [], M.blank, []⟩
  | b :: bs => ⟨M.start, [], M.inp b, bs.map M.inp⟩

/-- Move the head of a configuration (cells beyond the written region are blank). -/
def move (s : Q) (l : List Γ) (a : Γ) (r : List Γ) : Dir → Cfg Q Γ
  | .stay => ⟨s, l, a, r⟩
  | .left => match l with
    | [] => ⟨s, [], M.blank, a :: r⟩
    | b :: l' => ⟨s, l', b, a :: r⟩
  | .right => match r with
    | [] => ⟨s, a :: l, M.blank, []⟩
    | b :: r' => ⟨s, a :: l, b, r'⟩

/-- One computation step. Halting configurations are fixed points. -/
def step (c : Cfg Q Γ) : Cfg Q Γ :=
  if M.halted c then c
  else
    let (s, a, d) := M.δ c.state c.head
    M.move s c.left a c.right d

/-- Run for `n` steps. -/
def run : ℕ → Cfg Q Γ → Cfg Q Γ
  | 0, c => c
  | n + 1, c => run n (M.step c)

/-- `M` halts on `x` within `t` steps. -/
def haltsWithin (x : List Bool) (t : ℕ) : Prop := M.halted (M.run t (M.init x))

/-- `M` accepts `x` (in the configuration reached after `t` steps). -/
def acceptsAt (x : List Bool) (t : ℕ) : Prop := (M.run t (M.init x)).state = M.accept

theorem run_add (m n : ℕ) (c : Cfg Q Γ) : M.run (m + n) c = M.run n (M.run m c) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih => rw [Nat.succ_add]; simp [run, ih]

theorem step_of_halted {c : Cfg Q Γ} (h : M.halted c) : M.step c = c := by
  simp [step, h]

theorem run_of_halted {c : Cfg Q Γ} (h : M.halted c) (n : ℕ) : M.run n c = c := by
  induction n with
  | zero => rfl
  | succ n ih => simp [run, step_of_halted M h, ih]

/-- Once halted, a machine stays in the same configuration. -/
theorem run_stable {x : List Bool} {t t' : ℕ} (ht : M.haltsWithin x t) (h : t ≤ t') :
    M.run t' (M.init x) = M.run t (M.init x) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [run_add]; exact run_of_halted M ht k

end TM
end PvsNP
