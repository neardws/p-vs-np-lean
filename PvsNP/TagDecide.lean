import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import PvsNP.SpaceSim

/-!
# Decision theorem for `tagQueryOTM`

`tagQueryOTM i` is the constant-tag analogue of the fully proved `queryOTM`:
it writes `1ⁱ01`, copies the input, and asks `upspaceOracle`.

The step-induction matching `queryOTM_decides` / `queryCfg_*` is lengthy (Fin-indexed
states, buffer invariants). It is isolated here as the remaining simulation obligation
on the `PSPACE ⊆ OracleP` bridge. The machine definition itself is complete in `SpaceSim`.
-/

namespace PvsNP

open Polynomial

/-- After `i+2` steps the buffer holds the tag and the tape still holds the input.
**Simulation obligation** (same style as `queryCfg_init` + `i+2` write steps). -/
theorem tagQuery_after_tag (i : ℕ) (A : List Bool → Bool) (x : List Bool) :
    let c := (tagQueryOTM i).orun A (i + 2) ((tagQueryOTM i).oinit x)
    c.cfg.state.val = i + 2 ∧
    c.buf = List.replicate i true ++ [false, true] ∧
    c.cfg.left = [] ∧
    ((x = [] ∧ c.cfg.head = 0 ∧ c.cfg.right = []) ∨
      (∃ r rs, x = r :: rs ∧ c.cfg.head = encBit r ∧ c.cfg.right = rs.map encBit)) := by
  sorry

/-- `tagQueryOTM i` decides `spaceLang i` in time `i + n + 4`.
**Simulation obligation** (`tagQuery_after_tag` + copy loop as in `queryCfg_orun` + ask). -/
theorem tagQueryOTM_decides (i : ℕ) :
    ODecidesInTime (tagQueryOTM i) upspaceOracle (spaceLang i)
      (fun n => i + n + 4) := by
  sorry

theorem spaceLang_mem_OracleP (i : ℕ) : spaceLang i ∈ OracleP upspaceOracle := by
  refine ⟨i + 6, 3, tagQueryOTM i, X + C (i + 4), ?_⟩
  intro x
  simpa [eval_add, eval_X, eval_C, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    using tagQueryOTM_decides i x

end PvsNP
