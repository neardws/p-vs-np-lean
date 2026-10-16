# p-vs-np-lean

A Lean 4 + Mathlib formalization of the **P vs NP** problem and of two classical barriers to
resolving it: **relativization** (Baker–Gill–Solovay 1975) and **natural proofs**
(Razborov–Rudich 1997).

> P ≠ NP itself is open. It is stated as `PvsNP.P_ne_NP` with `sorry` and will stay that way.

## Versions
- Lean `v4.35.0` (`lean-toolchain`)
- Mathlib `v4.35.0` tag, commit `56a005855ea17e0b0958f73ec801ae140b0a1679` (`lake-manifest.json`)

## Build
```bash
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
lake exe cache get      # download the prebuilt Mathlib
lake build              # builds the PvsNP library
lake env lean Audit.lean  # axiom audit (#print axioms); output is in audit.log
```

## Layout
| File | Contents |
|---|---|
| `PvsNP/TuringMachine.lean` | Single-tape deterministic TMs: states, tape alphabet, `δ`, `step`, `run`, halting and acceptance |
| `PvsNP/Complexity.lean` | Polynomial time (`∃ p : ℕ[X]`, steps ≤ p(\|x\|)), `P`, `NP` (verifier definition), `coNP`, CNF and `SAT` |
| `PvsNP/Main.lean` | `theorem P_ne_NP : P ≠ NP := sorry` |
| `PvsNP/QueryDiag.lean` | Oracle query trees and the BGS diagonalization core (fully proved) |
| `PvsNP/Relativization.lean` | Oracle TMs, `P^A` and `NP^A`, unfolding of TM runs into query trees, the BGS theorem statements |
| `PvsNP/NaturalProofs.lean` | Circuits, `P/poly`, constructive, large and useful properties, the Razborov–Rudich statement |

## Proved vs pending
Every theorem marked ✅ is checked by `#print axioms` and uses only `propext`, `Classical.choice` and `Quot.sound`.

| Result | Status |
|---|---|
| `exists_oracle_diag`: for any countable family of oracle query trees that each make fewer than 2ⁿ queries infinitely often, some oracle B defeats them all on `L_B = {1ⁿ : ∃ y ∈ B, \|y\| = n}` | ✅ proved |
| `exists_length_not_mem` (counting lemma) | ✅ proved |
| `OTM.unfold_eval`, `unfold_depth`, `unfold_maxLen`: a t-step oracle TM run is a query tree with depth ≤ t and query length ≤ t | ✅ proved |
| `TM.run_stable`, SAT sanity lemmas | ✅ proved |
| `Large.mono`, `large_univ`, `UsefulAgainstPPoly.anti`, `UsefulAgainstPPoly.not_const`, `not_useful_univ` | ✅ proved |
| `P_ne_NP` | ⛔ open problem, `sorry` on purpose |
| `bgs_separation : ∃ B, P^B ≠ NP^B` | 🟡 `sorry`. Remaining: (1) enumerate the `OracleP` deciders as `ℕ → (machine, polynomial)`; (2) show p(n) < 2ⁿ infinitely often; (3) build an explicit verifier OTM for `testLang B ∈ NP^B`. The combinatorial core is already proved (see above). |
| `bgs_collapse : ∃ A, P^A = NP^A` | 🟡 `sorry`. Needs a PSPACE-complete or self-referential simulation oracle plus TM constructions. |
| `P ⊆ NP` | 🟡 not yet stated. Needs a TM that decodes `pair x y`. |
| Razborov–Rudich | 🟡 recorded as `RazborovRudichStatement PRFsExist`. A concrete definition of PRF security and the proof are pending. |

## Model notes (honesty)
- The oracle machines in `OracleP` have state set `Fin k` and alphabet `Fin m`, so the class is countable and uniform, and `P^A = NP^A` does **not** hold by definition. Each oracle query costs one step. The query buffer is write-only and is erased by the query.
- `QTree` is the standard decision-tree view of a deterministic oracle computation on a fixed input. The unfolding lemmas connect it to the machine model.

## 中文说明
本项目在 Lean 4 中形式化 P vs NP 问题，以及两个经典障碍：相对化（Baker–Gill–Solovay）和自然证明（Razborov–Rudich）。
- **已证明**（无 sorry，只用三个标准公理）：
  - BGS 分离定理的核心对角化引理 `exists_oracle_diag`；
  - 预言机图灵机运行展开成查询树的三个引理；
  - 自然证明里关于 largeness 和 usefulness 的基本引理；
  - 若干 SAT 和图灵机的基本引理。
- **待完成**：
  - `P_ne_NP` 是公开难题，永久保留 sorry；
  - `bgs_separation` 还差三步：机器枚举、多项式小于 2ⁿ、验证机构造；
  - `bgs_collapse` 还差 PSPACE 完全预言机的构造；
  - `P ⊆ NP`；
  - Razborov–Rudich 主定理（PRF 的定义和证明）。
