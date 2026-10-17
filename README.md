# p-vs-np-lean

A Lean 4 + Mathlib formalization of the **P vs NP** problem and of two classical barriers:
**relativization** (Baker–Gill–Solovay 1975) and **natural proofs** (Razborov–Rudich 1997).

> `P ≠ NP` itself is open. It is stated as `PvsNP.P_ne_NP` with `sorry` and will stay that way.

## Versions
- Lean `v4.35.0` (`lean-toolchain`)
- Mathlib `v4.35.0` tag (`lake-manifest.json`)

## Build
```bash
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
lake exe cache get
lake build
lake env lean Audit.lean   # axiom audit; see audit.log
```

## Layout
| File | Contents |
|---|---|
| `PvsNP/TuringMachine.lean` | Single-tape deterministic TMs |
| `PvsNP/Complexity.lean` | `P`, `NP`, `coNP`, `SAT` |
| `PvsNP/Main.lean` | `P_ne_NP` (intentional `sorry`) |
| `PvsNP/QueryDiag.lean` | Query trees + BGS diagonalization core |
| `PvsNP/PolyBound.lean` | `p(n) < 2ⁿ` infinitely often |
| `PvsNP/Relativization.lean` | Oracle TMs, `OracleP`, `OracleNP`, `bgs_collapse` |
| `PvsNP/Enumeration.lean` | Countable enumeration of `OracleP` machines |
| `PvsNP/Verifier.lean` | **`bgs_separation`** (fully proved) |
| `PvsNP/NaturalProofs.lean` | Circuits, `P/poly`, Razborov–Rudich framework |
| `PvsNP/Collapse.lean` | Length-symmetry of slice-`OracleNP` |

## Proved vs pending

Every ✅ theorem is checked by `#print axioms` and uses only `propext`, `Classical.choice`, `Quot.sound`.

| Result | Status |
|---|---|
| `exists_oracle_diag` | ✅ proved |
| `OTM.unfold_eval/depth/maxLen` | ✅ proved |
| `poly_lt_two_pow_infinitely_often` | ✅ proved |
| `enumTree_depth_lt_two_pow`, `OracleP.exists_enum` | ✅ proved |
| `testLang_mem_OracleNP`, `testLang_not_mem_OracleP_bgs` | ✅ proved |
| **`bgs_separation : ∃ B, OracleP B ≠ OracleNP B`** | ✅ **proved** |
| Natural-proofs lemmas (`Large.mono`, …) | ✅ proved |
| `P_ne_NP` | ⛔ open problem, `sorry` on purpose |
| `bgs_collapse : ∃ A, OracleP A = OracleNP A` | 🟡 `sorry` — classical target; see note below |
| `OracleNP.lengthSymmetric`, `not_lengthSymmetric_singleton_false` | ✅ proved (explains why slice-collapse fails) |
| `P_subset_NP` | 🟡 `sorry` (needs pairing-decoder TM) |
| Full Razborov–Rudich theorem | 🟡 definition only (`RazborovRudichStatement`); needs PRF security |

## Definition note: `OracleNP`

The current `OracleNP` is the **existential poly-length oracle-slice** form

```
L ∈ NP^A  ↔  ∃ q, ∀ x, x ∈ L ↔ ∃ y, |y| = q(|x|) ∧ A y
```

This is a **subclass** of the usual verifier-based `NP^A`. The classical BGS test language
`testLang A = {x | ∃ y, |y| = |x| ∧ A y}` lies in this subclass, so `bgs_separation`
is the classical Baker–Gill–Solovay separation theorem.

**Consequence for collapse.** Under this slice definition every language in `OracleNP A` is
length-symmetric, while `OracleP A` always contains non-length-symmetric languages from
ordinary `P`. So the classical collapse `∃ A, P^A = NP^A` requires upgrading `OracleNP` to
the full verifier form (or the x-oblivious form `∃ V ∈ P^A, ∃ q, x ∈ L ↔ ∃ y, |y|=q(|x|) ∧ y ∈ V`
with `queryLang A ∈ P^A`). Tracked as future work; `bgs_collapse` remains a classical-target `sorry`.

## Model notes
- Oracle machines in `OracleP` have state set `Fin k` and alphabet `Fin m` (countably many machines).
- Each oracle query costs one step; the query buffer is write-only and erased by a query.
- `QTree` is the decision-tree view of a deterministic oracle computation on a fixed input.

## 中文说明
本项目在 Lean 4 中形式化 P vs NP 以及相对化、自然证明两个障碍。

- **已证明**（无 sorry，只用三个标准公理）：
  - **`bgs_separation`**：存在预言机 B 使得 `P^B ≠ NP^B`（完整证明）；
  - BGS 对角化核心、机器枚举、多项式低于指数、查询树展开；
  - 自然证明中 largeness / usefulness 的基本引理。
- **关于 `OracleNP` 的定义**：当前采用「存在长度为 q(|x|) 的证书 y 使得 A(y)=true」的切片形式，是标准验证机 NP^A 的子类；BGS 分离对这个子类成立即得经典定理。
- **待完成**：
  - `P_ne_NP`：公开难题，永久 sorry；
  - `bgs_collapse`：经典陈述保留为 sorry；切片定义下 NP 语言都是长度对称的（已证 `OracleNP.lengthSymmetric`），与普通 P 冲突，故需先升级 `OracleNP` 再证 collapse；
  - `P_subset_NP`：sorry，需要 pair 解码图灵机；
  - Razborov–Rudich 主定理（PRF）；
  - 电路模型从公式升级为 DAG。

## Is this a usable verification framework?

**Partially yes for relativization-separation.** The project now has a complete, axiom-clean proof of
Baker–Gill–Solovay *separation*, with the supporting enumeration / poly-bound / query-tree layers.
New proofs that a language lies outside `OracleP` (or that a slice-`NP` language differs from `P`)
can reuse this machinery.

**Not yet for collapse, unrelativized `P ⊆ NP`, or natural-proof barriers.** Those need the
full verifier `NP`, a PSPACE theory, pairing TMs, DAG circuits, and a PRF definition.
