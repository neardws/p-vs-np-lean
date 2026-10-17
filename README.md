# p-vs-np-lean

A Lean 4 + Mathlib formalization of the **P vs NP** problem and of two classical barriers:
**relativization** (Baker–Gill–Solovay 1975) and **natural proofs** (Razborov–Rudich 1997).

> `P ≠ NP` itself is open. It is stated as `PvsNP.P_ne_NP` with `sorry` and will stay that way.

## Versions
- Lean `v4.35.0` (`lean-toolchain`)
- Mathlib `v4.35.0` / commit `56a00585` (`lake-manifest.json`)

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
| `PvsNP/Complexity.lean` | `P`, `NP`, `coNP`, `SAT`, `P_subset_NP` (blocked) |
| `PvsNP/Main.lean` | `P_ne_NP` (intentional `sorry`) |
| `PvsNP/QueryDiag.lean` | Query trees + BGS diagonalization core |
| `PvsNP/PolyBound.lean` | `p(n) < 2ⁿ` infinitely often |
| `PvsNP/Relativization.lean` | Oracle TMs, `OracleP`, `OracleNP` / `OracleNPSlice` / `OracleNPPair` |
| `PvsNP/Enumeration.lean` | Countable enumeration of `OracleP` machines |
| `PvsNP/OracleVerifiers.lean` | **`queryOTM`**: `{y \| A y}` ∈ `OracleP A` (fully proved) |
| `PvsNP/Verifier.lean` | **`bgs_separation`**, `OracleP ⊆ OracleNP` |
| `PvsNP/Collapse.lean` | PSPACE scaffolding + `bgs_collapse_of_bridges` |
| `PvsNP/NaturalProofs.lean` | Circuits, `P/poly`, Razborov–Rudich framework |
| `PvsNP/Pairing.lean` | `pair` / `doubled` lemmas |

## Definition of `OracleNP` (upgraded)

```
OracleNP A  =  OracleP A  ∪  OracleNPSlice A
```

where

```
L ∈ OracleNPSlice A  ↔  ∃ W ∈ OracleP A, ∃ q,
      ∀ x, x ∈ L ↔ ∃ y, |y| = q(|x|) ∧ y ∈ W
```

This is the **verifier-based** fragment consisting of
1. deterministic poly-time oracle languages, and
2. x-oblivious existential quantification over a `P^A` witness language.

It properly contains the old raw-oracle slice `{∃ y, |y|=q(|x|) ∧ A y}` because
`queryLang A = {y | A y} ∈ OracleP A` (proved via `queryOTM`).

The fully x-aware form is recorded as `OracleNPPair` (certificate `pair x y ∈ W`);
embedding the slice into it needs a pairing-decoder OTM (future work).

## Proved vs pending

Every ✅ theorem is checked by `#print axioms` and uses only `propext`, `Classical.choice`, `Quot.sound`.

| Result | Status |
|---|---|
| `exists_oracle_diag` | ✅ proved |
| `OTM.unfold_eval/depth/maxLen` | ✅ proved |
| `poly_lt_two_pow_infinitely_often` | ✅ proved |
| `enumTree_depth_lt_two_pow`, `OracleP.exists_enum` | ✅ proved |
| **`queryLang_mem_OracleP`**, `queryOTM_decides` | ✅ **proved** |
| `testLang_mem_OracleNP` | ✅ proved |
| `testLang_not_mem_OracleP_bgs` | ✅ proved |
| **`bgs_separation : ∃ B, OracleP B ≠ OracleNP B`** | ✅ **proved** |
| **`OracleP_subset_OracleNP`** (relativized P ⊆ NP) | ✅ **proved** |
| `OracleNPSlice.lengthSymmetric` | ✅ proved |
| `bgs_collapse_of_bridges` (conditional collapse) | ✅ proved (takes bridges as hyps) |
| Natural-proofs lemmas (`Large.mono`, …) | ✅ proved |
| `P_ne_NP` | ⛔ open problem, `sorry` on purpose |
| `P_subset_NP` | 🟡 **blocked** on pairing-decoder TM (documented) |
| `bgs_collapse` | 🟡 `sorry` — needs the three PSPACE bridges below |
| `OracleP_tqbf_subset_PSPACE` | 🟡 `sorry` — oracle-TM space simulation |
| `PSPACE_subset_OracleP_tqbf` | 🟡 `sorry` — TQBF completeness |
| `OracleNPSlice_tqbf_subset_PSPACE` | 🟡 `sorry` — NPSPACE = PSPACE + simulation |
| Full `OracleNPPair` decoder (`pairYQueryOTM`) | 🟡 defined in plan; not yet proved |
| Full Razborov–Rudich theorem | 🟡 definition only; needs PRF security + DAG circuits |

## Framework readiness

**Usable for relativization-separation.** Complete, axiom-clean proof of BGS *separation*
under the upgraded verifier `OracleNP`, with `queryOTM` as a concrete oracle verifier.

**Partially ready for collapse.** The conditional theorem `bgs_collapse_of_bridges` is proved;
the three PSPACE bridge lemmas remain.

**Not ready for unrelativized `P ⊆ NP`.** Needs a pairing-decoder / product TM.

**Not ready for natural-proof barriers.** Needs DAG circuits and a PRF definition.

## Model notes
- Oracle machines in `OracleP` have state set `Fin k` and alphabet `Fin m`.
- Each oracle query costs one step; the query buffer is write-only and erased by a query.
- `queryOTM` copies its input to the buffer, asks the oracle, and accepts iff the answer is yes.

## 中文说明

本项目在 Lean 4 中形式化 P vs NP 以及相对化、自然证明两个障碍。

### `OracleNP` 定义（已升级）
```
OracleNP A = OracleP A ∪ OracleNPSlice A
```
- `OracleNPSlice`：存在 `W ∈ P^A` 与多项式 `q`，使得
  `x ∈ L ↔ ∃ y, |y|=q(|x|) ∧ y ∈ W`（对 `x` 内容无感的验证机片段）。
- 旧的「直接查预言机切片」是它的特例：已证明 `queryLang A = {y | A y} ∈ OracleP A`。
- 完整的 `pair x y` 验证机形式记为 `OracleNPPair`，解码 OTM 尚待完成。

### 已证明（无 sorry，只用三个标准公理）
- **`bgs_separation`**：存在预言机 B 使得 `P^B ≠ NP^B`；
- **`queryLang_mem_OracleP`** / `queryOTM`：具体验证机；
- **`OracleP_subset_OracleNP`**：相对化的 P ⊆ NP（由并集定义）；
- BGS 对角化核心、机器枚举、多项式低于指数、查询树展开；
- 条件化坍缩定理 `bgs_collapse_of_bridges`。

### 待完成 / 受阻
- `P_ne_NP`：公开难题，永久 sorry；
- `P_subset_NP`：**受阻于 pairing 解码图灵机**（已在源码中说明）；
- `bgs_collapse`：差三条 PSPACE 桥梁引理（预言机空间模拟、TQBF 完全性、NPSPACE=PSPACE）；
- `OracleNPPair` 的 pairing 解码 OTM；
- Razborov–Rudich 主定理（PRF + DAG 电路）。
