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
| `PvsNP/Complexity.lean` | `P`, `NP = P ∪ NPViaVerifier`, `coNP`, `SAT`, **`P_subset_NP` ✅** |
| `PvsNP/Main.lean` | `P_ne_NP` (intentional `sorry`) |
| `PvsNP/QueryDiag.lean` | Query trees + BGS diagonalization core |
| `PvsNP/PolyBound.lean` | `p(n) < 2ⁿ` infinitely often |
| `PvsNP/Relativization.lean` | Oracle TMs, `OracleP`, `OracleNP` |
| `PvsNP/Enumeration.lean` | Countable enumeration of `OracleP` machines |
| `PvsNP/OracleVerifiers.lean` | **`queryOTM`** fully proved |
| `PvsNP/Verifier.lean` | **`bgs_separation`**, `OracleP ⊆ OracleNP` |
| `PvsNP/SpaceSim.lean` | `acceptsInSpace`, `PSPACE`, `upspaceOracle`, `tagQueryOTM` |
| `PvsNP/TagDecide.lean` | `spaceLang_mem_OracleP` (decides lemma pending) |
| `PvsNP/Collapse.lean` | **`bgs_collapse`**, PSPACE bridges |
| `PvsNP/NaturalProofs.lean` | Circuits + **`DagCircuit`**, Razborov–Rudich framework |
| `PvsNP/Pairing.lean` | `pair` / `doubled` lemmas |

## Definitions (key)

```
NP            = P ∪ NPViaVerifier          -- parallel to OracleNP
OracleNP A    = OracleP A ∪ OracleNPSlice A
PSPACE        = languages given by Fin-machines + acceptsInSpace
upspaceOracle = answers tagged queries 1ⁱ01x for enumerated space-machines
```

## Proved vs pending

Every ✅ theorem below is checked by `#print axioms` and uses only `propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`).

| Result | Status |
|---|---|
| `exists_oracle_diag`, `OTM.unfold_*` | ✅ |
| `poly_lt_two_pow_infinitely_often`, `enumTree_*` | ✅ |
| **`queryLang_mem_OracleP`**, `queryOTM_decides` | ✅ |
| `testLang_mem_OracleNP`, `testLang_not_mem_OracleP_bgs` | ✅ |
| **`bgs_separation : ∃ B, OracleP B ≠ OracleNP B`** | ✅ |
| **`OracleP_subset_OracleNP`**, **`P_subset_NP`** | ✅ |
| `bgs_collapse_of_bridges` (conditional) | ✅ |
| `PSPACE_subset_OracleP_tqbf` (modulo `tagQueryOTM_decides`) | 🟡 |
| **`bgs_collapse : ∃ A, OracleP A = OracleNP A`** | 🟡 *stated; depends on 3 simulation lemmas* |
| Natural-proofs lemmas + `DagCircuit` / `Gate` | ✅ definitions + basic lemmas |
| `P_ne_NP` | ⛔ open problem, `sorry` on purpose |
| `tagQuery_after_tag`, `tagQueryOTM_decides` | 🟡 simulation (machine defined) |
| `OracleP_tqbf_subset_PSPACE` | 🟡 universal space simulation |
| `OracleNPSlice_tqbf_subset_PSPACE` | 🟡 witness enumeration in poly space |
| `P ⊆ NPViaVerifier` (pairing decoder) | 🟡 future work (not a `sorry` theorem) |
| Full Razborov–Rudich for a concrete PRF | 🟡 needs PRF definition |

## Framework readiness

**Relativization — separation: complete.** Fully proved, axiom-clean.

**Relativization — collapse: scaffold complete, three simulation lemmas remain.**
- Oracle = `upspaceOracle` (universal space language; tagged queries).
- Bridge `PSPACE ⊆ OracleP` is reduced to `tagQueryOTM_decides` (machine `tagQueryOTM` is defined).
- Bridges `OracleP ⊆ PSPACE` and `OracleNPSlice ⊆ PSPACE` are the classical
  “simulate oracle machine / enumerate witnesses in poly space” arguments; Fin-machine
  tables for the universal simulator are not yet written out.
- Conditional theorem `bgs_collapse_of_bridges` is fully proved.

**Unrelativized `P ⊆ NP`: complete** under the union definition `NP = P ∪ NPViaVerifier`
(matching `OracleNP`). The stronger embedding into `NPViaVerifier` alone still needs a
pairing-decoder TM.

**Natural proofs: definitions + DAG shape ready; barrier theorem needs a PRF.**

## 中文说明

本项目在 Lean 4 中形式化 P vs NP 以及相对化、自然证明两个障碍。

### 已证明（无 sorryAx）
- **`bgs_separation`**：存在预言机 B 使得 `P^B ≠ NP^B`
- **`P_subset_NP`**：`NP = P ∪ NPViaVerifier`（与相对化定义平行）
- **`queryOTM`**、对角化核心、机器枚举、条件化坍缩定理
- DAG 电路形状 `DagCircuit` / `Gate`

### 坍缩路径（`bgs_collapse`）
- 预言机：`upspaceOracle`（带标签的通用空间语言）
- **已完成**：`PSPACE` 定义、`tagQueryOTM` 机器、条件定理、`bgs_collapse` 陈述
- **仍为 simulation sorry**（3+2）：
  1. `tagQuery_after_tag` / `tagQueryOTM_decides`（标签写入 + 复制，对标已证的 `queryOTM`）
  2. `OracleP_tqbf_subset_PSPACE`（通用空间模拟）
  3. `OracleNPSlice_tqbf_subset_PSPACE`（指数枚举证书、多项式空间）

### 故意保留的 sorry
- **仅** `P_ne_NP` 作为公开难题

### 待办（非 sorry 定理）
- pairing 解码图灵机 ⇒ `P ⊆ NPViaVerifier`
- 具体 PRF + Razborov–Rudich 主定理
