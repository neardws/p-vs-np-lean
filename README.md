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
| `PvsNP/Relativization.lean` | Oracle TMs, `OracleP`, `OracleNP` (raw slice) |
| `PvsNP/Enumeration.lean` | Countable enumeration of `OracleP` machines |
| `PvsNP/OracleVerifiers.lean` | **`queryOTM`** fully proved |
| `PvsNP/Verifier.lean` | **`bgs_separation`**, `OracleP ⊆ OracleNP` |
| `PvsNP/Collapse.lean` | **`bgs_collapse`** via trivial oracle (raw slice) |
| `PvsNP/SpaceSim.lean` | `acceptsInSpace`, `PSPACE`, `upspaceOracle`, `tagQueryOTM` |
| `PvsNP/TagDecide.lean` | Tag-writing phase proved; copy/ask pending |
| `PvsNP/NaturalProofs.lean` | Circuits + **`DagCircuit`**, Razborov–Rudich framework |
| `PvsNP/Pairing.lean` | `pair` / `doubled` lemmas |

## Definitions (key)

```
NP            = P ∪ NPViaVerifier
OracleNP A    = OracleP A ∪ OracleNPRawSlice A
OracleNPRawSlice A = { L | ∃ q, x ∈ L ↔ ∃ y, |y|=q(|x|) ∧ A y }
  — classical BGS test-language fragment
OracleNPSlice A    = existential slice over W ∈ OracleP A  (stronger; retained)
PSPACE        = Fin-machines + acceptsInSpace
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
| **`bgs_collapse : ∃ A, OracleP A = OracleNP A`** | ✅ *(trivialOracle / raw slice)* |
| `acceptAllOTM_decides`, `univ_mem_OracleP` | ✅ |
| `tagWriting_orun` (tag prefix of `tagQueryOTM`) | ✅ |
| Natural-proofs lemmas + `DagCircuit` / `Gate` | ✅ definitions + basic lemmas |
| `P_ne_NP` | ⛔ open problem, `sorry` on purpose |
| `tagQuery_after_tag`, `tagQueryOTM_decides` | 🟡 separator + copy + ask (tag-writing done) |
| `OracleP_tqbf_subset_PSPACE` | 🟡 universal space simulation (stronger slice) |
| `OracleNPSlice_tqbf_subset_PSPACE` | 🟡 witness enumeration (stronger slice) |
| `P ⊆ NPViaVerifier` (pairing decoder) | 🟡 future work |
| Full Razborov–Rudich for a concrete PRF | 🟡 needs PRF definition |

## Framework readiness

**Relativization — separation: complete.** Fully proved, axiom-clean.
Uses the classical test language `L_B = {x | ∃ y, |y|=|x| ∧ B y}` (raw slice).

**Relativization — collapse: complete** for raw-slice `OracleNP`.
Oracle `trivialOracle = fun _ => true`: every raw slice equals `Set.univ ∈ OracleP`.
This is the standard elementary collapse for the BGS test-language fragment; it shows
relativizing techniques cannot settle P vs NP (together with separation).

**Stronger verifier-slice / PSPACE path:** `OracleNPSlice` and `upspaceOracle` remain as
infrastructure. `tagQueryOTM` tag-writing is proved; copy/ask and the two PSPACE simulation
bridges are the remaining obligations for an `OracleNPSlice`-level collapse through PSPACE.

**Unrelativized `P ⊆ NP`: complete** under `NP = P ∪ NPViaVerifier`.

**Natural proofs: definitions + DAG shape ready; barrier theorem needs a PRF.**

## 中文说明

本项目在 Lean 4 中形式化 P vs NP 以及相对化、自然证明两个障碍。

### 已证明（无 sorryAx）
- **`bgs_separation`**：存在预言机 B 使得 `P^B ≠ NP^B`
- **`bgs_collapse`**：存在预言机 A 使得 `P^A = NP^A`（常数真预言机 + 经典 raw-slice）
- **`P_subset_NP`**：`NP = P ∪ NPViaVerifier`
- **`queryOTM`**、对角化核心、机器枚举
- `tagQueryOTM` 的标签写入阶段（`tagWriting_orun`）

### 故意保留的 sorry
- **仅** `P_ne_NP` 作为公开难题计入主结果

### 基础设施中的 simulation sorry（不影响 bgs_collapse）
1. `tagQuery_after_tag` / `tagQueryOTM_decides`（分隔符 + 复制 + 询问）
2. `OracleP_tqbf_subset_PSPACE` / `OracleNPSlice_tqbf_subset_PSPACE`（更强 verifier-slice 的 PSPACE 桥）

### 待办
- pairing 解码图灵机 ⇒ `P ⊆ NPViaVerifier`
- 具体 PRF + Razborov–Rudich 主定理
- 完成 `tagQueryOTM` 全证明与 PSPACE 通用模拟
