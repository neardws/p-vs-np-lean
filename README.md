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
| `PvsNP/Relativization.lean` | Oracle TMs; **`OracleNP = OracleP ∪ OracleNPSlice`** (verifier) |
| `PvsNP/Enumeration.lean` | Countable enumeration of `OracleP` machines |
| `PvsNP/OracleVerifiers.lean` | **`queryOTM`** fully proved |
| `PvsNP/Verifier.lean` | **`bgs_separation`** under verifier `OracleNP` ✅ |
| `PvsNP/Collapse.lean` | **`bgs_collapse`** via `upspaceOracle` (PSPACE-complete); 2 infrastructure sorries |
| `PvsNP/SpaceSim.lean` | `acceptsInSpace`, `PSPACE`, `upspaceOracle`, `tagQueryOTM` |
| `PvsNP/TagDecide.lean` | Tag-query / PSPACE bridges (4 infrastructure sorries) |
| `PvsNP/NaturalProofs.lean` | Circuits + Razborov–Rudich framework |
| `PvsNP/Pairing.lean` | `pair` / `doubled` lemmas |

## Definitions (key)

```
NP            = P ∪ NPViaVerifier
OracleNP A    = OracleP A ∪ OracleNPSlice A     -- VERIFIER form (project definition)
OracleNPSlice A = { L | ∃ W ∈ OracleP A, ∃ q, x ∈ L ↔ ∃ y, |y|=q(|x|) ∧ y ∈ W }
OracleNPRawSlice A = raw test-language fragment (retained; used in rawFragment sanity check)
PSPACE        = Fin-machines + acceptsInSpace
upspaceOracle = tagged poly-space acceptance (PSPACE-complete style)
```

## Proved vs pending

| Result | Status |
|---|---|
| `exists_oracle_diag`, `OTM.unfold_*` | ✅ |
| `queryLang_mem_OracleP`, `queryOTM_decides` | ✅ |
| `testLang_mem_OracleNPSlice` / `testLang_mem_OracleNP` | ✅ |
| **`bgs_separation : ∃ B, OracleP B ≠ OracleNP B`** | ✅ (verifier NP; axiom-clean) |
| **`OracleP_subset_OracleNP`**, **`P_subset_NP`** | ✅ |
| **`bgs_collapse_rawFragment`** (raw slice + trivial oracle) | ✅ axiom-clean sanity check |
| **`bgs_collapse`** (verifier NP + `upspaceOracle`) | 🟡 non-trivial oracle; depends on 2 PSPACE-simulation sorries |
| `tagQuery_after_tag`, `tagQueryOTM_decides` | 🟡 infrastructure |
| `OracleP_tqbf_subset_PSPACE`, `OracleNPSlice_tqbf_subset_PSPACE` | 🟡 (TagDecide copies; Collapse has its own) |
| `P_ne_NP` | ⛔ intentional open problem |

## Framework readiness

**Relativization — separation: complete** under verifier `OracleNP`.
Uses `testLang ∈ OracleNPSlice` via `queryLang ∈ OracleP`.

**Relativization — collapse: structured for verifier NP** with the PSPACE-complete
`upspaceOracle` (not the trivial raw-slice shortcut). The remaining obligations are
explicit Fin-machine simulations for `P^{PSPACE} ⊆ PSPACE` and certificate search
(`NPSPACE = PSPACE`). A fully axiom-clean raw-slice collapse is in `bgs_collapse_rawFragment`.

**Unrelativized `P ⊆ NP`: complete** under `NP = P ∪ NPViaVerifier`.

**Natural proofs: definitions ready; barrier theorem needs a PRF.**

## 中文说明

本项目在 Lean 4 中形式化 P vs NP 以及相对化、自然证明两个障碍。

### 定义
- **`OracleNP A = OracleP A ∪ OracleNPSlice A`**：预言机多项式时间验证器形式（证书由 `W ∈ OracleP A` 检查）。

### 已证明（分离侧无 sorryAx）
- **`bgs_separation`**：存在预言机 B 使得 `P^B ≠ NP^B`（验证器 `OracleNP`）
- **`queryOTM`**、对角化核心、机器枚举、`P_subset_NP`
- **`bgs_collapse_rawFragment`**：raw-slice + 常数真预言机的无 sorry 坍缩（对照用）

### 验证器坍缩（非平凡预言机 `upspaceOracle`）
- **`bgs_collapse`**：目标是 `P^A = NP^A`，A = PSPACE 完备风格的 `upspaceOracle`
- 仍缺：把 `OracleP` / `OracleNPSlice` 语言编译成 `SpaceDecider` 的有限状态模拟器（经典 `P^{PSPACE}⊆PSPACE` / `NPSPACE=PSPACE`）

### 故意保留的 sorry
- **`P_ne_NP`**：公开难题

### 基础设施 sorry（验证器坍缩路径）
1. `exists_PSPACE_decider_of_OracleP` / `exists_PSPACE_decider_of_slice`（Collapse）
2. `tagQuery_after_tag` / `tagQueryOTM_decides` / TagDecide 中两条 PSPACE 桥
