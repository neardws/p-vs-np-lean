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
| `PvsNP/SpaceSim.lean` | `PSPACE`, `upspaceOracle`, `QueryKind`, `tagQueryOTM` |
| `PvsNP/TagDecide.lean` | **`tagQueryOTM_decides_oracle` ✅** (tag + copy + ask) |
| `PvsNP/Collapse.lean` | Verifier `bgs_collapse` via `collapseA = upspaceOracle` |
| `PvsNP/NaturalProofs.lean` | Circuits + Razborov–Rudich framework |

## Definitions (key)

```
NP            = P ∪ NPViaVerifier
OracleNP A    = OracleP A ∪ OracleNPSlice A     -- VERIFIER form (project definition)
OracleNPSlice A = { L | ∃ W ∈ OracleP A, ∃ q, x ∈ L ↔ ∃ y, |y|=q(|x|) ∧ y ∈ W }
collapseA     = upspaceOracle                   -- PSPACE tag oracle
PSPACE        = Fin-machines + acceptsInSpace
```

## Proved vs pending

| Result | Status |
|---|---|
| `exists_oracle_diag`, `OTM.unfold_*` | ✅ |
| `queryLang_mem_OracleP`, `queryOTM_decides` | ✅ |
| `testLang_mem_OracleNP` / `testLang_not_mem_OracleP_bgs` | ✅ |
| **`bgs_separation : ∃ B, OracleP B ≠ OracleNP B`** | ✅ (verifier NP; axiom-clean) |
| **`OracleP_subset_OracleNP`**, **`P_subset_NP`** | ✅ |
| **`tagQuery_after_tag`**, **`tagWriting_orun`** | ✅ |
| **`tagQueryOTM_decides_oracle`**, **`spaceLang_mem_OracleP`** | ✅ axiom-clean |
| **`PSPACE_subset_OracleP_tqbf`** | ✅ axiom-clean |
| **`bgs_collapse`** (verifier NP + `collapseA = upspaceOracle`) | 🟡 `exists_slice_space_decider` |
| **`bgs_collapse_rawFragment`** | ✅ axiom-clean sanity check |
| `P_ne_NP` | ⛔ intentional open problem |

### Sole remaining bridge for verifier `bgs_collapse`

**`exists_slice_space_decider`** → **`sliceLang_mem_OracleP_upspace`** → **`bgs_collapse`**.

Semantic lemmas in `PvsNP/Collapse.lean` (axiom-clean):
- `mem_sliceLang_iff_exists_relative` — slice ↔ ∃ certificate in `relativeLang j`
- `query_maxLen_le_budget` — poly-time OTM queries have length ≤ time budget
- `sliceLang_mem_OracleP_of_space_decider` — any matching `SpaceDecider` lands in `OracleP`

**Gap (one `sorry`):** compile the classical `NP^{PSPACE} ⊆ PSPACE` simulator to an
explicit `SpaceDecider` (or an equivalent certificate-search `OTM` with oracle
passthrough to `upspaceOracle`):

1. Enumerate `y ∈ {0,1}^{q(|x|)}` reusing space.
2. Simulate `enumDecider j` for `p(|y|)` steps; answer space-tags via nested
   `acceptsInSpace` (or passthrough asks if building an `OTM` directly).
3. Accept iff some certificate accepts; set `d = sliceSpaceDegree j q`.

Until that TM/`OTM` table exists, `#print axioms bgs_collapse` lists `sorryAx`.
**`bgs_separation` does not. `tagQueryOTM_decides_oracle` does not.**

Alternative formalization path (not started): length-well-founded **hard-slice tag**
oracle + `sliceTagOTM` (write pad + header + `x`, one ask) — avoids a universal
space simulator but needs a variable-length padding writer `OTM` and WF oracle lemmas.

## Framework readiness

**Relativization — separation: complete** under verifier `OracleNP` (axiom-clean).

**Relativization — collapse: one classical PSPACE-closure bridge left**
(`exists_slice_space_decider` / `NP^{PSPACE} ⊆ PSPACE` as an explicit `TM`).
Semantic lemmas and `sliceLang_mem_OracleP_of_space_decider` are done; tag-query
infrastructure is complete.

**Unrelativized `P ⊆ NP`: complete** under `NP = P ∪ NPViaVerifier`.

**Natural proofs: definitions ready; barrier theorem needs a PRF.**

## 中文说明

- **`OracleNP A = OracleP A ∪ OracleNPSlice A`**：验证器形式（项目定义）。
- **`bgs_separation`**：已无 `sorryAx`（验证器 `OracleNP`）。
- **`tagQueryOTM_decides_oracle`**：标签写入 + 拷贝循环 + 询问，已完整证明（公理干净）。
- **`bgs_collapse`**：`collapseA = upspaceOracle`；只剩 `exists_slice_space_decider`
  （把 `NP^{PSPACE} ⊆ PSPACE` 编成显式 `SpaceDecider` / 直通 `OTM`）。语义引理已齐。
- **`P_ne_NP`**：故意保留的公开问题 `sorry`。
