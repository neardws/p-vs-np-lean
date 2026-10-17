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
| `PvsNP/TagDecide.lean` | Tag-writing proved; `tagQuery_after_tag` ✅; copy+ask bridge |
| `PvsNP/Collapse.lean` | Verifier `bgs_collapse` scaffold via `collapseA` |
| `PvsNP/NaturalProofs.lean` | Circuits + Razborov–Rudich framework |

## Definitions (key)

```
NP            = P ∪ NPViaVerifier
OracleNP A    = OracleP A ∪ OracleNPSlice A     -- VERIFIER form (project definition)
OracleNPSlice A = { L | ∃ W ∈ OracleP A, ∃ q, x ∈ L ↔ ∃ y, |y|=q(|x|) ∧ y ∈ W }
collapseA     = QueryKind tags evaluated against upspaceOracle
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
| **`tagQuery_after_tag`**, **`tagWriting_orun`** | ✅ axiom-clean |
| **`PSPACE_subset_OracleP_tqbf`** | 🟡 needs `tagQueryOTM_decides_oracle` |
| **`bgs_collapse`** (verifier NP + `collapseA`) | 🟡 depends on 2 bridges below |
| **`bgs_collapse_rawFragment`** | ✅ axiom-clean sanity check |
| `P_ne_NP` | ⛔ intentional open problem |

### Remaining bridges for verifier `bgs_collapse` (why blocked)

1. **`tagQueryOTM_decides_oracle`** — copy-loop + ask after the proved tag prefix.
   Pure TM reasoning; no theory gap. Needed so one-query machines sit in `OracleP`.

2. **`orun_upspace_iff_collapseA`** — show `enumDecider j` accepts under `collapseA`
   iff under `upspaceOracle`.  
   **Why this is hard:** `collapseA` properly extends `upspaceOracle` with slice/relative
   tags. A poly-time OTM in `OracleP collapseA` may query those extra tags, so the two
   oracles can disagree on a run. Proving agreement (or compiling the machine down to
   Fin space) is the classical `P^{PSPACE} ⊆ PSPACE` content. Fuel/limit encodings were
   explored; Bool-monotone fuel alone does not make OTM acceptance monotone, so the
   limit oracle does not automatically validate the fixed-point equation for relative
   codes.

Until both are closed, `#print axioms bgs_collapse` still lists `sorryAx`.
`bgs_separation` does **not**.

## Framework readiness

**Relativization — separation: complete** under verifier `OracleNP` (axiom-clean).

**Relativization — collapse: structured for verifier NP** with non-trivial `collapseA`
(QueryKind tags / PSPACE-complete style), not the trivial raw-slice shortcut.
Raw-slice collapse remains available as `bgs_collapse_rawFragment` (axiom-clean).

**Unrelativized `P ⊆ NP`: complete** under `NP = P ∪ NPViaVerifier`.

**Natural proofs: definitions ready; barrier theorem needs a PRF.**

## 中文说明

- **`OracleNP A = OracleP A ∪ OracleNPSlice A`**：验证器形式（项目定义）。
- **`bgs_separation`**：已无 `sorryAx`（验证器 `OracleNP`）。
- **`tagQuery_after_tag`**：标签写入已完整证明。
- **`bgs_collapse`**：验证器坍缩骨架已接上 `collapseA`；仍差两条桥
  （`tagQuery` 拷贝/询问、以及 `collapseA` vs `upspaceOracle` 的 `orun` 一致性）。
- **`P_ne_NP`**：故意保留的公开问题 `sorry`。
