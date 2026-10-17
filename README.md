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
| **`bgs_collapse`** (verifier NP + `collapseA = upspaceOracle`) | 🟡 one bridge below |
| **`bgs_collapse_rawFragment`** | ✅ axiom-clean sanity check |
| `P_ne_NP` | ⛔ intentional open problem |

### Sole remaining bridge for verifier `bgs_collapse`

**`sliceLang_mem_OracleP_upspace`** — show
`{x | QueryKind.eval upspaceOracle (.slice j q) x = true} ∈ OracleP upspaceOracle`.

This is the classical fact `NP^{PSPACE} ⊆ P^{PSPACE}` (equivalently: a poly-time
existential over a `P^{PSPACE}` predicate is in `PSPACE`, hence in `P^{PSPACE}`
via one space tag).

**Next proof plan (honest, no fuel/fixed-point shortcuts):**

1. **Build a `SpaceDecider` for `sliceLang j q`.**
   - On input `x`, enumerate all certificates `y` of length `q(|x|)` (reuse space).
   - For each `y`, simulate `(enumDecider j).M` for `p(|y|)` steps.
   - On each oracle ask with buffer `w`: decode `tagEncode i z` (or reject the query);
     answer by running `acceptsInSpace (enumSpaceDecider i).M z (bound)`.
   - Accept iff some certificate run accepts.
2. **Space bound:** poly in `|x|` for the outer search + the nested space bound
   `|z|^d + d` with `|z| ≤ poly(|x|)`. Pick `SpaceDecider.d` large enough.
3. **Conclude:** that `SpaceDecider` witnesses `sliceLang j q ∈ PSPACE`;
   surjectivity of `enumSpaceDecider` gives an index `i` with
   `sliceLang j q = spaceLang i`; apply `spaceLang_mem_OracleP`.

The previous bridge `orun_upspace_iff_collapseA` was removed by setting
`collapseA = upspaceOracle`: languages in `OracleP collapseA` are already decided
under `upspaceOracle`, so the slice characterization matches `QueryKind.eval`
with no oracle-agreement lemma.

Until `sliceLang_mem_OracleP_upspace` is closed, `#print axioms bgs_collapse`
still lists `sorryAx`. **`bgs_separation` does not.**
**`tagQueryOTM_decides_oracle` does not.**

## Framework readiness

**Relativization — separation: complete** under verifier `OracleNP` (axiom-clean).

**Relativization — collapse: one classical PSPACE-closure bridge left**
(`sliceLang ∈ OracleP upspaceOracle`). Tag-query infrastructure is complete.

**Unrelativized `P ⊆ NP`: complete** under `NP = P ∪ NPViaVerifier`.

**Natural proofs: definitions ready; barrier theorem needs a PRF.**

## 中文说明

- **`OracleNP A = OracleP A ∪ OracleNPSlice A`**：验证器形式（项目定义）。
- **`bgs_separation`**：已无 `sorryAx`（验证器 `OracleNP`）。
- **`tagQueryOTM_decides_oracle`**：标签写入 + 拷贝循环 + 询问，已完整证明（公理干净）。
- **`bgs_collapse`**：`collapseA = upspaceOracle`；只剩一条桥
  `sliceLang_mem_OracleP_upspace`（即 `NP^{PSPACE} ⊆ P^{PSPACE}` 的形式化）。
- **`P_ne_NP`**：故意保留的公开问题 `sorry`。
