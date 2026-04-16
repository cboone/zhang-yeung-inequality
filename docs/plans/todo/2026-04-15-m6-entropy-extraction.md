# M6: Entropy Extraction from PFR

## Context

The Zhang-Yeung project depends on PFR (`teorth/pfr`) for Shannon entropy definitions and basic inequalities. PFR brings substantial unneeded machinery: Ruzsa distance, tau functional, group-theoretic entropy, Balog-Szemer\'edi-Gowers, and the full Freiman-Ruzsa proof. Only the `ForMathlib/Entropy/` subtree (and even then, only the non-group, non-Ruzsa portions) is relevant. M6 extracts the needed subset into a local `ZhangYeung/Entropy/` module, then removes the PFR dependency. The project will depend only on Mathlib.

M6 is fully independent of the main proof chain (M1-M5) and runs in parallel. It can begin as soon as M0 lands. The swap from PFR imports to local imports happens at the end; no milestone blocks on it.

## Prerequisites

- M0 complete: `lakefile.toml` with PFR dep, `lean-toolchain`, green build
- M1-M3 are not prerequisites. The eventual proof-side imports may refine the retained API surface, but M6 proceeds independently from M0 onward and can adjust if later milestones reveal a missing lemma.

## PFR Entropy Architecture

PFR's entropy code is organized in three layers, bottom to top:

```
Measure.lean              Hm[mu], Im[mu]           (pure measures)
  |
  v
Kernel/Basic.lean         Hk[kappa, mu]             (kernel entropy)
  |
  v
Kernel/MutualInfo.lean    Ik[kappa, mu]             (kernel mutual info)
  |
  v
Basic.lean                H[X], H[X|Y], I[X:Y], I[X:Y|Z]  (random variables)
```

The RV-level definitions are thin wrappers: `entropy X mu := Hm[mu.map X]`, `condEntropy X Y mu := (mu.map Y)[fun y => H[X | Y <- y ; mu]]`, etc. The nontrivial proofs live at the kernel level and are lifted to the RV level via bridge lemmas (`entropy_eq_kernel_entropy`, `condEntropy_eq_kernel_entropy`, `condMutualInfo_eq_kernel_mutualInfo`). We must preserve this three-layer structure for the proofs to work.

Each layer also has a `Group.lean` and `RuzsaDist.lean` variant that we do not need.

## API Surface Required by M1-M5

### Definitions (all four RV-level operators)

| Operator | PFR name | Notation |
|----------|----------|----------|
| Shannon entropy | `entropy` | `H[X ; mu]` |
| Conditional entropy | `condEntropy` | `H[X \| Y ; mu]` |
| Mutual information | `mutualInfo` | `I[X : Y ; mu]` |
| Conditional mutual information | `condMutualInfo` | `I[X : Y \| Z ; mu]` |

Plus the measure-level (`measureEntropy`, `measureMutualInfo`) and kernel-level (`Kernel.entropy`, `Kernel.mutualInfo`) definitions that underpin them.

### Shannon inequalities needed

**Nonnegativity:**

- `entropy_nonneg`, `condEntropy_nonneg`, `mutualInfo_nonneg`, `condMutualInfo_nonneg`

**Chain rules:**

- `chain_rule`, `chain_rule'`, `chain_rule''` (joint entropy = marginal + conditional)
- `cond_chain_rule`, `cond_chain_rule'` (conditional joint = conditional marginal + conditional)

**Submodularity:**

- `entropy_submodular` ($H[X \mid Y, Z] \le H[X \mid Z]$)
- `entropy_triple_add_entropy_le` ($H[X,Y,Z] + H[Z] \le H[X,Z] + H[Y,Z]$)

**Data processing:**

- `entropy_comp_le`, `mutual_comp_le`, `mutual_comp_comp_le`, `condMutual_comp_comp_le`

**Conditioning reduces entropy:**

- `condEntropy_le_entropy`

**Mutual information relations:**

- `mutualInfo_def`, `mutualInfo_comm`
- `mutualInfo_eq_entropy_sub_condEntropy`, `entropy_sub_condEntropy`
- `condMutualInfo_eq`, `condMutualInfo_eq'`

**Independence characterizations:**

- `mutualInfo_eq_zero` ($I[X:Y] = 0 \iff \text{IndepFun}$)
- `condMutualInfo_eq_zero` ($I[X:Y\mid Z] = 0 \iff \text{CondIndepFun}$)
- `ent_of_cond_indep` (entropy identity under conditional independence)
- `IndepFun.condEntropy_eq_entropy`

**Upper bounds:**

- `entropy_le_log_card`, `condEntropy_le_log_card`, `entropy_pair_le_add`

**Injective invariance:**

- `entropy_comp_of_injective`, `condEntropy_comp_of_injective`

**Kernel-level (needed for copy lemma proof):**

- `Kernel.entropy`, `Kernel.mutualInfo` definitions
- `Kernel.chain_rule`, `Kernel.chain_rule'`
- `Kernel.entropy_compProd`, `Kernel.entropy_compProd_deterministic`
- `Kernel.mutualInfo_nonneg`, `Kernel.entropy_map_le` (data processing)
- `Kernel.entropy_triple_add_entropy_le` (submodularity)

### Typeclasses and infrastructure

- `FiniteRange` (PFR-local; audit in Step 1 and copy to `ZhangYeung/ForMathlib/FiniteRange.lean` unless the pinned Mathlib now provides an equivalent)
- `IsZeroOrProbabilityMeasure` (audit in Step 1; if the pinned Mathlib still lacks it, vendor a minimal shim under `ZhangYeung/Mathlib/` before continuing)
- `FiniteSupport` (measure-side support class defined in `Measure.lean`; extracted as part of Step 2)
- `AEFiniteKernelSupport`, `FiniteKernelSupport` (kernel-support infrastructure from the kernel layer; audit in Step 1 and either keep in `Kernel/Basic.lean` or extract a tiny support file if that yields a cleaner dependency boundary)

## PFR Non-Entropy Dependencies

The entropy modules import these PFR-local files that are *not* part of the entropy subtree:

| PFR import | Used by | Content |
|------------|---------|---------|
| `PFR.ForMathlib.FiniteRange.Defs` | Measure.lean, Basic.lean | `FiniteRange` typeclass |
| `PFR.Mathlib.MeasureTheory.Measure.Dirac` | Measure.lean | Patches to `Measure.dirac` |
| `PFR.Mathlib.MeasureTheory.Measure.Real` | Measure.lean | `Measure.real` and properties |
| `PFR.Mathlib.Probability.UniformOn` | Measure.lean | `uniformOn` measure |
| `PFR.Mathlib.MeasureTheory.Integral.Bochner.Set` | Kernel/Basic.lean | Bochner integral patches |
| `PFR.Mathlib.Probability.Kernel.Disintegration` | Kernel/Basic.lean | Kernel disintegration patches |
| `PFR.Mathlib.Probability.Kernel.Composition.Comp` | Kernel/MutualInfo.lean | Kernel composition patches |
| `PFR.ForMathlib.ConditionalIndependence` | Basic.lean | `CondIndepFun` extensions |
| `PFR.ForMathlib.Uniform` | Basic.lean | Uniform distribution tools |
| `PFR.Mathlib.Probability.ConditionalProbability` | Basic.lean | Conditional probability patches |

Each of these must be handled during extraction. Strategy for each:

1. **Check Mathlib**: Has the content been upstreamed since PFR rev `80daaf1`? If so, replace with a direct Mathlib import.
2. **Copy with attribution**: If not upstreamed, copy the file into `ZhangYeung/Mathlib/` (or `ZhangYeung/ForMathlib/`), stripping anything we do not use.
3. **Inline**: For files that contribute only 1-2 lemmas, inline them into the consuming file rather than copying the whole file.

This audit is the most labor-intensive part of M6. Each file must be read, its contents checked against current Mathlib, and a decision made.

## Target File Layout

```
ZhangYeung/
  Entropy/
    Measure.lean              # measureEntropy, measureMutualInfo, FiniteSupport
    Kernel/
      Basic.lean              # Kernel.entropy, kernel-support classes, chain rules, data processing
      MutualInfo.lean         # Kernel.mutualInfo, submodularity
    Basic.lean                # H[X], H[X|Y] definitions and proofs
    MutualInfo.lean           # I[X:Y], I[X:Y|Z] definitions and proofs
  ForMathlib/                 # Lemmas not yet in Mathlib, designed for upstream
    FiniteRange.lean          # FiniteRange typeclass (if not yet upstreamed)
    ConditionalIndependence.lean  # CondIndepFun extensions (if needed)
  Mathlib/                    # Temporary Mathlib patches (from PFR.Mathlib.*)
    ...                       # Only files not yet upstreamed; deleted as Mathlib catches up
```

This is 5 core files plus a variable number of patch files. The roadmap estimated 4-6 files, 1500-2000 lines for the core; the patch files are temporary scaffolding.

The split between `Basic.lean` and `MutualInfo.lean` at the RV level mirrors PFR's internal organization within its single large `Basic.lean`. PFR's `Basic.lean` is approximately 1400-1600 lines; splitting it keeps each file manageable.

## Steps

### Step 1: Audit PFR Mathlib patches against current Mathlib

For each of the 10 PFR non-entropy dependencies listed above, plus the support items listed under "Typeclasses and infrastructure":

- Read the PFR file at the pinned rev (`80daaf1`)
- Grep current Mathlib (at the rev pinned in `lakefile.toml`) for each definition and lemma
- Record the defining file for each support class or helper lemma if it is not already one of the 10 imports above
- Classify as: (a) fully upstreamed, (b) partially upstreamed, (c) not upstreamed
- For (a): record the Mathlib import path
- For (b)/(c): mark for copying or reimplementation, including the target local home (`Measure.lean`, `Kernel/Basic.lean`, `ZhangYeung/ForMathlib/*`, or `ZhangYeung/Mathlib/*`)

**Output:** A table mapping each PFR patch/support item to its disposition and planned local home.

### Step 2: Create `ZhangYeung/Entropy/Measure.lean`

Fork `PFR/ForMathlib/Entropy/Measure.lean`. Strip:

- Everything related to `uniformOn` (only needed for PFR's Ruzsa distance proofs; if Zhang-Yeung tests need uniform entropy, add it back selectively)
- Any lemma not in the API surface list above

Keep:

- `measureEntropy` definition and notation `Hm[mu]`
- `measureMutualInfo` definition and notation `Im[mu]`
- `FiniteSupport` class
- `measureEntropy_nonneg`, `measureMutualInfo_nonneg`
- Sum formulas (`measureEntropy_eq_sum`, `measureEntropy_of_isProbabilityMeasure`)
- Upper bounds (`measureEntropy_le_log_card`)
- Zero/Dirac values
- Injective-map invariance (`measureEntropy_map_of_injective`)
- Product entropy (`measureEntropy_prod`)
- `measureMutualInfo_def`, `measureMutualInfo_swap`

Update imports to point to `ZhangYeung.Mathlib.*` or `ZhangYeung.ForMathlib.*` (for patch files) and to Mathlib directly (for upstreamed content).

Add a module docstring with attribution to PFR, a `## References` section citing both PFR and the Zhang-Yeung paper, and Mathlib-style `## Main definitions` / `## Main statements` sections.

### Step 3: Create `ZhangYeung/Entropy/Kernel/Basic.lean`

Fork `PFR/ForMathlib/Entropy/Kernel/Basic.lean`. Strip:

- Group-related items (none expected in this file, but verify)
- Any lemma not in the API surface list

Keep:

- `Kernel.entropy` definition and notation `Hk[kappa, mu]`
- `FiniteKernelSupport` and `AEFiniteKernelSupport`, plus the finite-support transfer lemmas needed by later files
- Basics: `entropy_zero_measure`, `entropy_zero_kernel`, `entropy_congr`, `entropy_nonneg`, `entropy_const`
- Injective maps: `entropy_map_of_injective`, `entropy_map_swap`, `entropy_swapRight`
- Chain rules: `entropy_compProd`, `chain_rule`, `chain_rule'`
- `entropy_compProd_deterministic`, `entropy_deterministic`
- Products: `entropy_prod`
- Data processing: `entropy_map_le`, `entropy_snd_le`, `entropy_fst_le`

### Step 4: Create `ZhangYeung/Entropy/Kernel/MutualInfo.lean`

Fork `PFR/ForMathlib/Entropy/Kernel/MutualInfo.lean`. Strip:

- Group-related items
- Anything Ruzsa-distance-related

Keep:

- `Kernel.mutualInfo` definition and notation `Ik[kappa, mu]`
- Basics: `mutualInfo_def`, `mutualInfo_zero_measure`, `mutualInfo_zero_kernel`, `mutualInfo_congr`, `mutualInfo_swapRight`
- Nonnegativity: `mutualInfo_nonneg'`, `mutualInfo_nonneg`
- Alternative expressions: `mutualInfo_eq_fst_sub`, `mutualInfo_eq_snd_sub`
- Submodularity: `entropy_condKernel_le_entropy_fst`, `entropy_condKernel_le_entropy_snd`, `entropy_submodular_compProd`, `entropy_triple_add_entropy_le`, `entropy_triple_add_entropy_le'`
- Independence: `mutualInfo_prod`, `entropy_condKernel_compProd_triple`

### Step 5: Create `ZhangYeung/Entropy/Basic.lean`

Fork the first half of `PFR/ForMathlib/Entropy/Basic.lean` (the `entropy` and `condEntropy` sections). Strip:

- Group-related imports and items
- Ruzsa-distance-related items
- Anything importing from `PFR.ForMathlib.Entropy.Group` or `PFR.ForMathlib.Entropy.RuzsaDist`

Keep:

- `entropy` definition and all `H[X ; mu]` notation variants
- `condEntropy` definition and all `H[X | Y ; mu]` notation variants
- `entropy_nonneg`, `condEntropy_nonneg`
- `entropy_le_log_card`, `condEntropy_le_log_card`
- `condEntropy_le_entropy`
- `entropy_comp_le`, `entropy_comp_of_injective`
- `condEntropy_comp_of_injective`
- `entropy_pair_le_add`
- Chain rules: `chain_rule`, `chain_rule'`, `chain_rule''`, `cond_chain_rule`, `cond_chain_rule'`
- Submodularity: `entropy_submodular`, `entropy_triple_add_entropy_le`
- Kernel bridges: `entropy_eq_kernel_entropy`, `condEntropy_eq_kernel_entropy`
- Independence: `IndepFun.condEntropy_eq_entropy`

### Step 6: Create `ZhangYeung/Entropy/MutualInfo.lean`

Fork the second half of `PFR/ForMathlib/Entropy/Basic.lean` (the `mutualInfo` and `condMutualInfo` sections, plus data processing). Strip:

- Group-related items
- Ruzsa-distance-related items

Keep:

- `mutualInfo` definition and notation
- `condMutualInfo` definition and notation
- `mutualInfo_def`, `mutualInfo_nonneg`, `mutualInfo_comm`
- `mutualInfo_eq_entropy_sub_condEntropy`, `mutualInfo_eq_entropy_sub_condEntropy'`, `entropy_sub_condEntropy`
- `mutualInfo_eq_zero` (independence characterization)
- `condMutualInfo_eq`, `condMutualInfo_eq'`, `condMutualInfo_nonneg`
- `condMutualInfo_eq_zero` (conditional independence characterization)
- `ent_of_cond_indep`
- Data processing: `mutual_comp_le`, `mutual_comp_comp_le`, `condMutual_comp_comp_le`
- Kernel bridge: `condMutualInfo_eq_kernel_mutualInfo`

### Step 7: Create patch files under `ZhangYeung/ForMathlib/` and `ZhangYeung/Mathlib/`

Based on the audit from Step 1:

- For each non-upstreamed PFR patch, create a corresponding file
- Strip to only the definitions and lemmas actually used by our entropy files
- Add attribution headers citing PFR
- Add `@[deprecated]` or TODO comments for items expected to arrive in Mathlib soon
- If the audit shows `IsZeroOrProbabilityMeasure` or similar glue is still missing from Mathlib, vendor the smallest viable shim here rather than leaving the dependency implicit

The most critical patch file is `FiniteRange.lean`. The `FiniteRange` typeclass is PFR's primary finiteness mechanism and appears in nearly every theorem signature. If it is not in Mathlib, we must copy it faithfully.

The other infrastructure decision that must be made explicit is kernel support. If keeping `FiniteKernelSupport` and `AEFiniteKernelSupport` inside `Kernel/Basic.lean` creates awkward imports, split out a tiny helper module and record that choice in the Step 1 audit table; otherwise keep them co-located with the kernel entropy definitions.

### Step 8: Build and test

- Run `bin/bootstrap-worktree` if in a fresh worktree
- Run `lake build ZhangYeung.Entropy.MutualInfo` (the leaf of the extraction dependency chain)
- Verify all extracted files compile with no errors and no `sorry`
- Run `lake lint` and fix any lint warnings

### Step 9: Integration with M1-M5

This step happens after M1-M3 have landed (or at least have stable import lists).

- In `ZhangYeung/Prelude.lean`, replace `import PFR.ForMathlib.Entropy.Basic` with imports of the local entropy modules
- Update any `open` declarations if namespaces changed
- Update M1-M5 files to import from `ZhangYeung.Entropy.*` instead of `PFR.*`
- Verify `lake build ZhangYeung` succeeds

### Step 10: Remove PFR dependency

- Remove the `[[require]] name = "PFR"` block from `lakefile.toml`
- Run `lake update` to regenerate the lockfile
- Run `lake build ZhangYeung` to confirm nothing still references PFR
- Run `lake lint`

### Step 11 (optional): Bridge to `shannon-entropy`

Prove a connecting lemma:

```lean
theorem entropyNat_eq_entropy (X : Omega -> S) (mu : Measure Omega)
    [IsProbabilityMeasure mu] [Fintype S] :
    entropyNat (toProbDist X mu) = H[X ; mu] := by
  ...
```

This bridges the `ProbDist`-based definitions in `cboone/shannon-entropy` with the measure-theoretic definitions extracted from PFR. Low priority; only valuable if both projects are used together.

## Phasing and Parallelism

Steps 1-7 are the core extraction work. They proceed sequentially (each file depends on the previous layer). Within each step, the work is: read PFR source, strip unneeded content, update imports, verify compilation.

Step 8 (build) runs after steps 2-7.

Step 9 (integration) blocks on M1-M3 having stable import lists, but the extraction itself (steps 1-8) does not.

Step 10 (PFR removal) is the final step, performed after integration is confirmed.

Step 11 (bridge) is independent and optional.

**Practical sequencing relative to M1-M5:**

- Begin steps 1-8 immediately after M0 lands
- Step 9 happens when M3 (Theorem 3) is drafted and its imports are stable
- Step 10 happens after step 9 is confirmed green
- During steps 1-8, M1-M5 continue to import PFR directly; no disruption

## Verification

- `lake build ZhangYeung` exits 0 with no PFR dependency in `lakefile.toml`
- `lake lint` exits 0
- All notation (`H[X ; mu]`, `H[X | Y ; mu]`, `I[X : Y ; mu]`, `I[X : Y | Z ; mu]`) works after `open ProbabilityTheory`
- Grep confirms zero `import PFR` matches in project `.lean` files
- Any remaining textual `PFR` mentions in `.lean` files are limited to attribution comments or docstrings, not live imports or code references
- CI workflow passes

## Files created

| File | Source | Content |
|------|--------|---------|
| `ZhangYeung/Entropy/Measure.lean` | Fork of `PFR/ForMathlib/Entropy/Measure.lean` | `measureEntropy`, `measureMutualInfo` |
| `ZhangYeung/Entropy/Kernel/Basic.lean` | Fork of `PFR/ForMathlib/Entropy/Kernel/Basic.lean` | `Kernel.entropy`, chain rules |
| `ZhangYeung/Entropy/Kernel/MutualInfo.lean` | Fork of `PFR/ForMathlib/Entropy/Kernel/MutualInfo.lean` | `Kernel.mutualInfo`, submodularity |
| `ZhangYeung/Entropy/Basic.lean` | Fork of first half of `PFR/ForMathlib/Entropy/Basic.lean` | `entropy`, `condEntropy` |
| `ZhangYeung/Entropy/MutualInfo.lean` | Fork of second half of `PFR/ForMathlib/Entropy/Basic.lean` | `mutualInfo`, `condMutualInfo`, DPI |
| `ZhangYeung/ForMathlib/FiniteRange.lean` | Fork of `PFR/ForMathlib/FiniteRange/Defs.lean` | `FiniteRange` typeclass |
| `ZhangYeung/ForMathlib/ConditionalIndependence.lean` | Fork of `PFR/ForMathlib/ConditionalIndependence.lean` | `CondIndepFun` extensions |
| `ZhangYeung/Mathlib/*.lean` | Forks of `PFR/Mathlib/*.lean` | Temporary Mathlib patches |

The exact set of `ZhangYeung/Mathlib/*.lean` files depends on the Step 1 audit. Expect 3-6 files initially, shrinking to 0 as Mathlib catches up.

## Files modified

| File | Change |
|------|--------|
| `ZhangYeung/Prelude.lean` | Replace PFR imports with local entropy imports |
| `lakefile.toml` | Remove PFR dependency |
| `ZhangYeung.lean` | Update imports if needed |

## Risks

### PFR Mathlib patches not yet upstreamed (moderate-high)

The most labor-intensive risk. If many `PFR.Mathlib.*` patches are not yet in Mathlib, we must copy and maintain them. Each patch file adds maintenance burden and potential version-drift issues.

**Mitigation:** The audit in Step 1 determines the scope early. Patches that are close to upstream (open Mathlib PRs) can be marked with TODOs and replaced when they land. The `ZhangYeung/Mathlib/` directory is explicitly temporary.

### `FiniteRange` typeclass design mismatch (moderate)

`FiniteRange` is central to PFR's entropy API. If Mathlib adopts a different finiteness mechanism (e.g., `Finite (Set.range X)` or a `Countable` + `FiniteSupport` approach), our extracted code may need nontrivial refactoring.

**Mitigation:** Mathlib PR #34773 (Shannon entropy for PMFs) uses `Fintype` directly. Monitor its design decisions. If `FiniteRange` diverges from Mathlib's direction, plan a refactor as part of M7 (polish).

### PFR internal API changes (low)

We pin PFR at rev `80daaf1`. The extraction reads PFR source at that rev. After extraction, PFR can change freely since we no longer depend on it.

### Large file sizes (low)

PFR's `Basic.lean` is approximately 1400-1600 lines. Splitting it into `Basic.lean` (entropy, condEntropy) and `MutualInfo.lean` (mutualInfo, condMutualInfo, data processing) keeps each file under 800 lines.

### Namespace collisions (low)

PFR's entropy definitions live in `ProbabilityTheory`. Our extracted code uses the same namespace for Mathlib compatibility. No collision expected since PFR will no longer be imported.

**Mitigation:** After removing PFR, grep for any residual namespace conflicts.
