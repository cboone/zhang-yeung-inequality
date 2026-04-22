---
title: "Replace `native_decide` in `shannonCone_of_witness` with a structural submodularity proof"
created: 2026-04-21
status: done
branch: main
roadmap: docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md
depends_on: `docs/plans/done/2026-04-21-finite-fintype-pfr-alignment-and-native-decide-removal.md`; current `main` with `Delta`, `CopyLemma`, `Theorem2`, `Theorem3`, `EntropyRegion`, and the entropy-function bridge in `Theorem4` already aligned to PFR-style `[Finite]` assumptions.
---

## Status

Done. `ZhangYeung/Theorem4.lean` now proves witness submodularity structurally, not via `native_decide`. The landed proof follows the plan's preferred route: it decomposes `F_witness_ℚ` into `baseWitness + pairBonus`, proves submodularity for the cardinality-based base piece, isolates the exceptional-pair behavior through local helper lemmas, and reassembles the full witness proof in `F_witness_ℚ_submodular` before feeding that into `shannonCone_of_witness`. Only bounded `decide` checks remain in local canonicalization lemmas and in the concrete witness-evaluation tests.

## Context

The remaining proof obligation is the submodularity clause in:

```lean
theorem shannonCone_of_witness : shannonCone F_witness
```

namely

```lean
∀ α β : Finset (Fin 4),
  F_witness_ℚ (α ∪ β) + F_witness_ℚ (α ∩ β) ≤ F_witness_ℚ α + F_witness_ℚ β.
```

The witness values are:

- `0` on `∅`
- `2` on singletons
- `4` on `{0, 1}`
- `3` on the other two-element subsets
- `4` on triples and the full four-set

The mathematical point is simple: the witness is almost a concave cardinality function, with one exceptional two-element subset `{0, 1}` bumped from `3` to `4`. The remaining task is to formalize that statement in a way that is stable and Mathlib-quality, rather than handing the entire 256-case verification to the evaluator.

## Goal

Remove the last `native_decide` in `ZhangYeung/Theorem4.lean` by replacing the quantified submodularity proof of `F_witness_ℚ` with a structural proof that is:

1. readable to a reviewer,
2. robust under minor elaborator changes,
3. independent of `native_decide`. Small, bounded `decide` checks inside local sublemmas with a conceptually transparent statement (e.g., "the four subsets of `{0,1}` are `∅, {0}, {1}, {0,1}`") remain acceptable; the prohibition is on `native_decide`, not on kernel-reducing decidable instances in general.

The preferred end state is:

- no `native_decide` in the library `ZhangYeung` code;
- test-side concrete witness evaluations may continue to use `decide`;
- `lake lint` stays green.

## Non-goals

- No change to the mathematical witness itself.
- No change to the public theorems `theorem4_finite`, `theorem4`, or `theorem4_ge_four` beyond their proof terms.
- No attempt to remove `decide` from the concrete witness-value tests; the target here is the remaining quantified proof only.
- No prohibition on `decide` inside local sublemmas. `decide` is an accepted Mathlib-style tactic for small, decidable, bounded finite checks; the policy target is specifically `native_decide`.
- No heavy new abstraction layer unless the structural proof clearly benefits from it.

## Design sketch

### Route A (preferred): decompose the witness into simple set functions

#### Step 0: canonicalization helpers

Before the decomposition proper, pin down a few canonicalizing lemmas for the exceptional pair. These prevent the `{0,1}` vs `insert 0 {1}` vs `insert 1 {0}` normal-form divergence that bit the earlier `fin_cases` attempt listed under §Status.

```lean
private def pair01 : Finset (Fin 4) := {0, 1}

private lemma pair01_eq :
    pair01 = ({0, 1} : Finset (Fin 4)) := by decide

private lemma mem_pair01 :
    ∀ i : Fin 4, i ∈ pair01 ↔ i = 0 ∨ i = 1 := by decide

private lemma pair01_card : pair01.card = 2 := by decide
```

Use these as rewrites wherever the literal `{0, 1}` appears in a goal.

#### Decomposition

Decompose `F_witness_ℚ` as a sum of four pieces on `Finset (Fin 4)`:

1. the cardinality term `card(S)`;
2. a nonempty bonus `1_{S ≠ ∅}`;
3. a full-set penalty `-1_{S = univ}`;
4. an exceptional pair bonus `1_{S = pair01}`.

Concretely, prove a lemma of the form:

```lean
F_witness_ℚ S = (S.card : ℚ) + nonemptyBonus S - fullBonus S + pairBonus S
```

where:

- `nonemptyBonus S = if S.Nonempty then (1 : ℚ) else 0`
- `fullBonus S = if S = Finset.univ then (1 : ℚ) else 0`
- `pairBonus S = if S = pair01 then (1 : ℚ) else 0`

All three indicators are `ℚ`-valued from the start so no coercion noise appears in the decomposition lemma.

This representation is mathematically transparent:

- the cardinality profile `0, 2, 3, 4, 4` is exactly `card + nonemptyBonus - fullBonus`;
- the special value `F({0,1}) = 4` is the extra `pairBonus` term.

### Step 1: prove the base cardinality profile is submodular

Let

```lean
private def baseWitness (S : Finset (Fin 4)) : ℚ :=
  (S.card : ℚ) + nonemptyBonus S - fullBonus S
```

(The `(S.card : ℚ)` cast is explicit so no `Nat`-vs-`ℚ` arithmetic leaks into the submodularity goal.) Prove the three components separately.

#### 1a. `card` is modular

Use the standard identity:

```lean
card (α ∪ β) + card (α ∩ β) = card α + card β.
```

This should be a one-line `norm_num`-friendly cast from `Finset.card_union_add_card_inter`.

#### 1b. `nonemptyBonus` is submodular

Prove:

```lean
nonemptyBonus (α ∪ β) + nonemptyBonus (α ∩ β) ≤ nonemptyBonus α + nonemptyBonus β.
```

This is boolean logic:

- if `α ∩ β` is nonempty, then both `α` and `β` are nonempty;
- if `α ∪ β` is nonempty, at least one of `α`, `β` is nonempty.

This should be done by short case splits on `α = ∅` and `β = ∅`, or equivalent `by_cases hα : α.Nonempty`, `by_cases hβ : β.Nonempty`.

Indicative shape (the four leaf goals reduce to `ℚ` arithmetic between `0` and `1` and close by `norm_num`):

```lean
private lemma nonemptyBonus_submodular (α β : Finset (Fin 4)) :
    nonemptyBonus (α ∪ β) + nonemptyBonus (α ∩ β)
      ≤ nonemptyBonus α + nonemptyBonus β := by
  by_cases hα : α.Nonempty <;> by_cases hβ : β.Nonempty <;>
    simp [nonemptyBonus, hα, hβ, Finset.union_nonempty,
          Finset.inter_nonempty, Finset.not_nonempty_iff_eq_empty] <;>
    -- remaining goals are concrete `ℚ` comparisons like `1 + 0 ≤ 1 + 1`
    norm_num
```

Steps 1c and 2 follow the same template: case split on the relevant set predicates, `simp` the indicator definitions through, close numeric residues with `norm_num`.

#### 1c. `- fullBonus` is submodular

Equivalently, `fullBonus` is supermodular:

```lean
fullBonus α + fullBonus β ≤ fullBonus (α ∪ β) + fullBonus (α ∩ β).
```

This is also structural:

- if `α = univ` or `β = univ`, then `α ∪ β = univ`;
- if both are `univ`, then `α ∩ β = univ` as well.

Again, short case splits on `α = univ`, `β = univ` should suffice.

Combining 1a-1c yields a lemma:

```lean
baseWitnessSubmodular :
  baseWitness (α ∪ β) + baseWitness (α ∩ β) ≤ baseWitness α + baseWitness β
```

with `baseWitness = card + nonemptyBonus - fullBonus`.

### Step 2: isolate the exceptional pair defect

The pair bonus `pairBonus` is not submodular by itself. For example, with `α = {0}` and `β = {1}`:

```text
pairBonus(α ∪ β) + pairBonus(α ∩ β) = 1 + 0 > 0 = pairBonus α + pairBonus β.
```

So we need to classify exactly when the pair bonus creates a positive defect.

Define the defect:

```lean
pairBonusDefect α β := pairBonus (α ∪ β) + pairBonus (α ∩ β) - pairBonus α - pairBonus β
```

Prove that `pairBonusDefect α β` is positive only in two families.

#### 2a. Union hits the exceptional pair

If:

- `α ∪ β = pair01`, and
- neither `α` nor `β` equals `pair01`,

then necessarily `α = {0}` and `β = {1}`, or the swap.

In exactly that case, the `nonemptyBonus` gap contributes the needed slack `1`.

#### 2b. Intersection hits the exceptional pair

If:

- `α ∩ β = pair01`, and
- neither `α` nor `β` equals `pair01`,

then necessarily `α` and `β` are the two distinct three-element supersets of `pair01`:

- `{0,1,2}` and `{0,1,3}`.

In exactly that case, the `fullBonus` term contributes the needed slack `1`, because the union is `univ`.

The crucial point is that these are the only positive-defect configurations.

### Step 3: combine the pieces

Write:

```lean
F_witness_ℚ = baseWitness + pairBonus
```

as a small lemma `F_witness_ℚ_eq_base_add_pair`, discharged by `fin_cases S` or equivalently a 16-case `decide` on `S : Finset (Fin 4)` (bounded `decide` per §Non-goals).

Then in the final submodularity proof:

1. expand both sides using the decomposition lemma;
2. use `baseWitnessSubmodular` for the cardinality-profile part;
3. use the two classification lemmas to show that any positive pair-bonus defect is absorbed by the base slack.

The proof should no longer need either `native_decide` or a 256-case brute force split.

#### Alternative phrasing if indicator algebra gets noisy

If the four-indicator decomposition produces unwieldy `simp` sets (e.g., many spurious `ite` residues), collapse to a single definition

```lean
private def baseWitness' (S : Finset (Fin 4)) : ℚ := F_witness_ℚ S - pairBonus S
```

and prove `baseWitness'_submodular` directly by whatever combination of case analysis the four-indicator route would have used. The structural argument is the same; only the definitional packaging changes. Use this only if the four-indicator form proves to be heavier in `simp`/rewrite cost than the savings it brings in structural clarity.

### Route B (fallback): small explicit case table, but only for the exceptional defect

If the classification lemmas in Step 2 become awkward to phrase abstractly, keep the decomposition from Route A but prove only the defect-absorption step by a tiny explicit case split.

The enumeration is bounded and known exactly. The pair-bonus defect `pairBonusDefect α β` is strictly positive in only four ordered configurations:

- `α = {0}`, `β = {1}` (case 2a);
- `α = {1}`, `β = {0}` (case 2a, swap);
- `α = {0,1,2}`, `β = {0,1,3}` (case 2b);
- `α = {0,1,3}`, `β = {0,1,2}` (case 2b, swap).

In every other configuration `pairBonusDefect α β ≤ 0`, and the total submodularity defect is bounded by `baseWitnessSubmodular` alone. A Route-B proof therefore reduces to:

- one branch per ordered configuration above (four cases, each an explicit numeric check);
- one "otherwise" branch, closed by `baseWitnessSubmodular` plus `pairBonusDefect α β ≤ 0`.

Five cases total, not 256. This is still much better than a full brute-force proof, because the cardinality-profile part remains conceptual and only the exceptional configurations are enumerated; the bound "at most four ordered configurations" should be hard-coded into the proof structure so the fallback cannot silently drift back toward enumerating all pairs.

## Risks

1. **Set-equality normal forms.** `Finset` literals such as `{0,1}` and `insert 0 {1}` do not always normalize to the same syntax automatically. The canonicalization helpers in §Step 0 (`pair01_eq`, `mem_pair01`, `pair01_card`) are a first-class plan step, not a contingency; expect to reach for them whenever a goal mentions the literal `{0, 1}`.
2. **Indicator arithmetic overhead.** Expressing the witness as a sum of indicator functions introduces many casts to `ℚ`. Keep the indicator definitions as `ℚ`-valued from the start to avoid repeated coercion noise.
3. **Overengineering.** The proof should not introduce a large permanent API just to remove one linter warning. Prefer `private` defs and lemmas local to `Theorem4.lean` unless something is clearly reusable.
4. **Fallback temptation.** If the structural route gets bogged down in `Finset` bookkeeping, it is easy to slide back toward a disguised brute-force proof. Use the route-B fallback only for the exceptional pair configurations, not for all 256 cases.

## Verification

Mechanical gates. All must pass before the plan is considered done:

1. `ZhangYeung/Theorem4.lean` contains no occurrence of `native_decide` (verifiable by `grep -n 'native_decide' ZhangYeung/Theorem4.lean` returning no matches).
2. `ZhangYeungTest/Theorem4.lean` still contains no `native_decide` (pre-existing invariant).
3. `lake build ZhangYeung.Theorem4 ZhangYeungTest.Theorem4` passes.
4. `lake lint` passes with no new warnings.
5. `lake test` passes.
6. `make check` passes end-to-end.

## Exit criteria

Conceptual / review-quality bar. In addition to the mechanical gates above, the plan is complete only when:

- the submodularity proof of `shannonCone_of_witness` reads as a structural argument about the witness, not a brute-force opaque computation;
- any residual `decide` use is bounded and each invocation has a conceptually transparent statement a reviewer can recite in one sentence (e.g., "the four subsets of `{0,1}`" or "the pointwise decomposition over the 16 subsets of `Fin 4`");
- the section is justified by a proof a reviewer could reasonably describe as "Mathlib-quality": conceptually decomposed, finite, local, and not evaluator-dependent.
