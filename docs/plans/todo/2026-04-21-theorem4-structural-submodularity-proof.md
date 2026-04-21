---
title: "Replace `native_decide` in `shannonCone_of_witness` with a structural submodularity proof"
created: 2026-04-21
status: proposed
branch: TBD
roadmap: docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md
depends_on: `docs/plans/todo/2026-04-21-finite-fintype-pfr-alignment-and-native-decide-removal.md`; current `main` with `Delta`, `CopyLemma`, `Theorem2`, `Theorem3`, `EntropyRegion`, and the entropy-function bridge in `Theorem4` already aligned to PFR-style `[Finite]` assumptions.
---

## Status

Proposed focused follow-up for the single remaining library-side `native_decide` use in `ZhangYeung/Theorem4.lean`.

Current empirical state:

- `decide` already works for the empty-set witness check in `shannonCone_of_witness`.
- `decide` already works for the quantified monotonicity branch of `shannonCone_of_witness`.
- `decide` already works for the concrete witness-value checks used in `not_zhangYeungAt_witness_canonical` and in `ZhangYeungTest/Theorem4.lean`.
- Only the quantified submodularity branch of `shannonCone_of_witness` still needs `native_decide`.

Failed intermediate attempts already explored:

1. Replace the quantified submodularity proof with `decide` directly.
2. Rewrite `F_witness_ℚ` into a more automation-friendly cardinality match and retry `decide`.
3. Split the universal check into explicit `fin_cases` over all `α, β : Finset (Fin 4)`.

All three failed for proof-engineering reasons rather than mathematical ones: rational inequalities such as `4 + 2 ≤ 2 + 4` do not always reduce through Lean's `Decidable` instances in these contexts, and the naive 256-case proof either times out or produces brittle `Finset` representation mismatches.

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
3. independent of evaluator-specific proof search.

The preferred end state is:

- no `native_decide` in the library `ZhangYeung` code;
- test-side concrete witness evaluations may continue to use `decide`;
- `lake lint` stays green.

## Non-goals

- No change to the mathematical witness itself.
- No change to the public theorems `theorem4_finite`, `theorem4`, or `theorem4_ge_four` beyond their proof terms.
- No attempt to remove `decide` from the concrete witness-value tests; the target here is the remaining quantified proof only.
- No heavy new abstraction layer unless the structural proof clearly benefits from it.

## Design sketch

### Route A (preferred): decompose the witness into simple set functions

Define the fixed exceptional pair:

```lean
private def pair01 : Finset (Fin 4) := {0, 1}
```

Then decompose `F_witness_ℚ` as a sum of four pieces on `Finset (Fin 4)`:

1. the cardinality term `card(S)`;
2. a nonempty bonus `1_{S ≠ ∅}`;
3. a full-set penalty `-1_{S = univ}`;
4. an exceptional pair bonus `1_{S = pair01}`.

Concretely, prove a lemma of the form:

```lean
F_witness_ℚ S = (S.card : ℚ) + nonemptyBonus S - fullBonus S + pairBonus S
```

where:

- `nonemptyBonus S = if S.Nonempty then 1 else 0`
- `fullBonus S = if S = Finset.univ then 1 else 0`
- `pairBonus S = if S = pair01 then 1 else 0`

This representation is mathematically transparent:

- the cardinality profile `0, 2, 3, 4, 4` is exactly `card + nonemptyBonus - fullBonus`;
- the special value `F({0,1}) = 4` is the extra `pairBonus` term.

### Step 1: prove the base cardinality profile is submodular

Prove the three components separately.

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

Then in the final submodularity proof:

1. expand both sides using the decomposition lemma;
2. use `baseWitnessSubmodular` for the cardinality-profile part;
3. use the two classification lemmas to show that any positive pair-bonus defect is absorbed by the base slack.

The proof should no longer need either `native_decide` or a 256-case brute force split.

### Route B (fallback): small explicit case table, but only for the exceptional defect

If the classification lemmas in Step 2 become awkward to phrase abstractly, keep the decomposition from Route A but prove only the defect-absorption step by a tiny explicit case split over the handful of configurations where `{0,1}` can appear as `α ∪ β` or `α ∩ β`.

This is still much better than a full brute-force proof, because the cardinality-profile part remains conceptual and only the exceptional configurations are enumerated.

## Risks

1. **Set-equality normal forms.** `Finset` literals such as `{0,1}` and `insert 0 {1}` do not always normalize to the same syntax automatically. Plan to add a few local `simpa [Finset.ext]` or canonicalizing helper lemmas if needed.
2. **Indicator arithmetic overhead.** Expressing the witness as a sum of indicator functions introduces many casts to `ℚ`. Keep the indicator definitions as `ℚ`-valued from the start to avoid repeated coercion noise.
3. **Overengineering.** The proof should not introduce a large permanent API just to remove one linter warning. Prefer `private` defs and lemmas local to `Theorem4.lean` unless something is clearly reusable.
4. **Fallback temptation.** If the structural route gets bogged down in `Finset` bookkeeping, it is easy to slide back toward a disguised brute-force proof. Use the route-B fallback only for the exceptional pair configurations, not for all 256 cases.

## Verification

The work is complete when all of the following hold:

1. `ZhangYeung/Theorem4.lean` contains no `native_decide`.
2. `ZhangYeungTest/Theorem4.lean` may continue to use `decide`, but not `native_decide`.
3. `lake build ZhangYeung.Theorem4 ZhangYeungTest.Theorem4` passes.
4. `lake lint` passes.
5. `lake test` passes.
6. The resulting submodularity proof reads as a structural argument about the witness, not as a brute-force opaque computation.

## Exit criteria

Done when the only remaining computation in the witness section is concrete `decide`-based equality checking for explicit finite sets, and the theorem `shannonCone_of_witness` is justified by a proof a reviewer could reasonably describe as “Mathlib-quality”: conceptually decomposed, finite, local, and not evaluator-dependent.
