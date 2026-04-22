---
title: "Align `Finite`/`Fintype` usage with PFR and remove `native_decide` from `Theorem4`"
created: 2026-04-21
status: done
branch: main
roadmap: docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md
depends_on: Current lint configuration on `main` (`weak.linter.mathlibStandardSet = true` with `weak.linter.style.longLine = false`), plus the post-M4 / M4.5 public surfaces in `ZhangYeung/Delta.lean`, `ZhangYeung/CopyLemma.lean`, `ZhangYeung/Theorem2.lean`, `ZhangYeung/Theorem3.lean`, `ZhangYeung/Theorem4.lean`, and `ZhangYeung/EntropyRegion.lean`.
---

## Status

Done. The public theorem surface is now aligned with the intended PFR-style `[Finite]` / proof-local `Fintype` split across `ZhangYeung/Delta.lean`, `ZhangYeung/CopyLemma.lean`, `ZhangYeung/Theorem2.lean`, `ZhangYeung/Theorem3.lean`, `ZhangYeung/EntropyRegion.lean`, and `ZhangYeung/Theorem4.lean`. The remaining `native_decide` use in `Theorem4` was eliminated by the structural witness proof tracked in the sibling follow-up plan. Current verification on `main`: `lake lint`, `lake build ZhangYeung`, and `lake test` all pass, and no `native_decide` occurrences remain in the repository.

## Context

The current warning profile comes from a mismatch between the project's original proof-writing style and the stronger lint posture introduced by `weak.linter.mathlibStandardSet = true`.

### 1. What PFR actually does

PFR enables the same linter set and does not disable `unusedFintypeInType`:

- `PFR/lakefile.toml` sets `weak.linter.mathlibStandardSet = true`.
- No global `weak.linter.unusedFintypeInType = false` override is present.
- No local `set_option linter.unusedFintypeInType false` suppressions were found.

Instead, PFR mostly avoids the lint by three techniques:

1. **Prefer `[Finite]` in theorem statements** when the result does not literally quantify over a finite sum/product.
2. **Create a local `Fintype` only inside the proof**, via patterns such as `have := Fintype.ofFinite A` or `cases nonempty_fintype S`.
3. **Use `omit` aggressively** so section-level proof assumptions do not leak into exported theorem types.

Representative examples:

- `PFR/WeakPFR.lean:410-418`: theorem stated with `[Finite A]`, local `Fintype.ofFinite A` in the proof.
- `PFR/ForMathlib/Entropy/Basic.lean:450-456`: theorem stated with `[Finite T]`, local `cases nonempty_fintype T` in the proof.
- `PFR/TauFunctional.lean:94-101` and `PFR/RhoFunctional.lean:977-980`: `omit` removes proof-local finiteness assumptions from exported declarations.

### 2. Where this repo currently differs

This repo currently inherits many `[Fintype ...]` assumptions from section-level blocks even when the final theorem statement does not need them syntactically. That pattern was convenient while building against PFR's entropy API, but it now leaves public declarations with stronger assumptions than PFR would usually expose.

The current `unusedFintypeInType` warnings cluster in:

- `ZhangYeung/Delta.lean`
- `ZhangYeung/CopyLemma.lean`
- `ZhangYeung/Theorem2.lean`
- `ZhangYeung/Theorem3.lean`
- `ZhangYeung/Theorem4.lean`
- `ZhangYeung/EntropyRegion.lean`

### 3. `native_decide` is a separate issue

`native_decide` currently appears only in `ZhangYeung/Theorem4.lean`, where it is used to discharge the finite witness checks over `F_witness_ℚ : Finset (Fin 4) → ℚ`:

- the Shannon-cone membership proof `shannonCone_of_witness`
- the concrete witness-value evaluations in `not_zhangYeungAt_witness_canonical`

This is not an API-shape issue. It is a trust-model/style issue: Mathlib's linter rejects `native_decide` because it trusts the compiled evaluator, not just the kernel. The plan therefore treats `native_decide` removal as a targeted refactor in `Theorem4`, independent from the broader `Finite`/`Fintype` cleanup.

## Goal

Bring the project's finiteness assumptions into the same broad style as PFR while preserving the current mathematical public API as much as possible, and remove all uses of `native_decide` from `ZhangYeung/Theorem4`.

Concretely:

1. Keep `weak.linter.mathlibStandardSet = true`.
2. Keep `linter.unusedFintypeInType` enabled.
3. Refactor exported declarations so `[Fintype ...]` appears only when the theorem statement genuinely needs it.
4. Replace every use of `native_decide` in `Theorem4` with linter-acceptable proof terms.
5. Leave the repo with no remaining `unusedFintypeInType` or `native_decide` warnings under `lake build ZhangYeung`.

## Non-goals

- No change to the mathematical content of Theorems 2, 3, or 4.
- No attempt to generalize the repo away from finite/discrete codomains altogether. This plan is about API shape, not a foundational entropy generalization.
- No blanket global disable of `unusedFintypeInType` or `linter.style.nativeDecide` unless the implementation work proves disproportionate and a follow-up design decision is explicitly recorded.
- No opportunistic refactor of unrelated style warnings that are already green.
- No change to the witness `F_witness_ℚ` definition unless that is needed to support the `native_decide` replacement.

## Design sketch

### Phase A: inventory and classification

Start by classifying every current `unusedFintypeInType` warning into one of three buckets.

1. **Pure proof artifact.** The theorem type does not quantify over a sum/product on the finite type and can be weakened from `[Fintype α]` to `[Finite α]`, or can drop the finiteness assumption from the exported type entirely.
2. **Section leakage.** The theorem only carries `[Fintype α]` because it was proved inside a wider section. Fix with `omit` or by moving the declaration to a narrower section.
3. **Statement genuinely needs `Fintype`.** Keep `[Fintype α]` when the result explicitly mentions `∑`, `Finset.univ`, `Fintype.card`, or another construction whose type really depends on an enumeration.

The expected outcome is that most warnings in `Delta`, `CopyLemma`, `Theorem2`, `Theorem3`, `Theorem4`, and `EntropyRegion` fall into buckets (1) and (2), not (3).

### Phase B: PFR-style `Finite`/`Fintype` alignment

Apply the following rule module-by-module.

#### B1. Public theorem surface

For exported lemmas and theorems:

- Replace `[Fintype α]` with `[Finite α]` whenever the theorem statement does not literally use enumeration-dependent syntax.
- Preserve `[MeasurableSingletonClass α]` and other genuinely semantic assumptions.
- When a theorem statement no longer mentions any finiteness class at all, remove the assumption from the exported type instead of keeping a vacuous `[Finite α]`.

#### B2. Proof-local recovery of `Fintype`

Inside proofs, recover a local `Fintype` only where needed:

- use `letI := Fintype.ofFinite α` when a local instance is sufficient;
- use `have := Fintype.ofFinite α` when explicit access to the instance is more convenient;
- use `cases nonempty_fintype α` in the same style PFR uses when a local `[Fintype α]` plus `[Nonempty α]` interaction makes elaboration easier.

#### B3. `omit` and section narrowing

Follow PFR's section discipline:

- narrow section-level variable blocks where possible;
- add `omit [Fintype ...] in` to declarations that do not need inherited proof-local assumptions on their exported type;
- avoid adding new top-level helper sections that force heavy instance blocks onto unrelated declarations.

#### B4. Expected module shape

The likely first-pass sequence is:

1. `ZhangYeung/Delta.lean`
2. `ZhangYeung/CopyLemma.lean`
3. `ZhangYeung/Theorem3.lean`
4. `ZhangYeung/Theorem2.lean`
5. `ZhangYeung/EntropyRegion.lean`
6. `ZhangYeung/Theorem4.lean`

Reason: `Delta` and `CopyLemma` define much of the finiteness vocabulary used downstream; aligning them first should reduce duplication and make the later theorem modules more mechanical.

### Phase C: remove `native_decide` from `Theorem4`

Handle `native_decide` in escalating order, stopping at the first satisfactory route.

#### C1. Attempt the smallest replacement: `decide`

Try replacing each `native_decide` proof in `Theorem4` with `decide` while keeping the witness over `ℚ`.

This is the preferred first attempt because:

- the domain is tiny (`Finset (Fin 4)` has only 16 elements);
- the witness is already intentionally defined by a finite `if`-cascade over cardinals;
- the linter only objects to `native_decide`, not to `decide`.

If `decide` is fast enough and elaborates reliably, this closes the issue at very low cost.

#### C2. If `decide` is too slow or brittle, isolate value lemmas

Factor `F_witness_ℚ` arithmetic into explicit lemmas:

- `F_witness_ℚ ∅ = 0`
- singleton values equal `2`
- `{0,1}` equals `4`
- every other pair equals `3`
- all triples and the four-set equal `4`

Use those lemmas to reprove the canonical Zhang-Yeung violation by direct rewriting plus `norm_num`.

#### C3. Manual proof of Shannon-cone membership if needed

If the universal monotonicity/submodularity checks remain awkward under `decide`, replace them with structural proofs by cardinality pattern and the unique exceptional pair `{0,1}`.

This proof should be organized as:

1. classification lemmas for `F_witness_ℚ` by cardinality and the `{0,1}` exception;
2. monotonicity proof by case split on `(α, β)` cardinalities and whether the exceptional pair appears;
3. submodularity proof by case split on the cardinalities of `α`, `β`, `α ∩ β`, and `α ∪ β`, again isolating the `{0,1}` exceptional behavior.

This is the highest-effort route and should be taken only if C1 fails and C2 still leaves the universal checks stuck.

### Phase D: tests and API confirmation

After each module-level `Finite`/`Fintype` refactor:

- update the sibling test module if the public signature changes;
- prefer minimal test edits that only reflect the weaker, more general assumption surface;
- confirm that no test reaches into implementation details just to rebuild missing local `Fintype` instances.

The guiding rule is the same as PFR's downstream style: weaker assumptions in the public theorem should make test code easier, not harder.

### Phase E: commit slicing

Keep the work in small logical commits:

1. `Delta` / `CopyLemma` API weakening
2. `Theorem2` / `Theorem3` API weakening
3. `EntropyRegion` / `Theorem4` API weakening
4. `Theorem4` `native_decide` removal
5. any test-only or lint-only follow-up

This keeps review focused and makes it easy to stop after a bounded successful subset if the `native_decide` replacement expands unexpectedly.

## Risks

1. **Signature churn for downstream proofs.** Weakening `[Fintype]` to `[Finite]` changes implicit instance search at call sites. Most downstream uses should get easier, but some test proofs may need a local `letI := Fintype.ofFinite _`.
2. **Hidden reliance on section-level instances.** Some proofs may typecheck only because a broad section currently supplies `Fintype` automatically. Narrowing with `omit` can expose those dependencies abruptly. Budget time for local proof repair.
3. **`decide` performance may be acceptable locally but poor in CI.** Even if `decide` replaces `native_decide`, it still expands proof terms by kernel reduction. Verify rebuild time on `Theorem4` after the swap.
4. **Manual submodularity proof could sprawl.** If C3 is needed, the finite case split on a 16-point domain is still bounded, but the proof can become verbose without careful helper lemmas.
5. **False equivalence with PFR.** PFR is a style reference, not a hard law. Some local exported theorems may legitimately keep `[Fintype]` because the concrete entropy API here is more theorem-facing than PFR's internal helper layers.

## Verification

The work is complete when all of the following hold:

1. `lake build ZhangYeung` passes with no `unusedFintypeInType` warnings.
2. `lake build ZhangYeung` passes with no `native_decide` warnings.
3. `lake lint` passes.
4. `lake test` passes.
5. `make check` passes.
6. The sibling test modules continue to compile without importing implementation files.
7. At least one representative theorem per module has visibly weaker assumptions than before, matching the intended PFR-style shift from `[Fintype]` to `[Finite]` where appropriate.

## Exit criteria

Done when the repository satisfies all of the following:

- the remaining finiteness assumptions in public theorem statements are intentional rather than inherited proof artifacts;
- the project's `Finite`/`Fintype` usage looks recognizably PFR-style to a reader comparing the two codebases;
- `ZhangYeung/Theorem4.lean` contains no `native_decide` calls;
- no global lint suppression was required for either `unusedFintypeInType` or `linter.style.nativeDecide`.

If the work stalls after Phase C1 or C2, record the exact blocker in this plan and explicitly decide between:

1. completing the manual proof route C3, or
2. accepting a narrow local lint suppression in `Theorem4` as a documented exception.
