---
title: "Refactor and polish `ZhangYeung/Theorem2.lean`"
created: 2026-04-17
branch: refactor/theorem-2
supersedes_refs: docs/plans/done/2026-04-16-theorem-2-conditional-warm-up.md (M1.5 plan; landed the proof)
---

## Context

`ZhangYeung/Theorem2.lean` was landed by the M1.5 plan (`docs/plans/done/2026-04-16-theorem-2-conditional-warm-up.md`) and received a light simplify pass on 2026-04-17 (commit `b794b2d`) that removed dead code and narration-only comments. A code-review pass alongside that simplify run surfaced four structural improvements that are larger than single-edit cleanup and want their own commits. None change the set of public declarations (only `theorem2` itself is public; everything else is `private`), none change proof statements, and all are bounded by `make check` staying green.

The file is currently 1651 lines and builds in roughly 70 seconds after cache warm, dominated by two proofs (`delta_eq_sum_log_ratio` and `sum_joint_eq_sum_ptilde`) that each carry a bumped `maxHeartbeats`. The refactors below target those two proofs and the supporting marginal-helper block they depend on.

Four items, in the order they should land so each simplifies the next:

1. **Route marginal-sum helpers through Mathlib/PFR equivalents.** Nine private lemmas between lines 166 and 365 hand-roll facts that are one or two rewrites from existing Mathlib and PFR API. Replacing them reduces the file's surface area (and the style-review burden) before any consumer-side restructuring.

2. **Consolidate the eleven `hEq_*` marginal-swap blocks into one generic reindex helper.** Lines 1180 through 1420 (inside `sum_joint_eq_sum_ptilde`) are near-identical instantiations of a single pattern: for each of the eleven log-factors, project the 4-tuple down, reindex the filter-sum by a coordinate `Equiv`, and quote a `sum_ptilde_over_*` lemma. A single helper parameterised by the projection and the `p̃`-marginal lemma replaces roughly 240 lines of boilerplate.

3. **Hoist the shared `L`, `pXZ`, `pXU`, … abbreviations to module scope.** Both `delta_eq_sum_log_ratio` and `sum_joint_eq_sum_ptilde` open with the same eleven `set` abbreviations and the same `L` definition. Hoisting them to a `section`-scoped `private abbrev` block lets the two proofs share the same vocabulary, and lets the consolidation in step 2 reference `L t`'s decomposition without re-`set`-ing.

4. **Re-measure and drop or lower the two `maxHeartbeats` bumps.** `delta_eq_sum_log_ratio` (line 956) uses `3200000` and `sum_joint_eq_sum_ptilde` (line 1146) uses `2400000`. Both bumps were sized during incremental proving. Steps 2 and 3 shrink both proof bodies; after they land, the bumps should either disappear or drop to something closer to Mathlib's default (`200000`).

All four are proof-surface-preserving: no public or private signature changes (except as noted for step 1's deletions), no lemma-statement changes, no new theorems. Docstrings update where lemma names change.

## Scope

**In scope:**

- Replace `indepFun_map_pair_real_singleton` (line 368) with a direct call chain through `ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map` and `MeasureTheory.Measure.prod_real_singleton`. Inline at the one consumer (`phat_sum_eq_one`) and delete the helper.
- Replace the six pair/triple marginal-sum helpers (`sum_map_pair_first`/`_second`, `sum_map_triple_first`/`_second`/`_third`, lines 166 to 297) with direct applications of `MeasureTheory.measureReal_preimage_fst_singleton_eq_sum` / `_snd_` (PFR's `.lake/packages/pfr/PFR/Mathlib/MeasureTheory/Measure/Real.lean`) composed with `Measure.map_map`.
- Replace the four marginal bounds (`measureReal_map_pair_le_map_fst`/`_snd`, `measureReal_map_triple_le_map_pair_12`/`_13`, lines 300 to 365) with direct `Measure.map_map` + `measureReal_mono` calls at call sites or with a single three-line helper.
- Introduce a new private helper, tentatively `marg_swap_by_reindex`, that bundles: (a) an `Equiv` from the complement coordinates to the fibre, (b) the `sum_ptilde_over_*` family as a hypothesis parameter, (c) the `marg_swap_helper` call. Eleven explicit `hEq_*` blocks collapse to eleven one-or-two-line calls.
- Move the eleven `p*` abbreviations and the `L` definition out of `sum_joint_eq_sum_ptilde` and `delta_eq_sum_log_ratio` into a module-scope `section WeightedLog` (or similar) that opens the `variable` block and defines `private abbrev` names. Both proofs then reference `L` and `pXZ` directly.
- After steps 1 through 3, drop both `set_option maxHeartbeats` lines, rerun `make check`, and iteratively reintroduce a smaller cap (`400000`, then `800000`, then `1600000`) only if the default fails.

**Out of scope:**

- Any change to `theorem2` (the only public declaration) or `theorem2_shannon_identity` (the Shannon-algebra reduction). Both are stable and well-factored.
- Any change to the KL-divergence closing argument (`theorem2_delta_le_zero`, `Real.sum_mul_log_div_leq` wiring).
- Any change to `ZhangYeung.delta` or `ZhangYeung/Delta.lean`. This refactor is scoped to `Theorem2.lean`.
- Any change to `CondIndepFun`-related helpers (`condIndepFun_map_triple_real_singleton`) or `phat_sum_eq_one`'s positivity plumbing, which has no straightforward Mathlib replacement.
- Changing `lemma` to `theorem`, adding `@[simp]` tags, or changing `private` to `protected`.
- Updating the module docstring's `## Current state` paragraph (already reflects the post-simplify state).

## Sequencing: four commits

Splitting lets a reviewer bisect the structural changes and lets each step stand on its own `make check`. Each commit maintains a green build.

### Commit A: replace marginal helpers with Mathlib/PFR calls

Pure consumer-side rewrite plus helper deletion. No structural change to the two large proofs; they simply call different lemmas.

**`ZhangYeung/Theorem2.lean`:**

1. For each of `sum_map_pair_first` / `sum_map_pair_second` / `sum_map_triple_first` / `sum_map_triple_second` / `sum_map_triple_third`:
    - Locate every consumer via `grep`.
    - At each call site, rewrite the local goal through `Measure.map_map` to reduce `(μ.map (fun ω => proj (F ω)))` to `(μ.map F).map proj`, then invoke `measureReal_preimage_{fst,snd}_singleton_eq_sum` (PFR's lift of the Mathlib lemma to `.real`).
    - Once all consumers are rewritten, delete the helper.

2. For each of `measureReal_map_pair_le_map_fst` / `measureReal_map_pair_le_map_snd` / `measureReal_map_triple_le_map_pair_12` / `measureReal_map_triple_le_map_pair_13`:
    - Replace each proof body with `Measure.map_map` + `measureReal_mono` (plus `measure_ne_top` on the measure side). The bound reduces to showing a preimage inclusion, which is a single `intro`-and-project tactic.
    - Consider consolidating the four bounds into a single `measureReal_map_le_of_preimage_subset` generic lemma parameterised by the projection if the resulting statements share enough structure. Land the generic version only if the call-site shape genuinely simplifies; otherwise keep four specialised lemmas with shorter bodies.

3. For `indepFun_map_pair_real_singleton` (the only consumer of which is `phat_sum_eq_one`):
    - Unfold at the call site via `rw [(indepFun_iff_map_prod_eq_prod_map_map hX hY).mp h_indep, Measure.prod_real_singleton]`.
    - Delete the helper.

**`ZhangYeungTest/Theorem2.lean`:** no changes (the helpers are `private` and not part of the public API).

Run `make check` and confirm green before committing.

### Commit B: consolidate the eleven `hEq_*` marginal-swap blocks

Introduce `marg_swap_by_reindex` and reduce the eleven ad-hoc blocks to uniform calls.

**`ZhangYeung/Theorem2.lean`:**

1. Above `sum_joint_eq_sum_ptilde`, add a new private lemma (or inline `let`-bound helper, whichever the surrounding `variable` block permits):

    ```text
    private lemma marg_swap_by_reindex
        {γ δ : Type*} [Fintype γ] [Fintype δ] …
        (proj : S₁ × S₂ × S₃ × S₄ → γ) (hproj : Measurable proj)
        (embed : δ → S₁ × S₂ × S₃ × S₄)    -- reindex from complement type δ into the fibre
        (hembed : Function.Injective embed)
        (hfibre : ∀ t, t ∈ filter (proj · = b) ↔ ∃ d, embed d = t)
        (φ : γ → ℝ)
        (h_marg : ∀ b : γ, (∑ d : δ, ptilde X Y Z U μ (embed d)) =
            (μ.map (fun ω => proj (X ω, Y ω, Z ω, U ω))).real {b}) :
        (∑ t, pJoint X Y Z U μ t * φ (proj t))
          = ∑ t, ptilde X Y Z U μ t * φ (proj t)
    ```

    The helper absorbs the `Finset.sum_nbij'` + `Fintype.sum_prod_type` boilerplate. Implementation calls `marg_swap_helper` internally after reindexing the fibre sum via the given `embed`.

2. For each of the eleven `hEq_xz` / `hEq_xu` / `hEq_yz` / `hEq_yu` / `hEq_zu` / `hEq_z` / `hEq_u` / `hEq_x` / `hEq_y` / `hEq_xzu` / `hEq_yzu`, replace the body with a single `marg_swap_by_reindex` call that supplies (a) the projection, (b) the complement-type `Equiv`, (c) the already-proved `sum_ptilde_over_*` lemma.

3. Confirm the final `rw [h_split …, hEq_xz, …]` chain still closes the goal. If the shape of `marg_swap_by_reindex`'s conclusion differs from the old `hEq_*` conclusion, adjust the final `rw` arguments to match.

**`ZhangYeungTest/Theorem2.lean`:** no changes.

Run `make check`; expect the file length to drop by roughly 240 lines and the `sum_joint_eq_sum_ptilde` body to fit on one screen.

### Commit C: hoist `L` and the eleven `p*` abbreviations to module scope

Both `delta_eq_sum_log_ratio` and `sum_joint_eq_sum_ptilde` currently redefine `pXZ`, `pXU`, …, `pYZU`, and `L` at the top of their bodies. After commit B the `L` definition is still needed by both proofs; hoisting it to module scope removes the duplicate.

**`ZhangYeung/Theorem2.lean`:**

1. Open a new `section WeightedLog` scoped to the existing `variable` block. Inside:

    ```text
    private abbrev pXZ  (X : Ω → S₁) (Z : Ω → S₃)  (μ : Measure Ω) :
        S₁ × S₃ → ℝ := fun p => (μ.map (fun ω => (X ω, Z ω))).real {p}
    -- … the other ten.
    private abbrev L (X : Ω → S₁) (Y : Ω → S₂) (Z : Ω → S₃) (U : Ω → S₄) (μ : Measure Ω) :
        S₁ × S₂ × S₃ × S₄ → ℝ := fun t => …
    ```

    (Whether `private abbrev` or `private def` works best depends on whether the bodies unfold well in `ring` and `simp only [L]`. Start with `abbrev`; fall back to `def` with `@[simp]` unfolding lemmas if term-mode elaboration chokes.)

2. In `delta_eq_sum_log_ratio`, delete the `set pXZ … := …` block and the `set L … := …` block. References to `L t` and `pXZ (t.1, t.2.2.1)` now resolve to the module-level abbreviations.

3. In `sum_joint_eq_sum_ptilde`, same deletion.

4. If `abbrev` unfolding causes `ring` to fail on the `L`-expansion step, introduce a small `@[simp] lemma L_apply : L X Y Z U μ t = …` to drive the unfolding explicitly. Prefer not to add `@[simp]` globally; keep the unfolding lemma private and rewrite explicitly with `simp only [L_apply]` at the two call sites.

**`ZhangYeungTest/Theorem2.lean`:** no changes.

Run `make check`. Expect another 40 to 60 lines saved and both large proofs to share a common vocabulary.

### Commit D: drop or lower the `maxHeartbeats` bumps

After commits A through C, both proof bodies are materially shorter. The two bumps should be re-measured rather than kept as scaffolding.

**`ZhangYeung/Theorem2.lean`:**

1. Remove `set_option maxHeartbeats 3200000 in` above `delta_eq_sum_log_ratio`. Rerun `make build`. If it passes, keep the removal and move on to step 3. If it fails with a `maxHeartbeats` error, record the reported usage and set the cap to the next power-of-two-ish multiple of Mathlib's default (`200000`): try `400000`, then `800000`, then `1600000` in sequence.

2. Remove `set_option maxHeartbeats 2400000 in` above `sum_joint_eq_sum_ptilde`. Same escalating retry: default, then `400000`, `800000`, `1600000`.

3. If either bump turns out to still be needed, document the reason in a one-line comment above the `set_option`. Preferred shape:

    ```text
    -- The eleven entropy-lift rewrites are unavoidably sequential; default heartbeats is insufficient.
    set_option maxHeartbeats 400000 in
    ```

    That is a WHY-comment in the project's sense and is appropriate per the writing rule.

**`ZhangYeungTest/Theorem2.lean`:** no changes.

Run `make check` after each escalation; commit the final working configuration.

## Rollback

Each commit stands alone and leaves `make check` green. If any step introduces a regression that cannot be fixed within the commit, revert that commit with `git revert` (not `--amend` per project rules). The preceding commits remain on the branch and are safe to keep.

## Risks and unknowns

- **Mathlib API surface drift.** `measureReal_preimage_fst_singleton_eq_sum` lives in PFR's `Mathlib/MeasureTheory/Measure/Real.lean`. If PFR retires it during the branch's lifetime, commit A needs to adapt or pull its own version. Mitigation: lock the PFR revision in `lakefile.toml` during the refactor; upgrade in a separate PR afterwards.

- **`abbrev` vs `def` for `L`.** Term-mode unfolding in `ring` and `simp only` is sensitive to reducibility. If commit C's `abbrev` version fails elaboration on the pointwise `ring` step, escalate to `def` with an explicit `L_apply` unfolding lemma. Worst case: keep the `set` blocks inside each proof (no net hoist), accept that as a structural constraint, and close commit C by only hoisting `pXZ` through `pYZU` (which don't participate in `ring`).

- **Heartbeat surprises.** The two large proofs' cost is dominated by `Finset.sum_nbij'` elaboration, which commit B removes. If commit D still needs large bumps, the constraint has shifted from `sum_nbij'` to the eleven entropy-lift rewrites in `delta_eq_sum_log_ratio`. That is an unrelated issue and can be addressed by splitting the 12-entry `rw [hHZ, …, hHYZU]` chain into two smaller chains.

## What counts as done

- All nine marginal-helper lemmas in the current lines 166 to 365 are either deleted or reduced to two-line wrappers around Mathlib/PFR calls.
- `sum_joint_eq_sum_ptilde`'s body no longer contains eleven parallel `Finset.sum_nbij'` blocks; it calls a shared `marg_swap_by_reindex` helper eleven times.
- `delta_eq_sum_log_ratio` and `sum_joint_eq_sum_ptilde` share the same `L` and `p*` abbreviations, hoisted to module scope.
- Both `set_option maxHeartbeats` bumps are either removed, or reduced to the smallest cap that still compiles and carry a one-line WHY-comment.
- `make check` is green on every commit of the four-commit sequence.
- Total file length is expected to drop from 1651 lines to roughly 1150 to 1250 lines; no new public declarations added.

## Outcome (2026-04-17)

Commits A (90d813f), B (8513269), D (d2c2f9e) landed. Commit C was skipped.

**Commit A: marginal helpers routed through Mathlib/PFR.** `sum_map_pair_first`, `sum_map_pair_second`, `sum_map_triple_first`, and `indepFun_map_pair_real_singleton` were reduced to two- or three-line proofs via `Measure.map_map` + `measureReal_preimage_{fst,snd}_singleton_eq_sum` + `indepFun_iff_map_prod_eq_prod_map_map` + `Measure.prod_real_singleton`. `sum_map_triple_second`, `sum_map_triple_third`, and the four marginal bound lemmas were left in place; a reshape-based replacement would have been a lateral move since Mathlib's `preimage_{fst,snd}_singleton_eq_sum` covers only 2-tuples directly. Net: 37 lines saved.

**Commit B: eleven `hEq_*` blocks unified via `ptilde_filter_sum_eq_reindex`.** The new helper takes the embed/extract functions plus their three inversion properties and runs `Finset.sum_nbij'` once. Each of the eleven `hEq_*` bodies now reads as an `apply marg_swap_helper`, a destructure, a single `rw [ptilde_filter_sum_eq_reindex μ embed extract proj c h₁ h₂ h₃]`, and the existing `sum_ptilde_over_*` call. Net: 62 lines saved. File dropped to 1552 lines.

**Commit C: skipped.** A survey of the file showed 99 call sites to the 2- and 3-coord `p*` abbreviations alone; hoisting them to module scope would either require passing `X Y Z U μ` explicitly at every call site (net worse) or restructuring both large proofs into a new section with `variable {X Y Z U}` + `(μ)` bindings. Either change exceeded the expected ~30-line savings. `L`'s body references the `p*` family, so hoisting only `L` would either inflate its body with direct `μ.map` expressions or force the `p*` hoist as well. The plan's own risk section ("`abbrev` vs `def` for `L`") flagged this tradeoff; in practice the call-site cost dominated. Recorded as not-worth-the-churn.

**Commit D: one bump halved, one unchanged.** `delta_eq_sum_log_ratio` dropped from `3200000` to `1600000` (half). `sum_joint_eq_sum_ptilde` stayed at `2400000`: the `ptilde_filter_sum_eq_reindex` helper calls cost roughly what the inline `Finset.sum_nbij'` blocks did, because the helper takes three hypothesis arguments that re-elaborate at every call. Both bumps now carry a one-line WHY comment.

Final file length: 1554 lines (from 1651). Net savings 97 lines, below the 400-to-500-line plan estimate but above the Commit-A-alone baseline. `make check` green on every commit.

### Postscript (follow-up commit `aa1f3a2`)

After Commit D landed, a brief user question about whether Mathlib's >800000-heartbeat tech-debt line could be cleared prompted a fifth commit that eliminated both surviving bumps entirely.

**Mechanism.** Extract the eleven per-projection marginal-swap facts from `sum_joint_eq_sum_ptilde` into their own top-level `private lemma`s (`sum_joint_swap_proj_xz` … `sum_joint_swap_proj_yzu`). Because `set_option maxHeartbeats` is enforced *per declaration*, splitting the single large proof into twelve (eleven extracted + one slim combiner) gave each piece its own fresh 200000 budget. The slim combiner just invokes eleven pre-compiled closed terms, which elaborates nearly for free.

**Result.**

- `delta_eq_sum_log_ratio`: `1600000` → default `200000` (bump removed).
- `sum_joint_eq_sum_ptilde`: `2400000` → default `200000` (bump removed).
- Build time for `ZhangYeung.Theorem2`: ~70s → ~3.5s.
- File size: 1554 → 1642 lines (+88 for the eleven extracted signatures).
- No `set_option maxHeartbeats` anywhere in the module. Every declaration fits Mathlib's default budget.

**Takeaway.** When a Lean declaration wants `maxHeartbeats` above the ~400000 soft threshold, *split into sub-lemmas first, optimize tactically second*. The four commits A/B/D above tactically shrank both proofs by ~100 lines, compressed ~240 lines of marginal-swap boilerplate, and routed helpers through Mathlib/PFR — all worthwhile, but they left bumps 8× and 12× over default. A single structural split did the work of those four commits on the heartbeat axis, confirming the Mathlib folklore that extraction is order-of-magnitude more effective than tactical tweaking.

## References

- This plan's predecessor: `docs/plans/done/2026-04-16-theorem-2-conditional-warm-up.md` (the M1.5 plan that landed `Theorem2.lean`).
- The style model for this plan: `docs/plans/done/2026-04-17-delta-lemmas-refactor-polish.md`.
- Mathlib API candidates named in commit A:
  - `ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map` (`.lake/packages/mathlib/Mathlib/Probability/Independence/Basic.lean`).
  - `MeasureTheory.Measure.prod_real_singleton` (`.lake/packages/pfr/PFR/Mathlib/MeasureTheory/Measure/Real.lean`).
  - `MeasureTheory.measureReal_preimage_fst_singleton_eq_sum` / `_snd_` (`.lake/packages/pfr/PFR/Mathlib/MeasureTheory/Measure/Real.lean`).
  - `MeasureTheory.Measure.map_map` (`.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Map.lean`).
