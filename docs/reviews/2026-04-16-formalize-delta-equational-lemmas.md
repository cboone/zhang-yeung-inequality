## Branch Review: formalize/delta-equational-lemmas

Base: main (merge base: 75807782)
Commits: 13
Files changed: 9 (6 added, 3 modified, 0 deleted, 0 renamed)
Reviewed through: d7d6eda

### Summary

Lands Milestone M1 of the Zhang-Yeung formalization: defines `ZhangYeung.delta` and ten equational lemmas capturing the algebraic content of the paper's equations (20)-(23), adds a sibling `ZhangYeungTest` library wired into `lake build` with compile-time API regression tests for every exported lemma, and updates the roadmap to codify milestone-level testing requirements. A follow-up pass realigns the module docstring and plan/roadmap prose to cite the verified transcription (`references/transcriptions/zhangyeung1998.md`, verified 2026-04-16) using the project-standard `[@zhangyeung1998]` form.

### Changes by Area

#### Library API (new delta module)

- `ZhangYeung/Delta.lean` (new, 147 lines): `delta` definition matching eq. (20), plus `delta_def`, `delta_comm_cond`, `delta_self`, `delta_comm_main`, `delta_eq_entropy`, `form21_iff`, `form22_iff`, `form23_iff`, `form23_of_form21_form22`, `delta_le_mutualInfo`. Two-stage `variable` block: base `[MeasurableSpace Sᵢ]` for the pure-algebra lemmas, then a shared extension `[Fintype Sᵢ] [MeasurableSingletonClass Sᵢ]` for the lemmas that need PFR's discrete API. Uses `omit` on individual lemmas (e.g. `delta_comm_main`, `delta_le_mutualInfo`) to drop conditioning-variable finite-alphabet instances that are not actually used.
- `ZhangYeung.lean` (modified): add `import ZhangYeung.Delta` so the top-level library re-exports the new module.

#### Test harness (new sibling library)

- `ZhangYeungTest.lean` (new, 2 lines): top-level re-export for the test library.
- `ZhangYeungTest/Delta.lean` (new, 77 lines): a `PureAlgebra` section re-proving `delta_def`, `delta_comm_cond`, `delta_self`, `form21_iff`, `form22_iff`, and the composed `form23_of_form21_form22 → form23_iff` downstream use; a `FiniteAlphabet` section covering `delta_comm_main`, `delta_eq_entropy`, `delta_le_mutualInfo`. Tests live outside `ZhangYeung` namespace and open it explicitly, matching their purpose as public-API regression checks.

#### Build configuration

- `lakefile.toml` (modified): `defaultTargets = ["ZhangYeung", "ZhangYeungTest"]` plus a second `[[lean_lib]]` stanza for `ZhangYeungTest`. CI now builds both libraries by default.

#### Documentation

- `docs/plans/done/2026-04-15-delta-equational-lemmas.md` (new, 324 lines): M1 plan. Written at branch start, tightened twice (`f918272` to state the finite-alphabet specialization up front; `bbff1fd` to add the verified-transcription primary-reference line).
- `docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md` (modified, +44/−5): adds a `Source transcription` line to the preamble, expands M0-M6 sections with explicit testing requirements, adds a milestone-level testing rule in §8, and extends the Critical Files inventory with the `ZhangYeungTest/` modules.
- `docs/plans/done/2026-04-16-align-delta-with-verified-transcription.md` (new, 83 lines): the citation-alignment plan, moved to `done/` once applied.

### File Inventory

**New files (5):**

- `ZhangYeung/Delta.lean`
- `ZhangYeungTest.lean`
- `ZhangYeungTest/Delta.lean`
- `docs/plans/done/2026-04-15-delta-equational-lemmas.md`
- `docs/plans/done/2026-04-16-align-delta-with-verified-transcription.md`

**Modified files (3):**

- `ZhangYeung.lean`
- `lakefile.toml`
- `docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md`

**Deleted files:** none.

**Renamed files:** none.

### Notable Changes

- **New `lean_lib` target `ZhangYeungTest`.** The build surface now requires both libraries to compile green before CI passes. This is a structural change, intentional, and codified as a project convention in the roadmap.
- **PFR API surface used.** No new imports beyond `ZhangYeung.Prelude` (which imports `PFR.ForMathlib.Entropy.Basic`). Relies on `mutualInfo_comm`, `condMutualInfo_comm`, `condMutualInfo_def` / `mutualInfo_def`, `condMutualInfo_eq`, `condMutualInfo_nonneg`, and the `Finite G → FiniteRange X` instance pinned in PFR.
- **No new dependencies.** `lakefile.toml` does not touch the PFR require stanza; the pin remains at `80daaf1`.
- **Roadmap now has milestone-level testing requirements.** Every future milestone (M0-M6) has a matching `ZhangYeungTest/*.lean` expectation. This creates a recurring deliverable for every subsequent PR on this project.

### Plan Compliance

#### Compliance verdict

**Strong compliance.** The branch implements the M1 plan faithfully, including every "optional" item, and the follow-on citation-alignment plan is fully executed. Deviations are minor and reasonable; see below.

#### Overall progress

- M1 plan (`docs/plans/done/2026-04-15-delta-equational-lemmas.md`): **14/14 actionable items done (100%).**
- Citation-alignment plan (`docs/plans/done/2026-04-16-align-delta-with-verified-transcription.md`): **3/3 edits done (100%).**

#### Done items (M1)

1. **Create `ZhangYeung/Delta.lean` with module docstring, imports, shared `variable` block, and `delta` definition** — `1846b00`. Definition matches the plan signature exactly (variable order `Z, U, X, Y`, four independent `Sᵢ`, `noncomputable def`, `μ := by volume_tac`).
2. **Trivial lemmas `delta_def`, `delta_comm_cond`, `delta_self`** — `9aff8ff`. Proofs are `rfl` / `simp only [delta_def]; ring` as planned.
3. **`delta_comm_main`** — `197fe72`. Uses `mutualInfo_comm` and `condMutualInfo_comm` with explicit `hZ`, `hU` measurability hypotheses, matching the plan's "PFR declares `Measurable` as explicit args" style note. Correctly `omit`s the conditioning-variable instances that are not needed.
4. **`delta_eq_entropy`** — `e81f95e`. Proof is exactly the plan's one-liner (`rw [delta_def, mutualInfo_def, condMutualInfo_eq hZ hU hX, condMutualInfo_eq hZ hU hY]`). `[IsProbabilityMeasure μ]` left in place as planned.
5. **Form-equivalence lemmas `form21_iff`, `form22_iff`, `form23_iff`, `form23_of_form21_form22`** — `9ae0bf9`. All `constructor <;> intro h <;> linarith` or bare `linarith`; integer-scaled as planned.
6. **`delta_le_mutualInfo` (optional)** — `37b34cd`. Landed as an integer-scaled sanity bound. Deviates from the plan's signature (the plan asked for `[FiniteRange Z] [FiniteRange U]`; the implementation uses the module-level `Fintype` instances to discharge those implicitly, which is equivalent and cleaner).
7. **Update `ZhangYeung.lean`** — `2529981`.
8. **Test library `ZhangYeungTest` + `ZhangYeungTest/Delta.lean`** — `92894c2` and `d7d6eda`. The second commit adds the explicit re-export test that exercises `import ZhangYeung` (not `import ZhangYeung.Delta`), confirming the library entrypoint exports the full API.
9. **Wire tests into default build** — `2529981` (lakefile update).
10. **Bootstrap verification** — implicit, covered before branch start.
11. **Commits are small and conventional-commit-styled** — every commit is `feat:`, `chore:`, `test:`, or `docs:`.
12. **Plan tightening** — `f918272` pre-empted the "Finite/discrete codomain assumptions" risk by stating the finite-alphabet specialization up front.
13. **Roadmap testing requirements** — `3adcbde` extended the roadmap with milestone-level testing rules before the branch closed (not in the M1 plan, but a natural consequence of the M1 deliverables).
14. **Citation alignment** — `0e0ae41` plans it; `bbff1fd` executes it.

#### Partially done items

None.

#### Not started items

None.

#### Deviations

- **`delta_le_mutualInfo` signature.** Plan asked for `[FiniteRange Z] [FiniteRange U]` as explicit instances on the lemma; implementation instead lives under the finite-alphabet `variable` block and `omit`s only the `Sᵢ` instances it does not need. This is a strict improvement: the lemma now uses the same instance shape as the surrounding lemmas, and the `Finite G → FiniteRange X` instance pinned in PFR makes the `FiniteRange` annotations redundant anyway. Reasonable.
- **Test coverage wording.** Plan said "one composed downstream use that derives the paper's scaled form (23) from hypotheses in forms (21) and (22)"; the test module implements this exactly as `form23_of_form21_form22 → form23_iff`. No drift.
- **Docstring citation.** Plan originally showed `[ZhangYeung1998]` and a handwritten bibliography block; citation-alignment plan moved both to `[@zhangyeung1998]` and a single pointer at the transcription. Both `ZhangYeung/Delta.lean` and the M1 plan are now consistent with `references/README.md`.
- **Roadmap scope creep.** The milestone-level testing requirements added to the roadmap (`3adcbde`) go beyond the M1 plan's stated deliverables. They are a reasonable generalization of the M1 test-harness work and are explicitly scoped as a roadmap-level decision, not an M1 deliverable. Flagged as intentional scope addition rather than scope creep.

#### Fidelity concerns

- **Docstring reference to `ZhangYeung.Theorem3`.** The plan's example docstring referred to a future `ZhangYeung.Theorem3` module; the shipped docstring instead describes the quantity in prose and defers the bound to "a later milestone". This is a correct, non-misleading paraphrase. Fine.
- **Spot-checks pass:** every proof script is one of `rfl`, `simp only [...]; ring`, `rw [...]`, `constructor <;> intro h <;> linarith [...]`, or `linarith`. Nothing longer. Matches the plan's "Anything longer signals over-engineering" rule.

### Code Quality Assessment

#### Overall quality

**Ready to merge.** The Lean source is small, faithful to the plan, and leaves no loose ends. Proofs are all one- or two-line scripts against PFR's stable API; nothing here depends on proof internals. The test harness matches the planned scope exactly. Documentation is consistent with the project's citation convention.

#### Strengths

- **Careful instance hygiene.** `omit [Fintype S₃] [Fintype S₄] [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄] in` on `delta_comm_main` and `delta_le_mutualInfo` keeps the finite-alphabet assumptions minimal per-lemma while still using the shared `variable` block for the lemmas that need them. This pattern is exactly right for a future Mathlib contribution.
- **Two-stage `variable` block.** Pure-algebra lemmas do not require `Fintype`/`MeasurableSingletonClass`; the module defers those instances to a second `variable` block with a short section comment explaining why. Readers can skim the first half without knowing PFR's discrete API.
- **Test library is not just a smoke test.** Every exported lemma is restated as an `example` and one composed downstream use (`form23_of_form21_form22 → form23_iff`) exercises the intended M3 integration. The re-export test in `d7d6eda` adds a separate guard against the library entrypoint drifting.
- **Commits map 1:1 to plan steps.** Each `feat:` commit lands a contiguous group of lemmas; infrastructure (`chore:`, `test:`, `docs:`) is separated. Easy to bisect, easy to review.
- **Citation form matches project convention.** `[@zhangyeung1998]` lowercase, `@`-prefixed; `## References` section points at the verified transcription rather than duplicating the BibTeX entry.
- **Plan accuracy note in citation-alignment plan.** The explicit line-by-line cross-check against the verified transcription (delta eq. (20) line 294, form21 lines 302-303, etc.) is an unusually useful artifact for future reviewers. Keep doing this.

#### Issues to address

None blocking. The branch is mergeable as is.

#### Suggestions

- **Consider a brief `## Tags` deviation from Mathlib.** Mathlib's `Tags` sections are single-line keyword lists; the current `## Tags` line reads as one long sentence ("Shannon entropy, mutual information, non-Shannon information inequality, Zhang-Yeung"), which is fine. Not a blocker. Revisit once a second module lands so the house style stabilizes.
- **Future: notation `Δ[Z : U | X, Y ; μ]`.** The module docstring records the decision to defer; the plan and roadmap both mention revisiting after M3. No action needed now, but worth a follow-up ticket once M3 starts writing `delta` in proof scripts.
- **M3 transport lemma for copied conditioners.** `delta_self` handles only the literal `X = Y` case; the plan explicitly flags that `Δ(Z, U | X, X₁)` for a copy `X₁` needs a separate `condMutualInfo` transport lemma in M2 or M3. This is correctly scoped out of M1 but will be load-bearing in M3. Worth tracking as an item in the M2/M3 plan when those are written.
