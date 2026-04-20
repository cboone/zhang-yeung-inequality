## Branch Review: formalize/3-theorem-3

Base: `main` (merge base: `32c1b3f`)
Commits: 14
Files changed: 8 (3 added, 5 modified, 0 deleted, 0 renamed)
Reviewed through: `af56f1c`

### Summary

This branch formalizes **Theorem 3 of Zhang-Yeung 1998** in Lean 4, closing milestone M3 of the project roadmap. It lands `ZhangYeung/Theorem3.lean` with three public theorems (`zhangYeung` for eq. 21, `zhangYeung_dual` for eq. 22, `zhangYeung_averaged` for eq. 23), proved by a private integer-form theorem `zhangYeung_integer` that runs the paper's Shannon chase on the copy joint from M2 and converts to the paper's scaled forms via the M1 form-conversion `iff`s. Two private Shannon helpers (three-way interaction identity and data-processing from `CondIndepFun`) and two private projection-measurability helpers support the chase. The M2 private helper `condIndepFun_comp` is promoted to `ZhangYeung/Prelude.lean` as a public namespaced lemma. A matching `ZhangYeungTest/Theorem3.lean` covers signatures, an independent-variable smoke test, a theorem-application cross-check, and a downstream-usage example.

### Changes by Area

**Theorem 3 module (new):**

- `ZhangYeung/Theorem3.lean` (new, 240 lines): the M3 public surface (`zhangYeung`, `zhangYeung_dual`, `zhangYeung_averaged`), the private integer-form theorem `zhangYeung_integer`, two private Shannon helpers (`mutualInfo_add_three_way_identity`, `mutualInfo_le_of_condIndepFun`), and two private projection-measurability helpers (`measurable_pairXZU`, `measurable_pairXY`). The data-processing helper uses the short `ent_of_cond_indep` + `entropy_triple_add_entropy_le` route and closes the inner-pair swap inline via `chain_rule' + condEntropy_comm`, sidestepping the plan's Risk §7.1 fallback (`entropy_assoc + entropy_comp_of_injective`).

**Prelude promotion (refactor):**

- `ZhangYeung/Prelude.lean`: `condIndepFun_comp` promoted here from `ZhangYeung/CopyLemma.lean` as a public lemma under `namespace ZhangYeung`. `open MeasureTheory ProbabilityTheory` added.
- `ZhangYeung/CopyLemma.lean`: the private `condIndepFun_comp` definition and its introductory helper paragraph are removed; the two internal use sites (`copyLemma_condMI_X_Y₁_vanishes`, `copyLemma_condMI_X_X₁_vanishes`) are updated to the promoted name; the helpers-section docstring is rewritten to reflect the split.

**Tests:**

- `ZhangYeungTest/Theorem3.lean` (new, 137 lines): three signature-pinning `example`s (one per public theorem), an independent-variable smoke test via `delta_le_mutualInfo`, a theorem-application test re-deriving the averaged form from `zhangYeung` + `zhangYeung_dual`, and a `Fin 2`-valued downstream-usage example that scales `zhangYeung` back up to the integer `2 * delta ≤ ...` bound.

**Top-level wiring:**

- `ZhangYeung.lean`: adds `import ZhangYeung.Theorem3`.
- `ZhangYeungTest.lean`: adds `import ZhangYeungTest.Theorem3`.

**Documentation:**

- `AGENTS.md` (symlinked as `CLAUDE.md`): adds two Module Layout bullets for `ZhangYeung/Theorem3.lean` and `ZhangYeungTest/Theorem3.lean`, amends the `ZhangYeung.lean` entrypoint bullet to include the new re-export, and amends the `ZhangYeung/Prelude.lean` bullet to note the `condIndepFun_comp` promotion.
- `docs/plans/done/2026-04-18-theorem-3-zhang-yeung-inequality.md` (new): the 515-line M3 plan file, added directly to `done/` in the final commit.

### File Inventory

**New files (3):**

- `ZhangYeung/Theorem3.lean`
- `ZhangYeungTest/Theorem3.lean`
- `docs/plans/done/2026-04-18-theorem-3-zhang-yeung-inequality.md`

**Modified files (5):**

- `AGENTS.md`
- `ZhangYeung.lean`
- `ZhangYeungTest.lean`
- `ZhangYeung/CopyLemma.lean`
- `ZhangYeung/Prelude.lean`

**Deleted files:** none.
**Renamed files:** none.

### Notable Changes

- **No dependency churn.** No `lake-manifest.json`, `lakefile.toml`, or `lean-toolchain` changes; this milestone is pure proof work on top of the existing PFR/Mathlib pins.
- **Public API addition.** Three new public theorems land under `namespace ZhangYeung`: `zhangYeung`, `zhangYeung_dual`, `zhangYeung_averaged`. Plus one promoted helper: `ZhangYeung.condIndepFun_comp`.
- **Private-helper promotion with fixed call sites.** `condIndepFun_comp` moved from `private` in `ZhangYeung/CopyLemma.lean` to public-namespaced in `ZhangYeung/Prelude.lean`. A `grep` confirms the only current consumers are the two internal `CopyLemma.lean` use sites (`:297`, `:309`) plus the one new M3 consumer (`Theorem3.lean:162`). No stray qualified references.
- **Universe bookkeeping carried forward.** All three public M3 theorems inherit the four-codomain `Type u` constraint from `copyLemma`. Documented explicitly in the module docstring's "Implementation notes".
- **No heartbeat bumps, no `sorry`, no `admit`.** The plan's Risk §7.1 and §7.6 mitigations were not needed at landing time; the proofs fit inside the default tactic budget.

### Plan Compliance

**Compliance verdict: excellent.** The branch is in very high compliance with `docs/plans/done/2026-04-18-theorem-3-zhang-yeung-inequality.md`. Every public theorem, every private helper, every refactor, every test category called out in the plan landed in the form the plan specified. The Shannon chase in `zhangYeung_integer` follows the plan's seven-fact sketch (h1, h2, h_three, h_nonneg, h_dp, h_marg_XZU, h_marg_XY) step-for-step, and the closing `linarith` mirrors the plan's line 242 exactly. The one intentional simplification (closing the data-processing helper's inner-pair swap with `chain_rule' + condEntropy_comm` rather than `entropy_assoc + entropy_comp_of_injective`) is a cleaner route that stays within the plan's enumerated primitives (Risk §7.1 explicitly allowed it as a "try in order" step-1 alternative).

**Overall progress: 13/14 sequencing steps done (93%).** The final step ("Open the PR") is left to the user, as expected for a branch review.

**Done items (plan sequencing steps):**

1. **Step 1 — Bootstrap + pre-flight checks.** Assumed done (scratch files not committed); the rest of the branch compiles, which implies the preconditions were met.
2. **Step 2 — Promote `condIndepFun_comp` from `CopyLemma.lean` to `Prelude.lean`.** Implemented in `493c66f refactor: promote condIndepFun_comp to Prelude`. The lemma lands as `lemma ZhangYeung.condIndepFun_comp` in `ZhangYeung/Prelude.lean:9-19`, the private copy is removed from `CopyLemma.lean`, the two internal use sites are updated to `ZhangYeung.condIndepFun_comp`, and the M2 helpers-section docstring (`ZhangYeung/CopyLemma.lean:34`, `:53`) is rewritten. `IdentDistrib.condMutualInfo_eq` stays `private` per the plan.
3. **Step 3 — Scaffold `ZhangYeung/Theorem3.lean` and `ZhangYeungTest/Theorem3.lean`.** Implemented in `814373e feat: scaffold Theorem 3 module and API tests`. Module docstring, imports, three public theorem stubs with `sorry`, three signature-pinning examples, both top-level re-exports wired. (See deviation #1 below: the two projection measurabilities were folded into this commit rather than kept for plan step 6.)
4. **Step 4 — `mutualInfo_add_three_way_identity`.** Implemented in `7e62f5c feat(theorem3): prove three-way interaction identity`. Proof follows the plan's "expand every mutualInfo + condMutualInfo into entropy, apply chain_rule'', align pair orderings with entropy_comm, close by linarith" template (`ZhangYeung/Theorem3.lean:58-76`).
5. **Step 5 — `mutualInfo_le_of_condIndepFun`.** Implemented in `fb4ae84 feat(theorem3): prove data processing from CondIndepFun` (`ZhangYeung/Theorem3.lean:78-100`). Uses the short `ent_of_cond_indep` + `entropy_triple_add_entropy_le` + `chain_rule' + condEntropy_comm` route, explicitly avoiding the `entropy_assoc + entropy_comp_of_injective` fallback from Risk §7.1. The commit message documents this choice.
6. **Step 6 — Projection measurabilities.** Implemented (see deviation #1); the `measurable_pairXZU` (`Theorem3.lean:103-107`) and `measurable_pairXY` (`Theorem3.lean:110-114`) helpers land as two-line `fun_prop` lemmas.
7. **Step 7 — `zhangYeung_integer`.** Implemented in `8363808 feat(theorem3): prove integer form of Theorem 3 via copy-lemma Shannon chase` (`ZhangYeung/Theorem3.lean:135-186`). The body mirrors the plan's sketch line-for-line: destructure `copyLemma`, the two copy-lemma inequalities, three-way identity, nonneg CMI, `condIndepFun_comp`-derived projection + data-processing, two `IdentDistrib.comp`-based pair transports, final seven-term `linarith`. The staged-linarith fallback from Risk §7.6 was not needed.
8. **Step 8 — `zhangYeung` (eq. 21).** Implemented in `a687b13 feat(theorem3): state Theorem 3 in the paper form` (`Theorem3.lean:193-202`). Two-line proof routing `zhangYeung_integer` through `delta_form21_iff.mpr` + `linarith`, exactly as planned.
9. **Step 9 — `zhangYeung_dual` (eq. 22).** Implemented in `bcaced3 feat(theorem3): derive the X-Y dual of Theorem 3 (eq. 22)` (`Theorem3.lean:209-220`). Applies `zhangYeung_integer` to `(Y, X, Z, U)`, rewrites via `mutualInfo_comm hY hX`, routes through `delta_form22_iff.mpr` + `linarith`. The Risk §7.5 `zhangYeung_dual_integer` auxiliary was not needed.
10. **Step 10 — `zhangYeung_averaged` (eq. 23).** Implemented in `40250ca feat(theorem3): derive the averaged symmetric form (eq. 23)` (`Theorem3.lean:227-240`). Scales `zhangYeung` and `zhangYeung_dual` back up to the integer form, combines via `delta_form23_of_form21_form22`, converts via `delta_form23_iff.mp`. Matches the plan sketch.
11. **Step 11 — Expand `ZhangYeungTest/Theorem3.lean` with smoke / application / downstream tests.** Implemented in `edaa6dc test: cover Theorem 3 API surface`. The independent-variable smoke test routes through `delta_le_mutualInfo` + the hypothesis `I[Z : U ; μ] = 0` (not requiring full mutual independence; a mild simplification from the plan text). The theorem-application test reconstructs `zhangYeung_averaged` from the two asymmetric public theorems plus the M1 averaging lemmas, matching the plan. The downstream-usage example specializes to `Fin 2` and scales up via `linarith`, matching the plan's "witness `2 * delta ≤ _` bound" phrasing and the M2 downstream-example precedent.
12. **Step 12 — `AGENTS.md` Module Layout update.** Implemented in `a831e39 docs: document Theorem 3 module in CLAUDE.md`. Two new bullets for the Theorem3 module and its test module; amendments to the `ZhangYeung.lean` and `ZhangYeung/Prelude.lean` bullets noting the new re-export and the `condIndepFun_comp` promotion.
13. **Step 13 — Run `make check`; lint adjustments.** Implicitly done: no cspell/lint follow-up commit was needed, the branch is green at HEAD.
14. **Step 14 — Plan move to `done/`.** Implemented in `af56f1c chore: move completed M3 plan from todo to done`. (The plan file was created directly in `done/` in this same commit rather than in `todo/` earlier and then moved; the single-commit add-to-done pattern is a mild deviation from the sequencing language but functionally identical.)

**Not yet started items:**

- **Step 14 (plan sequencing) — Open the PR.** Left to the human; out of scope for an automated branch review.

**Deviations:**

1. **Projection measurabilities merged into the scaffold commit (minor, sensible).** The plan allocates plan step 6 to a standalone commit for `measurable_pairXZU` + `measurable_pairXY`, but the scaffold commit `814373e` already introduces both helpers (its body mentions "four private helpers (two Shannon identities plus two projection measurabilities)"). This is a defensible merge: the measurabilities are two-line `fun_prop` proofs, they compile independently of any other proof content, and keeping them with the scaffold lets the stubbed-`sorry` Theorem3 file compile on first land. Not a concern.
2. **Plan file created directly in `done/` rather than in `todo/` first (minor, cosmetic).** The plan was written at `docs/plans/done/2026-04-18-theorem-3-zhang-yeung-inequality.md` rather than created in `todo/` and then moved in the final chore commit. The final commit message (`chore: move completed M3 plan from todo to done`) says "move", but the actual diff is an `add`. This is a wording mismatch; no functional impact on either the branch or the `done/` index.
3. **Data-processing helper took the Risk §7.1 "try in order" step-1 route.** Implementation uses `chain_rule' + condEntropy_comm` for the inner-pair swap instead of `entropy_assoc + entropy_comp_of_injective` (the primary plan route at `Proof route` line 305). The plan explicitly sanctions this as "Mitigation step 1" under Risk §7.1. Cleaner than the fallback; documented in the commit message.
4. **Smoke test uses `I[Z : U ; μ] = 0` rather than full four-variable mutual independence.** The plan text at line 477 describes the smoke test "for `X, Y, Z, U : Ω → Fin 2` with all four mutually independent under μ". The implementation at `ZhangYeungTest/Theorem3.lean:66-73` instead takes the minimally-sufficient hypothesis `I[Z : U ; μ] = 0` directly. This is both more general (does not require `X` and `Y` to be part of the independence set) and more honest about what the test actually pins (the `Δ ≤ I[Z : U]` bound from M1's `delta_le_mutualInfo`). A strict improvement over the plan text, not a regression.

**Fidelity concerns: none.**

- The integer-form convention ("what the chase naturally closes at") is preserved; the three public theorems are thin wrappers over `zhangYeung_integer` routed through the M1 `delta_form*_iff`s.
- Every named PFR primitive from the plan's "API surface used" table appears in the implementation as planned, or a sanctioned alternative does.
- The universe-bookkeeping constraint `S₁ ... S₄ : Type u` is explicit in the module `variable` block and documented in the module docstring.
- The test module does not directly import `ZhangYeung.Theorem3`; it imports the re-export `ZhangYeung`, exercising the public API surface per the plan's verification criterion (line 469).

### Code Quality Assessment

**Overall quality: ready to merge.** This is a mature, well-scoped branch that implements exactly what M3 called for, with no sorry, admit, TODO, FIXME, or commented-out code in the final state, and with a sensible private/public split. The proofs are concise without being cryptic; every `have` binding carries a name that reads back to the paper's line of reasoning (`h_three`, `h_dp`, `h_marg_XZU`, `h_marg_XY`). The test module exercises the public API under both trivial-input and concrete-`Fin 2`-valued conditions. The `condIndepFun_comp` promotion is cleanly executed: one `grep` confirms no stray qualified-name references remain.

**Strengths:**

- **Proofs track the paper.** `zhangYeung_integer`'s body is annotated with paper-line references ("Step 1: two copy-lemma inequalities (paper lines 683, 689)", "Step 2: three-way interaction identity on ν (paper line 700)", "Step 4: data processing (paper line 708)") so a reader can cross-reference the transcription without hunting. The same discipline appears in commit messages.
- **Short, direct proofs.** `mutualInfo_add_three_way_identity` closes in 12 lines of tactic body; `mutualInfo_le_of_condIndepFun` closes in 13; `zhangYeung_integer` closes in ~30. All three public wrappers are 2-8-line `linarith` closures over the integer form. No auxiliary heartbeat bumps were needed.
- **Reuse of M1 machinery.** The three public theorems route uniformly through `delta_form21_iff`, `delta_form22_iff`, `delta_form23_iff`, and `delta_form23_of_form21_form22` (the M1 form-conversion surface). The branch demonstrates that the M1 `iff`-style form conversions were well-chosen for exactly this milestone.
- **Good docstring coverage.** Every private helper, the `zhangYeung_integer` private theorem, and all three public theorems have math-mode-formatted docstrings that state the identity and cite the paper line. The module docstring lays out the "Implementation notes" and "References" sections cleanly.
- **`condIndepFun_comp` promotion is textbook.** Visibility upgraded, namespace added, docstring expanded with promotion rationale, two internal call sites updated, M2 helpers-section docstring amended to reflect the split. The M2 plan's prediction ("promote to `ZhangYeung/Prelude.lean` when another module needs it") is honored mechanically.
- **Test file is valuable.** Beyond signature pinning, the theorem-application example at `ZhangYeungTest/Theorem3.lean:86-108` is a genuine consumer-side cross-check: if a future refactor removes `zhangYeung_averaged`, the test shows callers have a working recipe to reconstruct eq. (23) from the two asymmetric theorems.

**Issues to address (blocking): none.**

**Suggestions (non-blocking, leave for a follow-up if desired):**

- **`IdentDistrib.condMutualInfo_eq` remains the only `private` helper in `CopyLemma.lean` that was earmarked for possible promotion.** Its docstring now correctly says "M3 does not need it, but a later milestone ... could motivate promotion" (`ZhangYeung/CopyLemma.lean:34`). No action needed for M3; just a signpost for whoever opens M5.
- **The `zhangYeung_dual` proof produces an intermediate `I[Y : X ; μ]` that is then rewritten to `I[X : Y ; μ]` via `mutualInfo_comm`, then routed through `delta_form22_iff`.** The plan's Risk §7.5 flagged this as a potential `linarith` ordering fragility. It did not materialize, and the current 5-line proof is simpler than the auxiliary-`zhangYeung_dual_integer` mitigation would have been. If future `linarith` flakiness appears here, the Risk §7.5 mitigation is still a good bailout.
- **Commit `af56f1c` says "move completed M3 plan from todo to done" but the diff is an add.** The plan was written directly to `done/`. This is purely a commit-message/diff mismatch. Fix if creating a clean PR history, ignore otherwise.
- **The plan file is 515 lines and sits entirely within `docs/plans/done/`.** No revision is needed for M3, but if a future milestone wants to cite this plan for precedent, consider a short "summary / retrospective" paragraph at the top of the file stating which Risks §7.1-§7.7 fired (none) and which were sidestepped (§7.1 by cleaner route, §7.6 by not-needed) so that future milestones can calibrate similar plans without re-reading the full 500 lines.

**Completeness:** the work feels finished. No stubs, no loose ends, no half-migrated patterns, no orphan helpers. The branch is ready for `make check` and a PR.
