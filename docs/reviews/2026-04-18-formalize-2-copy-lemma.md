## Branch Review: formalize/2-copy-lemma

Base: main (merge base: 28d2db37)
Commits: 20
Files changed: 8 (4 added, 4 modified, 0 deleted, 0 renamed) -- 1,507 insertions, 1 deletion
Reviewed through: 01e931e

### Summary

This branch completes milestone M2 of the Zhang-Yeung formalization roadmap: the copy lemma of Zhang-Yeung 1998 §III (equations 44-45). It adds `ZhangYeung/CopyLemma.lean` (477 lines) containing the main `copyLemma` existential built as a thin wrapper around PFR's `ProbabilityTheory.condIndep_copies`, the abstract Shannon identity `delta_of_condMI_vanishes_eq` (Lemma 2, Form A), and six specialized corollaries that ship two delta transports (between the original law μ and the copy law ν), two Form-B delta identities (specialized to the copy projections), and two inequality forms (`Δ ≤ I[X' : Y₁ ; ν]` and `I[Z:U] - 2·I[Z:U|X] ≤ I[X' : X₁ ; ν]`). A matching test module (`ZhangYeungTest/CopyLemma.lean`, 224 lines) signature-pins every public declaration and exercises the full M2-to-M3 flow on concrete `Fin 2`-valued random variables, including a Shannon-chase smoke test combining both inequality corollaries.

### Changes by Area

**Copy lemma implementation (`ZhangYeung/CopyLemma.lean`, new, 477 lines)**

The main deliverable. Structured as:

- `section Helpers` with two `private` generic helpers: `condIndepFun_comp` (target-side post-composition for PFR's random-variable form of `CondIndepFun`, filling a gap left by Mathlib's σ-algebra-form `CondIndepFun.comp`) and `IdentDistrib.condMutualInfo_eq` (three-variable `condMutualInfo` transport, filling a gap between PFR's `IdentDistrib.condEntropy_eq` and `IdentDistrib.mutualInfo_eq`).
- `theorem copyLemma` -- the main existential, proved by direct destructuring of `condIndep_copies (⟨X, Y⟩) (⟨Z, U⟩)` and repacking of the pair-level outputs into the six individual projections plus the 4-variable `IdentDistrib`s.
- `theorem delta_of_condMI_vanishes_eq` -- Lemma 2 Form A as an abstract Shannon identity under the vanishing-CMI hypothesis. Proof follows M1.5's `theorem2_shannon_identity` template (expand every MI/condMI to entropy via `mutualInfo_def` and `condMutualInfo_eq`, apply `chain_rule''`, align with `entropy_comm`, close with `linarith`). Closes at default `maxHeartbeats`.
- `section Consequences` nested into four sub-sections:
  - `TripleIdentDistribs`: three `private` triple-level `IdentDistrib` facts extracted from the copy's 4-variable outputs via `IdentDistrib.comp` with `projZUA` / `projZUB`.
  - `Finite`: two `private` conditional-MI vanishing facts (`X'`-`Y₁` and `X'`-`X₁`) and two public Form-B identities (`copyLemma_delta_identity_Y₁`, `copyLemma_delta_identity_X_X₁`).
  - `Transport`: two public bridge identities (`copyLemma_delta_transport_Y_to_Y₁`, `copyLemma_delta_transport_X_to_X₁`) and two public inequality corollaries (`copyLemma_delta_le_mutualInfo_Y₁`, `copyLemma_delta_le_mutualInfo_X_X₁`).

Files: `ZhangYeung/CopyLemma.lean` (new).

**Test coverage (`ZhangYeungTest/CopyLemma.lean`, new, 224 lines)**

Signature-pin `example` for each of the eight public theorems (one for `copyLemma`, one for `delta_of_condMI_vanishes_eq`, six for the `copyLemma_delta_*` corollaries). Two downstream-usage examples on concrete `Fin 2`-valued inputs:

1. Apply `copyLemma` then `copyLemma_delta_le_mutualInfo_Y₁` to close a `delta ≤ I[X' : Y₁]` inequality.
2. Shannon-chase smoke test: combine both inequality corollaries to witness `2·I[Z:U] - 3·I[Z:U|X] - I[Z:U|Y] ≤ I[X':Y₁] + I[X':X₁]` via `linarith` on `delta_def`.

Uncommitted change in this file: the `Signature` section variable block drops four instances (`[Fintype S₁]`, `[Fintype S₂]`, `[MeasurableSingletonClass S₁]`, `[MeasurableSingletonClass S₂]`) that `lake lint`'s unused-section-var detector would flag once the signature body itself only needs them on the S₃/S₄ side.

Files: `ZhangYeungTest/CopyLemma.lean` (new, with trailing uncommitted lint cleanup).

#### Module wiring and docs

- `ZhangYeung.lean` and `ZhangYeungTest.lean` each gain one `import` line for the new modules, preserving alphabetical ordering.
- `AGENTS.md`'s `Module Layout` section gains two entries (one for `CopyLemma.lean`, one for `ZhangYeungTest/CopyLemma.lean`) and updates the entrypoint line to reflect the new re-export ordering.
- `cspell-words.txt` gains 11 entries for new vocabulary in docstrings and plan docs (`ADBC`, `derivability`, `destructures`, `Distribs`, `Frobenius`, `informations`, `measurabilities`, `metaprogram`, `nilpotent`, `parameterizations`, `repackings`).

Files: `ZhangYeung.lean`, `ZhangYeungTest.lean`, `AGENTS.md`, `cspell-words.txt`.

#### Planning documents

- `docs/plans/done/2026-04-17-copy-lemma.md` (628 lines): the M2 plan, authored incrementally across four commits (initial plan, discovery-program side plan, assumptions refinement, review-feedback reconciliation), then moved from `todo/` to `done/` once all 14 sequencing steps had landed. Contains a substantive `Outcome` section documenting the three proof-engineering notes that diverged from the plan, the linter feedback that trimmed `copyLemma`'s signature, and the `omit [...] in` pattern used to keep `lake lint` green.
- `docs/plans/todo/2026-04-17-non-shannon-inequality-discovery-program.md` (162 lines): an exploratory research-program plan pointing at M2 (and beyond) as a dependency. Working-tree change updates its `depends_on` and end-of-file pointer from `todo/2026-04-17-copy-lemma.md` to `done/2026-04-17-copy-lemma.md` in step with the plan move.

Files: `docs/plans/done/2026-04-17-copy-lemma.md` (new), `docs/plans/todo/2026-04-17-non-shannon-inequality-discovery-program.md` (new, with trailing uncommitted pointer update).

### File Inventory

**New files (4):**

- `ZhangYeung/CopyLemma.lean`
- `ZhangYeungTest/CopyLemma.lean`
- `docs/plans/done/2026-04-17-copy-lemma.md`
- `docs/plans/todo/2026-04-17-non-shannon-inequality-discovery-program.md`

**Modified files (4):**

- `AGENTS.md`
- `ZhangYeung.lean`
- `ZhangYeungTest.lean`
- `cspell-words.txt`

**Deleted files:** none.

**Renamed files:** none. (The M2 plan was added directly to `docs/plans/todo/` and then relocated to `docs/plans/done/` via a `git mv` in `edb7133`; `git diff main..HEAD --name-status` collapses this into a single add under the final path, which is why no rename appears in the base-to-HEAD summary.)

### Notable Changes

- **New hard dependency on PFR's `condIndep_copies`.** This is the first module in the project to consume `ProbabilityTheory.condIndep_copies` (M1.5 pivoted to a KL route specifically to avoid it). The branch therefore puts weight for the first time on PFR's kernel-based two-copy construction; a future PFR revision bump that changes `condIndep_copies`'s signature or side conditions will require updating `CopyLemma.lean`'s main-theorem body (not its public signature -- the public signature is stated in PFR-agnostic terms).
- **Universe deviation from M1.** `copyLemma` binds `S₁ S₂ S₃ S₄ : Type u` rather than M1's `Type*`, because `condIndep_copies` requires its two codomains at a single universe. The deviation is documented inside the module docstring.
- **Two candidate-for-upstream helpers shipped `private`.** `condIndepFun_comp` and `IdentDistrib.condMutualInfo_eq` are both stated at generic signatures that would be useful to later Zhang-Yeung milestones and potentially to Mathlib or PFR. The plan defers promotion to `ZhangYeung/Prelude.lean` until another module needs them, which is a reasonable policy.
- **Two untracked files in the working tree (`server.heapsnapshot`, `tui.heapsnapshot`).** These look like Node.js V8 heap dumps (a debug artifact from some tool -- likely Claude Code or a terminal/TUI utility -- rather than a project artifact). They are not referenced by the build, the tests, or any commit on this branch; they should either be deleted from the worktree or added to `.gitignore` before merging so they do not leak into subsequent commits.

### Plan Compliance

**Plan:** `docs/plans/done/2026-04-17-copy-lemma.md`.

**Compliance verdict:** **Excellent.** The branch is in tight, thorough compliance with the plan. Every item in the plan's `Public surface` list is present at the signature the plan specified. Every sequencing step landed as a discrete commit, and the `Outcome` section at the end of the plan gives an honest accounting of the three places the implementation diverged from the plan's initial sketches. The deviations are all proof-engineering details that surfaced during implementation, not scope changes.

**Overall progress:** 14/14 sequencing steps done (100%).

**Done items (by public surface):**

- `copyLemma` -- `a946f4b`. Matches the plan's step 5 and signature exactly, minus the unused `[Fintype S₁] [Fintype S₂] [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]` instances trimmed in `3078d40` after linter feedback. The signature remains universe-polymorphic at `Type u`, as predicted.
- `delta_of_condMI_vanishes_eq` -- `f9ac054`. Matches the plan's step 8 signature and proof route (expand every MI/condMI, apply `chain_rule''`, align with `entropy_comm`, close by `linarith`). Plan budget was 30-40 tactic lines at potentially bumped heartbeats; the delivered proof is 39 lines at default heartbeats.
- `copyLemma_delta_identity_Y₁`, `copyLemma_delta_identity_X_X₁` -- `4140ed4`. Form-B Shannon identities, each a one-line application of `delta_of_condMI_vanishes_eq`.
- `copyLemma_delta_transport_Y_to_Y₁`, `copyLemma_delta_transport_X_to_X₁` -- `7a41801`. Bridge identities between Δ under μ and Δ under ν. The X-to-X₁ variant uses the `linarith`-over-three-`have`s workaround the plan did *not* anticipate; see "Fidelity concerns" below.
- `copyLemma_delta_le_mutualInfo_Y₁`, `copyLemma_delta_le_mutualInfo_X_X₁` -- `487ac23`. Inequality corollaries. Proofs are the predicted three-line combination of transport + identity + `condMutualInfo_nonneg` via `linarith`.

**Done items (by private helpers):**

- `condIndepFun_comp`, `IdentDistrib.condMutualInfo_eq` -- `786d90c`. Both in a dedicated `section Helpers` with matching docstrings pointing at the PFR/Mathlib gaps each fills.
- Three triple-level `IdentDistrib`s (`copyLemma_triple_XFirst`, `copyLemma_triple_YSecond`, `copyLemma_triple_XSecond`) -- `769a210`. The plan's reconciliation commit (`8c32187`) had dropped the redundant first-copy `Y` triple; the final implementation matches that reconciled list, not the pre-reconciliation list.
- Two conditional-MI vanishing facts (`copyLemma_condMI_X_Y₁_vanishes`, `copyLemma_condMI_X_X₁_vanishes`) -- `fe38d66`. Each uses `condIndepFun_comp` with explicit named implicits `(φ := Prod.fst) (ψ := Prod.snd)` -- the named-implicit annotation is one of the three divergences from the plan noted in the `Outcome` section.
- Measurable projection helpers (`projZUA`, `projZUB`, `measurable_projZUA`, `measurable_projZUB`, `measurable_pairZU`). The first four landed in `769a210`; `measurable_pairZU` was factored out post-hoc in `01e931e` when the author noticed both transport lemmas inlined the identical `fun p => (p.2.2.1, p.2.2.2)` measurability proof.

**Done items (by test coverage):**

- Signature-pin `example` for `copyLemma` -- `2a74bd0` (step 3).
- Signature-pin `example` for `delta_of_condMI_vanishes_eq` -- `1062019` (step 9).
- Signature-pin `example`s for all six `copyLemma_delta_*` corollaries, downstream-usage `example`, and Shannon-chase smoke test -- `0069540` (step 13).

**Done items (by documentation):**

- `AGENTS.md` Module Layout update -- `8f33789` (step 14).
- `cspell-words.txt` update -- `3078d40` (step 16).

**Not started items:** none.

**Partially done items:** none.

**Deviations:**

- **Extra pre-plan commits.** Four commits predate the implementation proper: `cc0cb8a` (initial plan), `2b136c3` (discovery-program side plan), `8e0e0e5` (plan assumptions refinement), `8c32187` (plan review-feedback reconciliation). These are all planning artifacts, not implementation drift. The plan's sequencing step 1 includes bootstrap + pre-flight checks; no scratch `.lean` files from those pre-flights remained in the tree, consistent with the plan's "delete after" directive. **Assessment:** not problematic -- normal plan-evolution commits.
- **Post-plan refactor.** `01e931e` (the HEAD commit) factors a duplicated measurability proof into `measurable_pairZU`. This is a lint/readability cleanup that landed after the plan's step 16 had already committed the final `make check` pass. **Assessment:** good incremental cleanup, correctly noted in the `Outcome` section.
- **Side-plan addition.** `docs/plans/todo/2026-04-17-non-shannon-inequality-discovery-program.md` is not mentioned in the M2 plan's `Files` section; it was added in commit `2b136c3` during planning. It describes an exploratory post-M2 research program and does not depend on anything M2 delivers beyond the copy lemma's existence. **Assessment:** out-of-scope for the M2 deliverable but justified by the author's reasoning that it belongs in the repo as project direction; its `depends_on` pointer now correctly references the copy lemma in `done/` after the working-tree update.

**Fidelity concerns:**

- **`copyLemma_delta_transport_X_to_X₁` proof style.** The plan's step 12 ("Land the two delta-transport lemmas. Each is ~8-12 tactic lines: expand `delta_def` twice, transport the three MI terms via `IdentDistrib.mutualInfo_eq` ... and `IdentDistrib.condMutualInfo_eq` ..., close with `ring` or `linarith`") implies a symmetric proof structure across the two transports. In practice the X-to-X₁ variant could not use `rw [..., IdentDistrib.condMutualInfo_eq ..., IdentDistrib.condMutualInfo_eq ...]` because both rewrite targets share the LHS pattern `I[Z : U | X ; μ]` -- the μ-side has `X` in both conditioner slots of `delta Z U X X μ`, so the first `rw` consumes both occurrences. The proof closes via `have e1, e2, e3 : ...` facts fed to `linarith`. This is noted accurately in the plan's `Outcome` section point 3. **Assessment:** minor, well-documented fidelity gap -- implementation matches the intent but not the tactic-level template.
- **`condIndepFun_comp` call sites need named implicits.** Per the `Outcome` section point 2, calls to `condIndepFun_comp` need explicit `(φ := Prod.fst) (ψ := Prod.snd)` annotations to defeat Lean's bidirectional elaboration, which otherwise unifies `φ := X'` with `f := id` and fails. The plan did not anticipate this. **Assessment:** fine -- discovered and handled, not papered over.
- **Shadowing of PFR's `condMutualInfo_eq`.** Per the `Outcome` section point 1, the `private` `IdentDistrib.condMutualInfo_eq` helper shadows PFR's `condMutualInfo_eq` via `open ProbabilityTheory` + dot notation, forcing callers to fully qualify as `ProbabilityTheory.condMutualInfo_eq`. **Assessment:** local idiom noted and applied consistently, but this is the kind of thing that would be worth a brief inline comment at the first shadowed call site, since future readers may trip on it.

### Code Quality Assessment

**Overall quality: ready to merge.** The code is clear, well-organized, consistent with the existing `ZhangYeung/Delta.lean` and `ZhangYeung/Theorem2.lean` conventions (same section structure, same docstring template, same namespace idiom), and has thorough test coverage. The implementation matches the plan's intent where it could and documents the three places it could not. No `sorry`, no `admit`, no `maxHeartbeats` bumps, no TODO/FIXME/HACK/XXX markers. Proofs are short and use Mathlib/PFR primitives directly rather than redundant scaffolding. The two working-tree items (the test-block lint cleanup and the plan pointer update) are small, correct, and should be committed before the PR merges.

**Strengths:**

- **Thorough, paper-anchored docstrings.** Every public declaration cites the paper equation or line number it formalizes, and the module docstring (lines 5-43 of `CopyLemma.lean`) summarizes the full paper-to-Lean mapping with a pointer to the verified transcription. Implementation-note paragraphs explain *why* each helper is private and *why* the universe binding is at `Type u` rather than `Type*`.
- **Well-structured proof skeleton.** The `section Helpers` -> main theorems -> `section Consequences` (itself broken into `TripleIdentDistribs` -> `Finite` -> `Transport`) layout mirrors the plan's recommended structure one-to-one, and each section's `variable` block declares precisely the instances that section's lemmas need and no more. Combined with the `omit [Fintype S₂] [MeasurableSingletonClass S₂] in` directives in the X-X₁-flavored lemmas, `lake lint`'s unused-section-var detector has nothing to flag.
- **Test coverage matches the public surface one-to-one.** The `ZhangYeungTest/CopyLemma.lean` signature-pin pattern is sound -- a future signature change breaks the test at compile time, which is exactly the right guardrail while M3 is not yet built. The Shannon-chase smoke test is a particularly valuable inclusion: it exercises the M1-to-M2 bridge explicitly rather than trusting that "two inequalities in scope will compose cleanly downstream".
- **Clean refactor in `01e931e`.** Noticing the duplicated `h4to2` measurability proof across two transport lemmas and hoisting it to `measurable_pairZU` -- alongside the existing `measurable_projZUA` / `measurable_projZUB` helpers -- is the right instinct: three sibling projection measurabilities in one place beats two inlined copies plus one already-hoisted helper.
- **Honest `Outcome` section.** The plan's final section calls out three proof-engineering divergences from the sketch and explains each one. That is the right level of post-hoc documentation: specific enough to be useful to a future reader, not so verbose that it replicates the proof body.

**Issues to address (before merge):**

1. **Commit the uncommitted test-file cleanup.** `ZhangYeungTest/CopyLemma.lean`'s `Signature` section drops four unused instances. This is a correct `lake lint` cleanup (matches the pattern applied to `copyLemma` itself in `3078d40`) and should land as a follow-up `chore: ...` commit rather than sit in the working tree through the PR.
2. **Commit the discovery-program plan pointer update.** `docs/plans/todo/2026-04-17-non-shannon-inequality-discovery-program.md` updates `depends_on:` and the final "M2 plan:" pointer from `todo/2026-04-17-copy-lemma.md` to `done/2026-04-17-copy-lemma.md`, matching the plan move in `edb7133`. This is a one-line internal reference fix that ideally would have been part of `edb7133`; committing it now keeps the reference accurate.
3. **Clean up or gitignore the two heap-snapshot files.** `server.heapsnapshot` and `tui.heapsnapshot` are sitting untracked in the worktree. They are almost certainly accidental debug artifacts; either `git clean` them locally or add `*.heapsnapshot` to the project `.gitignore` to avoid leaking them into a future commit.

**Suggestions (non-blocking):**

- **Consider adding a one-line inline comment** at the first use site of the shadowed `ProbabilityTheory.condMutualInfo_eq` call inside `delta_of_condMI_vanishes_eq`'s proof, noting the shadowing-via-`IdentDistrib.condMutualInfo_eq` subtlety. The `Outcome` section of the plan captures this, but plans rot; a single-line `--` comment at the proof noting the shadowing would survive longer. Not a blocker.
- **When M3 lands**, revisit whether `condIndepFun_comp` and `IdentDistrib.condMutualInfo_eq` want promotion from `private` to `ZhangYeung/Prelude.lean`. The plan flags this as deferred work; the decision becomes concrete as soon as a second module needs either helper.
- **The cspell-words additions include `Frobenius` and `nilpotent`**, which come from the adjacent discovery-program plan, not from `CopyLemma.lean`. These tokens are not strictly needed by the M2 deliverable; committing them alongside the M2 lint fix (`3078d40`) is harmless but blurs the commit's scope slightly. Not worth rewriting history for.
