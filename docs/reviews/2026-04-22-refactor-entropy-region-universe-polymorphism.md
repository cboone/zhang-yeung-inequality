## Branch Review: refactor/entropy-region-universe-polymorphism

Base: main (merge base: 7b77858)
Commits: 3
Files changed: 6 (0 added, 6 modified, 0 deleted, 1 renamed)
Reviewed through: c61a4c4

### Summary

This branch executes the follow-up plan `2026-04-20-entropy-region-universe-polymorphism.md`, generalizing `entropyRegion_n` and `almostEntropicRegion_n` from a `Type 0`-pinned existential to one that quantifies over the ambient `universe u` already declared in `ZhangYeung/EntropyRegion.lean`. The change is surgical: the definitions themselves, the two transport lemmas on that module, three private destructuring lemmas in `ZhangYeung/Theorem4.lean`, and both top-level exact-closure theorems (`theorem4`, `theorem4_ge_four`) now thread the same universe parameter. The test suite pins the new direct-membership surface (`entropyFn_n X μ ∈ entropyRegion_n.{u} n`), and both the originating M4.5 plan and the follow-up plan are updated to reflect the landed state.

### Changes by Area

**Entropy-region surface (`ZhangYeung/EntropyRegion.lean`)**
Rewrites `entropyRegion_n` to bind `(Ω : Type u)` and `(S : Fin n → Type u)` via the module-level `universe u` declaration (no `.{u}` on the def head, matching the local style used by `entropyFn_n`). `almostEntropicRegion_n` explicitly forwards the universe with `closure (entropyRegion_n.{u} n)`. The two transport lemmas `restrictFirstFour_mem_entropyRegion_n` and `restrictFirstFour_mem_almostEntropicRegion_n` gain `.{u}` annotations on both their hypotheses and their conclusions so that the restriction is a same-universe map. `Fintype` and `MeasurableSingletonClass` are retained inside the existential as the plan directed.

**Exact-theorem statements (`ZhangYeung/Theorem4.lean`)**
Three private helpers (`entropyRegion_four_subset_zhangYeungRegion_4`, `almostEntropicRegion_four_subset_zhangYeungRegion_4`, `not_mem_almostEntropicRegion_witness`) thread `.{u}` through their statements. The two public exact theorems `theorem4` and `theorem4_ge_four` now express the non-membership claim against `almostEntropicRegion_n.{u}`, keeping them universe-polymorphic. No proof bodies change beyond the universe annotations (and the `.{u}` routing through `h_restrict` in `theorem4_ge_four`).

**Tests (`ZhangYeungTest/EntropyRegion.lean`, `ZhangYeungTest/Theorem4.lean`)**
Region-surface pins add `.{u}` where needed, and a new `example` under `section Regions` witnesses the core motivating consequence: a `Type u` entropy function is literally a member of `entropyRegion_n.{u} n`, constructed by `⟨Ω, inferInstance, μ, inferInstance, S, …, X, hX, rfl⟩`. The Theorem 4 test module pins both `theorem4.{u}` and `theorem4_ge_four.{u}` at the universe-annotated signatures.

**Plan documentation (`docs/plans/...`)**
The M4.5 plan `2026-04-19-exact-theorem-4-entropic-region-closure.md` has its Universe discipline paragraph (Design §2) and Risks §4 rewritten to point at the follow-up plan and record that the `Type 0` restriction has been lifted. The follow-up plan `2026-04-20-entropy-region-universe-polymorphism.md` moves from `docs/plans/todo/` to `docs/plans/done/` with `status: done` and `branch: refactor/entropy-region-universe-polymorphism`, plus a completed-state Status section.

### File Inventory

**Modified (5)**

- `ZhangYeung/EntropyRegion.lean`
- `ZhangYeung/Theorem4.lean`
- `ZhangYeungTest/EntropyRegion.lean`
- `ZhangYeungTest/Theorem4.lean`
- `docs/plans/done/2026-04-19-exact-theorem-4-entropic-region-closure.md`

**Renamed (1)**

- `docs/plans/todo/2026-04-20-entropy-region-universe-polymorphism.md` → `docs/plans/done/2026-04-20-entropy-region-universe-polymorphism.md` (59% similarity; content also edited during the move to flip `status: proposed` → `status: done`, record the branch, rewrite Status and Goal to reflect the landed route-1 choice, add the "retain Fintype" and "single-universe convention" key decisions, expand Risks §1's downstream-surface enumeration, and note that `universe u` is already declared).

### Notable Changes

- **API-shape change on a public surface.** `entropyRegion_n`, `almostEntropicRegion_n`, `theorem4`, and `theorem4_ge_four` all gain an implicit universe parameter. Existing callers that left the universe free will still elaborate (Lean defaults them), but any caller that explicitly annotated `entropyRegion_n.{0}` previously did not exist; any new downstream code that *does* care about universes now has a literal set-membership path. No deprecation is needed, only documentation.
- **No dependency, CI, or build-config changes.** Lake config, toolchain, and CI workflows are untouched.
- **No new definitions or theorems.** Everything on the branch is either a universe annotation, a plan-doc edit, or one new `example` in the test module.

### Plan Compliance

**Compliance verdict: excellent.** The branch implements route 1 of the plan cleanly and exhaustively: every item the plan identified as part of the downstream sweep is updated, the key decisions the plan called out (retain `Fintype`, single-universe convention, plain `def` with ambient `universe u`) are all honored, and the exit criterion (a caller can write `F ∈ entropyRegion_n n` for a `Type u` entropy function without a manual `Type 0` detour) is pinned directly in the test module. No scope creep, no quality shortcuts, and both plan documents are kept in sync with the landed code.

**Overall progress: 5/5 verification criteria met.**

**Done items (route 1, from the plan's Design sketch and Key decisions):**

1. `entropyRegion_n` consumes the ambient `universe u` and binds `(Ω : Type u)`, `(S : Fin n → Type u)`. Implemented verbatim (`EntropyRegion.lean:70-75`), matching the plan's code block including the `Fintype` retention inside the existential.
2. `almostEntropicRegion_n` inherits the universe parameter, realized via the explicit `closure (entropyRegion_n.{u} n)` (`EntropyRegion.lean:79`). The plan's "likely yes" is resolved affirmatively.
3. Both transport lemmas (`restrictFirstFour_mem_entropyRegion_n`, `restrictFirstFour_mem_almostEntropicRegion_n`) thread `.{u}` through hypotheses, conclusions, and intermediate `MapsTo` constructions (`EntropyRegion.lean:123-146`).
4. All three private destructuring lemmas in `ZhangYeung/Theorem4.lean` (`entropyRegion_four_subset_zhangYeungRegion_4`, `almostEntropicRegion_four_subset_zhangYeungRegion_4`, `not_mem_almostEntropicRegion_witness`) are updated at lines 729-750. The Risks §1 enumeration called these out explicitly; every one is handled.
5. `theorem4` and `theorem4_ge_four` state the non-membership claim against `almostEntropicRegion_n.{u}` (`Theorem4.lean:753-757, 843-851`). These are the public paper-level theorems, kept universe-polymorphic as the plan's Key decisions §2 suggested.
6. Test-module pins refreshed: `ZhangYeungTest/EntropyRegion.lean:37,40,50,108` and `ZhangYeungTest/Theorem4.lean:107-108, 201-202`. The universe implicit is made explicit via `.{u}`, per Risk §2's warning.
7. Direct-membership example added (`ZhangYeungTest/EntropyRegion.lean:43-51`): `entropyFn_n X μ ∈ entropyRegion_n.{u} n` for arbitrary `Ω : Type u` and `S : Fin n → Type u`. This is the literal artefact that the plan's Goal and Exit criteria called for — the thing a user could not previously write without a detour.
8. The M4.5 plan's Universe-discipline section (`docs/plans/done/2026-04-19-exact-theorem-4-entropic-region-closure.md`, Design §2 and Risks §4) is rewritten to reflect the lifted restriction, satisfying Verification criterion 5.
9. Plan moved from `todo/` to `done/` with `status: done` and the branch recorded.

**Partially done items: none.**

**Not started items: none.**

**Deviations: none of substance.**

- *Minor stylistic deviation.* The plan's Risks §2 warned that universe parameters "may need to be annotated" in test pins, suggesting the annotation would be a response to breakage. In the diff, `.{u}` is used consistently across test pins even where elaboration alone might have succeeded. This is strictly more explicit and avoids coupling the tests to Lean's universe defaulting, which I read as an improvement on what the plan literally asked for, not a regression.
- *Cascading universe sweep was exactly the predicted surface.* Risks §1 in the plan enumerated nine declarations as the downstream blast radius. The diff touches precisely those nine (plus the test modules that pin them and the two plan docs), with no extra churn.

**Fidelity concerns: none.**

The implementation matches the plan's intent down to the stylistic choices — plain `def entropyRegion_n` with ambient `universe u` (not a `.{u}` head), single shared universe between `Ω` and `S` (matching `theorem4_finite`), and retained `Fintype`. The plan's Exit criterion names two alternative outcomes; the stronger one landed.

### Code Quality Assessment

**Overall quality: ready to merge.** The diff is small, focused, mechanical where it should be mechanical, and type-disciplined where it should be type-disciplined. It does exactly one thing and it does it cleanly.

**Strengths:**

- *Minimal surface touched.* Six files, no new definitions, one new `example`. Every line change is either a universe annotation or a plan-doc edit. That is the correct shape for a universe-polymorphism refactor and it minimizes review burden on downstream consumers.
- *Universe parameter routed explicitly where it matters.* The transport lemmas (`restrictFirstFour_mem_entropyRegion_n`, `restrictFirstFour_mem_almostEntropicRegion_n`) write `entropyRegion_n.{u} n` on both sides of the `MapsTo`. This rules out a class of failure mode where Lean unifies the two sides at different universes and produces an inscrutable error downstream.
- *Direct-membership test is exactly the right shape.* The new `example` at `ZhangYeungTest/EntropyRegion.lean:43-51` is the closest thing to a regression test for the stated goal: a `Type u` entropy function is now literally a member of the region set. It is proved by a single `⟨…⟩` with `inferInstance`, which is the cleanest possible witness that typeclass inference is intact and the membership is definitional.
- *Private helpers in `Theorem4.lean` were not overlooked.* The plan flagged that the destructuring pattern matches had to be updated. They are, correctly; the `letI`-heavy preamble in `entropyRegion_four_subset_zhangYeungRegion_4` (`Theorem4.lean:732-737`) continues to work because the shared universe makes typeclass transport trivial.
- *Documentation trail is good.* Both the originating M4.5 plan and the follow-up plan are updated in the same commit series. A future reader looking at either plan gets a consistent story; the M4.5 plan's Risks §4 "Resolution" paragraph even names the follow-up plan file.
- *Docstring on `entropyRegion_n` is updated to describe the new behaviour.* The phrasing "a `Type u` realization is literally a member of the set" is the clearest possible framing of what changed.

**Issues to address: none blocking.**

**Suggestions (optional, non-blocking):**

- *Docstring asymmetry on `almostEntropicRegion_n`.* The `entropyRegion_n` docstring was updated to mention the universe change, but `almostEntropicRegion_n`'s docstring (`EntropyRegion.lean:77`) still reads "The almost-entropic region `closure (Γ_n^*)`." A single line noting that the closure also ranges over the ambient `u` would match the symmetry the code already has. This is minor — the code itself is clear and the plan's Exit criterion does not call for it.
- *No public-lemma commentary on the universe implicit in `theorem4`.* `theorem4`'s docstring (`Theorem4.lean:752`) is unchanged. A reader who notices `almostEntropicRegion_n.{u}` in the statement and wonders whether `theorem4` is universe-polymorphic or `u`-fixed has to read `Theorem4.lean`'s header. A one-line addition to the docstring ("the non-membership claim holds at every universe `u`") would close that gap. Again, minor.
- *The explicit `theorem4.{u}` / `theorem4_ge_four.{u}` in the test module is belt-and-suspenders.* Since those theorems take their universe from the enclosing `universe u` at `ZhangYeungTest/EntropyRegion.lean:15` / `ZhangYeungTest/Theorem4.lean`, the `.{u}` annotation is explicit but not required. I read this as a deliberate defensive choice and would leave it; mentioning it only for completeness.

**Completeness:**

- No TODO, FIXME, HACK, or XXX comments introduced.
- No placeholder or commented-out code.
- New API surface (universe parameter on `entropyRegion_n`, `almostEntropicRegion_n`, `theorem4`, `theorem4_ge_four`) has a corresponding test example.
- Documentation is updated.
- No partial-implementation or half-migrated patterns visible.

The branch is in a ready-to-merge state. No follow-up work is implied by the diff.
