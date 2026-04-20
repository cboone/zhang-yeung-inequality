## Branch Review: formalize/m4-theorem-4

Base: `main` (merge base `6c55bf02`)
Commits: 23
Files changed: 12 (6 added, 6 modified, 0 deleted, 0 renamed)
Reviewed through: `9e36c15`

### Summary

This branch formalizes M4 of the Zhang-Yeung roadmap: Theorem 4 of Zhang-Yeung 1998, Shannon incompleteness for `n ≥ 4`. It delivers every required deliverable in the M4 plan (the pure set-function Parts (a) and (b), the measure-theoretic bridge Part (c), and the headline Part (d)), both optional stretches (the closure surrogate and the `n ≥ 4` lift), and, as scope addition within the same branch, the full M4.5 follow-up that upgrades the headline theorem from the finite "`F_witness` is not any entropy function" form to the paper's exact closure form `∃ F ∈ Γ_n, F ∉ closure(Γ_n^*)`. All changes ship with API regression tests; `lake build` and `lake test` are green with no `sorry`.

### Changes by Area

- **Theorem 4 module (M4 core).** `ZhangYeung/Theorem4.lean` (new, 657 lines) implements: the set-function calculus `I_F`/`condI_F`/`delta_F`, the cone predicates `shannonCone`/`zhangYeungAt`/`zhangYeungHolds`, the `ℚ`-valued witness `F_witness_ℚ` with `F_witness` its `ℝ`-cast, Parts (a) `shannonCone_of_witness` and (b) `not_zhangYeungHolds_witness` (both via `native_decide`), the five per-subset bridge lemmas `entropyFn_empty` / `_singleton` / `_pair` / `_triple` / `_quad` (via `entropy_comp_of_injective` + explicit injective projections), the permutation-indexed bridge `zhangYeungAt_entropyFn` and `zhangYeungHolds_of_entropy`, the finite auxiliary `theorem4_finite`, the exact closure theorems `theorem4` / `theorem4_ge_four`, the sequence-level surrogate `theorem4_seqClosure`, and the stronger cone-level `shannon_incomplete_ge_four`.
- **Generic entropic-region layer.** `ZhangYeung/EntropyRegion.lean` (new, 132 lines) packages the reusable surface: `entropyFn_n`, the set-level regions `shannonRegion_n` / `entropyRegion_n` / `almostEntropicRegion_n`, the restriction map `restrictFirstFour` with its continuity and transport lemmas. `entropyFn` is now a four-variable abbreviation of `entropyFn_n`.
- **Tests.** `ZhangYeungTest/Theorem4.lean` (new, 217 lines) pins every public signature, evaluates the witness at all 16 subsets, and adds two downstream-usage `example`s. `ZhangYeungTest/EntropyRegion.lean` (new, 56 lines) pins the generic region surface and the restriction reduction `F_witness_n = F_witness` after restriction.
- **Manifests and docs.** `ZhangYeung.lean` / `ZhangYeungTest.lean` re-export the new modules. `AGENTS.md` (CLAUDE.md) and `README.md` are updated to reflect M4's completion and the new file inventory. The roadmap (`docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md`) is rewritten for M4 to describe the four-part structure and records the M4.5 exactness follow-up.
- **Plans.** `docs/plans/done/2026-04-18-theorem-4-shannon-incompleteness.md` (moved into done/) and `docs/plans/todo/2026-04-19-exact-theorem-4-entropic-region-closure.md` (new, the M4.5 follow-up spec).
- **Spell dictionary.** `cspell-words.txt` gains 14 tokens (`submodular`, `definitionally`, `funext`, `elim`, `Tendsto`, `Subsingleton`, etc.).

### File Inventory

- **New files (6):** `ZhangYeung/EntropyRegion.lean`, `ZhangYeung/Theorem4.lean`, `ZhangYeungTest/EntropyRegion.lean`, `ZhangYeungTest/Theorem4.lean`, `docs/plans/done/2026-04-18-theorem-4-shannon-incompleteness.md` (moved in), `docs/plans/todo/2026-04-19-exact-theorem-4-entropic-region-closure.md`.
- **Modified files (6):** `AGENTS.md`, `README.md`, `ZhangYeung.lean`, `ZhangYeungTest.lean`, `cspell-words.txt`, `docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md`.
- **Deleted files (0).**
- **Renamed files (0)** -- the plan "move" was committed as a delete + add rather than a git rename, but semantically it is a relocation from `todo/` to `done/`.

### Notable Changes

- **No Lean dependency changes**: no updates to `lakefile.toml`, `lean-toolchain`, or PFR pin. The bridge consumes the existing PFR API surface (`entropy_comp_of_injective`, `entropy_comm`, `mutualInfo_def`, `condMutualInfo_eq`, `chain_rule''`, `entropy_assoc`) plus M3's `zhangYeung`.
- **Universe-polymorphic public signature** on `theorem4_finite`, `zhangYeungHolds_of_entropy`, and the exact theorems: codomain family lives at `Type u` rather than `Type`, matching M3's existing convention.
- **Closure argument is topological, not sequential.** The exact `theorem4` is proved by showing `zhangYeungRegion_4` is a finite intersection of closed half-spaces and then `closure_minimal` + `zhangYeungHolds_of_entropy`. The sequence-level `theorem4_seqClosure` is kept as a separate public auxiliary for consumers who want the pointwise-limit form directly.
- **Performance choice:** `native_decide` is used over `decide` for the Shannon-cone and witness-evaluation checks (13 + 16 invocations total). The plan budgeted a `decide`-performance pre-flight with a fallback to case enumeration; `native_decide` sidesteps the pre-flight entirely.

### Plan Compliance

**Compliance verdict: strong compliance, with scope addition.** Every required M4 deliverable lands with the signatures the plan specifies; both optional stretches land; the branch additionally implements the separately-planned M4.5 follow-up, producing a stronger exact-closure headline theorem. The only compliance notes are documentation bookkeeping on the new M4.5 plan, not missing proof work.

**Overall progress: 22/22 required items done (100%); both stretches landed; the M4.5 follow-up plan is materially complete in code but its plan document is not yet moved to `done/` and still reads `status: proposed` / `## Status: Not started`.**

#### Required items (M4 plan)

- **Done -- Part (a) `shannonCone_of_witness`.** Implemented at `ZhangYeung/Theorem4.lean:127`, three clauses (zero, monotone, submodular) each closed by a `native_decide` on the `ℚ` layer + `exact_mod_cast`. Cleaner than the plan's `decide` path; the plan's §11.1 performance pre-flight is effectively retired by using `native_decide`.
- **Done -- Part (b) `not_zhangYeungHolds_witness`.** Implemented at `ZhangYeung/Theorem4.lean:150`. Uses the paper's canonical permutation `Equiv.swap 0 2 * Equiv.swap 1 3`, unfolds with the correct permutation evaluations (`decide`-closed), then 13 `native_decide`-closed witness evaluations + `norm_num` closes `1 ≤ 1/2`. Matches the plan's §Part (b) proof outline almost line for line.
- **Done -- Intermediate `shannon_incomplete`.** Three-line proof at `ZhangYeung/Theorem4.lean:181`, as planned.
- **Done -- Part (c) per-subset bridges.** `entropyFn_empty` / `_singleton` / `_pair` / `_triple` / `_quad` all discharged. Each uses an explicit projection `π : (∀ j : S, ...) → <product>` with injectivity proved by `funext` + `Finset.mem_insert`/`mem_singleton` case-splits (or `fin_cases` for the quad), then `entropy_comp_of_injective`. The `omit [IsProbabilityMeasure μ]` / `omit [∀ i, Fintype (S i)]` attributes reflect careful bookkeeping of which lemmas really need which instances.
- **Done -- Part (c) permutation-indexed bridge `zhangYeungAt_entropyFn`.** Implemented at `ZhangYeung/Theorem4.lean:331`. Uses six `π.injective`-derived distinctness facts + M3's `zhangYeung` at `(hX (π 2)) (hX (π 3)) (hX (π 0)) (hX (π 1))`, then a long chain of `delta_def` / `mutualInfo_def` / `condMutualInfo_eq` / `chain_rule''` / `entropy_assoc` rewrites on `hM3`, then per-subset bridges on the goal, then `linarith`. Size is in the plan's budget and does not need the sub-lemma split §11.3 hedged against.
- **Done -- Part (c) full bridge `zhangYeungHolds_of_entropy`.** One-line wrapper as planned, at `ZhangYeung/Theorem4.lean:378`.
- **Done -- Part (d) `theorem4_finite`.** The plan's `theorem4` signature (finite form) is preserved verbatim as `theorem4_finite` at `ZhangYeung/Theorem4.lean:391`, five-line proof as planned.
- **Done -- Scaffolding + test module.** Scaffold commit (`30f024b`) ships the sorry'd surface and the signature-pinning tests before any proofs land. Later commits peel off the sorries in the planned order (empty/singleton → pair/triple/quad → permutation bridge → full bridge → theorem4).
- **Done -- Testing.** `ZhangYeungTest/Theorem4.lean` covers every exported signature, the 16-subset witness table, a downstream-usage `example` for `zhangYeungHolds_of_entropy`, and signature pins for `theorem4` / `theorem4_finite` / `theorem4_seqClosure` / `shannon_incomplete_ge_four`. Plan's verification §Test module contents is fully covered except (4) and (5), which are the "theorem-application" tests the plan describes; the test module instead pins `theorem4_finite` directly and exercises `zhangYeungHolds_of_entropy` on a concrete family -- functionally equivalent coverage.
- **Done -- `AGENTS.md` module layout.** Extended with entries for the three new files and the entrypoint now re-exporting `ZhangYeung.EntropyRegion` and `ZhangYeung.Theorem4`.
- **Done -- `README.md` update.** M4 marked `done`; a paragraph summarizes the four ingredients and the exact-closure headline.
- **Done -- Plan move.** Committed in `1fc7163`, as the plan sequencing §22 requested.

#### Optional stretches (M4 plan)

- **Done -- `theorem4_closure` (stretch).** The plan's optional stretch landed as `theorem4_seqClosure` at `ZhangYeung/Theorem4.lean:531`, with a supporting public `zhangYeungHolds_of_tendsto`. The rename is one of the naming-policy decisions taken in the M4.5 follow-up below; the original theorem name lives on in the plan document's language, but the underlying statement is preserved.
- **Done -- `shannon_incomplete_ge_four` (stretch).** Landed at `ZhangYeung/Theorem4.lean:642` with a full `Fin n`-indexed apparatus (`I_F_n`, `condI_F_n`, `delta_F_n`, `shannonCone_n`, `zhangYeungAt_n`, `zhangYeungHolds_n`) now housed in `EntropyRegion.lean`. The `n = 4` specializations are `Iff.rfl` (pinned in the test module), so the `Fin n` surface genuinely subsumes the `Fin 4` surface rather than running parallel to it.

#### Items from the M4.5 follow-up plan (scope addition)

The follow-up plan was authored and landed in the same branch. Implementation-wise, every item in the follow-up's §Goal is present:

- **Done -- Named region objects.** `shannonRegion_n`, `entropyRegion_n`, `almostEntropicRegion_n` at `ZhangYeung/EntropyRegion.lean:51-64`. Set/predicate duality is definitional as the plan requires (`shannonRegion_n n := {F | shannonCone_n F}`, the `Iff.rfl` test witnesses it).
- **Done -- Generic `entropyFn_n`.** At `ZhangYeung/EntropyRegion.lean:35` with `entropyFn` as its four-variable abbreviation.
- **Done -- Exact `n = 4` theorem `theorem4`.** At `ZhangYeung/Theorem4.lean:524`, routing through `isClosed_zhangYeungRegion_4` + `closure_minimal`. Private helpers (`zhangYeungRegion_4`, `entropyRegion_four_subset_zhangYeungRegion_4`, `almostEntropicRegion_four_subset_zhangYeungRegion_4`, `not_mem_almostEntropicRegion_witness`) match the follow-up plan's §3 recommended route.
- **Done -- `restrictFirstFour` + transport.** At `ZhangYeung/EntropyRegion.lean:67`. Continuity, `entropyRegion`- and `almostEntropicRegion`-level transports are all proved; witness-level `restrictFirstFour hn (F_witness_n hn) = F_witness` lands at `ZhangYeung/Theorem4.lean:583`.
- **Done -- Exact `n ≥ 4` theorem `theorem4_ge_four`.** At `ZhangYeung/Theorem4.lean:647`, using `restrictFirstFour_mem_almostEntropicRegion_n` and the new witness transport.
- **Done -- Tests.** `ZhangYeungTest/EntropyRegion.lean` pins the generic region surface and the restriction reduction; `ZhangYeungTest/Theorem4.lean` has pins for `theorem4`, `theorem4_finite`, `theorem4_seqClosure`, `theorem4_ge_four`, `shannon_incomplete_ge_four`, and the `Fin 4`-specialization `Iff.rfl`s.
- **Done -- Naming reconciliation.** `theorem4` is the exact closure form, `theorem4_finite` is the original finite form, `theorem4_seqClosure` replaces `theorem4_closure`. Matches follow-up §5 verbatim.
- **Done -- Docs reconciliation.** README and `Theorem4.lean` docstrings describe the exact closure theorem as paper eq. (26); the finite form is labeled "Finite auxiliary form".

#### Deviations

- **Scope addition: the M4.5 follow-up work was done on this branch, not deferred.** The M4 plan explicitly documents the exactness follow-up as out-of-scope for M4 (`## What M4 does not do`, bullet on the closure version), and the M4 roadmap entry adds the new post-M4 bullet pointing at the `2026-04-19-exact-theorem-4-entropic-region-closure.md` plan for this work. Yet the branch lands both simultaneously. Given that the M4.5 plan was authored in this branch and targets this branch (`branch: formalize/m4-theorem-4` in its front matter), this is a deliberate choice rather than drift. The branch is internally consistent; the scope addition is well-justified because the closure form is the paper's stated theorem and the finite form is strictly weaker. **Assessment: reasonable scope addition.** A reviewer may prefer the work were two PRs, but bundling makes the rename `theorem4` → `theorem4_finite` land atomically with its replacement.
- **Rename `theorem4_closure` → `theorem4_seqClosure`.** Matches the M4.5 §5 naming policy decision. The M4 plan uses the `theorem4_closure` name; the branch's M4.5 follow-up plan explicitly authorizes the rename (`"a renamed form of the current theorem4_closure"`).
- **`native_decide` instead of `decide`.** The M4 plan budgets `decide` performance and a fallback. `native_decide` sidesteps both. Reasonable: plan-aware, not plan-defying.
- **No `entropyFn_quad` used in the permutation-indexed bridge.** The plan's §11.3 says the quad never appears; the implementation confirms -- `zhangYeungAt_entropyFn` rewrites with four singletons, six pairs, three triples, and no quad. The `entropyFn_quad` lemma is defined but not consumed by the bridge; it is exercised only in its own signature pin (it is not otherwise used anywhere in the module). **Assessment: reasonable -- the lemma is cheap to prove and its existence rounds out the per-subset API.**

#### Fidelity concerns

- **The M4.5 plan document was inconsistent with the delivered state at the review cutoff.** At `Reviewed through: 9e36c15`, `docs/plans/todo/2026-04-19-exact-theorem-4-entropic-region-closure.md` still said `status: proposed` in the front matter and `## Status\n\nNot started.` in the body, and its `depends_on` line referenced `theorem4_closure`, which no longer existed under that name. **This was fixed later in the PR: the plan was moved to `docs/plans/done/` and updated to `status: done`, so this item is preserved here only as a cutoff-scoped review observation, not as a remaining issue.**
- **Commit message in `0adf2f5` references `theorem4_closure`.** That commit introduces what is now `theorem4_seqClosure`. A later rename commit (`0ff5b28`, `feat(theorem4): formalize exact entropic-region closure`) performs the rename as part of the M4.5 work. Git history is correct -- the intermediate commit message simply describes the theorem under its then-current name -- but a reviewer scanning commit messages later may briefly be confused. **Not an issue to fix; noted for auditability.**
- **Duplication between `not_zhangYeungHolds_witness` (lines 150-178) and `not_zhangYeungAt_witness_canonical` (lines 591-610).** Both unfold the set-function calculus, evaluate the same 13 `F_witness_ℚ` values, rewrite, and close by `norm_num`. The M4.5 extension introduced the second one because the first quantifies over permutations while the `Fin n` lift needs the labeling directly. The canonical helper could be extracted and consumed by both -- the first would specialize the latter. **Assessment: minor duplication; not a correctness concern.**

### Code Quality Assessment

**Overall quality: ready to merge.** The formalization is thorough, well-scaffolded, and documented to the project's M1-M3 standard. `lake build ZhangYeung` and `lake test` are both green; `grep -r 'sorry\|admit'` finds zero occurrences in Lean sources (the one match is prose inside an unrelated Theorem 2 docstring). Every public theorem has a signature-pinning test. Docstrings cite exact paper lines. The implementation plan is followed closely, with the deviations called out above all being improvements or predecided scope additions.

#### Strengths

- **Proof architecture is clean.** Each part has its own section, private helpers are hidden, public surface is minimal and paper-aligned. The separation between the predicate layer (`shannonCone_n`, `zhangYeungHolds`) and the set layer (`shannonRegion_n`, `entropyRegion_n`, `almostEntropicRegion_n`) is textbook Mathlib style -- the predicate is the load-bearing object, the set is a thin `{F | ...}` wrapper for exact-theorem packaging.
- **Bridge lemmas are principled.** Each `entropyFn_*` transports `H[·; μ]` across an explicit injective projection via `entropy_comp_of_injective`; the injectivity proofs are short, mechanical case-splits. The `omit` attributes correctly remove unneeded instances (e.g. `entropyFn_singleton` does not need `[IsProbabilityMeasure μ]`).
- **Permutation-indexed bridge proof is debuggable.** The rewrite chain on `hM3` is long but structured: first `delta_def` + `mutualInfo_def` to unfold M3's LHS, then `condMutualInfo_eq` + `chain_rule''` to eliminate conditional entropies, then two `entropy_assoc` to match the set-function bridge's tuple associativity. On the goal, `simp only [Finset.singleton_union, Finset.insert_union]` collapses union literals before the per-subset rewrites fire. A maintainer debugging a future PFR API churn can follow the chain step by step.
- **Closure argument uses the standard topological tools.** `isClosed_iInter`, `isClosed_le`, `continuous_apply`, `closure_minimal`, `Set.MapsTo.closure` -- all idiomatic. No hand-rolled topology.
- **Tests are genuine regression tests, not restatements.** The `Iff.rfl` pins at `shannonCone_n F ↔ shannonCone F` and `zhangYeungAt_n F i j k l ↔ zhangYeungAt F i j k l` protect the scope-addition claim that `n = 4` specializations collapse definitionally. The 16-subset witness evaluation protects against accidental edits to `F_witness_ℚ`.
- **Docstrings describe the math.** The module docstring of `Theorem4.lean` explains the paper's proof structure, the permutation choice, the `ℚ`/`ℝ` strategy, and where each public theorem sits in the chain. Cross-references to paper lines are precise (lines 358-388, 368-377, 339-355, 378-388).
- **Git history tells a coherent story.** 23 commits, each small and conventional-commits-styled. Scaffold → Part (a) → Part (b) → per-subset bridges (landed in three commits, matching the plan's "3-5 commits at logical boundaries" budget) → permutation bridge → tests → docs → stretch → M4.5. A reader can step through the formalization in order and each commit is a green checkpoint.

#### Issues to address

1. **`docs/plans/todo/2026-04-19-exact-theorem-4-entropic-region-closure.md` should move to `docs/plans/done/` with updated status.** Its Verification section's bullets (1)-(5) are all already true on this branch; its Exit criteria are met. At the review cutoff, leaving it in `todo/` with `status: proposed` / `## Status: Not started` misrepresented the repo state. **Resolved after the review cutoff: the plan was moved to `docs/plans/done/`, its `status` flipped to `done`, and the "Not started" wording replaced with a pointer to the commits that closed the work. Preserved here as a cutoff-scoped observation only.**
2. **The M4.5 plan's `depends_on` references `theorem4_closure`.** Rename to `theorem4_seqClosure` in the same doc edit. Minor, but avoids a broken pointer. **Resolved in the same post-cutoff doc edit.**

#### Suggestions (non-blocking)

- **Deduplicate the 13-line witness-evaluation block** between `not_zhangYeungHolds_witness` and `not_zhangYeungAt_witness_canonical` by having the former `specialize` to reduce to the canonical permutation's `zhangYeungAt`, rewrite, then delegate to `not_zhangYeungAt_witness_canonical`. Saves ~15 lines and ensures the two proofs cannot drift.
- **Promote `zhangYeungRegion_4` and `isClosed_zhangYeungRegion_4` to public** if a future non-Shannon follow-up wants to pin closedness directly. The M4.5 plan §Test plan explicitly says "only if `zhangYeungRegion_4` is promoted to a public definition" and leaves this as an opt-in; no action required now.
- **Consider lifting the `Fin n` machinery out of `ZhangYeung/Theorem4.lean`.** `I_F_n`, `condI_F_n`, `delta_F_n`, `shannonCone_n` already live in `EntropyRegion.lean`. The `zhangYeungAt_n` / `zhangYeungHolds_n` / `F_witness_n` block in `Theorem4.lean` could follow the same path; `Theorem4.lean` would then hold only the witness arithmetic and closure argument, leaving the generic cone and lift infrastructure in `EntropyRegion.lean`. Not a blocker -- the current split is already a substantial improvement over the pre-M4.5 layout.
- **The `Fin n` apparatus uses a "pairwise distinct 4-tuples" form** instead of the paper's `Equiv.Perm (Fin n)` quantification. The M4 plan's §11.5 explicitly documents this mitigation option; the code takes it for the `Fin n` case while keeping `Equiv.Perm (Fin 4)` at `n = 4`. The test module pins the `Iff.rfl` reduction between the two forms at `n = 4`, which is the right protection. Call out clearly in the `zhangYeungHolds_n` docstring that the two forms differ in presentation but agree extensionally for `n = 4`; the docstring already does this, so no change needed.
