## Branch Review: formalize/m5-theorem-5

Base: main (merge base: db7483d8)
Commits: 5 (reviewed) + follow-up cleanups
Files changed: 11 (3 added, 8 modified, 0 deleted, 0 renamed)
Reviewed through: e322f64 (both Code Quality issues resolved in follow-up commits; see §Issues to address)

### Summary

This branch lands milestone M5 of the Zhang-Yeung formalization roadmap: the n+2-variable generalization of the Zhang-Yeung inequality (Theorem 5 of the 1998 paper, eqs. 27 and 28), whose proof the paper omits with the cryptic remark "uses exactly the same idea used in the proof of Theorem 3 and an inductive argument." The branch reconstructs that argument as a single tuple-valued copy-lemma application followed by a pairwise Lemma 2 chase, an n-ary chain-rule MI domination step proved by induction on `n`, data processing, and tuple-level marginal-equality transports. Two public theorems land (`theorem5`, `theorem5_averaged`), backed by four test-module `example`s including a base-case compatibility check that recovers the integer form of Theorem 3 at `n = 2`. As a prerequisite, three previously-private generic Shannon helpers are promoted to `ZhangYeung/Prelude.lean`.

### Changes by Area

**Theorem 5 (new module).** `ZhangYeung/Theorem5.lean` (393 lines, new). Five private helper lemmas (three measurability projections, one tuple-CondIndep projection, and the n-ary chain-rule MI domination `mutualInfo_add_n_way_inequality`) plus the two public theorems. The chase runs internally in `(Z, U)` order and rewrites to the paper's `I[U : Z]` order at the public boundary via `mutualInfo_comm` / `condMutualInfo_comm`.

**Test surface (new module).** `ZhangYeungTest/Theorem5.lean` (188 lines, new). Two signature-pinning `example`s, one `n = 2` base-case-compatibility `example` that recovers the Theorem 3 integer form, one assumption-level smoke test at `n = 3`, and one averaged-from-point-form derivation at `n = 3`.

**Generic-helper promotion.** Three previously `private` helpers are moved to `ZhangYeung/Prelude.lean`:

- `IdentDistrib.condMutualInfo_eq` (from `ZhangYeung/CopyLemma.lean`).
- `mutualInfo_add_three_way_identity` (from `ZhangYeung/Theorem3.lean`).
- `mutualInfo_le_of_condIndepFun` (from `ZhangYeung/Theorem3.lean`).

The two donor modules drop the helpers and rely on the public Prelude versions (their callers continue to resolve via `open ZhangYeung` / unqualified names; no API breakage).

**Module wiring.** `ZhangYeung.lean` and `ZhangYeungTest.lean` each gain one `import` line for the new modules.

**Documentation.** `AGENTS.md` (`CLAUDE.md`) gets a new Module Layout entry for `ZhangYeung/Theorem5.lean` and `ZhangYeungTest/Theorem5.lean`, and the existing `ZhangYeung/Prelude.lean` entry is updated to reflect the three new public helpers. The roadmap entry for M5 is tightened to describe the actual proof strategy (single tuple copy + pairwise Lemma 2 + internal induction) instead of the earlier "one auxiliary copy per X_j" phrasing. The full M5 plan lives at `docs/plans/done/2026-04-22-theorem-5-n-plus-two-variables.md`.

**Tooling.** `cspell-words.txt` gains new identifiers / fragments introduced in docstrings and proof bodies (`Binit`, `Btuple`, `castSucc`, `Xprime`, `Xstar`, `Xtuple`, `nlinarith`, `nomatch`, `nsmul`, `succ`, helper-name fragments `hpack`, `hsum`, `htail`, `htuple`, `hdiv`, `hfinal`, `hconst`).

### File Inventory

**New files (3):**

- `ZhangYeung/Theorem5.lean`
- `ZhangYeungTest/Theorem5.lean`
- `docs/plans/done/2026-04-22-theorem-5-n-plus-two-variables.md`

**Modified files (8):**

- `AGENTS.md`
- `ZhangYeung.lean`
- `ZhangYeung/CopyLemma.lean`
- `ZhangYeung/Prelude.lean`
- `ZhangYeung/Theorem3.lean`
- `ZhangYeungTest.lean`
- `cspell-words.txt`
- `docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md`

### Notable Changes

- **API surface expansion.** Three new public lemmas in `ZhangYeung.Prelude`. Promotion is API-additive for the existing donor modules (their previous `private` declarations had no public callers), so no breakage.
- **No new dependencies.** No `lakefile.toml`, `lake-manifest.json`, or `lean-toolchain` changes.
- **No CI changes.** Both `.github/workflows/ci.yml` and `text-lint.yml` are untouched.

### Plan Compliance

**Compliance verdict: strong on substance, lighter on commit granularity.** The branch lands every public deliverable the plan specifies and stays within all stated budgets, but it consolidates the plan's twelve sequenced commits into five.

**Overall progress: 12/12 deliverables landed (100%).**

#### Done items

1. **Bootstrap and pre-flight checks (sequencing step 1).** Implicitly performed; no separate commit, but the resulting `condIndep_copies` specialization at the tuple codomain is in place and works. The plan asked for the elaborator outcomes to be recorded in the bootstrap commit message; this trace is missing (see deviations).
2. **Promote three generic Shannon helpers (step 2).** ✅ `bc7fbd3 refactor: promote generic Shannon helpers to Prelude`. Promoted exactly the three helpers the plan called out (`mutualInfo_add_three_way_identity`, `mutualInfo_le_of_condIndepFun`, `IdentDistrib.condMutualInfo_eq`). Donor-module docstrings are updated to point at the new home.
3. **Scaffold `Theorem5` and test modules with sorries (step 3).** Bundled into the single `e322f64` feat commit; no intermediate scaffolding commit landed.
4. **`Fin n` projection helpers (step 4).** ✅ `measurable_pairZU`, `measurable_pairXZU`, `measurable_projZUX` land as `private` lemmas in `Theorem5.lean` (each one-line `fun_prop`).
5. **`tuple_condIndepFun_pairProj` (step 5).** ✅ Lands as a one-line invocation of `ZhangYeung.condIndepFun_comp` with `measurable_pi_apply`. Within budget.
6. **`mutualInfo_add_n_way_inequality` (step 6).** ✅ ~75 lines, just under the plan's ~80-line "split into its own module" trigger. The induction is `Nat.rec` over `n` with `Fin.sum_univ_castSucc` to peel the last coordinate, sidestepping the `Fin n` / pi-type friction the plan flagged in §7.1.iii.
7. **`theorem5` (step 7).** ✅ Lands as the main public theorem. Internal `(Z, U)` order with the rewrite back to the paper's `I[U : Z]` order at the boundary, exactly as planned. Within the §6.4.7 budget.
8. **`theorem5_averaged` (step 8).** ✅ Lands; ~50 lines (vs the plan's ≤20-line budget). The overage is in the explicit arithmetic bookkeeping (`hleft`, `hright`, `hdiv`, `hsplit`) needed to push the `n` coefficient through `Finset.sum_le_sum`. Not a concern.
9. **Test module expansion (step 9).** ✅ All four planned `example`s land: signature pin, base-case compatibility at `n = 2`, assumption-level smoke test at `n = 3`, averaged-from-point-form at `n = 3`.
10. **Update `AGENTS.md` / `CLAUDE.md` (step 10).** ✅ Both new module-layout entries land; the Prelude entry is updated to mention all three helpers.
11. **Run `make check` and address lint (step 11).** Build and `lake test` are both green; `cspell-words.txt` has been extended.
12. **Open the PR (step 12).** Out of scope for the current branch state.

#### Partially done items

None.

#### Not started items

None.

#### Deviations

1. **Commit granularity (significant procedural deviation).** The plan sequenced twelve commits, each a "small unit" maintaining a green build + lint + test, with explicit conventional-commit messages (`feat: scaffold Theorem 5 module and API tests`, `feat(theorem5): add Fin-indexed projection helpers`, `feat(theorem5): prove pairwise projection of tuple-level CondIndepFun`, `feat(theorem5): prove n-ary MI chain-rule domination`, `feat(theorem5): prove Theorem 5 via n-fold copy-lemma chase`, `feat(theorem5): derive the averaged symmetric form (eq. 28)`, `test: cover Theorem 5 API surface`, `docs: document Theorem 5 module in CLAUDE.md`, `chore: address lint feedback`). The branch instead has five commits, with all of steps 3-11 collapsed into the single `e322f64 feat: prove Theorem 5 n-plus-two-variable generalization`. **Assessment:** procedurally inconsistent with the plan's bisection-friendly cadence, but the resulting state is correct and complete. For a future failure, `git bisect` will land you on a 1200-line commit with no narrower scope. The user's `CLAUDE.md` standing rule "Prefer frequent small commits at each logical boundary rather than large batches" reinforces the plan's intent here. Worth a course-correct on future milestones.
2. **Bootstrap-commit elaborator-outcomes trace.** Plan §6.1 / §7.1 asked for pre-flight elaborator outcomes (tuple-codomain `condIndep_copies` specialization, `Finset` summation rehearsal) to be recorded in the bootstrap commit message so the audit leaves a trace after `scratch/m5-preflight.lean` is deleted. There is no bootstrap commit on the branch, so this trace is absent. **Assessment:** minor — the audit goal (confirming the API works) was clearly achieved since the proofs compile, but the documentary record is lost.
3. **`hn : 2 ≤ n` made anonymous in `theorem5`.** Plan headline at lines 110-127 of the plan kept the hypothesis named (`hn : 2 ≤ n`); the implementation uses `(_ : 2 ≤ n)` paired with a `match ‹2 ≤ n› with | _ => ...` wrapper around the conclusion (`ZhangYeung/Theorem5.lean:218,223`). The wrapper is semantically a no-op; it appears to be a workaround for the unused-argument lint. **Assessment:** see Code Quality §5d, item 1. Not a substantive change to the theorem, but unidiomatic.
4. **`theorem5_averaged` size overage (~50 vs ~20 lines).** Acknowledged above; not a concern.
5. **No `chore: address lint feedback` commit.** The lint adjustments (cspell additions) are bundled into the same `e322f64` feat commit. Procedural, not substantive.

#### Fidelity concerns

The implementation matches the plan's intent. Specifically:

- The chase runs in `(Z, U)` order internally and rewrites at the boundary, exactly as §6.4 stipulates.
- `mutualInfo_add_n_way_inequality` is built locally from `entropy_triple_add_entropy_le` via `Nat.rec`, exactly as §7.4 anticipated, and the predicted fallback to `List`-indexed induction was not needed.
- The plan's risk-7.1 (tuple-codomain `condIndep_copies`) materialized cleanly: the elaboration cost is one `let Xtuple := fun ω j => X j ω` plus `measurable_pi_lambda` (`Theorem5.lean:271`), with no awkward casting.
- The plan's risk-7.6 (heartbeat budget for `theorem5_integer`) is mooted because the eq. 27 chase has no `(1/2)` rescale and no integer stepping-stone is needed; the plan was tightened in commit `57d585e` to drop that stepping-stone.

### Code Quality Assessment

**Overall quality: ready to merge after two minor cleanups.** The proofs are clean, the structure mirrors the plan, all helpers are well-named and locally scoped, the test module exercises all four planned scenarios, and `lake build` + `lake test` are both green with no `sorry` or `admit`. Two cosmetic items below; both are straightforward to address.

#### Strengths

- **Faithful reconstruction.** The chase tracks the plan's six-step sketch (§6.4) and the §6 expanded body verbatim, which makes the proof readable next to the plan.
- **Helper scoping is right.** Five private helpers in `Theorem5.lean` (three measurability, one CondIndep projection, one chain-rule MI domination), all generic-looking but Theorem 5-specific in their immediate use; three genuinely generic helpers promoted to `Prelude.lean`. The split is principled.
- **Universe discipline preserved.** `S_U, S_Z, S i : Type u` matches M3/M4 conventions (Theorem5.lean:209).
- **Public-API order matches the paper.** Internal `(Z, U)` chase, rewrites to `I[U : Z]` at the boundary via `mutualInfo_comm` / `condMutualInfo_comm` (Theorem5.lean:332-355). Citation fidelity is preserved.
- **Test module is thorough.** Four `example`s: two signature pins, one base-case compatibility (`n = 2` recovers Theorem 3 integer form via the pi-to-prod entropy rewrite using `MeasurableEquiv.piFinTwo`), one assumption-level smoke test at `n = 3`, and one averaged-from-point-form derivation at `n = 3` proving the public surface is composable.
- **Docstrings are crisp.** Each public theorem cites the exact paper equation and section; the module docstring lays out the proof strategy.
- **Plan-prescribed risk mitigations applied.** The `Nat.rec` induction in `mutualInfo_add_n_way_inequality` (Theorem5.lean:124-201) avoids the `Fin n`-indexed pi-type-shrinking friction the plan flagged in §7.1.iii. The chase is decomposed into ~12 named `have`s, each with a bounded `linarith`, matching §7.6's split-before-bump guidance.

#### Issues to address

1. **`(_ : 2 ≤ n)` + `match ‹2 ≤ n› with | _ => …` wrapper in `theorem5`** (`ZhangYeung/Theorem5.lean:218`, `:223-228`). ✅ Resolved in `0570a91` (rename to `(_hn : 2 ≤ n)`, drop the match wrapper) and the Copilot-feedback follow-up that re-dropped the match wrapper while keeping `@[nolint unusedArguments]` + `_hn` for lint suppression. `theorem5` now matches `theorem5_averaged`'s style.
   The hypothesis was anonymous, then the conclusion wrapped in `match ‹2 ≤ n› with | _ => …`. This evaluates to its single arm, so the wrapper was semantically a no-op; its only purpose was consuming the hypothesis to suppress an unused-argument warning. The docstring at `:216` is honest about it ("the proof term itself does not need it"), but the syntax was unidiomatic and obscured the conclusion type when reading the signature. `theorem5_averaged` already used the conventional `(hn : 2 ≤ n)` (Theorem5.lean:357) where it is genuinely consumed, so the inconsistency was jarring inside one module.

2. **Duplicate `cboone` entry in `cspell-words.txt`** (lines 19 and 21). ✅ Resolved in `e43b9f1` (drop the duplicate that was inserted between `Btuple` and `castSucc`; the pre-existing alphabetized entry stays).

#### Suggestions

- **Consider promoting `mutualInfo_add_n_way_inequality` to `Prelude` in a follow-up.** It carries no Zhang-Yeung-specific content, and the plan flagged it as a Mathlib-upstream candidate (§roadmap §9). Not for this PR; for a roadmap §9 follow-up.
- **Consider extracting the explicit arithmetic in `theorem5_averaged` (`hleft`, `hright`, `hsplit`) to a private arithmetic lemma.** The proof would shrink from ~50 to ~25 lines and the closing `linarith` chain would be uniform with `theorem5`. Not required; the current structure is auditable.
- **The base-case-compatibility `example` (`ZhangYeungTest/Theorem5.lean:53-99`) uses pattern-matched `let`/`letI`/`have` bindings on `S`, `X`, the typeclass instances, and `hX`.** This is concise and works, but it does stress the elaborator. If a future Lean / Mathlib bump breaks it, an explicit `Matrix.cons`-style `![X₁, X₂]` family with `Fin.cases` proofs is the obvious fallback.
- **Future commit-discipline reminder.** Falling back from twelve planned commits to five collapses several genuinely independent units (helper additions, public theorem proofs, test landings, docs). For M6 onwards, sticking to the plan's commit cadence keeps `git bisect` precise and review chunks legible.
