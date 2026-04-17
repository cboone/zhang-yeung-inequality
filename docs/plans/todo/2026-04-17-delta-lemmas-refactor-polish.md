---
title: "Refactor and polish `ZhangYeung/Delta.lean`"
created: 2026-04-17
branch: refactor/delta-lemmas
supersedes_refs: docs/plans/done/2026-04-15-delta-equational-lemmas.md (M1 plan; delivered the module), docs/plans/done/2026-04-16-align-delta-with-verified-transcription.md (citation alignment; adjusted only docstring references)
---

## Context

`ZhangYeung/Delta.lean` was landed by the M1 plan (`docs/plans/done/2026-04-15-delta-equational-lemmas.md`) and nudged by the citation-alignment plan (`docs/plans/done/2026-04-16-align-delta-with-verified-transcription.md`). The current branch, `refactor/delta-lemmas`, exists to sand down three sources of friction that a re-read against project and Mathlib naming/style conventions surfaced. No mathematical content changes, no imports change, no proofs lengthen.

1. **Naming inconsistency.** Every lemma in the module starts with `delta_*` except the four paper-equation lemmas (`form21_iff`, `form22_iff`, `form23_of_form21_form22`, `form23_iff`). Outside the `ZhangYeung` namespace, `ZhangYeung.form21_iff` reads as if it concerns an abstract notion of «form» rather than the Zhang-Yeung delta, and readers lose the link to `delta` at call sites. Mathlib composes lemma names as subject-operation-property; `delta_form21_iff` fits that scheme.

2. **Variable-block scoping via `omit`.** The finite-alphabet block adds `[Fintype Sᵢ] [MeasurableSingletonClass Sᵢ]` for all four codomains, then uses `omit` on two lemmas (`delta_comm_main`, `delta_le_mutualInfo`) that only need the fixtures on the measured pair `S₁, S₂`. This works but costs two four-class `omit` lines and an extra mental hop per lemma. Two nested `section`s (outer adds fixtures on the measured pair; inner extends to the conditioning pair) express the dependency directly and eliminate the `omit`s.

3. **Explicit `X`, `Y` where they're inferrable.** `delta_comm_main` and `delta_le_mutualInfo` take `(X : Ω → S₃) (Y : Ω → S₄)` explicitly, but `X` and `Y` always appear in the conclusion and elaborator can infer them from the goal. PFR makes measured random variables implicit whenever the goal type determines them; conforming matches PFR call-site style and trims two arguments off each test-module invocation.

Two small docstring cleanups come along for the ride: `delta_comm_cond` carries a proof-sketch clause («; addition is commutative») that doesn't describe the statement; `delta_self`'s docstring mixes what-it-states with a caveat about copy-variable transport that belongs with the module-level design notes.

## Scope

**In scope:**

- Rename the four `formNN_*` lemmas to `delta_formNN_*` and propagate the rename through `ZhangYeungTest/Delta.lean`.
- Restructure the finite-alphabet block into two nested `section`s (outer `MeasuredFinite`, inner `AllFinite`), remove both `omit` clauses, and reorder `delta_eq_entropy` to the last position so it lives inside the inner section.
- Make `X`, `Y` implicit on `delta_comm_main` and `delta_le_mutualInfo`; drop those explicit arguments at the test-file call sites.
- `delta_comm_cond` docstring: drop the trailing «; addition is commutative» clause.
- `delta_self` docstring: keep only the one-sentence statement; move the copy-variable-transport caveat into the module's `## Implementation notes` section.
- Update the module docstring's `## Main statements` list to use the new names, and the `## Implementation notes` variable-staging paragraph to describe the two nested sections.

**Out of scope:**

- Any change to lemma statements (propositions), proof bodies, or the `delta` definition.
- Any new lemmas, new notation, new imports, or new typeclass assumptions.
- Any change to `ZhangYeung.lean` (the entrypoint manifest legitimately re-imports both `Prelude` and `Delta` per `.github/lean.instructions.md`) or to `ZhangYeung/Prelude.lean`.
- Any `@[simp]` tagging (`delta_def` is not tagged; PFR's analogous `mutualInfo_def` isn't tagged either).
- Any `lemma` → `theorem` switch (PFR uses `lemma` throughout and this project matches).

## Sequencing: two commits

Splitting lets a reviewer bisect naming concerns from structural ones.

### Commit A: rename form-family lemmas and tighten docstrings

Pure mechanical rename plus docstring edits. Compiles independently.

**`ZhangYeung/Delta.lean`:**

1. Rename, bodies and signatures otherwise unchanged:
    - `form21_iff` → `delta_form21_iff`
    - `form22_iff` → `delta_form22_iff`
    - `form23_of_form21_form22` → `delta_form23_of_form21_form22`
    - `form23_iff` → `delta_form23_iff`

2. Update the `## Main statements` block of the module docstring to reference the four new names (three bullet lines change).

3. `delta_comm_cond` docstring: replace

    ```
    /-- Swapping the two conditioning arguments leaves `delta` unchanged; addition is commutative. -/
    ```

    with

    ```
    /-- Swapping the two conditioning arguments leaves `delta` unchanged. -/
    ```

4. `delta_self` docstring: replace the two-sentence version with

    ```
    /-- The case `X = Y`: `Δ(Z, U | X, X) = I(Z; U) - 2·I(Z; U | X)`. -/
    ```

    and append a new paragraph to the module-level `## Implementation notes` section (keep each paragraph as a single long line, per project rule):

    ```
    The `delta_self` lemma handles only the *literal* repeated-conditioner case `X = Y`. Bridging `Δ(Z, U | X, X₁)` where `X₁` is merely a copy of `X` requires a separate transport lemma for `condMutualInfo` (under the copy construction's `IdentDistrib` hypotheses), which is out of scope for this module.
    ```

**`ZhangYeungTest/Delta.lean`:**

Four call-site renames inside `section PureAlgebra`:

- `form21_iff Z U X Y μ` → `delta_form21_iff Z U X Y μ`
- `form22_iff Z U X Y μ` → `delta_form22_iff Z U X Y μ`
- `(form23_iff Z U X Y μ).mp` → `(delta_form23_iff Z U X Y μ).mp`
- `form23_of_form21_form22 h21 h22` → `delta_form23_of_form21_form22 h21 h22`

Commit message: `refactor: rename delta form lemmas and tighten docstrings`.

Run `make check` and confirm green before starting commit B.

### Commit B: nest finite-alphabet sections and make `X`/`Y` implicit

**`ZhangYeung/Delta.lean`:**

1. Delete the existing single `variable [Fintype S₁] [Fintype S₂] [Fintype S₃] [Fintype S₄] [MeasurableSingletonClass …]` block and both `omit` clauses.

2. Replace the span from the `### Lemmas requiring finite-alphabet structure` separator through `end ZhangYeung` with two nested sections:

    ```lean
    /-! ### Lemmas requiring finite-alphabet structure

    The remaining lemmas rely on PFR's commutativity and entropy-expansion results, which are stated under discrete/countable hypotheses on the codomains of the measured random variables. An outer section fixes `[Fintype Sᵢ]` and `[MeasurableSingletonClass Sᵢ]` on the measured pair `S₁, S₂` for the symmetry and bounding lemmas; a nested inner section extends the same fixtures to the conditioning codomains `S₃, S₄` for the entropy-expansion lemma. Each fixture supplies the relevant `FiniteRange` obligations via the instance `{Ω G : Type*} (X : Ω → G) [Finite G] : FiniteRange X`. -/

    section MeasuredFinite

    variable [Fintype S₁] [Fintype S₂]
      [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]

    /-- Swapping the two measured arguments leaves `delta` unchanged, via `mutualInfo_comm` and `condMutualInfo_comm`. -/
    lemma delta_comm_main
        {Z : Ω → S₁} {U : Ω → S₂} (hZ : Measurable Z) (hU : Measurable U)
        {X : Ω → S₃} {Y : Ω → S₄} (μ : Measure Ω) :
        delta Z U X Y μ = delta U Z X Y μ := by
      simp only [delta_def, mutualInfo_comm hZ hU, condMutualInfo_comm hZ hU]

    /-- `Δ(Z, U | X, Y) ≤ I(Z; U)`: the delta is bounded above by the unconditional mutual information, since conditional mutual information is non-negative. -/
    lemma delta_le_mutualInfo
        {Z : Ω → S₁} {U : Ω → S₂} (hZ : Measurable Z) (hU : Measurable U)
        {X : Ω → S₃} {Y : Ω → S₄} (μ : Measure Ω) :
        delta Z U X Y μ ≤ I[Z : U ; μ] := by
      have h₁ : 0 ≤ I[Z : U | X ; μ] := condMutualInfo_nonneg hZ hU
      have h₂ : 0 ≤ I[Z : U | Y ; μ] := condMutualInfo_nonneg hZ hU
      rw [delta_def]; linarith

    section AllFinite

    variable [Fintype S₃] [Fintype S₄]
      [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]

    /-- Expand `delta` all the way down to raw entropy terms, using `mutualInfo_def` and `condMutualInfo_eq`. This is the bridge to any reasoning at the entropy layer directly (for example, evaluating `delta` on a concrete four-variable distribution when checking bounds or building counterexamples). -/
    lemma delta_eq_entropy
        {Z : Ω → S₁} {U : Ω → S₂} {X : Ω → S₃} {Y : Ω → S₄}
        (hZ : Measurable Z) (hU : Measurable U) (hX : Measurable X) (hY : Measurable Y)
        (μ : Measure Ω) [IsProbabilityMeasure μ] :
        delta Z U X Y μ
          = (H[Z ; μ] + H[U ; μ] - H[⟨Z, U⟩ ; μ])
            - (H[Z | X ; μ] + H[U | X ; μ] - H[⟨Z, U⟩ | X ; μ])
            - (H[Z | Y ; μ] + H[U | Y ; μ] - H[⟨Z, U⟩ | Y ; μ]) := by
      rw [delta_def, mutualInfo_def, condMutualInfo_eq hZ hU hX, condMutualInfo_eq hZ hU hY]

    end AllFinite

    end MeasuredFinite

    end ZhangYeung
    ```

    Signature deltas inside this reshape:

    - `delta_comm_main`: `(X : Ω → S₃) (Y : Ω → S₄)` → `{X : Ω → S₃} {Y : Ω → S₄}`.
    - `delta_le_mutualInfo`: `(X : Ω → S₃) (Y : Ω → S₄)` → `{X : Ω → S₃} {Y : Ω → S₄}`.
    - `delta_eq_entropy`: same signature; moved to the end.
    - Lemma order inside the finite-alphabet block: `delta_comm_main` → `delta_le_mutualInfo` → `delta_eq_entropy`, matching increasing strength of typeclass requirements.

3. Update the `## Implementation notes` paragraph that describes variable-block staging. Replace the current single-block-plus-omit description with wording that names the two nested sections and what each adds (outer adds fixtures on `S₁, S₂` for symmetry and bounding; inner extends to `S₃, S₄` for the entropy expansion). Keep the paragraph a single long line.

**`ZhangYeungTest/Delta.lean`:**

Two call-site edits inside `section FiniteAlphabet`:

- `simpa using delta_comm_main hZ hU X Y μ` → `simpa using delta_comm_main hZ hU μ`
- `simpa using delta_le_mutualInfo hZ hU X Y μ` → `simpa using delta_le_mutualInfo hZ hU μ`

Keep each `example` header with its explicit `(X : Ω → S₃) (Y : Ω → S₄)` binders: the test deliberately exercises call-site inference, which is the regression surface we want to protect.

The test file's own `section PureAlgebra` / `section FiniteAlphabet` structure stays flat (not nested); the test file doesn't need the `MeasuredFinite`-vs-`AllFinite` distinction because each `example` passes typeclass fixtures via the section's `variable` block uniformly.

Commit message: `refactor: nest finite-alphabet sections and make X, Y implicit in delta lemmas`.

## Final file shape

After both commits, `ZhangYeung/Delta.lean` is organized as:

1. `import ZhangYeung.Prelude`.
2. Module docstring (updated `## Main statements` with new names; updated `## Implementation notes` with the `delta_self` caveat paragraph and the two-section staging description).
3. `namespace ZhangYeung`, `open MeasureTheory ProbabilityTheory`, outer `variable {Ω …} {S₁ … S₄ …}` with `MeasurableSpace` fixtures only.
4. `delta` definition (unchanged).
5. `delta_def` (unchanged).
6. `delta_comm_cond` (docstring tightened).
7. `delta_self` (docstring tightened).
8. `delta_form21_iff` (renamed).
9. `delta_form22_iff` (renamed).
10. `delta_form23_of_form21_form22` (renamed).
11. `delta_form23_iff` (renamed).
12. Sectioning comment `### Lemmas requiring finite-alphabet structure`.
13. `section MeasuredFinite` with `S₁`+`S₂` finite-alphabet fixtures:
    1. `delta_comm_main` (`X`, `Y` implicit).
    2. `delta_le_mutualInfo` (`X`, `Y` implicit).
    3. `section AllFinite` extends fixtures to `S₃`, `S₄`:
        1. `delta_eq_entropy` (moved to end).
    4. `end AllFinite`.
14. `end MeasuredFinite`.
15. `end ZhangYeung`.

Zero `omit` lines. Net line count roughly unchanged (two four-class `omit`s drop out; two `section …` / `end …` pairs are added).

## Reused code and conventions

- **PFR API surface** (unchanged imports via `ZhangYeung.Prelude`): `mutualInfo_comm`, `condMutualInfo_comm`, `condMutualInfo_eq`, `mutualInfo_def`, `condMutualInfo_nonneg`. The `FiniteRange` instance `{Ω G} (X : Ω → G) [Finite G] : FiniteRange X` continues to discharge PFR's finite-range obligations via `Fintype`.
- **Mathlib naming composition**: subject `delta` + paper-equation tag `formNN` + property `iff` / `of_…` matches the `<subject>_<operation>_<property>` pattern (cf. `Finset.sum_comm`, `MulAction.mul_smul`).
- **PFR signature style**: implicit random variables where the goal determines them; explicit `Measurable` hypotheses as function arguments; explicit `Measure Ω` and `[IsProbabilityMeasure μ]` where needed. Mirrored in the refactored signatures.
- **Project entrypoint manifest rule** (`.github/lean.instructions.md`): `ZhangYeung.lean` re-imports `Prelude` and `Delta` explicitly; do not collapse to a single transitive import. No edit here.
- **Test-mirroring rule** (project `CLAUDE.md`): every proof-module change lands with the matching `ZhangYeungTest/` update in the same commit.

## Verification

Run from the worktree root. If this is a fresh clone or worktree, run `bin/bootstrap-worktree` first.

Per commit, in order:

1. `lake build ZhangYeung`: the refactor target compiles.
2. `lake build ZhangYeungTest`: the test mirror type-checks against the updated public API. Any missed rename surfaces as «unknown identifier»; any missed implicit-arg update surfaces as a too-many-arguments error.
3. `lake lint`: runs `batteries/runLinter`; catches missing docstrings and unused-variable warnings.
4. `lake test`: canonical test driver (equivalent to step 2; keeps the workflow aligned with CI).
5. `make check`: full gate — markdown + spelling + Lean lint + build + test. Matches CI.

Between commits A and B, `make check` must be green. If it isn't, do not proceed — bisect first.

After commit B, eyeball `git diff main...HEAD -- ZhangYeung/Delta.lean ZhangYeungTest/Delta.lean` to confirm:

1. All four form-lemma renames from commit A are preserved.
2. No `omit` lines remain anywhere in `Delta.lean`.
3. The inner `section AllFinite` / `end AllFinite` pair is balanced and nested inside `section MeasuredFinite`.
4. `delta_eq_entropy` is the last lemma before `end AllFinite`.
5. `X` and `Y` are implicit on both `delta_comm_main` and `delta_le_mutualInfo`.
6. The module docstring's `## Main statements` section lists the renamed lemmas.
7. The module docstring's `## Implementation notes` section contains the new `delta_self` caveat paragraph and the two-section staging description.

No external verification (reviewers, downstream builds) is required at this stage; the refactor is internal to the module and its mirror test file.

## Critical files

- `ZhangYeung/Delta.lean`: primary refactor target (renames, section restructure, signature flips, docstring edits).
- `ZhangYeungTest/Delta.lean`: mirror updates in the same commit per project test-mirroring rule.
- `.github/lean.instructions.md`: read-only; constrains `ZhangYeung.lean`'s double-import to stay untouched.
- `Makefile`: read-only; source of truth for the `make check` gate.
- `docs/plans/done/2026-04-15-delta-equational-lemmas.md`: read-only; M1 plan, origin of the lemma signatures being refactored.
