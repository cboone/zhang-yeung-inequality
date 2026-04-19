---
title: "M4.5: exact Theorem 4 via entropic-region closure"
created: 2026-04-19
status: proposed
branch: formalize/m4-theorem-4
roadmap: docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md
depends_on: M4 (`ZhangYeung/Theorem4.lean`), especially `F_witness`, `F_witness_n`, `zhangYeungHolds_of_entropy`, `zhangYeungHolds_of_tendsto`, `theorem4_closure`, and `shannon_incomplete_ge_four`. This follow-up closes the remaining gap between the current M4 implementation and the paper's exact statement `\bar{\Gamma}_n^* \neq \Gamma_n`.
---

## Status

Not started. The current branch has the core mathematics of the witness argument, but its exported theorem packaging still stops short of the paper's exact top-level statement.

## Context

Theorem 4 of [@zhangyeung1998, §II, eq. 26; `references/transcriptions/zhangyeung1998.md` lines 357-379] states:

$$
\bar{\Gamma}_n^* \neq \Gamma_n \qquad (n \ge 4).
$$

The current M4 branch proves three nearby statements instead:

- `theorem4`: there exists `F : Finset (Fin 4) → ℝ` in `Γ_4` that is not the entropy function of any single four-variable discrete family.
- `theorem4_closure`: `F_witness` is not the pointwise limit of any sequence in `\tilde{\Gamma}_4`.
- `shannon_incomplete_ge_four`: for each `n ≥ 4`, there exists `F : Finset (Fin n) → ℝ` in `Γ_n` with `F ∉ \tilde{\Gamma}_n`.

These results are mathematically useful, and together they strongly suggest the paper's theorem, but the repo still lacks the exact set-theoretic formalization of the entropic region `\Gamma_n^*`, its closure `\bar{\Gamma}_n^*`, and the `n ≥ 4` separation stated in the paper.

## Goal

Land the exact paper-level theorem as a named Lean theorem whose statement is genuinely about the closure of the entropic region.

Concretely, the follow-up should end with:

1. a named set of Shannon-region points `Γ_n` on `Finset (Fin n) → ℝ`,
2. a named set of entropic points `Γ_n^*`,
3. a named set of almost-entropic points `\bar{\Gamma}_n^* := closure(Γ_n^*)`,
4. an exact `n = 4` theorem `∃ F ∈ Γ_4, F ∉ \bar{\Gamma}_4^*`,
5. an exact `n ≥ 4` theorem `∃ F ∈ Γ_n, F ∉ \bar{\Gamma}_n^*`.

## Non-goals

- No work on Theorem 5.
- No work on Theorem 6 or inner-bound material.
- No attempt to formalize a broader theory of entropic cones beyond what Theorem 4 needs.
- No compatibility layer for old theorem names unless a concrete downstream user requires it.

## Design

### 1. Introduce named region objects

The current code has predicates such as `shannonCone_n`, but the paper's theorem is naturally a statement about sets. The follow-up should add named set-level wrappers on `Finset (Fin n) → ℝ`.

Recommended public names:

- `shannonRegion_n (n : ℕ) : Set (Finset (Fin n) → ℝ)` for `Γ_n`.
- `entropyRegion_n (n : ℕ) : Set (Finset (Fin n) → ℝ)` for `Γ_n^*`.
- `almostEntropicRegion_n (n : ℕ) : Set (Finset (Fin n) → ℝ)` for `\bar{\Gamma}_n^*`, defined as `closure (entropyRegion_n n)`.

`shannonCone` and `shannonCone_n` remain useful predicate-level APIs and should stay public. The new set-level objects are wrappers used by the exact theorem packaging, not replacements.

### 2. Generalize the entropy-function surface from `Fin 4` to `Fin n`

The exact theorem needs a generic notion of an `n`-variable entropy function. Add:

```lean
noncomputable def entropyFn_n
    {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} {S : Fin n → Type u}
    [∀ i, MeasurableSpace (S i)]
    (X : ∀ i : Fin n, Ω → S i) (μ : Measure Ω) : Finset (Fin n) → ℝ := ...
```

Then define the current `entropyFn` as the `n = 4` specialization, either by direct abbreviation or by restating the definition through `entropyFn_n`. This keeps the existing M4 API available while giving the exact theorem a generic entropic-region object.

The corresponding entropic-region definition should be existential over the probability space, the codomain family, and the measurable random variables:

```lean
def entropyRegion_n (n : ℕ) : Set (Finset (Fin n) → ℝ) :=
  {F | ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (S : Fin n → Type u),
      ... ,
      F = entropyFn_n X μ}
```

This is the first point where the repository will literally name `Γ_n^*` rather than reasoning around it.

### 3. Prove the exact `n = 4` theorem through a closed-cone argument

The current `theorem4_closure` works with sequences in `\tilde{\Gamma}_4`. The exact theorem should instead route through an actual closed-set proof.

Recommended route:

1. Define the set `zhangYeungRegion_4 : Set (Finset (Fin 4) → ℝ) := {F | zhangYeungHolds F}`.
2. Prove `IsClosed zhangYeungRegion_4` directly in the topology on `Finset (Fin 4) → ℝ`.
3. Prove `entropyRegion_n 4 ⊆ zhangYeungRegion_4` using the existing `zhangYeungHolds_of_entropy` bridge.
4. Deduce `almostEntropicRegion_n 4 ⊆ zhangYeungRegion_4` by `closure_minimal`.
5. Use `not_zhangYeungHolds_witness` to conclude `F_witness ∉ almostEntropicRegion_n 4`.

This yields the exact `n = 4` paper statement without appealing to a sequential-closure surrogate.

The proof of `IsClosed zhangYeungRegion_4` should be topological, not sequential. The cleanest implementation is to express `zhangYeungHolds` as a finite intersection over permutations of preimages of closed `≤`-relations under continuous coordinate-linear maps.

### 4. Lift from `n = 4` to all `n ≥ 4` by restriction to the first four coordinates

The paper says it suffices to handle `n = 4`. The implementation should follow that strategy directly rather than proving a fresh `n`-ary Zhang-Yeung bridge.

Add a restriction map:

```lean
def restrictFirstFour (hn : 4 ≤ n) :
    (Finset (Fin n) → ℝ) → (Finset (Fin 4) → ℝ) :=
  fun F α => F (α.image (Fin.castLE hn))
```

or the equivalent preimage-based form, whichever makes the witness lemmas cleaner.

Required lemmas:

1. `restrictFirstFour` is continuous.
2. `restrictFirstFour hn (F_witness_n hn) = F_witness`.
3. If `F ∈ entropyRegion_n n`, then `restrictFirstFour hn F ∈ entropyRegion_n 4`.
4. Therefore, if `F ∈ almostEntropicRegion_n n`, then `restrictFirstFour hn F ∈ almostEntropicRegion_n 4`.

With these in hand, the exact `n ≥ 4` theorem is immediate: if `F_witness_n hn` were almost entropic in dimension `n`, its restriction would make `F_witness` almost entropic in dimension `4`, contradicting the exact `n = 4` theorem.

This route is preferable to proving that every `n`-variable entropy function lies in a generalized `\tilde{\Gamma}_n`, because it matches the paper's reduction and reuses the current M4 bridge instead of rebuilding it at higher arity.

### 5. Recommended theorem naming

The current theorem names are historically useful but slightly misleading relative to the paper.

Recommended final state:

- `theorem4_finite`: the current theorem stating that `F_witness` is not any four-variable entropy function.
- `theorem4`: the exact paper-level theorem, stated as `∃ F ∈ Γ_4, F ∉ \bar{\Gamma}_4^*` or its `n ≥ 4` form if that is the preferred headline.
- `theorem4_ge_four`: the exact paper-level theorem for all `n ≥ 4`, if the `n = 4` and `n ≥ 4` statements are exported separately.
- `theorem4_seqClosure` or `zhangYeungRegion_seqClosed`: a renamed form of the current `theorem4_closure` if its stronger sequence-level statement is kept public.

Because the project has not released a stable API, the default should be to rename toward paper-accurate names rather than to preserve the current weaker naming. If a concrete downstream consumer appears before this work lands, revisit that decision explicitly.

## File layout

Preferred layout:

```text
ZhangYeung/
  EntropyRegion.lean         # NEW: `entropyFn_n`, region sets, restriction maps, continuity lemmas
  Theorem4.lean              # witness arithmetic, closedness of `tildeΓ_4`, exact theorems
ZhangYeungTest/
  EntropyRegion.lean         # NEW: API tests for generic region objects
  Theorem4.lean              # updated exact-theorem tests and renamed finite/sequence theorems
```

`EntropyRegion.lean` is justified because the generic entropic-region surface is reusable beyond Theorem 4 and would otherwise make `Theorem4.lean` carry both witness arithmetic and all reusable topology infrastructure.

If the generic region layer stays under roughly 100 lines after prototyping, it may remain inside `Theorem4.lean`, but the default implementation should start with the split above.

## Sequencing

### Commit 1: scaffold the generic entropy-region layer

- Add `ZhangYeung/EntropyRegion.lean` with `entropyFn_n`, `shannonRegion_n`, `entropyRegion_n`, `almostEntropicRegion_n`.
- Define `entropyFn` as the `n = 4` specialization if it moves out of `Theorem4.lean`.
- Add `ZhangYeungTest/EntropyRegion.lean` with signature pins for the new definitions.
- Wire `ZhangYeung.lean`, `ZhangYeungTest.lean`, `AGENTS.md`, and `README.md` if a new public module lands.

Suggested commit: `feat(entropy-region): add generic entropic-region surface`

### Commit 2: add the first-four restriction map and transport lemmas

- Implement `restrictFirstFour`.
- Prove continuity.
- Prove `restrictFirstFour hn (F_witness_n hn) = F_witness`.
- Prove transport of actual entropy functions under restriction.
- Add API tests for the restriction map and the `F_witness_n` reduction.

Suggested commit: `feat(entropy-region): add first-four restriction transport`

### Commit 3: prove the exact `n = 4` theorem

- Define `zhangYeungRegion_4` (or keep it private if the public surface does not need it).
- Prove it is closed.
- Prove `entropyRegion_n 4 ⊆ zhangYeungRegion_4`.
- Derive `almostEntropicRegion_n 4 ⊆ zhangYeungRegion_4`.
- Use `F_witness` to prove the exact `n = 4` closure separation.
- Rename the current `theorem4` / `theorem4_closure` pair if the naming decision is taken here.

Suggested commit: `feat(theorem4): prove exact n-equals-4 closure separation`

### Commit 4: lift the exact theorem to `n ≥ 4`

- Use `restrictFirstFour` and the lifted witness `F_witness_n`.
- Prove the exact `n ≥ 4` theorem.
- Keep `shannon_incomplete_ge_four` as a useful cone-level corollary unless it becomes redundant.

Suggested commit: `feat(theorem4): lift exact theorem 4 to n-ge-4`

### Commit 5: reconcile docs and tests with the final theorem names

- Update `ZhangYeungTest/Theorem4.lean` to pin the exact theorem statement and any renamed finite/sequence auxiliaries.
- Update module docstrings, `README.md`, `AGENTS.md`, and roadmap references so that only the exact closure theorem is described as paper eq. (26).
- Retain a short note that the finite witness theorem and the sequence-level surrogate remain useful auxiliaries.

Suggested commit: `docs(theorem4): align public claims with exact paper theorem`

## Test plan

New or updated tests should cover the public API, not the implementation proofs.

`ZhangYeungTest/EntropyRegion.lean`:

- signature pin for `entropyFn_n`,
- signature pin for `shannonRegion_n`, `entropyRegion_n`, `almostEntropicRegion_n`,
- signature pin for `restrictFirstFour`,
- one concrete restriction example reducing `F_witness_n` to `F_witness`.

`ZhangYeungTest/Theorem4.lean`:

- exact theorem statement pin for the new paper-level theorem,
- finite theorem statement pin if `theorem4_finite` becomes the auxiliary name,
- sequence-level theorem pin if the current `theorem4_closure` remains public,
- one downstream consumer specializing the exact theorem at `n = 4`,
- one downstream consumer specializing the exact theorem at arbitrary `n ≥ 4`.

## Risks

### 1. Topological closure over function spaces

The point-set topology proof may be more awkward than the current sequence-based lemmas.

Mitigation: work with explicit coordinate-evaluation maps on the finite product `Finset (Fin 4) → ℝ`; avoid abstract functional-analysis infrastructure.

### 2. Naming churn in a pre-release library

Renaming `theorem4` to a finite auxiliary and promoting the exact theorem into the headline slot is the mathematically correct end state, but it will touch docs and tests in one sweep.

Mitigation: decide the naming policy before Commit 3, then update all tests and docs in the same change rather than carrying transitional names across multiple commits.

### 3. Generic `entropyFn_n` elaboration

The dependent codomain family `S : Fin n → Type u` and the subtype-indexed joint variable can produce elaboration noise when generalized away from `n = 4`.

Mitigation: keep `entropyFn_n` definitionally identical to the current `entropyFn` pattern, and prove the transport-to-subfamily lemmas before attempting the closure argument.

## Verification

The work is complete when all of the following hold:

1. `lake build ZhangYeung.EntropyRegion` passes if the new module lands.
2. `lake build ZhangYeung.Theorem4` passes with no `sorry`.
3. `lake build ZhangYeungTest.EntropyRegion` and `lake build ZhangYeungTest.Theorem4` pass.
4. `lake test` passes.
5. `make check` passes.
6. `README.md` and `ZhangYeung/Theorem4.lean` describe the exact closure theorem, not the weaker finite surrogate, as paper eq. (26).

## Exit criteria

This follow-up is done when the repository can honestly say, without qualification, that it formalizes Theorem 4 of Zhang and Yeung (1998) as stated:

$$
\bar{\Gamma}_n^* \neq \Gamma_n \qquad (n \ge 4).
$$

At that point, the current finite witness theorem and sequence-level surrogate become supporting lemmas in the proof story rather than substitutes for the paper's headline result.
