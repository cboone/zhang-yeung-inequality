---
title: "Universe-polymorphic `entropyRegion_n` for exact Theorem 4"
created: 2026-04-20
status: proposed
branch: TBD
roadmap: docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md
depends_on: M4 / M4.5 (`ZhangYeung/EntropyRegion.lean`, `ZhangYeung/Theorem4.lean`) -- in particular `entropyRegion_n`, `almostEntropicRegion_n`, `restrictFirstFour`, `zhangYeungHolds_of_entropy`, `theorem4`, and `theorem4_ge_four`.
---

## Status

Proposed. Follow-up to the M4.5 exact-closure work that landed on `formalize/m4-theorem-4` (PR #11). Suggested by a Copilot PR review on `ZhangYeung/EntropyRegion.lean:68`.

## Context

`entropyRegion_n` currently pins its existential over probability spaces and codomain families to universe 0:

```lean
def entropyRegion_n (n : ℕ) : Set (Finset (Fin n) → ℝ) :=
  {F | ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (S : Fin n → Type) (_ : ∀ i, MeasurableSpace (S i)) (_ : ∀ i, Fintype (S i))
      (_ : ∀ i, MeasurableSingletonClass (S i))
      (X : ∀ i : Fin n, Ω → S i),
      (∀ i, Measurable (X i)) ∧ F = entropyFn_n X μ}
```

This was a deliberate choice at the M4.5 design stage (see `docs/plans/done/2026-04-19-exact-theorem-4-entropic-region-closure.md`, Design §2 and Risks §4). Quantifying `(Ω : Type u)` inside a `Set (Finset (Fin n) → ℝ)` (whose carrier is in `Type`) raises a predicativity issue without an explicit universe parameter on `entropyRegion_n` itself. The plan chose to pin to `Type 0` up front and revisit only if a downstream consumer required it.

The gap is real. `theorem4_finite` is stated universe-polymorphically (its `{Ω : Type u}` and `{S : Fin 4 → Type u}` are implicit generic parameters), but `theorem4` is a statement about membership in `almostEntropicRegion_n 4`, whose underlying `entropyRegion_n 4` only sees probability spaces in `Type 0`. An entropy function realized over, say, a higher-universe state space is not directly a member, even though its values are real numbers.

Mathematically this is harmless for the paper-level theorem: every finite-codomain entropy function admits a `Type 0` realization (replace each `Fintype (S i)` with `Fin (Fintype.card (S i))`). But the API gap is visible to callers, and closing it would let `theorem4_finite` and `theorem4` share a single uniform statement surface.

## Goal

Offer a universe-polymorphic entropic-region surface without breaking existing Lean API users.

Two routes, roughly in order of preference:

1. **Parameterize `entropyRegion_n` by a universe.** Introduce `universe u` in `ZhangYeung/EntropyRegion.lean` and restate `entropyRegion_n` with `(Ω : Type u)` and `(S : Fin n → Type u)`. The carrier `Set (Finset (Fin n) → ℝ)` stays in `Type 0`; only the existential ranges over `Type u`. Current callers default to `u = 0` and are unaffected. Downstream users instantiate with whichever universe fits.

2. **Keep the `Type 0` region; add a transport lemma.** If universe polymorphism bleeds awkwardly through `almostEntropicRegion_n`, `restrictFirstFour_mem_entropyRegion_n`, and `restrictFirstFour_mem_almostEntropicRegion_n`, retain the current definitions and publish a public lemma of the form "any finite-codomain entropy function over `Type u` is already realized by a `Type 0` entropy function." Callers then transport explicitly.

Prefer route 1 if the surrounding lemmas accept a `universe u` parameter cleanly; fall back to route 2 if not.

## Non-goals

- No change to the paper-level theorem statements (`theorem4`, `theorem4_ge_four`) unless route 1 forces a signature-level edit. If it does, record the rename in the same PR.
- No broader universe-polymorphism sweep across `ZhangYeung.Delta` or `ZhangYeung.Theorem2`. Limit scope to `ZhangYeung/EntropyRegion.lean` and any immediate consumers.
- No attempt to introduce a universe-polymorphic `shannonRegion_n`; the Shannon cone is a property of a `Finset (Fin n) → ℝ`-valued function and already lives in `Type 0`.

## Design sketch

### Route 1: universe parameter on `entropyRegion_n`

Add `universe u` at the top of `ZhangYeung/EntropyRegion.lean` (it may already be there for `entropyFn_n`). Rewrite `entropyRegion_n` as:

```lean
def entropyRegion_n.{u} (n : ℕ) : Set (Finset (Fin n) → ℝ) :=
  {F | ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (S : Fin n → Type u) (_ : ∀ i, MeasurableSpace (S i)) (_ : ∀ i, Fintype (S i))
      (_ : ∀ i, MeasurableSingletonClass (S i))
      (X : ∀ i : Fin n, Ω → S i),
      (∀ i, Measurable (X i)) ∧ F = entropyFn_n X μ}
```

Every downstream consumer (`restrictFirstFour_mem_entropyRegion_n`, `almostEntropicRegion_n`, `theorem4`, `theorem4_ge_four`) either becomes universe-polymorphic in the same variable or fixes `u := 0` explicitly when that is the intended scope.

Key decisions:

- Does `almostEntropicRegion_n` take the universe parameter as well? Likely yes: it is literally `closure (entropyRegion_n n)` and its closure argument does not care about `u`.
- Does `theorem4` fix `u := 0` or stay polymorphic? If universe-polymorphic, its `F_witness` non-membership claim becomes "for every universe `u`, `F_witness ∉ almostEntropicRegion_n.{u} 4`"; proving that is still a one-liner through `zhangYeungRegion_4`'s closedness because the closedness argument lives entirely at the level of `Finset (Fin 4) → ℝ`.

### Route 2: transport lemma

Introduce a public lemma (or corollary to `entropy_comp_of_injective`) roughly:

```lean
theorem entropyFn_n_mem_entropyRegion_n_of_universe
    {n : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {S : Fin n → Type u} [∀ i, MeasurableSpace (S i)] [∀ i, Fintype (S i)]
    [∀ i, MeasurableSingletonClass (S i)]
    (X : ∀ i : Fin n, Ω → S i) (hX : ∀ i, Measurable (X i))
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    entropyFn_n X μ ∈ entropyRegion_n n
```

The proof uses the `Fintype (S i)`-to-`Fin (Fintype.card (S i))` equivalence and transports the joint along its product. This is strictly weaker than route 1 -- it says the `Type 0` region already contains every universe-`u` realization up to equality as a set function -- but it closes the API gap without touching existing signatures.

## Risks

1. **Cascading universe parameters.** Adding `universe u` to `entropyRegion_n` forces surrounding lemmas to either lift or pin. If the downstream surface is small (it currently is: just `restrictFirstFour_mem_entropyRegion_n`, `restrictFirstFour_mem_almostEntropicRegion_n`, and the three exact-theorem statements), the sweep is bounded.
2. **Test-module breakage.** `ZhangYeungTest/EntropyRegion.lean` and `ZhangYeungTest/Theorem4.lean` pin signatures; a universe parameter shows up as an implicit and may need to be annotated. Budget time to refresh the pins.
3. **Elaboration cost.** Pinning `u := 0` at every call site is cheap, but diagnosing universe errors in downstream proofs takes learned practice. Prefer route 2 if the first attempt at route 1 produces opaque universe-unification failures.

## Verification

The work is complete when all of the following hold:

1. `lake build ZhangYeung` passes.
2. `lake test` passes.
3. `make check` passes.
4. One of the two routes lands:
   - Route 1: `entropyRegion_n` takes a universe parameter, and at least one consumer (`theorem4` or `theorem4_ge_four`) is either universe-polymorphic or explicitly fixes `u := 0`.
   - Route 2: a public transport lemma witnesses that any universe-`u` entropy function is already in `entropyRegion_n n` as a set function.
5. The M4.5 plan's universe-discipline section is updated to note that the polymorphic surface now exists (or explicitly that route 2 was taken).

## Exit criteria

Done when a downstream user can write an entropy function over a `Type u` probability space and either:

- pass it directly to `theorem4_finite` and to membership in `entropyRegion_n` / `almostEntropicRegion_n` without a manual `Type 0` detour, or
- invoke a named public lemma that performs the transport.
