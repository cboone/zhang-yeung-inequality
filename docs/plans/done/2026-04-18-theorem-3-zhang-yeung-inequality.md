---
title: "M3: Theorem 3, the Zhang-Yeung inequality (1998, §III, Theorem 3 / eqs. 21-23)"
created: 2026-04-18
branch: formalize/3-theorem-3
roadmap: docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md
milestone: M3
depends_on: M2 (`ZhangYeung/CopyLemma.lean`, merged into `main` via PR #8). M1 (`ZhangYeung/Delta.lean`) and M1.5 (`ZhangYeung/Theorem2.lean`) are also on `main`. No prerequisites beyond what is already merged; the worktree `3-theorem-3` is branched from the tip of `main` and starts from a green `make check`.
---

## Context

Milestone M3 of the Zhang-Yeung roadmap (§6) formalizes the headline theorem of the 1998 paper: the **Zhang-Yeung inequality** itself, the first known non-Shannon-type information inequality for four discrete random variables. M2 landed the copy construction and the two Lemma-2-powered "opening" inequalities of the proof; M3 closes the remaining Shannon chase that turns those two inputs into the paper's eq. (21), derives the `X ↔ Y` dual (eq. 22), and the symmetric averaged corollary (eq. 23).

**Primary reference:** `references/transcriptions/zhangyeung1998.md` (verified 2026-04-16). Equation and line numbers below reference that transcription. The proof proper is on lines 680-709.

The paper's Theorem 3 statement (line 290):

> For any four discrete random variables $X, Y, Z, U$, let
> $$
> \Delta(Z, U \mid X, Y) := I(Z; U) - I(Z; U \mid X) - I(Z; U \mid Y).
> $$
> Then
> $$
> \Delta(Z, U \mid X, Y) \;\le\; \tfrac{1}{2}\bigl[I(X; Y) + I(X; Z, U) + I(Z; U \mid X) - I(Z; U \mid Y)\bigr]. \tag{21}
> $$

By symmetry in $X \leftrightarrow Y$,
$$
\Delta(Z, U \mid X, Y) \;\le\; \tfrac{1}{2}\bigl[I(X; Y) + I(Y; Z, U) - I(Z; U \mid X) + I(Z; U \mid Y)\bigr]. \tag{22}
$$

Averaging (21) and (22):
$$
\Delta(Z, U \mid X, Y) \;\le\; \tfrac{1}{2}\, I(X; Y) + \tfrac{1}{4}\bigl[I(X; Z, U) + I(Y; Z, U)\bigr]. \tag{23}
$$

Equation (23) is the symmetric form Zhang-Yeung highlight as the paper's headline result; eq. (21) is the "copy-lemma-natural" asymmetric form that the proof actually produces.

### Why M3 lands now

1. **All M3 ingredients are in place.** M2 shipped `copyLemma`, the abstract Lemma 2 (`delta_of_condMI_vanishes_eq`), and six copy-projection corollaries including the two inequality forms `copyLemma_delta_le_mutualInfo_Y₁` and `copyLemma_delta_le_mutualInfo_X_X₁` that open the Shannon chase on paper lines 680-689. M1 shipped the three-way form-conversion equivalences `delta_form21_iff`, `delta_form22_iff`, `delta_form23_iff`, plus the averaging lemma `delta_form23_of_form21_form22`. M3 is the chase that glues these together.
1. **The chase is pure Shannon.** Once both copy-lemma inequalities are in hand, eq. (21) follows by five arithmetic moves (three-way interaction identity, nonneg CMI drop, data processing, two marginal-equality transports). No further non-Shannon ingredients are needed; M3 exercises exactly the "Shannon chase on the copy joint" predicted by M2's plan (`docs/plans/done/2026-04-17-copy-lemma.md`, §"Out-of-scope for M2").
1. **M2's Shannon-chase smoke test already performs the first step.** `ZhangYeungTest/CopyLemma.lean:192-211` derives `2 I[Z:U] - 3 I[Z:U|X] - I[Z:U|Y] ≤ I[X':Y₁] + I[X':X₁]` from `copyLemma_delta_le_mutualInfo_Y₁` + `copyLemma_delta_le_mutualInfo_X_X₁` + `linarith`. M3 picks up exactly where that test stops, extending the RHS down to `I[X:Y] + I[X:⟨Z,U⟩]` via the three remaining Shannon steps.

### What M3 does not do

- **Theorem 4 (Shannon is incomplete).** Parallelizable with M3 per roadmap §6; handled by Worktree B.
- **Theorem 5 (n+2-variable generalization).** Stretch goal, roadmap §M5.
- **Exact identity form with explicit slack $R(X, Y, Z, U, X_1, Y_1)$** (paper p. 1446, transcription lines 711-768). Post-release extension ranked #2 on roadmap §9; would upgrade $\le$ to $=$ with a fully characterized remainder. Out of scope for M3 because the roadmap checkpoint targets the inequality (21), not the equality-with-remainder form.

## Paper proof (transcription, lines 680-709)

Under the copy law $\nu$, set $X_1, Y_1$ to be the second-copy projections and $X', Z', U'$ to be the first-copy projections. Two applications of Lemma 2 (M2's `copyLemma_delta_le_mutualInfo_Y₁` and `copyLemma_delta_le_mutualInfo_X_X₁`) give paper lines 683 and 689:
$$
\Delta(Z, U \mid X, Y) \;\le\; I(X; Y_1) \qquad \text{and} \qquad I(Z; U) - 2\, I(Z; U \mid X) \;\le\; I(X; X_1).
$$

Summing (literally: adding the two inequalities and expanding $\Delta$ via `delta_def`) gives
$$
2\, I(Z; U) - 3\, I(Z; U \mid X) - I(Z; U \mid Y) \;\le\; I(X; Y_1) + I(X; X_1). \tag{*}
$$

The paper then chases the right-hand side through four Shannon identities (lines 697-707):

1. **Three-way interaction identity.** $I(X; Y_1) + I(X; X_1) = I(X; X_1, Y_1) + I(X; X_1; Y_1)$, where the three-way interaction $I(X; X_1; Y_1) := I(X_1; Y_1) - I(X_1; Y_1 \mid X)$. Equivalent to a pair of chain-rule applications on $I(X; \langle X_1, Y_1 \rangle)$.
1. **Nonneg CMI drop.** $I(X_1; Y_1 \mid X) \ge 0$, so $I(X; X_1, Y_1) + I(X; X_1; Y_1) \le I(X; X_1, Y_1) + I(X_1; Y_1)$.
1. **Data processing.** Under the copy law's `CondIndepFun ⟨X', Y'⟩ ⟨X_1, Y_1⟩ ⟨Z', U'⟩ ν`, projection to the first coordinate gives `X ⊥ ⟨X_1, Y_1⟩ | ⟨Z', U'⟩`, hence $I(X; X_1, Y_1) \le I(X; Z', U')$ (paper's "data processing inequality" step, line 708).
1. **Marginal equalities.** By the copy-lemma `IdentDistrib` projections, $I(X_1; Y_1)_\nu = I(X; Y)_\mu$ (line 709, "the fact that $I(X; Y) = I(X_1; Y_1)$") and $I(X'; Z', U')_\nu = I(X; Z, U)_\mu$.

Combining:
$$
2\, I(Z; U) - 3\, I(Z; U \mid X) - I(Z; U \mid Y) \;\le\; I(X; Z, U) + I(X; Y), \tag{21'}
$$

which is `delta_form21_iff.mpr` applied to M3's conclusion.

The dual (22) is the $X \leftrightarrow Y$ swap of (21): apply Theorem 3 to $(Y, X, Z, U)$, use `mutualInfo_comm` to rewrite $I(Y; X) = I(X; Y)$, and convert through `delta_form22_iff`. The averaged corollary (23) is `delta_form23_of_form21_form22` + `delta_form23_iff`.

Every step above is pure Shannon algebra on the copy space $\nu$; the only non-Shannon ingredient is the copy construction's existence (landed in M2). M3 is therefore a chase, not a construction.

## Prerequisites

M1 delivered (merged into `main` via PR #4):

- `ZhangYeung/Delta.lean` with the `ZhangYeung.delta` definition and the form-conversion equivalences `delta_form21_iff`, `delta_form22_iff`, `delta_form23_iff`, and the averaging lemma `delta_form23_of_form21_form22`.

M2 delivered (merged into `main` via PR #8):

- `ZhangYeung/CopyLemma.lean` with:
  - `copyLemma`: the main existential producing `Ω', ν, X', Y', X₁, Y₁, Z', U'` + three structural facts (two 4-variable `IdentDistrib`s, one `CondIndepFun`).
  - `delta_of_condMI_vanishes_eq` (Lemma 2, abstract).
  - `copyLemma_delta_transport_Y_to_Y₁`, `copyLemma_delta_transport_X_to_X₁` (bridges between $\Delta_\mu$ and $\Delta_\nu$).
  - `copyLemma_delta_identity_Y₁`, `copyLemma_delta_identity_X_X₁` (Lemma 2 Form B specializations).
  - `copyLemma_delta_le_mutualInfo_Y₁`: `delta Z U X Y μ ≤ I[X' : Y₁ ; ν]` (paper line 683).
  - `copyLemma_delta_le_mutualInfo_X_X₁`: `I[Z : U ; μ] - 2 * I[Z : U | X ; μ] ≤ I[X' : X₁ ; ν]` (paper line 689).
- Two `private` helpers in `section Helpers`: `condIndepFun_comp` (post-composition of PFR's `CondIndepFun` by measurable codomain functions) and `IdentDistrib.condMutualInfo_eq` (triple-level `condMutualInfo` transport). M3 is the first downstream module; if it needs either helper, promote it to `ZhangYeung/Prelude.lean` in the same change per the M2 design note (`ZhangYeung/CopyLemma.lean:34`).

Before starting M3, in the `3-theorem-3` worktree: `bin/bootstrap-worktree`, then `make check`. Confirm the tip is green with M1 + M1.5 + M2 in place and `lake env lean --version` reports the Lean toolchain PFR compiles against.

## PFR and Mathlib API surface used

All declarations live under `namespace ProbabilityTheory` unless noted. Line numbers are against `.lake/packages/pfr/PFR/ForMathlib/Entropy/Basic.lean` at the currently-pinned PFR revision.

**Shannon primitives (PFR, already used by M1/M1.5/M2):**

- `mutualInfo_def : I[X : Y ; μ] = H[X ; μ] + H[Y ; μ] - H[⟨X, Y⟩ ; μ]` (definitional, Basic.lean `I[...]` notation).
- `mutualInfo_comm : I[X : Y ; μ] = I[Y : X ; μ]` (Basic.lean:823). Used for the $X \leftrightarrow Y$ swap step in the dual.
- `mutualInfo_eq_entropy_sub_condEntropy : I[X : Y ; μ] = H[X ; μ] - H[X | Y ; μ]` (Basic.lean:827). Occasionally useful when entering the entropy layer from the MI side.
- `condMutualInfo_eq : I[X : Y | Z ; μ] = H[X | Z ; μ] + H[Y | Z ; μ] - H[⟨X, Y⟩ | Z ; μ]` (Basic.lean:941). Used inside the data-processing helper.
- `condMutualInfo_eq' : I[X : Y | Z ; μ] = H[X | Z ; μ] - H[X | ⟨Y, Z⟩ ; μ]` (Basic.lean:956). Alternative CMI form, used if the route bypasses pair-ordering juggling.
- `condMutualInfo_eq_zero : I[X : Y | Z ; μ] = 0 ↔ CondIndepFun X Y Z μ` (Basic.lean:1042). The bridge from the copy's `CondIndepFun` to an algebraic zero.
- `condMutualInfo_nonneg : 0 ≤ I[X : Y | Z ; μ]` (Basic.lean:924).
- `mutualInfo_nonneg : 0 ≤ I[X : Y ; μ]` (Basic.lean).
- `chain_rule'`, `chain_rule`, `chain_rule''`: entropy chain rules (Basic.lean:546, :573, :579).
- `cond_chain_rule'`, `cond_chain_rule`: conditional entropy chain rules (Basic.lean:617, :634).
- `entropy_comm : H[⟨X, Y⟩ ; μ] = H[⟨Y, X⟩ ; μ]` (Basic.lean, referenced throughout).
- `entropy_assoc : H[⟨X, ⟨Y, Z⟩⟩ ; μ] = H[⟨⟨X, Y⟩, Z⟩ ; μ]` (Basic.lean:343). New to this module (M1/M1.5/M2 did not use it).
- `entropy_comp_of_injective : Function.Injective f → H[f ∘ X ; μ] = H[X ; μ]` (Basic.lean:160). New to this module, used for the inner-pair-swap entropy identity inside the data-processing helper.
- `entropy_triple_add_entropy_le : H[⟨X, ⟨Y, Z⟩⟩ ; μ] + H[Z ; μ] ≤ H[⟨X, Z⟩ ; μ] + H[⟨Y, Z⟩ ; μ]` (Basic.lean:1117). **Submodularity.** New to this module, used inside the data-processing helper. Not used anywhere in M1/M1.5/M2.
- `entropy_submodular : H[X | ⟨Y, Z⟩ ; μ] ≤ H[X | Z ; μ]` (Basic.lean:1087). Conditional-entropy form of submodularity; available as an alternative route for the data-processing helper.
- `condEntropy_comm : H[⟨X, Y⟩ | Z ; μ] = H[⟨Y, X⟩ | Z ; μ]` (Basic.lean:531). Inner-pair swap for the conditioned variable (not the conditioner).

**Identical distribution and conditional independence (PFR + Mathlib, carried forward from M2):**

- `IdentDistrib.mutualInfo_eq` (Basic.lean:691). Pair-form `IdentDistrib` → equal mutual informations. Used for the two marginal-equality transports of the chase.
- `IdentDistrib.comp`, `.symm` (Mathlib `Probability/IdentDistrib.lean`). Used to project the 4-variable `hFirst`, `hSecond` into pair-level `IdentDistrib`s.
- `CondIndepFun` (PFR `ForMathlib/ConditionalIndependence.lean:105`). Random-variable form.
- `ent_of_cond_indep` (Basic.lean:1064). Packages `CondIndepFun X Y Z μ` into the entropy identity `H[⟨X, ⟨Y, Z⟩⟩ ; μ] = H[⟨X, Z⟩ ; μ] + H[⟨Y, Z⟩ ; μ] - H[Z ; μ]`; this is the shortest entry point for M3's data-processing helper.
- M2's private `condIndepFun_comp` (currently at `ZhangYeung/CopyLemma.lean:58`). Used to project the copy's `CondIndepFun ⟨X', Y'⟩ ⟨X_1, Y_1⟩ ⟨Z', U'⟩ ν` to `CondIndepFun X' ⟨X_1, Y_1⟩ ⟨Z', U'⟩ ν` for the data-processing step. **Promotion trigger:** M3 is the second module to consume this helper; promote from `ZhangYeung/CopyLemma.lean` (private) to `ZhangYeung/Prelude.lean` (public under `ZhangYeung` namespace) in the same change. This matches the M2 plan's prediction ("if later milestones need them, promote to `ZhangYeung/Prelude.lean`", `ZhangYeung/CopyLemma.lean:34`; roadmap `docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md:247`).

**From the current project:**

- `ZhangYeung.delta`, `ZhangYeung.delta_def`, `ZhangYeung.delta_comm_cond`, `ZhangYeung.delta_self`: from `ZhangYeung/Delta.lean`.
- `ZhangYeung.delta_form21_iff`, `ZhangYeung.delta_form22_iff`, `ZhangYeung.delta_form23_iff`, `ZhangYeung.delta_form23_of_form21_form22`: the M1 form-conversion lemmas, used to move between the integer-scaled form (what the chase naturally produces) and the paper's $(1/2)$ / $(1/4)$ form.
- `ZhangYeung.copyLemma`, `ZhangYeung.copyLemma_delta_le_mutualInfo_Y₁`, `ZhangYeung.copyLemma_delta_le_mutualInfo_X_X₁`: the three M2 artifacts M3 calls by name.

### `IdentDistrib.condMutualInfo_eq`

The M2 private helper is not needed by M3: the two marginal-equality transports used in M3's chase are `I[X' : ⟨Z', U'⟩ ; ν] = I[X : ⟨Z, U⟩ ; μ]` and `I[X₁ : Y₁ ; ν] = I[X : Y ; μ]`, both unconditional (pair-level) mutual informations that route through the plain `IdentDistrib.mutualInfo_eq`. No conditional-MI transport is required. Leave `IdentDistrib.condMutualInfo_eq` as a `private` helper in `ZhangYeung/CopyLemma.lean` for now. A later milestone (for example, an exact-identity refinement of Theorem 3 per roadmap §9 extension #2, which needs to transport the explicit remainder $R(X, Y, Z, U, X_1, Y_1)$) may revisit the promotion decision.

### `condIndepFun_comp`

M3 needs this to project the copy's `CondIndepFun ⟨X', Y'⟩ ⟨X_1, Y_1⟩ ⟨Z', U'⟩ ν` down to `CondIndepFun X' ⟨X_1, Y_1⟩ ⟨Z', U'⟩ ν`, which is the input to the data-processing helper. The projection is `condIndepFun_comp (φ := Prod.fst) (ψ := id) measurable_fst measurable_id hCond`, producing `CondIndepFun (Prod.fst ∘ ⟨X', Y'⟩) (id ∘ ⟨X_1, Y_1⟩) ⟨Z', U'⟩ ν`, which reduces to `CondIndepFun X' ⟨X_1, Y_1⟩ ⟨Z', U'⟩ ν` by the same pointwise pair-eta identity M2 uses at `ZhangYeung/CopyLemma.lean:142`. Since M3 is the second module to consume it, promote `condIndepFun_comp` to `ZhangYeung/Prelude.lean` per the M2 design note.

## The M3 theorems

### Headline: Theorem 3 (paper eq. 21)

```lean
theorem zhangYeung
    {Ω : Type*} [MeasurableSpace Ω]
    {S₁ S₂ S₃ S₄ : Type u}
    [MeasurableSpace S₁] [MeasurableSpace S₂]
    [MeasurableSpace S₃] [MeasurableSpace S₄]
    [Fintype S₁] [Fintype S₂] [Fintype S₃] [Fintype S₄]
    [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
    [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    delta Z U X Y μ
      ≤ (1/2) * (I[X : Y ; μ] + I[X : ⟨Z, U⟩ ; μ] + I[Z : U | X ; μ] - I[Z : U | Y ; μ])
```

This matches the roadmap checkpoint literally (`docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md:248`, modulo the conjunctive-form pretty-printing the roadmap writes inline). The universe constraint `S₁ ... S₄ : Type u` is forced by `copyLemma` (same reason as M2; see `docs/plans/done/2026-04-17-copy-lemma.md` §7.1).

### Dual: paper eq. (22)

```lean
theorem zhangYeung_dual ... :
    delta Z U X Y μ
      ≤ (1/2) * (I[X : Y ; μ] + I[Y : ⟨Z, U⟩ ; μ] - I[Z : U | X ; μ] + I[Z : U | Y ; μ])
```

Proof: apply `zhangYeung` with `X` and `Y` swapped, rewrite the left-hand side back to `delta Z U X Y μ` via `delta_comm_cond`, rewrite `I[Y : X ; μ] = I[X : Y ; μ]` via `mutualInfo_comm hY hX`, and close by `delta_form22_iff` + `linarith`.

### Averaged corollary: paper eq. (23)

```lean
theorem zhangYeung_averaged ... :
    delta Z U X Y μ
      ≤ (1/2) * I[X : Y ; μ] + (1/4) * (I[X : ⟨Z, U⟩ ; μ] + I[Y : ⟨Z, U⟩ ; μ])
```

Proof: combine `zhangYeung` and `zhangYeung_dual` (after scaling back up to the `2 * delta ≤ ...` form), apply `delta_form23_of_form21_form22`, then `delta_form23_iff.mp`.

## Proof sketch: the Shannon chase for `zhangYeung`

Internally, the cleanest proof produces the integer-scaled form first (because that is what the chase naturally closes) and converts at the end. A short private helper captures the integer form:

```lean
private theorem zhangYeung_integer ... :
    2 * I[Z : U ; μ] - 3 * I[Z : U | X ; μ] - I[Z : U | Y ; μ]
      ≤ I[X : Y ; μ] + I[X : ⟨Z, U⟩ ; μ]
```

Proof body (approximate, expanded for exposition):

```lean
by
  -- Step 0: destructure the copy lemma.
  obtain ⟨Ω', _, ν, X', Y', X₁, Y₁, Z', U',
      _, hX', hY', hX₁, hY₁, hZ', hU', hFirst, hSecond, hCond⟩ :=
    copyLemma hX hY hZ hU μ
  -- Step 1: two copy-lemma inequalities (paper lines 683, 689).
  have h1 : delta Z U X Y μ ≤ I[X' : Y₁ ; ν] :=
    copyLemma_delta_le_mutualInfo_Y₁ hX hY hZ hU hX' hY₁ hZ' hU' hFirst hSecond hCond
  have h2 : I[Z : U ; μ] - 2 * I[Z : U | X ; μ] ≤ I[X' : X₁ ; ν] :=
    copyLemma_delta_le_mutualInfo_X_X₁ hX hZ hU hX' hX₁ hZ' hU' hFirst hSecond hCond
  rw [delta_def] at h1
  -- h1 : I[Z : U ; μ] - I[Z : U | X ; μ] - I[Z : U | Y ; μ] ≤ I[X' : Y₁ ; ν]
  -- Summing h1 + h2:
  --   2 I[Z : U] - 3 I[Z : U | X] - I[Z : U | Y] ≤ I[X' : Y₁] + I[X' : X₁]       (*)
  -- Step 2: three-way interaction identity on ν (paper line 700).
  have h_three :
      I[X' : X₁ ; ν] + I[X' : Y₁ ; ν]
        = I[X' : ⟨X₁, Y₁⟩ ; ν] + I[X₁ : Y₁ ; ν] - I[X₁ : Y₁ | X' ; ν] :=
    mutualInfo_add_three_way_identity hX' hX₁ hY₁ ν
  -- Step 3: drop the nonneg CMI term.
  have h_nonneg : 0 ≤ I[X₁ : Y₁ | X' ; ν] := condMutualInfo_nonneg hX₁ hY₁
  -- Step 4: data processing (paper line 708).
  have hCond_proj : CondIndepFun X' (fun ω => (X₁ ω, Y₁ ω))
                      (fun ω => (Z' ω, U' ω)) ν :=
    ZhangYeung.condIndepFun_comp (φ := Prod.fst) (ψ := id)
      measurable_fst measurable_id hCond
  have h_dp : I[X' : ⟨X₁, Y₁⟩ ; ν] ≤ I[X' : ⟨Z', U'⟩ ; ν] :=
    mutualInfo_le_of_condIndepFun hX' (hX₁.prodMk hY₁) (hZ'.prodMk hU') ν hCond_proj
  -- Step 5: transport I[X' : ⟨Z', U'⟩ ; ν] = I[X : ⟨Z, U⟩ ; μ] via hFirst.
  have h_marg_XZU : I[X' : ⟨Z', U'⟩ ; ν] = I[X : ⟨Z, U⟩ ; μ] := by
    have hPairXZU : IdentDistrib
        (fun ω' => (X' ω', (Z' ω', U' ω'))) (fun ω => (X ω, (Z ω, U ω))) ν μ :=
      hFirst.comp measurable_pairXZU
    exact hPairXZU.mutualInfo_eq
  -- Step 6: transport I[X₁ : Y₁ ; ν] = I[X : Y ; μ] via hSecond.
  have h_marg_XY : I[X₁ : Y₁ ; ν] = I[X : Y ; μ] := by
    have hPairXY : IdentDistrib
        (fun ω' => (X₁ ω', Y₁ ω')) (fun ω => (X ω, Y ω)) ν μ :=
      hSecond.comp measurable_pairXY
    exact hPairXY.mutualInfo_eq
  -- Close by linarith over all of the above.
  linarith [h1, h2, h_three, h_nonneg, h_dp, h_marg_XZU, h_marg_XY]
```

where `measurable_pairXZU : Measurable (fun p : S₁ × S₂ × S₃ × S₄ => (p.1, (p.2.2.1, p.2.2.2)))` and `measurable_pairXY : Measurable (fun p : S₁ × S₂ × S₃ × S₄ => (p.1, p.2.1))` are two one-line projection-measurability helpers private to `ZhangYeung/Theorem3.lean`, analogous to M2's `measurable_pairZU` / `measurable_projZUA` / `measurable_projZUB` at `ZhangYeung/CopyLemma.lean:222-235`. (Keep these as three-line `fun_prop` lemmas inside a small `section Helpers`; do not pre-generalize.)

The two external Shannon helpers (`mutualInfo_add_three_way_identity` and `mutualInfo_le_of_condIndepFun`) are detailed in the next section.

### The two private Shannon helpers

Both helpers are generic Shannon identities that do not reference the copy construction. Each is self-contained and can live under a `section Helpers` at the top of `ZhangYeung/Theorem3.lean`, outside the main `section Consequences`. Both are candidates for eventual promotion to `ZhangYeung/Prelude.lean` or upstreaming to PFR if a later milestone needs them. For M3 they stay `private`.

#### `mutualInfo_add_three_way_identity`

```lean
private lemma mutualInfo_add_three_way_identity
    {Ω : Type*} [MeasurableSpace Ω]
    {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    {X : Ω → α} {Y : Ω → β} {Z : Ω → γ}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    I[X : Y ; μ] + I[X : Z ; μ]
      = I[X : ⟨Y, Z⟩ ; μ] + I[Y : Z ; μ] - I[Y : Z | X ; μ]
```

This is the standard "peeling chain rule twice" identity
$$
I(X; Y) + I(X; Z) = I(X; Y, Z) + I(X; Y; Z) = I(X; Y, Z) + I(Y; Z) - I(Y; Z \mid X),
$$
where $I(X; Y; Z) := I(Y; Z) - I(Y; Z \mid X)$ is the three-way interaction information (symmetric in all three slots). The M3 chase consumes it with $(X, Y, Z) := (X', X_1, Y_1)$.

**Proof route.** Following the M1.5 `theorem2_shannon_identity` / M2 `delta_of_condMI_vanishes_eq` template: expand every `mutualInfo` and `condMutualInfo` into entropy terms via `mutualInfo_def`, `condMutualInfo_eq`; apply `chain_rule''` to eliminate conditional entropies; align pair orderings with `entropy_comm`; close with `linarith`. Budget ~25 tactic lines. No heartbeat bumps expected (M2 `delta_of_condMI_vanishes_eq` is 39 lines and landed at default heartbeats; this identity has strictly fewer entropy terms).

**Primitives used:** `mutualInfo_def` (×4), `condMutualInfo_eq` (×1), `chain_rule''` (×4-6), `entropy_comm` (×2-3).

#### `mutualInfo_le_of_condIndepFun` (data processing)

```lean
private lemma mutualInfo_le_of_condIndepFun
    {Ω : Type*} [MeasurableSpace Ω]
    {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    {X : Ω → α} {Y : Ω → β} {Z : Ω → γ}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : CondIndepFun X Y Z μ) :
    I[X : Y ; μ] ≤ I[X : Z ; μ]
```

This is the data-processing inequality for the Markov chain $X \to Z \to Y$: if $X$ and $Y$ are conditionally independent given $Z$, then $I(X; Y) \le I(X; Z)$. PFR exposes three post-composition data-processing lemmas (`mutual_comp_le`, `mutual_comp_comp_le`, `condMutual_comp_comp_le` at `Basic.lean:1151`, `:1162`, `:1174`), and it also already exposes `ent_of_cond_indep` (Basic.lean:1064), which packages the entropy identity forced by `CondIndepFun`. None of the post-composition lemmas matches M3's hypothesis shape directly; the shortest path here is therefore to start from `ent_of_cond_indep` and finish the remaining entropy algebra locally.

**Proof route.** First invoke `ent_of_cond_indep hX hY hZ μ h` to obtain
$$
H[\langle X, \langle Y, Z \rangle \rangle ; \mu] = H[\langle X, Z \rangle ; \mu] + H[\langle Y, Z \rangle ; \mu] - H[Z ; \mu].
$$
Then apply `entropy_triple_add_entropy_le hX hZ hY`, so the shared variable is $Y$:
$$
H[\langle X, \langle Z, Y \rangle \rangle ; \mu] + H[Y ; \mu] \le H[\langle X, Y \rangle ; \mu] + H[\langle Z, Y \rangle ; \mu].
$$
Align the left triple entropy with the `ent_of_cond_indep` shape via a small inner-pair-swap lemma proved from `entropy_assoc` + `entropy_comp_of_injective`; rewrite `H[\langle Z, Y \rangle ; \mu]` to `H[\langle Y, Z \rangle ; \mu]` with `entropy_comm`; then expand `I[X : Y ; μ]` and `I[X : Z ; μ]` via `mutualInfo_def` and close by `linarith`.

Budget ~15-20 tactic lines. The only genuinely delicate step is still the inner-pair swap; `ent_of_cond_indep` removes the need to re-derive the conditional-independence entropy identity from `condMutualInfo_eq_zero` by hand. See Risk §7.1 below for the fallback if the alignment proves awkward.

**Primitives used:** `ent_of_cond_indep`, `entropy_triple_add_entropy_le`, `entropy_comm`, `entropy_assoc`, `entropy_comp_of_injective`, `mutualInfo_def`.

**Alternative route (fallback, see Risk §7.1).** If `ent_of_cond_indep` does not rewrite cleanly at the desired triple shape, fall back to the direct entropy derivation from `condMutualInfo_eq_zero` / `condMutualInfo_eq` / `chain_rule''`. That route is longer but remains local and uses the same pair-swap lemma.

## File layout

```text
ZhangYeung/
  Prelude.lean              # promote `condIndepFun_comp` here from CopyLemma.lean
  Delta.lean                # unchanged (M1)
  Theorem2.lean             # unchanged (M1.5)
  CopyLemma.lean            # drop the now-promoted `condIndepFun_comp`
  Theorem3.lean             # NEW: this milestone
ZhangYeung.lean             # add `import ZhangYeung.Theorem3`
ZhangYeungTest/
  Delta.lean                # unchanged
  Theorem2.lean             # unchanged
  CopyLemma.lean            # unchanged (private helper move is non-breaking for the public API)
  Theorem3.lean             # NEW: this milestone
ZhangYeungTest.lean         # add `import ZhangYeungTest.Theorem3`
AGENTS.md (aka CLAUDE.md)   # extend `## Module Layout` with two lines
```

### Section structure inside `ZhangYeung/Theorem3.lean`

```text
├── Module docstring (## Main statements, ## Implementation notes, ## References, ## Tags)
├── Imports: ZhangYeung.CopyLemma, ZhangYeung.Delta, ZhangYeung.Prelude
├── namespace ZhangYeung
├── section Helpers (universe-monomorphic; local to this file)
│     - measurable_pairXZU, measurable_pairXY (projection measurabilities)
│     - private lemma mutualInfo_add_three_way_identity
│     - private lemma mutualInfo_le_of_condIndepFun
├── section MainTheorems (reuses the M2 `Fintype` + `MeasurableSingletonClass` module-scope block)
│     - private theorem zhangYeung_integer
│     - theorem zhangYeung
│     - theorem zhangYeung_dual
│     - theorem zhangYeung_averaged
└── end ZhangYeung
```

The module docstring follows the M2 pattern: opening paragraph stating the role of the module, `## Main statements` listing `zhangYeung`, `zhangYeung_dual`, `zhangYeung_averaged` with one-sentence descriptions, `## Implementation notes` explaining the integer-form / paper-form split and the two Shannon helpers, `## References` pointing at `references/transcriptions/zhangyeung1998.md` (equations 21-23 on lines 290-360, proof on lines 680-709), and `## Tags`.

## Sequencing: commits

Each commit maintains a green build + lint + test. Each commit is a conventional-commit-styled small unit.

1. **Bootstrap + pre-flight checks.** In the `3-theorem-3` worktree: `bin/bootstrap-worktree`; confirm `make check` is green with M1 + M1.5 + M2 on `main`. Then run two pre-flight experiments in a scratch `.lean` file (delete after):

    1. **PFR primitives grep.** Confirm `entropy_assoc` (Basic.lean:343), `entropy_comp_of_injective` (:160), `ent_of_cond_indep` (:1064), `entropy_triple_add_entropy_le` (:1117), `entropy_submodular` (:1087), `condMutualInfo_eq'` (:956), `condEntropy_comm` (:531) all exist at the currently-pinned PFR revision. These are the new-to-M3 primitives; the M2 audit already covered the rest.
    1. **`IdentDistrib.comp` rehearsal.** Apply `IdentDistrib.comp` to an example `hFirst`-shaped 4-variable `IdentDistrib` with a two-line projection `(a, b, c, d) ↦ (a, (c, d))` and confirm the resulting `IdentDistrib.mutualInfo_eq` invocation elaborates cleanly. This validates the `measurable_pairXZU` measurability pattern before the real use site.

    Halt on any failure; investigate before writing new module code.

1. **Promote `condIndepFun_comp` from `ZhangYeung/CopyLemma.lean` to `ZhangYeung/Prelude.lean`.** This is a non-API-breaking refactor: the signature stays identical, only the visibility and the file changes. In `Prelude.lean`, land the lemma as a plain `lemma ZhangYeung.condIndepFun_comp ...` (public, namespaced). In `CopyLemma.lean`, drop the private copy and replace its two use sites (`copyLemma_condMI_X_Y₁_vanishes` and `copyLemma_condMI_X_X₁_vanishes`) with `ZhangYeung.condIndepFun_comp` calls. Adjust docstrings: the M2 "private helpers" note (`ZhangYeung/CopyLemma.lean:34`) becomes a "promoted-to-Prelude" retrospective. `make check` must stay green. Commit as `refactor: promote condIndepFun_comp to Prelude`.

    Note: `IdentDistrib.condMutualInfo_eq` stays `private` in `CopyLemma.lean`. Update the M2 policy comment there to reflect that only `condIndepFun_comp` was promoted.

1. **Scaffold `ZhangYeung/Theorem3.lean` and `ZhangYeungTest/Theorem3.lean` in the same change.** Add the module docstring, imports, and the three public theorem stubs in `ZhangYeung/Theorem3.lean`, add the matching signature-pinning `example`s for `zhangYeung`, `zhangYeung_dual`, `zhangYeung_averaged` in `ZhangYeungTest/Theorem3.lean`, and wire both top-level re-export files (`ZhangYeung.lean`, `ZhangYeungTest.lean`). This keeps the repo aligned with the project rule that every public `ZhangYeung/` module lands with its matching `ZhangYeungTest/` module in the same change. Confirm `lake build ZhangYeung.Theorem3`, `lake build ZhangYeung`, and `lake test` all pass. Commit as `feat: scaffold Theorem 3 module and API tests`.

1. **Land `mutualInfo_add_three_way_identity` as a private helper inside `section Helpers`.** Pure Shannon algebra, ~25 tactic lines following the M2 `delta_of_condMI_vanishes_eq` template. Commit as `feat(theorem3): prove three-way interaction identity`.

1. **Land `mutualInfo_le_of_condIndepFun` as a private helper inside `section Helpers`.** ~15-20 tactic lines. Start from PFR's `ent_of_cond_indep`, combine it with `entropy_triple_add_entropy_le`, and isolate the inner-pair-swap step via `entropy_comp_of_injective`. If the pair swap does not close cleanly inline, apply the split-before-bump lesson (`feedback_lean_split_before_bump.md`): factor `H[⟨X, ⟨Z, Y⟩⟩ ; μ] = H[⟨X, ⟨Y, Z⟩⟩ ; μ]` out as its own ~4-line private lemma, then close the main helper over that rewrite. Commit as `feat(theorem3): prove data processing from CondIndepFun`.

1. **Land `measurable_pairXZU` and `measurable_pairXY` projection helpers.** Each is a two-line `fun_prop` proof. Together they are one commit: `feat(theorem3): add projection measurabilities for Theorem 3 chase`.

1. **Land `zhangYeung_integer` as a private theorem inside `section MainTheorems`.** This is the main Shannon chase, ~25-35 tactic lines following the sketch above. Close the two `measurable_pairXZU` / `measurable_pairXY` + `IdentDistrib.mutualInfo_eq` transports inline; keep the final `linarith` over all seven intermediate facts. Commit as `feat(theorem3): prove integer form of Theorem 3 via copy-lemma Shannon chase`.

1. **Land `zhangYeung` as a public theorem.** One-line proof using `delta_form21_iff.mpr` applied to `zhangYeung_integer`, scaled by `linarith` to convert `2 * delta ≤ ...` to `delta ≤ (1/2) * ...`. Commit as `feat(theorem3): state Theorem 3 in the paper form`.

1. **Land `zhangYeung_dual`.** Proof: apply `zhangYeung_integer` with `X, Y` swapped, rewrite the left-hand side by `delta_comm_cond`, rewrite `mutualInfo_comm hY hX`, and convert via `delta_form22_iff.mpr` + `linarith`. ~5 lines. Commit as `feat(theorem3): derive the X-Y dual of Theorem 3 (eq. 22)`.

1. **Land `zhangYeung_averaged`.** Proof: combine `zhangYeung` and `zhangYeung_dual` (scaled back to `2 * delta ≤ ...` form via `linarith`), apply `delta_form23_of_form21_form22`, then `delta_form23_iff.mp`. ~8 lines. Commit as `feat(theorem3): derive the averaged symmetric form (eq. 23)`.

1. **Expand `ZhangYeungTest/Theorem3.lean` to cover the full public API.** Step 3 and steps 8-10 have established the signature-pinning `example`s and public theorems; expand with:
    - An independent-variable smoke test: for `X, Y, Z, U : Ω → Fin 2` with all four mutually independent under `μ`, all MI terms on the RHS of (21) collapse to 0 and the bound reads `delta Z U X Y μ ≤ 0`, which is `delta_le_mutualInfo` combined with `I[Z:U] = 0`.
    - A theorem-application test deriving the averaged form (23) from the public `zhangYeung` and `zhangYeung_dual` theorems plus the M1 form-conversion machinery. This is a direct cross-check that `zhangYeung_averaged`'s proof route is reconstructible from the two asymmetric theorems alone.
    - A pinned downstream-usage example: given concrete `Fin n`-valued `X, Y, Z, U`, consume `zhangYeung` and conclude a witness `2 * delta Z U X Y μ ≤ _` bound, exercising the full M2-to-M3 universe handling.

    Commit as `test: cover Theorem 3 API surface`.

1. **Update `AGENTS.md` (aka `CLAUDE.md`) Module Layout.** Add one line pointing to `ZhangYeung/Theorem3.lean` and one line pointing to `ZhangYeungTest/Theorem3.lean`. Note the `condIndepFun_comp` promotion in the entry for `ZhangYeung/Prelude.lean`. Commit as `docs: document Theorem 3 module in CLAUDE.md`.

1. **Run `make check`.** Address any remaining lint or build issues, and update `cspell-words.txt` with any new tokens introduced in docstrings (likely none: the module vocabulary is Shannon/information-theoretic, largely covered by the M2 additions). Commit any cspell/lint adjustments as `chore: address lint feedback`.

1. **Open the PR.** Title: `feat: prove Theorem 3, the Zhang-Yeung inequality`. Body links this plan and the roadmap, summarizes the three public theorems (eq. 21 headline, eq. 22 dual, eq. 23 averaged), and calls out the `condIndepFun_comp` promotion as a prerequisite refactor.

If the `zhangYeung_integer` proof in step 7 sprawls past 50 lines without closing, halt and reconsider: either split the chase into per-step sub-lemmas (one for the three-way interaction + CMI drop combined, one for the data-processing step, one for the final linarith), or rescope the two Shannon helpers to take weaker hypothesis signatures that better match what `copyLemma`'s `obtain` produces. Recap the precedent: M2's `delta_of_condMI_vanishes_eq` was budgeted for 30-40 lines and landed at 39; `zhangYeung_integer`'s body is a strictly easier chase because all the Shannon algebra is already encapsulated in the two helper lemmas.

## Open questions and known risks

### 7.1 Data-processing helper's inner-pair swap (low-moderate)

The `mutualInfo_le_of_condIndepFun` helper now starts from PFR's `ent_of_cond_indep`, but it still needs to align `H[⟨X, ⟨Z, Y⟩⟩ ; μ]` (from `entropy_triple_add_entropy_le hX hZ hY`) with `H[⟨X, ⟨Y, Z⟩⟩ ; μ]` (the triple shape `ent_of_cond_indep` returns). That alignment still routes through `entropy_assoc` + `entropy_comp_of_injective` with the inner-pair-swap bijection, so the only real implementation risk is the same pair-swap elaboration.

**Mitigation (try in order):**

1. Land the pair-swap identity `H[⟨X, ⟨Z, Y⟩⟩ ; μ] = H[⟨X, ⟨Y, Z⟩⟩ ; μ]` as its own ~4-line private lemma inside `section Helpers`. Proof route: `entropy_assoc` + `entropy_comp_of_injective`. Then the data-processing proof consumes it as a single `rw` between `entropy_triple_add_entropy_le` and `ent_of_cond_indep`.
1. If the `entropy_comp_of_injective` invocation is awkward because of universe / elaboration issues, fall back to the longer direct proof route via `condMutualInfo_eq_zero` + `condMutualInfo_eq` + `chain_rule''`, reusing the same pair-swap lemma once the triple entropy is on the page.
1. If both routes stall, factor out the pair-swap identity as a public lemma promoted to `ZhangYeung/Prelude.lean`. That lemma is generically useful for any future Shannon chase involving 4+ variables.

### 7.2 Universe bookkeeping (carried over from M2)

`copyLemma` binds `S₁, S₂, S₃, S₄ : Type u` at a single universe. M3's `zhangYeung_integer` applies `copyLemma` internally, so its signature inherits the `Type u` constraint. All three public M3 theorems (`zhangYeung`, `zhangYeung_dual`, `zhangYeung_averaged`) therefore also bind codomains at `Type u`. This is the same constraint M2 documented at `docs/plans/done/2026-04-17-copy-lemma.md:299-301`.

**Mitigation:** the universe constraint is expected not to cause friction for concrete callers (all four `S_i` at `Fin n` for some `n` elaborate at a fixed universe). If M4 (the counterexample) or M5 (the n+2-variable generalization) finds the universe constraint awkward, promoting `zhangYeung` to `Type*` via a wrapper that inserts `ULift` shims is a follow-up refactor, not M3's problem.

### 7.3 `condIndepFun_comp` promotion mechanics (low)

Promoting a `private` helper to a `public` namespaced lemma requires changing the visibility, updating all call sites, and ensuring no downstream module accidentally imported the private name via a qualified path. M2 does not import `condIndepFun_comp` from outside `ZhangYeung/CopyLemma.lean`, and the current tree has two actual use sites inside `CopyLemma.lean` (`copyLemma_condMI_X_Y₁_vanishes` and `copyLemma_condMI_X_X₁_vanishes`).

**Mitigation:** run `grep -n "condIndepFun_comp" ZhangYeung/ ZhangYeungTest/` before and after the refactor; confirm the only non-docstring use sites are still those same two internal `CopyLemma.lean` applications, with no new downstream consumer.

### 7.4 `measurable_pairXZU` vs M2's `measurable_projZUA` naming clash (low)

M2's `ZhangYeung/CopyLemma.lean` defines `projZUA : S₁ × S₂ × S₃ × S₄ → S₃ × S₄ × S₁` projecting to the `(Z, U, X)` triple (`:215`). M3 needs a different projection: `pairXZU : S₁ × S₂ × S₃ × S₄ → S₁ × (S₃ × S₄)`, projecting to `(X, ⟨Z, U⟩)`. The two are similarly named but have distinct shapes. Keep them in separate files (M2 projections stay `private` in `CopyLemma.lean`, M3 projections land `private` in `Theorem3.lean`) to avoid any namespace collision.

**Mitigation:** prefix M3's new projections with a `Theorem3` disambiguator if needed (e.g., `measurable_theorem3_pairXZU`). Do not promote either to `Prelude.lean`; their specific shapes are tied to the chase.

### 7.5 `delta_form22_iff` term ordering at the `linarith` step (low)

The integer form of eq. (22) that `zhangYeung_integer` applied with `(Y, X)` swapped produces is
$$
2\, I[Z:U;\mu] - 3\, I[Z:U|Y;\mu] - I[Z:U|X;\mu] \le I[Y:X;\mu] + I[Y:\langle Z, U \rangle;\mu].
$$
`delta_form22_iff`'s iff-RHS is
$$
2\, I[Z:U;\mu] - I[Z:U|X;\mu] - 3\, I[Z:U|Y;\mu] \le I[X:Y;\mu] + I[Y:\langle Z, U \rangle;\mu].
$$
These are `linarith`-equivalent but differ in three small ways: the swapped theorem first produces `delta Z U Y X μ`, which must be rewritten back to `delta Z U X Y μ` via `delta_comm_cond`; the RHS has `I[Y:X]` instead of `I[X:Y]`; and the conditional-MI terms appear in the opposite order. After the `delta_comm_cond` and `mutualInfo_comm hY hX` rewrites, `linarith` handles the remaining arithmetic reordering.

**Mitigation:** if the term ordering proves fragile, state an auxiliary `zhangYeung_dual_integer` matching `delta_form22_iff`'s RHS shape literally and route the `delta_form22_iff.mpr` call through it. One extra line, no proof-style cost.

### 7.6 Heartbeat budget for `zhangYeung_integer` (low)

The chase has seven intermediate facts (two copy-lemma inequalities, one three-way identity, one CMI nonneg, one data processing, two marginal transports) closing via `linarith`. The default heartbeat budget is comfortable for a seven-term `linarith` closure. Risk is low.

**Mitigation:** if the `linarith` closure hits the heartbeat limit, extract the integer bound as an intermediate `have` with the explicit arithmetic written out:

```lean
have h_combined :
    2 * I[Z : U ; μ] - 3 * I[Z : U | X ; μ] - I[Z : U | Y ; μ]
      ≤ I[X' : ⟨X_1, Y_1⟩ ; ν] + I[X_1 : Y_1 ; ν] := by linarith [h1, h2, h_three, h_nonneg]
linarith [h_combined, h_dp, h_marg_XZU, h_marg_XY]
```

Splitting the linarith into two stages halves the coefficient-space `linarith` has to search.

### 7.7 PFR API churn (low, documented)

Same as M2 Risk §7.6. This project treats PFR as a permanent pinned dependency (roadmap §3). M3 may surface PFR API issues; log them, any upstream cleanup is optional follow-up work.

## Verification

Per the roadmap M3 checkpoint: `theorem zhangYeung ... : delta Z U X Y μ ≤ (1/2) * (I[X : Y ; μ] + I[X : ⟨Z, U⟩ ; μ] + I[Z : U | X ; μ] - I[Z : U | Y ; μ])` with all hypotheses explicit; averaged corollary follows mechanically, and the theorem test module builds.

Operationally:

- `lake build ZhangYeung.Theorem3` compiles with no warnings, no `sorry`, no `admit`.
- `lake build ZhangYeung` compiles with `ZhangYeung.lean` re-exporting `ZhangYeung.Theorem3` cleanly.
- `lake build ZhangYeungTest.Theorem3` compiles; the test module imports only `ZhangYeung` and not `ZhangYeung.Theorem3` directly, exercising the public API surface.
- `lake build` and `lake test` both succeed on the default targets; CI goes green.
- `lake lint` passes (batteries linter via the `lintDriver`).
- `make check` passes in full.

**Test module contents** (`ZhangYeungTest/Theorem3.lean`, established incrementally in sequencing steps 3 and 8-11):

1. Signature-pinning `example` for each of the three public theorems (`zhangYeung`, `zhangYeung_dual`, `zhangYeung_averaged`). Snapshot against accidental drift in hypothesis order, universe bindings, or conclusion shape. Three `example`s.
1. Independent-variable smoke test: for `X, Y, Z, U : Ω → Fin 2` with all four mutually independent under `μ`, the inequality collapses to `delta Z U X Y μ ≤ 0`, recoverable from `delta_le_mutualInfo` + `I[Z:U] = 0`. This is a sanity check that `zhangYeung` does not produce nontrivial bounds on trivially independent inputs.
1. Theorem-application test deriving the averaged form (eq. 23) from the public `zhangYeung` and `zhangYeung_dual` plus the M1 form-conversion machinery. Confirms that `zhangYeung_averaged`'s proof route is reconstructible from the two asymmetric theorems alone.
1. Downstream-usage example: consume `zhangYeung` in a `Fin n`-valued concrete setting and conclude a named bound, exercising the full universe handling end-to-end. Analogous to M2's downstream example at `ZhangYeungTest/CopyLemma.lean:175`.

Each `example` lives inside `namespace ZhangYeungTest` with `open ZhangYeung`, following `ZhangYeungTest/Delta.lean`, `ZhangYeungTest/Theorem2.lean`, and `ZhangYeungTest/CopyLemma.lean`.

Land these in the same commits as the corresponding public surface (signatures in step 3, integer form in step 7, public theorems in steps 8-10, smoke / application / downstream tests in step 11, same branch), so `lake test` exercises the public API continuously through the milestone.

**Out-of-scope for M3** (documented here so M4 and M5 can pick them up):

- No exact-identity form with explicit remainder (paper's eq. 50, p. 1446). Roadmap §9 extension #2.
- No counterexample construction (Theorem 4, roadmap §M4). Worktree B handles this in parallel per roadmap §6 parallelism analysis.
- No n+2-variable generalization (Theorem 5, roadmap §M5).
- No promotion of either Shannon helper (`mutualInfo_add_three_way_identity`, `mutualInfo_le_of_condIndepFun`) to `Prelude.lean` or Mathlib. Both stay `private` unless a later milestone demonstrates concrete need.

## Critical files

**This milestone:**

- `ZhangYeung/Theorem3.lean` (new).
- `ZhangYeungTest/Theorem3.lean` (new).
- `ZhangYeung/Prelude.lean` (modified: add `condIndepFun_comp` promoted from `CopyLemma.lean`).
- `ZhangYeung/CopyLemma.lean` (modified: remove the private `condIndepFun_comp`, update its two internal use sites to use the promoted version, adjust the helpers-section docstring).
- `ZhangYeung.lean` (modified, add one `import` line).
- `ZhangYeungTest.lean` (modified, add one `import` line).
- `AGENTS.md` / `CLAUDE.md` (modified, two-line addition under "Module Layout", plus a note on the `Prelude` change).

**Read-only references:**

- `ZhangYeung/Delta.lean` (M1 output; `ZhangYeung.delta` and form-conversion lemmas).
- `ZhangYeung/CopyLemma.lean` (M2 output; `copyLemma`, the two `delta_le_mutualInfo_*` inequalities, and the transport scaffolding M3 calls by name).
- `ZhangYeung/Theorem2.lean` (M1.5 output; style precedent for Shannon-algebra identities).
- `references/transcriptions/zhangyeung1998.md` (paper transcription; Theorem 3 statement on line 290, proof on lines 680-709, explicit remainder $R$ on lines 711-768).
- `.lake/packages/pfr/PFR/ForMathlib/Entropy/Basic.lean` (all Shannon primitives listed in the "PFR and Mathlib API surface used" section).
- `.lake/packages/pfr/PFR/ForMathlib/ConditionalIndependence.lean` (`CondIndepFun` at line 105; `condIndep_copies` at line 135).
- `.lake/packages/mathlib/Mathlib/Probability/IdentDistrib.lean` (`IdentDistrib`, `IdentDistrib.comp`, `IdentDistrib.symm`).
- `docs/plans/done/2026-04-17-copy-lemma.md` (M2 plan; source of the style precedent for this plan, and the policy comment about promoting `condIndepFun_comp` when M3 needs it).

Reference: the `write-lean-code` skill is authoritative for Lean naming and proof style; the `write-math` skill governs the module docstring and any mathematical prose inside comments; the `write-pandoc-markdown` skill governs this plan document.
