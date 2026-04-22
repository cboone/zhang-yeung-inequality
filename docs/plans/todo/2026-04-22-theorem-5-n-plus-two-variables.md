---
title: "M5: Theorem 5, the n+2-variable Zhang-Yeung generalization (1998, §III, eqs. 27-28)"
created: 2026-04-22
branch: formalize/m5-theorem-5
roadmap: docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md
milestone: M5
depends_on: M1 (`ZhangYeung/Delta.lean`), M2 (`ZhangYeung/CopyLemma.lean`), M3 (`ZhangYeung/Theorem3.lean`), and M4 (`ZhangYeung/{EntropyRegion,Theorem4}.lean`), all merged into `main`. M4 is not a proof-level prerequisite for M5, but its `entropyFn_n` infrastructure and `Fin n`-family conventions (heterogeneous codomains `S : Fin n → Type u`, dependent products `∀ i, Ω → S i`) are reused at the statement level. The `m5-theorem-5` worktree starts from the tip of `main` after PR #13 (entropy-region universe polymorphism) and PR #12 (the M4 exact closure theorems) have landed.
---

## Context

Milestone M5 of the Zhang-Yeung roadmap (§6) formalizes **Theorem 5** of the 1998 paper: the n+2-variable generalization of the Zhang-Yeung inequality. The paper states it in two forms (eqs. 27 and 28) and omits the proof with the remark that it follows "using exactly the same idea used in the proof of Theorem 3 and an inductive argument" (`references/transcriptions/zhangyeung1998.md:408`). M5 is the roadmap's scope-resolved **stretch** milestone (roadmap §4, "Stretch"); the core roadmap deliverables M0-M4 landed on `main` before M5 begins.

**Primary reference:** `references/transcriptions/zhangyeung1998.md` (verified 2026-04-16). The statement lives on lines 388-408. Equation and line numbers below reference that transcription.

The paper's Theorem 5 statement:

> For any set of $n+2$ discrete random variables $U, Z, X_{1}, \ldots, X_{n}$ (with $n \ge 2$) and any $i \in \{1, 2, \ldots, n\}$,
> $$
> n \, I(U; Z) - \sum_{j=1}^{n} I(U; Z \mid X_{j}) - n \, I(U; Z \mid X_{i}) \;\le\; I(X_{i}; U, Z) + \sum_{j=1}^{n} H(X_{j}) - H(X_{1}, X_{2}, \ldots, X_{n}). \tag{27}
> $$
> Furthermore, by averaging (27) over $i$,
> $$
> n \, I(U; Z) - 2 \sum_{j=1}^{n} I(U; Z \mid X_{j}) \;\le\; \frac{1}{n} \sum_{i=1}^{n} I(X_{i}; U, Z) + \sum_{j=1}^{n} H(X_{j}) - H(X_{1}, X_{2}, \ldots, X_{n}). \tag{28}
> $$

The trailing expression $\sum_{j=1}^{n} H(X_{j}) - H(X_{1}, \ldots, X_{n})$ is the **total correlation** (a.k.a. multi-information) $T(X_{1}, \ldots, X_{n})$; for $n = 2$ it reduces to $I(X_{1}; X_{2})$, and eq. (27) collapses to Theorem 3 in the form produced by `delta_form21_iff.mpr` after relabeling $(Z, U) \leftrightarrow (U, Z)$ and $(X, Y) \leftrightarrow (X_{1}, X_{2})$. That base-case recovery is the bridge from M3 to the general statement.

### Why M5 lands now

1. **All non-Shannon ingredients exist.** M2 shipped the copy lemma (`copyLemma` and the abstract Lemma 2 `delta_of_condMI_vanishes_eq`) and already contains a private conditional-mutual-information transport helper `IdentDistrib.condMutualInfo_eq`. M3 shipped the data-processing helper `mutualInfo_le_of_condIndepFun` and the three-way interaction identity `mutualInfo_add_three_way_identity` (both `private` in `ZhangYeung/Theorem3.lean`, candidates for promotion here -- see §7.3). Theorem 5's proof is the same Shannon chase as Theorem 3, summed over a family of pairwise copy-lemma applications, plus one new Shannon ingredient: an iterated version of the three-way identity, equivalent to iterated conditional subadditivity (§6.4.3 below).
1. **`condIndep_copies` applies to tuples.** PFR's `ProbabilityTheory.condIndep_copies` (verified at `.lake/packages/PFR/PFR/ForMathlib/ConditionalIndependence.lean:135`) is a 2-copy construction but parametric over the codomain $\alpha$ of the first argument. Specializing $\alpha = \prod_{i : \mathrm{Fin}\, n} S_{i}$ recovers "two conditionally-independent copies of the full n-tuple" in a single invocation; there is no need for an n-ary `iCondIndep_copies` (which PFR does not provide, confirmed 2026-04-22). The pairwise projections of this tuple-level copy are what drive the chase.
1. **M4's `entropyFn_n` + `Fin n`-family conventions.** M4 landed the heterogeneous family presentation `X : ∀ i : Fin n, Ω → S i`, the pi-type codomain `∀ i : Fin n, S i`, and their measurability/finiteness instances. M5 uses the same family shape, so the statement layer of M5 matches M4's (and is less work to write and read).
1. **The paper's `(U, Z)` vs. M3's `(Z, U)` asymmetry is vacuous.** Paper eq. (27) writes $I(U; Z)$; M3's `zhangYeung` uses $I(Z; U)$ on the measured-pair side of `delta`. The two are equal by `mutualInfo_comm` / `condMutualInfo_comm`, and M1 already captured both orderings via `delta_comm_main`. M5 keeps the public theorem in the paper's `I[U : Z]` order for citation fidelity, but the proof can and should run internally in `(Z, U)` order to match `delta` and avoid unnecessary pair repacking.

### What M5 does not do

- **Equality form of Theorem 5.** The paper states Theorem 5 as an inequality only and does not extract an explicit remainder analogous to $R(X, Y, Z, U, X_{1}, Y_{1})$ for Theorem 3 (roadmap §9, extension #2). No equality upgrade is planned for M5.
- **Extraction of the new Shannon helpers.** The iterated subadditivity lemma and the generalized three-way identity stay `private` in `ZhangYeung/Theorem5.lean` unless a further milestone demands them. Promotion / upstreaming is roadmap §9 future work, not M5.
- **n+2-variable witness for Theorem 4 at $n \ge 4$.** `theorem4_ge_four` already handles the n ≥ 4 Theorem 4 lift (M4). M5 does not re-lift to Theorem 4's witness at n ≥ 4; that bridge is closed.
- **Theorem 6 (the paper's seven-construction inner bound on $\overline{\Gamma^{*}_{4}}$).** Out of S2 scope; roadmap §9.

## Paper equations this milestone formalizes

Equation (27), Theorem 5 (the asymmetric form, indexed by $i$):

$$
n \, I(U; Z) - \sum_{j=1}^{n} I(U; Z \mid X_{j}) - n \, I(U; Z \mid X_{i}) \;\le\; I(X_{i}; U, Z) + \sum_{j=1}^{n} H(X_{j}) - H(X_{1}, \ldots, X_{n}).
$$

Equation (28), the averaged symmetric form (no new measure-theoretic content; `linarith` over $n$ instances of (27)):

$$
n \, I(U; Z) - 2 \sum_{j=1}^{n} I(U; Z \mid X_{j}) \;\le\; \frac{1}{n} \sum_{i=1}^{n} I(X_{i}; U, Z) + \sum_{j=1}^{n} H(X_{j}) - H(X_{1}, \ldots, X_{n}).
$$

M5 does **not** introduce a `Fin n → ...` set-function surface for Theorem 5; the random-variable form lives in a single module (`ZhangYeung/Theorem5.lean`) and the set-function bridge step is out of scope (no Theorem 4 analogue is needed for $n$-variable discussion).

## Prerequisites

M1 delivers (merged into `main` via PR #4):

- `ZhangYeung/Delta.lean` with the `delta` definition, `delta_def`, `delta_self`, `delta_comm_cond`, `delta_comm_main`, and the form-conversion lemmas `delta_form21_iff`, `delta_form22_iff`, `delta_form23_iff`, `delta_form23_of_form21_form22`.

M2 delivers (merged via PR #8):

- `ZhangYeung/CopyLemma.lean` with:
  - `copyLemma` (the 4-variable wrapper around `condIndep_copies`).
  - `delta_of_condMI_vanishes_eq` (Lemma 2, abstract, under a vanishing-CMI hypothesis).
  - Six copy-projection corollaries (`copyLemma_delta_{transport_Y_to_Y₁,transport_X_to_X₁,identity_Y₁,identity_X_X₁,le_mutualInfo_Y₁,le_mutualInfo_X_X₁}`).
  - The private helper `IdentDistrib.condMutualInfo_eq`, a promotion candidate for M5's delta-transport step.

M3 delivers (merged via PR #10):

- `ZhangYeung/Theorem3.lean` with `zhangYeung` (eq. 21), `zhangYeung_dual` (eq. 22), `zhangYeung_averaged` (eq. 23), and the private `zhangYeung_integer` proof precedent (not exported).
- The private Shannon helpers inside `ZhangYeung/Theorem3.lean`: `mutualInfo_add_three_way_identity` (three-way interaction) and `mutualInfo_le_of_condIndepFun` (data processing). Both are promotion candidates for M5 (§7.3).
- `ZhangYeung/Prelude.lean` with `ZhangYeung.condIndepFun_comp` (post-composition of `CondIndepFun` by measurable codomain functions), promoted during M3.

M4 delivers (merged via PR #11 and PR #12):

- `ZhangYeung/EntropyRegion.lean` with the generic `Fin n`-family infrastructure (`entropyFn_n`, `shannonRegion_n`, `entropyRegion_n`, `almostEntropicRegion_n`, `restrictFirstFour` with transport lemmas).
- `ZhangYeung/Theorem4.lean` with the exact closure theorems.

Before starting M5, run `bin/bootstrap-worktree` in the `m5-theorem-5` worktree, confirm `make check` is green, and verify `lake env lean --version` reports the same toolchain the pinned PFR revision compiles against.

## PFR and Mathlib API surface used

All declarations below live under `namespace ProbabilityTheory` unless noted. Line numbers reference `.lake/packages/PFR/PFR/ForMathlib/Entropy/Basic.lean` at the currently-pinned PFR revision.

**Carried forward from M1-M4 (no audit needed):**

- Shannon primitives: `mutualInfo_def`, `mutualInfo_comm`, `condMutualInfo_eq`, `condMutualInfo_eq_zero`, `condMutualInfo_nonneg`, `chain_rule'`, `chain_rule''`, `entropy_comm`, `entropy_assoc`, `entropy_submodular`, `condEntropy_comm`, `entropy_triple_add_entropy_le`, `ent_of_cond_indep`.
- Identical distribution / conditional independence: `IdentDistrib`, `IdentDistrib.comp`, `IdentDistrib.symm`, `IdentDistrib.entropy_congr`, `IdentDistrib.condEntropy_eq`, `IdentDistrib.mutualInfo_eq`, `CondIndepFun`, `condIndep_copies`.
- From the project: `ZhangYeung.delta`, `delta_def`, `delta_self`, `delta_comm_main`, `delta_form21_iff`; `copyLemma`, `delta_of_condMI_vanishes_eq`, the six transport corollaries; `zhangYeung`; `condIndepFun_comp`.

**New to M5 (to audit before the first commit -- §6.1):**

- `Finset.sum_*` API for manipulating $\sum_{j=1}^{n}$ (i.e. `Finset.univ.sum` over `Fin n`): `Finset.sum_congr`, `Finset.sum_le_sum`, `Finset.sum_const`, `Finset.sum_add_distrib`, `Finset.sum_sub_distrib`, `Finset.univ_sum_single`.
- `PFR/ForMathlib/FiniteRange/Defs.lean`: the automatic `FiniteRange` instances on finite codomains that discharge `condIndep_copies`'s conditioned-variable hypothesis for `fun ω => (Z ω, U ω)`.
- `Mathlib/Probability/Independence/Conditional.lean`: candidate iterated / pairwise conditional-independence lemmas, though none are strictly required -- M5's use of pairwise conditional independence routes through `condIndepFun_comp` applied to the tuple-level `CondIndepFun` from `condIndep_copies`.
- `Mathlib/MeasureTheory/MeasurableSpace/Pi.lean` / instances: `MeasurableSpace.pi`, `Fintype.pi`-form instances, `MeasurableSingletonClass.pi`, `Finite (∀ i : Fin n, S i)`. Needed at statement level to feed the pi-type codomain into `condIndep_copies`.
- `Mathlib/Logic/Equiv/Fin.lean` / `Fintype.equivFin`: small-arity `Fin n` bijections / index manipulations if the proof needs to permute summation ranges.
- No ready-made PFR or Mathlib primitive for `H[⟨B_1, ..., B_n⟩ | A ; μ] ≤ ∑_k H[B_k | A ; μ]` (iterated conditional subadditivity) was found in the bootstrapped dependency tree. Derive it locally by induction on `n` from `entropy_triple_add_entropy_le` (see §6.4.3).

## The M5 theorems

### Headline: Theorem 5 (paper eq. 27)

```lean
theorem theorem5
    {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 2 ≤ n)
    {S_U S_Z : Type u} {S : Fin n → Type u}
    [MeasurableSpace S_U] [MeasurableSpace S_Z]
    [∀ i, MeasurableSpace (S i)]
    [Finite S_U] [Finite S_Z] [∀ i, Finite (S i)]
    [MeasurableSingletonClass S_U] [MeasurableSingletonClass S_Z]
    [∀ i, MeasurableSingletonClass (S i)]
    {U : Ω → S_U} {Z : Ω → S_Z} {X : ∀ i : Fin n, Ω → S i}
    (hU : Measurable U) (hZ : Measurable Z) (hX : ∀ i, Measurable (X i))
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (i : Fin n) :
    n * I[U : Z ; μ] - ∑ j, I[U : Z | X j ; μ] - n * I[U : Z | X i ; μ]
      ≤ I[X i : ⟨U, Z⟩ ; μ]
        + ∑ j, H[X j ; μ]
        - H[(fun ω : Ω => fun j : Fin n => X j ω) ; μ]
```

The universe constraints (`S_U, S_Z, S i : Type u`) are forced by the tuple-level `condIndep_copies` application inside the proof, matching M2 and M3. The hypothesis `hn : 2 ≤ n` handles the degenerate $n < 2$ case (the statement is vacuous but well-typed for $n = 0, 1$; the proof does not require $n \ge 2$, but the paper's statement does, and keeping the hypothesis prevents spurious specializations).

Internally the proof runs in `(Z, U)` order, producing the natural `delta Z U ...` arithmetic that matches M3 and `delta_of_condMI_vanishes_eq`; the public theorem is then rewritten back to the paper's `I[U : Z]` order by `mutualInfo_comm` and `condMutualInfo_comm`.

**Note on the tuple expression.** `(fun ω => fun j : Fin n => X j ω) : Ω → (∀ j : Fin n, S j)` is the joint-entropy variable. It reduces to `fun ω => (X 0 ω, X 1 ω)` at $n = 2$ modulo a pi-to-prod encoding. The tuple-level entropy can equivalently be written as `H[⟨X 0, X 1, ..., X (n-1)⟩ ; μ]` after a small-$n$ specialization; leave it in the pi-type form to match M4's `entropyFn_n` idiom.

### Averaged: Theorem 5 eq. (28)

```lean
theorem theorem5_averaged
    {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 2 ≤ n)
    {S_U S_Z : Type u} {S : Fin n → Type u}
    [MeasurableSpace S_U] [MeasurableSpace S_Z]
    [∀ i, MeasurableSpace (S i)]
    [Finite S_U] [Finite S_Z] [∀ i, Finite (S i)]
    [MeasurableSingletonClass S_U] [MeasurableSingletonClass S_Z]
    [∀ i, MeasurableSingletonClass (S i)]
    {U : Ω → S_U} {Z : Ω → S_Z} {X : ∀ i : Fin n, Ω → S i}
    (hU : Measurable U) (hZ : Measurable Z) (hX : ∀ i, Measurable (X i))
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    n * I[U : Z ; μ] - 2 * (∑ j, I[U : Z | X j ; μ])
      ≤ (1 / n : ℝ) * (∑ i, I[X i : ⟨U, Z⟩ ; μ])
        + ∑ j, H[X j ; μ]
        - H[(fun ω : Ω => fun j : Fin n => X j ω) ; μ]
```

Proof: sum `theorem5` over `i : Fin n`, divide by `n` using `Finset.sum_div`, and close by `Finset.sum_le_sum` / `linarith`. No additional measure-theoretic content. **Budget:** ≤ 20 tactic lines.

### Base case compatibility: Theorem 5 at $n = 2$ equals Theorem 3

An `example` in the test module pins:

```lean
example
    {Ω : Type*} [MeasurableSpace Ω]
    {S_U S_Z S₁ S₂ : Type u}
    [MeasurableSpace S_U] [MeasurableSpace S_Z]
    [MeasurableSpace S₁] [MeasurableSpace S₂]
    [Finite S_U] [Finite S_Z] [Finite S₁] [Finite S₂]
    [MeasurableSingletonClass S_U] [MeasurableSingletonClass S_Z]
    [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
    {U : Ω → S_U} {Z : Ω → S_Z} {X₁ : Ω → S₁} {X₂ : Ω → S₂}
    (hU : Measurable U) (hZ : Measurable Z) (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    2 * I[U : Z ; μ] - 3 * I[U : Z | X₁ ; μ] - I[U : Z | X₂ ; μ]
      ≤ I[X₁ : ⟨U, Z⟩ ; μ] + I[X₁ : X₂ ; μ] := by
  -- One-line reduction: apply `theorem5` at `n = 2`, `i = 0`, with the `Fin 2`-indexed
  -- family `![X₁, X₂]`; rewrite the entropy-tuple term to `I[X₁ : X₂ ; μ]` using the
  -- pi-to-prod bijection, then close by `linarith`.
  sorry
```

The point of this example is to exercise that the M5 statement at $n = 2$ recovers the integer form of Theorem 3 (the form `delta_form21_iff` converts between). No new theorem; it is a compile-time check that `theorem5` specializes cleanly.

## Proof sketch: the Shannon chase for `theorem5`

The paper's remark that Theorem 5's proof "uses exactly the same idea used in the proof of Theorem 3 and an inductive argument" admits a cleaner interpretation than literal induction on $n$: the **"same idea"** is the copy construction and the pairwise Lemma 2 inequality; the **"inductive argument"** is the chain-rule expansion of joint entropy (equivalently, iterated conditional subadditivity), which inducts internally over the tuple index $j$ but does not require induction in the outer theorem statement.

The resulting proof is a single Shannon chase over a tuple-level copy-lemma output, summed over a family of pairwise applications. It parallels M3's chase with the following modifications:

1. **Copy lemma at a tuple codomain.** Apply PFR's `condIndep_copies` to the pair `(⟨X 0, ..., X (n-1)⟩, ⟨Z, U⟩)`. This gives two conditionally-independent tuple copies `X' : Ω' → (∀ j, S j)` and `X* : Ω' → (∀ j, S j)`, each identically distributed with `⟨X 0, ..., X (n-1)⟩` under the shared `(Z', U')`. All M5 projection measurabilities ("apply `X' j := fun ω => X' ω j`") are one-line `measurable_pi_apply` invocations.
1. **Pairwise Lemma 2 applied $n$ times.** For each `k : Fin n`, instantiate `delta_of_condMI_vanishes_eq` at `(A, B, C, D) := (X' i, Z', U', X* k)`. The vanishing-CMI hypothesis `I[X' i : X* k | ⟨Z', U'⟩ ; ν] = 0` follows by projecting the tuple-level `CondIndepFun X' X* ⟨Z', U'⟩ ν` to the pair `(i, k)` via `ZhangYeung.condIndepFun_comp`. This yields `delta Z' U' (X' i) (X* k) ν = I[X' i : X* k ; ν] - I[X' i : X* k | Z' ; ν] - I[X' i : X* k | U' ; ν] - I[Z' : U' | ⟨X' i, X* k⟩ ; ν]`, hence `delta Z' U' (X' i) (X* k) ν ≤ I[X' i : X* k ; ν]` by conditional-MI nonnegativity.
1. **Marginal equality, summed.** Transport the $n$ pairwise delta inequalities back to the $(Z, U)$ side using one use of `IdentDistrib.mutualInfo_eq` for the unconditional `I[Z : U]` term and two uses of `IdentDistrib.condMutualInfo_eq` (promoted from M2 in §7.3) for the conditional terms. Summing over $k$ gives $n \, I(Z; U) - n \, I(Z; U \mid X_{i}) - \sum_{k} I(Z; U \mid X_{k}) \le \sum_{k} I(X'_{i}; X^{*}_{k})$.
1. **Chain-rule MI domination ($n$-ary three-way identity).** $\sum_{k} I(X'_{i}; X^{*}_{k}) \le I(X'_{i}; \langle X^{*}_{1}, \ldots, X^{*}_{n}\rangle) + T(X^{*}_{1}, \ldots, X^{*}_{n})$, where $T$ is the total correlation. Equivalent to iterated conditional subadditivity: $H(\langle B_{1}, \ldots, B_{n}\rangle \mid A) \le \sum_{k} H(B_{k} \mid A)$, itself a one-direction induction on $n$ from `entropy_triple_add_entropy_le`.
1. **Data processing.** $I(X'_{i}; \langle X^{*}_{1}, \ldots, X^{*}_{n}\rangle) \le I(X'_{i}; \langle Z', U'\rangle)$, via the tuple-level `CondIndepFun X' X* ⟨Z', U'⟩ ν` projected to `(X' i, X* 1..n)` and plugged into M3's `mutualInfo_le_of_condIndepFun` (promoted in §7.3).
1. **Closing marginal equalities.** $I(X'_{i}; \langle Z', U'\rangle) = I(X_{i}; \langle Z, U\rangle)$ via the first-copy triple `IdentDistrib`; the total-correlation term is transported by tuple-level `IdentDistrib` plus `IdentDistrib.entropy_congr` for the joint entropy and coordinate projections for the single-variable entropy summands.
1. **Close by `linarith`.** All intermediate facts combine linearly.

This is the detailed structure of the "same idea + inductive argument" the paper sketches. The only genuinely new Shannon content beyond M3 is step 4 (the $n$-ary three-way identity / iterated conditional subadditivity).

### Proof body, expanded for exposition

```lean
theorem theorem5 ... := by
  -- Step 0: tuple-level copy lemma.
  let Xtuple : Ω → (∀ j : Fin n, S j) := fun ω j => X j ω
  have hXtuple : Measurable Xtuple := measurable_pi_lambda _ (fun j => hX j)
  have hZU : Measurable (fun ω => (Z ω, U ω)) := hZ.prodMk hU
  obtain ⟨Ω', mΩ', Xprime, Xstar, VZU, ν, _, hXprime, hXstar, hVZU,
      hCond, hIdent₁, hIdent₂⟩ :=
    condIndep_copies Xtuple (fun ω => (Z ω, U ω)) hXtuple hZU μ
  -- Project out Z', U' from VZU and X' j, X* j from Xprime, Xstar via `measurable_pi_apply`.
  let Z' : Ω' → S_Z := fun ω => (VZU ω).1
  let U' : Ω' → S_U := fun ω => (VZU ω).2
  let X' : ∀ j : Fin n, Ω' → S j := fun j ω => Xprime ω j
  let X* : ∀ j : Fin n, Ω' → S j := fun j ω => Xstar ω j
  have hZ' : Measurable Z' := measurable_fst.comp hVZU
  have hU' : Measurable U' := measurable_snd.comp hVZU
  have hX' : ∀ j, Measurable (X' j) := fun j => (measurable_pi_apply j).comp hXprime
  have hX* : ∀ j, Measurable (X* j) := fun j => (measurable_pi_apply j).comp hXstar
  -- Step 1: build n pairwise delta-le-mutualInfo inequalities.
  --   For each k : Fin n, Δ(Z', U' | X' i, X* k) ≤ I[X' i : X* k ; ν].
  -- The vanishing-CMI hypothesis `I[X' i : X* k | ⟨Z', U'⟩ ; ν] = 0` projects the
  -- tuple-level `CondIndepFun` directly; no `(U', Z')` repacking is needed because
  -- the copy is constructed over `(Z, U)` from the start.
  have h_vanish : ∀ k : Fin n,
      I[X' i : X* k | (fun ω' => (Z' ω', U' ω')) ; ν] = 0 := fun k => by
    refine (condMutualInfo_eq_zero (hX' i) (hX* k)).mpr ?_
    -- Project `CondIndepFun Xprime Xstar VZU ν` to coordinate (i, k) on the paired side.
    sorry
  have h_pair : ∀ k : Fin n, delta Z' U' (X' i) (X* k) ν ≤ I[X' i : X* k ; ν] := by
    intro k
    -- Apply `delta_of_condMI_vanishes_eq` at `(A, B, C, D) := (X' i, Z', U', X* k)`
    -- and drop the three nonnegative CMI terms on the right-hand side.
    sorry
  -- Step 2: transport each delta via `IdentDistrib.condMutualInfo_eq` to the μ-side.
  have h_transport : ∀ k : Fin n, delta Z U (X i) (X k) μ = delta Z' U' (X' i) (X* k) ν := by
    intro k
    -- Build pair-level `IdentDistrib ⟨Z, U⟩ ~ ⟨Z', U'⟩` for the unconditional term,
    -- and triple-level IdentDistribs `(Z, U, X i) ~ (Z', U', X' i)` and
    -- `(Z, U, X k) ~ (Z', U', X* k)` for the two conditional terms. Expand `delta`
    -- via `delta_def`, then transport with one `IdentDistrib.mutualInfo_eq` and two
    -- uses of `IdentDistrib.condMutualInfo_eq`.
    sorry
  -- Step 3: sum over k : Fin n.
  have h_sum :
      n * I[Z : U ; μ] - n * I[Z : U | X i ; μ] - ∑ k, I[Z : U | X k ; μ]
        ≤ ∑ k, I[X' i : X* k ; ν] := by
    -- LHS = sum over k of [I[Z:U] - I[Z:U|X i] - I[Z:U|X k]] = sum of delta Z U (X i) (X k).
    -- Apply h_pair and h_transport pointwise; close by `Finset.sum_le_sum` + `linarith`.
    sorry
  -- Step 4: chain-rule MI domination.
  have h_chain :
      ∑ k, I[X' i : X* k ; ν]
        ≤ I[X' i : (fun ω' => fun k : Fin n => X* k ω') ; ν]
          + (∑ k, H[X* k ; ν])
          - H[(fun ω' => fun k : Fin n => X* k ω') ; ν] := by
    -- The `mutualInfo_add_n_way_inequality` helper (§6.4.3) specialized to A = X' i,
    -- B_k = X* k. Proof: expand each MI via `mutualInfo_eq_entropy_sub_condEntropy` and
    -- reduce to iterated conditional subadditivity.
    sorry
  -- Step 5: data processing.
  have h_dp :
      I[X' i : (fun ω' => fun k : Fin n => X* k ω') ; ν] ≤ I[X' i : ⟨Z', U'⟩ ; ν] := by
    -- `mutualInfo_le_of_condIndepFun` (promoted from M3, §7.3) applied to the projected
    -- `CondIndepFun X' Xstar ⟨Z', U'⟩ ν`.
    sorry
  -- Step 6: closing marginal equalities.
  have h_marg_XUZ : I[X' i : ⟨Z', U'⟩ ; ν] = I[X i : ⟨Z, U⟩ ; μ] := by
    -- Transport via triple `(X i, Z, U) ~ (X' i, Z', U')` extracted from `hIdent₁`.
    sorry
  have h_marg_T :
      H[(fun ω' => fun k : Fin n => X* k ω') ; ν] = H[(fun ω => fun k : Fin n => X k ω) ; μ]
      ∧ ∀ k : Fin n, H[X* k ; ν] = H[X k ; μ] := by
    -- Tuple-level `IdentDistrib` from `hIdent₂` gives the joint-entropy transport via
    -- `IdentDistrib.entropy_congr`; projecting to each coordinate gives the single-entropy equalities.
    sorry
  -- Close by `linarith` over all of the above.
  sorry
```

Replace each `sorry` with its body during sequencing steps 5-11 below.

### Size and structure

The body of `theorem5` will end up roughly the size of `zhangYeung_integer` (~35 lines) **plus** the helper definitions for the $n$-ary chain-rule MI domination and the pairwise projection of the tuple-level `CondIndepFun` (~40 lines combined). Total new code in `ZhangYeung/Theorem5.lean`: ~200-250 lines including docstrings, matching M3's scale. If the body exceeds 400 lines, halt and reconsider: either factor more of the chase into private helper lemmas, or (more likely) split the $n$-ary chain-rule identity into its own module.

## File layout

```text
ZhangYeung/
  Prelude.lean              # Promote `mutualInfo_le_of_condIndepFun`, `mutualInfo_add_three_way_identity`, and `IdentDistrib.condMutualInfo_eq` here from Theorem3/CopyLemma (§7.3).
  Delta.lean                # unchanged (M1)
  CopyLemma.lean            # drop the promoted `IdentDistrib.condMutualInfo_eq` helper, reroute local call sites to `ZhangYeung.*`
  EntropyRegion.lean        # unchanged (M4)
  Theorem2.lean             # unchanged (M1.5)
  Theorem3.lean             # drop the two promoted helpers, reroute local call sites to `ZhangYeung.*`
  Theorem4.lean             # unchanged (M4)
  Theorem5.lean             # NEW: this milestone
ZhangYeung.lean             # add `import ZhangYeung.Theorem5`
ZhangYeungTest/
  Delta.lean                # unchanged
  CopyLemma.lean            # unchanged
  EntropyRegion.lean        # unchanged
  Theorem2.lean             # unchanged
  Theorem3.lean             # unchanged (promotion is API-preserving for the public surface)
  Theorem4.lean             # unchanged
  Theorem5.lean             # NEW: this milestone
ZhangYeungTest.lean         # add `import ZhangYeungTest.Theorem5`
AGENTS.md (aka CLAUDE.md)   # add two Module Layout entries; note the three helper promotions into `Prelude`.
```

### Section structure inside `ZhangYeung/Theorem5.lean`

```text
├── Module docstring (## Main statements, ## Implementation notes, ## References, ## Tags)
├── Imports: ZhangYeung.CopyLemma, ZhangYeung.Delta, ZhangYeung.EntropyRegion, ZhangYeung.Prelude, ZhangYeung.Theorem3
├── namespace ZhangYeung
├── section Helpers
│     - measurable/projection helpers for the tuple-level copy (§6.4.1)
│     - `tuple_condIndepFun_pairProj` : project `CondIndepFun Xprime Xstar VZU ν` to a pair (§6.4.2)
│     - `mutualInfo_add_n_way_inequality` : n-ary chain-rule MI domination / iterated cond. subadditivity (§6.4.3)
├── section MainTheorems
│     - private theorem `theorem5_integer` : the integer-scaled form the chase naturally produces
│     - theorem `theorem5` : paper eq. (27)
│     - theorem `theorem5_averaged` : paper eq. (28)
└── end ZhangYeung
```

## Sequencing: commits

Each commit maintains a green build + lint + test. Each commit is a conventional-commit-styled small unit.

1. **Bootstrap + pre-flight checks.** In the `m5-theorem-5` worktree: `bin/bootstrap-worktree`; confirm `make check` is green with M0-M4 on `main`. Run two pre-flight experiments in a scratch `.lean` file (delete after):

    1. **PFR primitives grep.** Confirm `condIndep_copies` still exists at `.lake/packages/PFR/PFR/ForMathlib/ConditionalIndependence.lean:135` and its codomain-polymorphic signature still accepts `α := ∀ j : Fin n, S j`. Audit the actual side conditions on the conditioned variable `fun ω => (Z ω, U ω) : Ω → S_Z × S_U`: `[Countable (S_Z × S_U)]`, `[MeasurableSingletonClass (S_Z × S_U)]`, and `[FiniteRange (fun ω => (Z ω, U ω))]` (the last one should be automatic from finite codomain).
    1. **`Finset` summation rehearsal.** Confirm `∑ j : Fin n, H[X j ; μ]` elaborates cleanly with `Finset.univ_sum_le_sum` and `Finset.sum_le_sum` available; confirm `Finset.sum_div` or equivalent is available to close `theorem5_averaged`.

    Halt on any failure.

1. **Promote three generic helpers to `ZhangYeung/Prelude.lean`.** `mutualInfo_add_three_way_identity` and `mutualInfo_le_of_condIndepFun` both live `private` inside `ZhangYeung/Theorem3.lean`; `IdentDistrib.condMutualInfo_eq` lives `private` inside `ZhangYeung/CopyLemma.lean` (§7.3). M5 is the first downstream consumer that needs all three, so promote them in a single non-API-breaking refactor commit. Reroute the existing local call sites in `ZhangYeung/Theorem3.lean` and `ZhangYeung/CopyLemma.lean` to the promoted public names. `make check` stays green. Commit as `refactor: promote generic Shannon helpers to Prelude`.

1. **Scaffold `ZhangYeung/Theorem5.lean` and `ZhangYeungTest/Theorem5.lean` in the same change.** Land the module docstring, imports, the three-section skeleton (Helpers / MainTheorems, with `sorry` stubs for the two main theorems), the matching signature-pinning `example`s for `theorem5` and `theorem5_averaged` in the test module, and wire both top-level re-export files. `lake build` and `lake test` both succeed (with the `sorry`s producing warnings). Commit as `feat: scaffold Theorem 5 module and API tests`.

1. **Land the `Fin n` projection helpers.** Small measurability lemmas for `measurable_pi_apply`-style projections of tuple-valued random variables, plus the pair/triple projection maps consumed by `IdentDistrib.comp` in the delta-transport step. One commit; ≤ 20 lines. `feat(theorem5): add Fin-indexed projection helpers`.

1. **Land `tuple_condIndepFun_pairProj`.** The key projection lemma: given `CondIndepFun Xprime Xstar ⟨Z', U'⟩ ν` at the tuple codomain `∀ j, S j`, and two indices `i k : Fin n`, derive `CondIndepFun (fun ω => Xprime ω i) (fun ω => Xstar ω k) ⟨Z', U'⟩ ν`. Proof: two `ZhangYeung.condIndepFun_comp` applications, one on each measured side, with `measurable_pi_apply i` and `measurable_pi_apply k`. ≤ 10 lines. Commit: `feat(theorem5): prove pairwise projection of tuple-level CondIndepFun`.

1. **Land `mutualInfo_add_n_way_inequality`.** The $n$-ary chain-rule MI domination. Statement:

    ```lean
    private lemma mutualInfo_add_n_way_inequality
        {Ω : Type*} [MeasurableSpace Ω]
        {n : ℕ} {α : Type*} {β : Fin n → Type*}
        [Finite α] [∀ k, Finite (β k)]
        [MeasurableSpace α] [∀ k, MeasurableSpace (β k)]
        [MeasurableSingletonClass α] [∀ k, MeasurableSingletonClass (β k)]
        {A : Ω → α} {B : ∀ k : Fin n, Ω → β k}
        (hA : Measurable A) (hB : ∀ k, Measurable (B k))
        (μ : Measure Ω) [IsProbabilityMeasure μ] :
        ∑ k, I[A : B k ; μ]
          ≤ I[A : (fun ω => fun k : Fin n => B k ω) ; μ]
            + ∑ k, H[B k ; μ]
            - H[(fun ω => fun k : Fin n => B k ω) ; μ]
    ```

    Proof plan: rewrite the inequality as `H[⟨B 0, ..., B (n-1)⟩ | A ; μ] ≤ ∑ k, H[B k | A ; μ]` (iterated conditional subadditivity), then prove by induction on `n`. The base case `n = 0` is `H[0 | A ; μ] = 0 ≤ 0`; the base case `n = 1` is reflexive; the inductive step uses `entropy_triple_add_entropy_le` once. The bootstrapped dependency audit did not reveal a ready-made `n`-ary `pi` / `Finset` entropy bound, so this local induction is the primary plan, not a fallback. Budget ~40 lines, split across ~3 private helper lemmas if the induction proof proves fragile (follow the split-before-bump guideline). Commit: `feat(theorem5): prove n-ary MI chain-rule domination`.

1. **Land `theorem5_integer` as a private theorem.** The main Shannon chase, stated in the natural internal `(Z, U)` order that matches `delta` and the copy-lemma transport steps. Follow the six-step body sketched in §6 above. All helper lemmas already in place; this file is linear. Budget ~60 tactic lines. Commit: `feat(theorem5): prove integer form of Theorem 5 via n-fold copy-lemma chase`.

1. **Land `theorem5` as a public theorem.** Thin wrapper rescaling the integer form and rewriting back to the paper's `I[U : Z]` order via `mutualInfo_comm` / `condMutualInfo_comm`. ≤ 10 lines. Commit: `feat(theorem5): state Theorem 5 in the paper form (eq. 27)`.

1. **Land `theorem5_averaged` as a public theorem.** Average `theorem5` over `i : Fin n` via `Finset.sum_le_sum`. ≤ 20 lines. Commit: `feat(theorem5): derive the averaged symmetric form (eq. 28)`.

1. **Expand `ZhangYeungTest/Theorem5.lean`.** Sequence step 3 landed the signature-pinning `example`s; expand with:
    - **Base-case compatibility.** The `n = 2` specialization `example` from §5 above: pin that `theorem5` at `n = 2`, `i = 0` with the `Fin 2`-indexed family `![X₁, X₂]` entails the integer form of Theorem 3. Closing proof: one `linarith` combined with a pi-to-prod `entropy_comp_of_injective` for the $H(X_{1}, X_{2})$ entropy-tuple term.
    - **Assumption-level specialization smoke test.** Add an API-level example, in the style of `ZhangYeungTest/Theorem3.lean`, that specializes `theorem5` under simple entropy / mutual-information hypotheses and checks that the public theorem rewrites to the expected bound without constructing an explicit independence witness.
    - **Averaged form from the point form.** Derive `theorem5_averaged` at a concrete `n = 3` from three applications of `theorem5` at `i = 0, 1, 2`, confirming that the averaging step is mechanically recoverable from the public surface.

    Commit: `test: cover Theorem 5 API surface`.

1. **Update `AGENTS.md` / `CLAUDE.md`.** Two new Module Layout lines (one each for `ZhangYeung/Theorem5.lean` and `ZhangYeungTest/Theorem5.lean`). Update the `ZhangYeung/Prelude.lean` entry to note the three promoted public helpers. Commit: `docs: document Theorem 5 module in CLAUDE.md`.

1. **Run `make check`.** Address any remaining lint or build issues; update `cspell-words.txt` with any new tokens introduced in docstrings. Commit any cspell/lint adjustments as `chore: address lint feedback`.

1. **Open the PR.** Title: `feat: prove Theorem 5, the n+2-variable Zhang-Yeung generalization`. Body links this plan and the roadmap, summarizes `theorem5` and `theorem5_averaged`, and calls out the prerequisite helper promotions (`mutualInfo_add_three_way_identity`, `mutualInfo_le_of_condIndepFun`, `IdentDistrib.condMutualInfo_eq`). Note the base-case compatibility `example` as the core correctness check.

If `theorem5_integer`'s body (step 7) sprawls past 100 lines without closing, halt and reconsider: either split the chase into per-step sub-lemmas (one for "pairwise delta inequality over the copy law", one for "marginal-equality transports", one for "n-ary MI chain-rule step + data processing"), or rescope `mutualInfo_add_n_way_inequality` to take a weaker hypothesis signature that matches what the chase actually supplies. Recap the precedent: M3's `zhangYeung_integer` landed at 45 lines; M5's chase has $O(n)$ more bookkeeping but the same fundamental structure.

## Open questions and known risks

### 7.1 Proof-reconstruction is the core risk (moderate-high)

The paper omits Theorem 5's proof. The chase above (§6) is a reconstruction via the "direct n-tuple copy + pairwise Lemma 2 + n-ary chain rule" strategy, not a transcription from the paper. Three places where the reconstruction could fail:

1. **The `condIndep_copies` tuple specialization.** PFR's `condIndep_copies` is stated at a single pair `(X : Ω → α, Y : Ω → β)` with `[Countable β]` and `[FiniteRange Y]`. In M5 the copied variable is the tuple `Xtuple : Ω → ∀ j : Fin n, S j`, while the conditioned variable is `fun ω => (Z ω, U ω) : Ω → S_Z × S_U`; the countability and measurable-singleton obligations therefore sit on `S_Z × S_U`, not on the tuple codomain. `FiniteRange (fun ω => (Z ω, U ω))` is automatic from the finite codomain. **Risk:** the tuple-valued copy's `Xprime, Xstar : Ω' → (∀ j, S j)` may still elaborate awkwardly against PFR's `⟨X₁, X₂, Y'⟩` convention. **Mitigation:** rehearse the `condIndep_copies` specialization at step 1 of the sequencing (pre-flight check); if the elaboration is fragile, wrap the tuple codomain with a one-line `let` binding and cast as needed.
1. **The pairwise vanishing-CMI step.** `I[X' i : X* k | ⟨Z', U'⟩ ; ν] = 0` follows from the tuple-level `CondIndepFun Xprime Xstar VZU ν` by projecting each side via `condIndepFun_comp` with `measurable_pi_apply i` (resp. `measurable_pi_apply k`). Because the copy is constructed over `(Z, U)` from the start, no `(U', Z')` to `(Z', U')` repacking lemma is needed. **Mitigation:** keep the entire chase in `(Z, U)` order internally and rewrite back to the paper's `(U, Z)` order only at the public theorem boundary.
1. **The $n$-ary chain-rule MI domination.** Statement is elementary (iterated conditional subadditivity), but the inductive proof over `n : ℕ` with a `Fin n`-indexed family adds bookkeeping. **Mitigation:** if the `Fin n` induction is fragile, prove a `List`-indexed version first (easier induction) and convert via `Fin n → List` at the use site.

**Escalation plan:** if any of these three sub-problems proves much harder than §6 anticipates, halt and write an addendum to this plan articulating the new understanding; do not chip at the chase with `simp; sorry` bypasses.

### 7.2 Universe bookkeeping (carried over from M2/M3/M4)

`condIndep_copies` binds its codomains at a single universe $u$. M5's tuple codomain `∀ j : Fin n, S j` picks up a single universe from the family `S : Fin n → Type u`, so `theorem5` binds `S_U, S_Z, S j : Type u` at the same universe. This is consistent with `entropyFn_n` (EntropyRegion.lean:50-55) and with M3's `zhangYeung` / M4's Theorem 4 surface. No new constraints beyond what is already documented.

**Mitigation:** none; universe constraint is expected.

### 7.3 Generic helper promotion mechanics (low)

`mutualInfo_add_three_way_identity` and `mutualInfo_le_of_condIndepFun` are both `private` in `ZhangYeung/Theorem3.lean:65-104`. `IdentDistrib.condMutualInfo_eq` is `private` in `ZhangYeung/CopyLemma.lean:63-96`. M5 consumes all three: the first for the generalized $n$-way chain-rule identity (specialized to $n = 2$ for the inductive step of `mutualInfo_add_n_way_inequality`), the second for the data-processing step (step 5 of the chase), and the third for the delta-transport step (step 3 of the chase). Promote all three to `ZhangYeung/Prelude.lean` in sequencing step 2 following the same pattern used for `condIndepFun_comp` in M3. All three are generic (no Zhang-Yeung-specific content), and all three are good Mathlib-upstream candidates in follow-up work.

**Mitigation:** before sequencing step 2, confirm the existing call sites are exactly the two uses inside `zhangYeung_integer` plus the local uses inside `CopyLemma` (grep: `grep -rn "mutualInfo_add_three_way_identity\|mutualInfo_le_of_condIndepFun\|IdentDistrib\.condMutualInfo_eq" ZhangYeung/ ZhangYeungTest/`). If an unexpected second downstream module already depends on any of them, reroute that module in the same commit.

### 7.4 Iterated conditional subadditivity (moderate)

The $n$-ary chain-rule identity at step 6 of the chase reduces to

$$
H(\langle B_{1}, \ldots, B_{n}\rangle \mid A) \le \sum_{k=1}^{n} H(B_{k} \mid A).
$$

This is **iterated conditional subadditivity**. The base case `n = 2` is `entropy_triple_add_entropy_le` (PFR Basic.lean:1117), and the inductive step chains the pair `(B_{1}, \langle B_{2}, \ldots, B_{n}\rangle)`. The bootstrapped dependency grep did not reveal any ready-made `n`-ary `pi` / `Finset` conditional-entropy bound under a usable name.

**Confirmed dependency state (§6.1, sequencing step 1):**

```bash
grep -rn "entropy.*pi.*le_sum\|cond_entropy.*le_sum\|sum_cond_entropy\|entropy_iSup\|entropy_finset" \
  .lake/packages/PFR/ .lake/packages/mathlib/Mathlib/Probability/
```

No usable lemma was found, so `mutualInfo_add_n_way_inequality` should be built locally via `Fin.induction` / `Nat.rec` over $n$. Budget the local build at 40 lines split across ~3 helpers.

**Mitigation:** if the `Fin n` induction is awkward, prove first a `List`-indexed version on a `List (Ω → β_k)`, which admits a clean `List.rec` proof, and convert via `List.ofFn X` at the use site.

### 7.5 `IdentDistrib` transport at tuple codomain (low-moderate)

The closing marginal equality `T(X^{*}_{1}, \ldots, X^{*}_{n}) = T(X_{1}, \ldots, X_{n})` needs the tuple-level `IdentDistrib`:

$$
(X^{*}_{1}, \ldots, X^{*}_{n}, Z', U') \;\sim\; (X_{1}, \ldots, X_{n}, Z, U).
$$

This is exactly what `hIdent₂` from `condIndep_copies` provides, modulo the pi-to-prod encoding at the tuple entropy boundary. The entropy transport `H[⟨X^{*}_{1}, \ldots, X^{*}_{n}\rangle ; \nu] = H[\langle X_{1}, \ldots, X_{n}\rangle ; \mu]` should route through `IdentDistrib.comp` plus PFR's existing `IdentDistrib.entropy_congr`; the single-coordinate entropy transports are coordinate projections of the same tuple-level `IdentDistrib`.

**Risk:** the fragile part is not a missing entropy lemma, but the measurable projection shape needed to feed `IdentDistrib.comp` at the tuple codomain. Confirm the exact projection terms in the §6.1 pre-flight audit.

**Mitigation:** if the tuple projection shape proves awkward, add a small local measurable projection helper; do not introduce a new generic entropy-transport lemma unless the bootstrapped API turns out to be insufficient in practice.

### 7.6 Heartbeat budget for `theorem5_integer` (low-moderate)

The chase has $O(n)$ intermediate facts, each tagged to a `∑` over `Fin n`. The default heartbeat budget is comfortable for M3's 7-term `linarith`, but M5's closing `linarith` may be $3n + 4$ terms. **Apply the split-before-bump guideline:** extract the "sum of pairwise delta inequalities" step, the "sum over `Fin n` collapses to the target LHS coefficients" arithmetic, and the "chain-rule + DP + marginal transport" step as three separate `have` statements, each closed by a bounded `linarith` on a constant-size family of facts. Do not raise `maxHeartbeats` as a shortcut.

**Mitigation:** if the closing `linarith` still exceeds budget after splitting, lift the $\sum$-over-`Fin n` arithmetic into its own private arithmetic lemma `sum_delta_eq_n_times_mutualInfo_minus` (no measure-theoretic content, pure `Finset.sum_*` algebra), then the closing `linarith` is on a fixed constant-size family.

### 7.7 `hn : 2 ≤ n` vs. degenerate `n = 0, 1` (low)

The paper requires $n \ge 2$. For $n = 0$ the statement is vacuous (empty sums, and `H[⟨⟩ ; μ] = 0`). For $n = 1$ the statement is Shannon-implied: `I(U;Z) - I(U;Z|X_{1}) - I(U;Z|X_{1}) = I(U;Z) - 2 I(U;Z|X_{1}) ≤ I(X_{1}; UZ) + H(X_{1}) - H(X_{1}) = I(X_{1}; UZ)`, which follows from `mutualInfo_le_entropy`.

**Option A (cleaner):** keep `hn : 2 ≤ n` as a hypothesis on `theorem5`. The chase works for all $n ≥ 0$, but the paper's statement is for $n ≥ 2$, and keeping the hypothesis flags degenerate specializations for callers.

**Option B:** drop `hn`. The chase proves the statement for all $n ≥ 0$ as long as the copy-lemma invocation does not have an implicit nonnegativity assumption. Quick check: `condIndep_copies` is fine at `n = 0` (the tuple `∀ k : Fin 0, S k` is the unit type), and the `Finset.sum` over `Fin 0` is zero. So the chase should go through. **Caveat:** the averaged form (28) divides by `n`, which is zero at `n = 0` and 1 at `n = 1`; the `n = 0` averaged form needs a separate `if 0 < n` guard.

**Decision:** go with Option A (keep `hn`). Simpler, matches the paper, avoids the averaged-form division-by-zero question.

**Mitigation:** if a downstream milestone needs `theorem5` at `n = 1`, prove a thin wrapper there; do not lift M5's statement.

### 7.8 PFR API churn (low, documented)

Same as M2-M4. Treat PFR as a permanent pinned dependency; log any API drift encountered in M5 for a subsequent pin bump.

## Verification

Per the roadmap M5 checkpoint: `theorem theorem5 ... : n * I[U : Z ; μ] - ∑ j, I[U : Z | X j ; μ] - n * I[U : Z | X i ; μ] ≤ I[X i : ⟨U, Z⟩ ; μ] + ∑ j, H[X j ; μ] - H[(fun ω => fun j => X j ω) ; μ]` with all hypotheses explicit; averaged variant `theorem5_averaged` (paper eq. 28) follows mechanically, and the Theorem 5 test module builds.

Operationally:

- `lake build ZhangYeung.Theorem5` compiles with no warnings, no `sorry`, no `admit`.
- `lake build ZhangYeung` compiles with `ZhangYeung.lean` re-exporting `ZhangYeung.Theorem5` cleanly.
- `lake build ZhangYeungTest.Theorem5` compiles; the test module imports only `ZhangYeung` and not `ZhangYeung.Theorem5` directly, exercising the public API surface.
- `lake build` and `lake test` both succeed on the default targets; CI goes green.
- `lake lint` passes.
- `make check` passes in full.

**Test module contents** (`ZhangYeungTest/Theorem5.lean`, established incrementally in sequencing steps 3 and 10):

1. Signature-pinning `example` for each of the two public theorems (`theorem5`, `theorem5_averaged`). Three `example`s total (including the base-case compatibility one).
1. Base-case compatibility `example` per §5 above: Theorem 5 at `n = 2, i = 0` recovers the integer form of Theorem 3 (the shape `delta_form21_iff` converts between), after the expected `mutualInfo_comm` / `condMutualInfo_comm` rewrites. This is a cross-check that the headline statement specializes cleanly.
1. Assumption-level specialization smoke test at `n = 3`, in the style of `ZhangYeungTest/Theorem3.lean`: specialize `theorem5` under simple entropy / mutual-information hypotheses and check that the public theorem rewrites to the expected bound without constructing an explicit independence witness.
1. Averaged-form-from-point-form `example` at `n = 3`: derive the averaged form (28) from three applications of the point form (27) plus `Finset.sum_le_sum`. Confirms `theorem5_averaged`'s proof route is reconstructible from the public surface alone.

Each `example` lives inside `namespace ZhangYeungTest` with `open ZhangYeung`, following `ZhangYeungTest/Delta.lean`, `ZhangYeungTest/Theorem2.lean`, `ZhangYeungTest/CopyLemma.lean`, `ZhangYeungTest/Theorem3.lean`, and `ZhangYeungTest/Theorem4.lean`.

Land these in the same commits as the corresponding public surface (signatures in step 3, integer form in step 7, public theorems in steps 8-9, smoke + base-case + averaged-form tests in step 10, same branch), so `lake test` exercises the public API continuously through the milestone.

**Out-of-scope for M5** (documented here so follow-up milestones can pick them up):

- No exact-equality form (paper does not state Theorem 5 as an equality, and no analogue to $R(X, Y, Z, U, X_{1}, Y_{1})$ is derived).
- No upstreaming of `mutualInfo_add_n_way_inequality` or the three promoted generic helpers to Mathlib. All four are good candidates; defer to roadmap §9 extensions.
- No n+2-variable set-function bridge (no Theorem 4 analogue at $n \ge 4$ for Theorem 5; the existing `theorem4_ge_four` already handles the four-variable-witness embedding at higher $n$).
- No refined witness constructions (paper's Section V examples are scope of Theorem 6, roadmap §9).

## Critical files

**This milestone:**

- `ZhangYeung/Theorem5.lean` (new).
- `ZhangYeungTest/Theorem5.lean` (new).
- `ZhangYeung/Prelude.lean` (modified: add `mutualInfo_add_three_way_identity`, `mutualInfo_le_of_condIndepFun`, and `IdentDistrib.condMutualInfo_eq` promoted from `Theorem3.lean` / `CopyLemma.lean`).
- `ZhangYeung/CopyLemma.lean` (modified: drop the private `IdentDistrib.condMutualInfo_eq` helper; reroute local call sites to the promoted public name).
- `ZhangYeung/Theorem3.lean` (modified: drop the two private helpers; reroute the two `zhangYeung_integer` call sites to the promoted public names; update the "Implementation notes" docstring).
- `ZhangYeung.lean` (modified, add one `import` line).
- `ZhangYeungTest.lean` (modified, add one `import` line).
- `AGENTS.md` / `CLAUDE.md` (modified, two-line addition under "Module Layout"; note on the helper promotions into `Prelude`).

**Read-only references:**

- `ZhangYeung/Delta.lean` (M1 output).
- `ZhangYeung/Theorem2.lean` (M1.5 output; style precedent for Shannon-algebra identities).
- `ZhangYeung/Theorem3.lean` (M3 output; structural precedent for the Shannon chase and the two helper promotions).
- `ZhangYeung/Theorem4.lean` / `ZhangYeung/EntropyRegion.lean` (M4 outputs; structural precedent for the heterogeneous `Fin n`-family conventions, `entropyFn_n`, pi-type codomain instances).
- `references/transcriptions/zhangyeung1998.md` (paper transcription; Theorem 5 statement on lines 388-408; Theorem 3 proof on lines 680-709 as structural reference).
- `.lake/packages/PFR/PFR/ForMathlib/Entropy/Basic.lean` (all Shannon primitives).
- `.lake/packages/PFR/PFR/ForMathlib/ConditionalIndependence.lean` (`CondIndepFun` at line 105; `condIndep_copies` at line 135).
- `.lake/packages/mathlib/Mathlib/Probability/IdentDistrib.lean` (`IdentDistrib`, `IdentDistrib.comp`, `IdentDistrib.symm`).
- `.lake/packages/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Pi.lean` (pi-type measurable-space instances).
- `docs/plans/done/2026-04-17-copy-lemma.md`, `docs/plans/done/2026-04-18-theorem-3-zhang-yeung-inequality.md`, `docs/plans/done/2026-04-18-theorem-4-shannon-incompleteness.md` (prior milestone plans; source of the style precedent for this plan).

Reference: the `write-lean-code` skill is authoritative for Lean naming and proof style; the `write-math` skill governs the module docstring and any mathematical prose inside comments; the `write-pandoc-markdown` skill governs this plan document; the `write-formalization-roadmap` skill governs the roadmap update if M5 closing requires one (it likely does not -- Theorem 5 was already scoped into the roadmap as a stretch milestone).
