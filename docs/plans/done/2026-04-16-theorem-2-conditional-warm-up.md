---
title: "M1.5: Theorem 2 (Zhang-Yeung 1997 conditional inequality via KL divergence)"
created: 2026-04-16
updated: 2026-04-17
branch: formalize/1.5-theorem-2
roadmap: docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md
milestone: M1.5
depends_on: M1 (`ZhangYeung/Delta.lean`, merged into `main` via PR #4)
---

## Status (2026-04-17): complete; all three KL sorries closed

This section supersedes the original single-copy-construction plan; see "Historical context (pre-pivot design)" at the bottom of the document for the pre-pivot design.

### What landed

The implementation in `ZhangYeung/Theorem2.lean` follows the [@zhangyeung1997, Theorem 3] auxiliary-PMF + KL-divergence argument, not the single-copy kernel construction the original plan was written around. **M1.5 is complete: `theorem2` has no `sorry`, the full `make check` (build + lint + tests) is green.**

The Shannon-algebra reduction `theorem2_shannon_identity` (target ⟺ `Δ(Z, U | X, Y) ≤ 0` under (16)) is closed. The `theorem2_delta_le_zero` assembly is wired end-to-end around `Real.sum_mul_log_div_leq` (the log-sum inequality), with the absolute-continuity side condition discharged inline via marginal-bound lemmas.

All three KL sorries from the original plan are closed:

- **`ptilde_sum_eq_one`** via a direct fibrewise computation (uses `ptilde_fibre_sum`).
- **`phat_sum_eq_one`** via the 4-step telescope (`∑_z` via CondIndep product, `∑_y, ∑_x` via marginal identities, `∑_u` via the probability-measure property). New helpers: `condIndepFun_map_triple_real_singleton` and `condIndep_normalized_pair_eq_triple`.
- **`sum_joint_eq_sum_ptilde`** via 11 applications of `sum_mul_proj_eq_of_marginal_eq`, factored through `marg_swap_helper`. Pointwise log decomposition proved on the support of `p̃` with positivity propagation from triple marginals.
- **`delta_eq_sum_log_ratio`** via `entropy_eq_sum_joint` (new helper) lifting each of the eleven signed entropy terms to a 4-tuple weighted sum, followed by `sub_eq_add_neg` + `← Finset.sum_add_distrib` + `← Finset.sum_neg_distrib` to combine into a single `Finset.sum`, then `ring` on the pointwise residual.

Eleven marginal-match helpers for `p̃` (covering the eleven factors of `p̂/p̃`), eight generic Fintype utilities (marginal summation for pairs and triples, marginal bounds, the `IndepFun` product formula, the fibrewise-swap helper `sum_mul_proj_eq_of_marginal_eq`, the pushforward-fibre-sum helper `sum_filter_map_real_eq_map_comp`), and the module-level variable block are all landed.

### What remains

Nothing in the M1.5 scope. Follow-up:

- Push the branch and open the PR (title "feat: prove Theorem 2 (Zhang-Yeung 1997 conditional inequality)").
- M2 copy-construction helpers (see "Out of scope: M2 copy-construction helpers" below) are a separate task.

### Reframing: Theorem 2 is not a warm-up

The original plan framed M1.5 as "a warm-up for the unconditional result (M3, Theorem 3)" exercising "the same kernel-composition and identical-distribution bookkeeping." Three subsequent findings undercut this framing:

1. **Paper structure.** Theorem 2 is stated in the 1998 paper's introduction (Section I, eqs. 16-17), cites [@zhangyeung1997] for the proof, and is never invoked in the proofs of Theorems 3, 4, 5, or 6. It functions as historical context motivating Conjecture 1 (the closure separation `\bar{Γ}_n^* ≠ Γ_n`), which Theorem 3 answers independently via the copy-lemma construction in §III. Nothing downstream on the roadmap depends on M1.5 as a mathematical prerequisite; removing M1.5 would break no subsequent milestone.
2. **Kaced-Romashchenko (arXiv:1207.5742, IEEE TIT 2013).** This paper is the most careful published post-1997 treatment of the inequality. It classifies Theorem 2 as (ℐ1) in a family of essentially conditional inequalities. Theorem 3 + Claim 1 (loc. cit.) prove (ℐ1) is essentially conditional: no Lagrange combination `λ₁ I(A;B|C) + λ₂ I(A;B)` of the premises added to any unconditional Shannon-type inequality produces (ℐ1). Theorem 5 shows (ℐ1) fails on the closure `\bar{Γ}₄*` of the entropic region. Operational consequence: no pure copy-lemma + Shannon-chase argument can derive (ℐ1) purely from Shannon-type primitives. The 1997 KL route is effectively the only known route.
3. **Previous in-branch evidence.** Commit `249da6d` landed the structural work for the original Candidate A via PFR's `condIndep_copies` (which, unanticipated by §7.1 of the pre-pivot plan, sidesteps `StandardBorelSpace` entirely). The Shannon chase closing (16) ⇒ (17) from the three auxiliary facts was never attempted; the subsequent commit `b3ab851` pivoted to the KL route before attempting it, describing the copy construction as "dead code for the closing chase." Kaced-Romashchenko confirm that this chase cannot close at all.

Taken together, M1.5 is a **standalone formalization** of the first known non-Shannon-type conditional information inequality, with independent value as (a) the first formalization of any non-Shannon-type information inequality in any proof assistant (per the 2026-04-17 literature survey: none exists in Lean, Rocq/infotheo, Isabelle/HOL, HOL Light, or Mizar), and (b) insurance against M3 / Theorem 3 taking longer to land than budgeted. It is *not* a warm-up for M2's copy lemma; the copy-construction machinery M2 needs is disjoint from the KL machinery that discharges (16) ⇒ (17).

### Plan from here

All four steps below are done:

1. ✓ The three KL sorries are closed. Routes documented in "Finishing plan" below match what actually landed.
2. ✓ `Theorem2.lean`'s module docstring carries the standalone framing and the linking note to the 1998 copy construction.
3. ✓ `make check` passes (build + lint + test).
4. Remaining: push the branch and land via PR framed as a standalone result, not as a warm-up.

M2 copy-construction infrastructure is valuable, still wanted, and orthogonal; see "Out of scope: M2 copy-construction helpers" for the follow-up task.

## Finishing plan: close three KL sorries

### `phat_sum_eq_one`

**Claim.** `∑ t : S₁ × S₂ × S₃ × S₄, phat X Y Z U μ t = 1`, under `I[X:Y;μ] = 0` and `I[X:Y|Z;μ] = 0`.

**Route.** The 1997 paper's computation (p. 1986). Unfold `p̂`, collapse denominator factors pairwise using the two hypotheses, telescope the 4-tuple sum.

Symbolically, on the support `{p(z) > 0, p(u) > 0, p(x) > 0, p(y) > 0}`:

```text
p̂(x, y, z, u) = p(x,z) p(x,u) p(y,z) p(y,u) / [p(z) p(u) p(x) p(y)]
              = [p(x,z) p(y,z) / p(z)] · p(x,u) p(y,u) / [p(u) p(x) p(y)]
              = p(x,y,z) · p(x,u) p(y,u) / [p(u) p(x) p(y)]         (h₂: CondIndepFun ⇒ p(x,y,z) = p(x,z) p(y,z) / p(z))
              = p(x,y,z) · p(x,u) p(y,u) / [p(u) p(x,y)]            (h₁: IndepFun   ⇒ p(x,y) = p(x) p(y))
```

Then telescope:

- `∑_z p̂(x, y, z, u) = p(x,y) · p(x,u) p(y,u) / [p(u) p(x,y)] = p(x,u) p(y,u) / p(u)` via `∑_z p(x,y,z) = p(x,y)`.
- `∑_y p(x,u) p(y,u) / p(u) = p(x,u) · (∑_y p(y,u)) / p(u) = p(x,u) · p(u) / p(u) = p(x,u)`.
- `∑_x p(x,u) = p(u)`.
- `∑_u p(u) = 1`.

**Helpers to add.**

- **`condIndepFun_map_triple_real_singleton`** (new, generic): the conditional analogue of the existing `indepFun_map_pair_real_singleton`. Given `CondIndepFun f g h μ` with `μ` a probability measure and `(μ.map h).real {c} ≠ 0`:

  ```text
  (μ.map ⟨f, g, h⟩).real {(a, b, c)} · (μ.map h).real {c}
    = (μ.map ⟨f, h⟩).real {(a, c)} · (μ.map ⟨g, h⟩).real {(b, c)}
  ```

  Proof sketch: unfold `CondIndepFun` to get fiberwise `IndepFun f g (μ[|h ← c])`, apply `IndepFun.measure_inter_preimage_eq_mul` on the fiber, and multiply by `(μ.map h).real {c}` to return to unconditional measures. PFR may expose a more direct route; grep `ForMathlib/ConditionalIndependence.lean` for `CondIndepFun.prod_singleton` or related before writing fresh.
- **Support-split bookkeeping.** Follow the `ptilde_sum_eq_one` pattern: `by_cases` on the denominator factor; close the zero-measure branch via the already-landed marginal-bound lemmas (`measureReal_map_pair_le_map_fst`, `measureReal_map_triple_le_map_pair_12` etc.), which force the numerator to vanish when a denominator factor does.

**Sequencing.** Land `condIndepFun_map_triple_real_singleton` first as a standalone helper in the "Generic finite-alphabet utilities" section. Then close `phat_sum_eq_one` by unfolding `phat`, applying the new helper + `indepFun_map_pair_real_singleton`, and telescoping the 4-tuple sum.

### `delta_eq_sum_log_ratio`

**Claim.** `delta Z U X Y μ = ∑ t, pJoint(t) · log (phat(t) / ptilde(t))`.

**Route.** Expand the three mutual-information terms in `delta` via entropy:

- `I[Z:U ; μ] = H[Z] + H[U] - H[⟨Z, U⟩]`
- `I[Z:U | X ; μ] = H[⟨Z, X⟩] + H[⟨U, X⟩] - H[⟨⟨Z, U⟩, X⟩] - H[X]`
- `I[Z:U | Y ; μ] = H[⟨Z, Y⟩] + H[⟨U, Y⟩] - H[⟨⟨Z, U⟩, Y⟩] - H[Y]`

So

```text
delta = H[Z] + H[U] + H[⟨⟨Z,U⟩, X⟩] + H[⟨⟨Z,U⟩, Y⟩] + H[X] + H[Y]
      − H[⟨Z, U⟩] − H[⟨Z, X⟩] − H[⟨U, X⟩] − H[⟨Z, Y⟩] − H[⟨U, Y⟩]
```

Each `H[f ; μ]` where `f` is a projection of `⟨X, Y, Z, U⟩` rewrites as `−∑_{(x,y,z,u)} p(x, y, z, u) · log p_f(f(x, y, z, u))` by the "lift to 4-tuple" identity `∑_a p_f(a) log p_f(a) = ∑_t p(t) log p_f(f(t))`, which follows from `Finset.sum_fiberwise` and the marginal-summation helpers already landed.

Combining the eleven log contributions:

```text
delta = ∑_{(x,y,z,u)} p(x,y,z,u) · log [ p(x,z) p(x,u) p(y,z) p(y,u) p(z,u)
                                        / (p(z) p(u) p(x) p(y) p(x,z,u) p(y,z,u)) ]
      = ∑_{(x,y,z,u)} p(x,y,z,u) · log (p̂(x,y,z,u) / p̃(x,y,z,u))
```

**Helpers to add.**

- **`entropy_eq_sum_joint_log_marg`** (new, generic, or grep for PFR equivalent first): for measurable `f : Ω → α` and `π : α → β` with appropriate singleton-class side conditions, `H[π ∘ f ; μ] = −∑_a (μ.map f).real {a} · Real.log ((μ.map (π ∘ f)).real {π(a)})`. Generalizes PFR's `entropy_eq_sum_negMulLog` from a single-variable entropy to a "lift to a larger joint" form. PFR may already have this; `entropy_eq_sum`, `entropy_eq_sum_finset`, and `entropy_comp_of_injective` are the likely neighborhoods to check first.
- Care with `Real.log 0 = 0` / `Real.negMulLog 0 = 0` on zero-measure fibers.

**Sequencing.** Land `entropy_eq_sum_joint_log_marg` first. Instantiate it for each of the eleven entropy terms (ten distinct projections, since `H[⟨Z, X⟩]` and `H[⟨X, Z⟩]` etc. are handled via `entropy_comm` already). Combine via arithmetic. The combinatorial identification of the 11 factors with the log-ratio structure is mechanical once the lift lemma is in place.

### `sum_joint_eq_sum_ptilde`

**Claim.** `∑ t, pJoint(t) · log (phat(t) / ptilde(t)) = ∑ t, ptilde(t) · log (phat(t) / ptilde(t))`.

**Route.** Split `log(p̂/p̃)` into 11 additive contributions:

- **Positive:** `log p(x,z)`, `log p(x,u)`, `log p(y,z)`, `log p(y,u)`, `log p(z,u)`.
- **Negative:** `log p(z)`, `log p(u)`, `log p(x)`, `log p(y)`, `log p(x,z,u)`, `log p(y,z,u)`.

For each contribution, apply `sum_mul_proj_eq_of_marginal_eq` (already landed at `Theorem2.lean:388+`) with `f := pJoint`, `g := ptilde`, the appropriate projection (e.g., `(x,y,z,u) ↦ (x,z)` for the `p(x,z)` factor), and the appropriate log-of-marginal as `φ`. The hypothesis `h_marg` for each call is supplied by one of the eleven already-landed marginal-match lemmas (`sum_ptilde_over_y`, `sum_ptilde_over_y_u`, `sum_ptilde_over_y_z_u`, etc.).

**Helpers to add.** None beyond what's landed. Zero-measure handling piggybacks on Lean's `Real.log 0 = 0` convention plus the existing marginal-bound lemmas.

**Sequencing.** Write the 11 applications of `sum_mul_proj_eq_of_marginal_eq` in sequence, sum them, and reassemble the log via `Real.log_mul` / `Real.log_div` where denominators are nonzero (zero-denominator branches close trivially via the log-zero convention). Use `ring` or term-by-term combination to finalize.

## Docstring updates

### Add the linking note

Insert the following paragraph into the `## Implementation notes` section of `Theorem2.lean`'s module docstring, after the existing description of the KL-divergence argument:

> **Connection to the 1998 copy construction.** The auxiliary PMF `p̃(x, y, z, u) := p(x, z, u) p(y, z, u) / p(z, u)` defined above is precisely the `(X', Y₁, Z', U')`-marginal of the extended probability measure `ν` that PFR's `ProbabilityTheory.condIndep_copies`, applied to `⟨X, Y⟩` conditioned on `⟨Z, U⟩`, would produce. Projecting the copy: set `X' := Prod.fst ∘ W₁`, `Y₁ := Prod.snd ∘ W₂`, `⟨Z', U'⟩ := V`; then the conditional independence `X' ⟂ Y₁ | ⟨Z', U'⟩` plus the marginal identities `(X', Z', U') ∼ (X, Z, U)` and `(Y₁, Z', U') ∼ (Y, Z, U)` force `p_ν(x, y, z, u) = p(x, z, u) p(y, z, u) / p(z, u) = p̃(x, y, z, u)`. So the 1997 KL proof and the 1998 two-copy copy-lemma framework reach the same object from two directions: the 1997 paper constructs `p̃` as a PMF and closes via `Real.sum_mul_log_div_leq`; the 1998 paper (Lemma 2 in §III, eq. 44-45) constructs `ν` via kernel composition and closes Theorem 3 (the unconditional inequality) via a Shannon chase on the copy joint. For Theorem 2 specifically, a pure copy + Shannon-chase close is ruled out: Kaced and Romashchenko (arXiv:1207.5742, Theorem 3 + Claim 1, Theorem 5) show this inequality is essentially conditional and fails on the closure of the entropic region, so no combination of basic Shannon inequalities plus Lagrange multiples of the premises can derive it. This module follows the 1997 KL route rather than attempting the copy-construction framing.

### Reframe the module docstring opening

Replace the current "single-auxiliary-distribution warm-up for the two-copy construction" framing (around the second paragraph of the module docstring) with a standalone-result framing. Draft:

> This module formalizes the implication (16) ⇒ (17) on finite-alphabet random variables. It is a standalone formalization of the first known non-Shannon-type conditional information inequality, originally proved in [@zhangyeung1997, Theorem 3]. Kaced and Romashchenko classify it as (ℐ1) in their family of essentially conditional inequalities ([@kaced2013]): it holds on the set `Γ₄*` of constructible entropy functions but fails on its closure `\bar{Γ}₄*` (loc. cit., Theorem 5), so it is not derivable from the basic Shannon inequalities under any Lagrange combination of the hypotheses.

### Update tags

Append `essentially conditional inequality` to the `## Tags` line.

### Add the Kaced-Romashchenko reference

Extend `## References` with an entry for `[@kaced2013]` matching the format of the existing `[@zhangyeung1997]` and `[@zhangyeung1998]` entries: Kaced and Romashchenko, *Conditional Information Inequalities for Entropic and Almost Entropic Points*, IEEE Transactions on Information Theory 59(11), 2013, pp. 7149-7167 (arXiv:1207.5742). The entry should note that they classify the inequality as $(\mathcal{I}_1)$ and prove its essential-conditionality (Theorem 3 + Claim 1) and failure on the closure of the entropic region (Theorem 5).

The BibTeX entry for `@kaced2013` is in `references/papers.bib`.

## Out of scope: M2 copy-construction helpers

The `condIndep_copies` invocation pattern, the `condIndepFun_comp` post-composition helper, projection measurability patterns, and `IdentDistrib` four-way-joint manipulation are valuable M2 prep but do not belong in `Theorem2.lean`'s KL proof. Commit `249da6d` landed most of this scaffolding before the pivot to KL; it is preserved in git history and directly recoverable.

**Proposed follow-up task** (out of scope for this PR): open a separate milestone (either labeled "M1.75 copy helpers" or folded into M2 prep) that lands `ZhangYeung/CopyHelpers.lean` with:

- `condIndepFun_comp` (`CondIndepFun` post-composition by measurable codomain functions).
- A templated invocation of `condIndep_copies` on a pair `⟨X, Y⟩` conditioned on a pair `⟨Z, U⟩`, producing the four-way joint `IdentDistrib` and the projected `CondIndepFun`.
- Projection measurability helpers for pair-valued random variables.

Plus a matching `ZhangYeungTest/CopyHelpers.lean` exercising the API. Scope and namespace are decided when that task opens. This module feeds M2 directly and does not depend on Theorem 2's proof route.

## Historical context (pre-pivot design, 2026-04-16)

The remainder of this document is the original pre-pivot M1.5 plan. It describes a single-copy kernel construction (Candidates A and B via `condDistrib` / `Kernel.comap`, plus an `aux_measure` / `aux_identDistrib` / `aux_condIndep` lemma skeleton) that the landed implementation does not follow. Specific guidance on what is still accurate versus superseded:

- **Accurate.** §Context (partial; see reframing in the 2026-04-17 status section above), §Paper equations this milestone formalizes, §Prerequisites, §Files, §Signature, and §Verification. The theorem statement, file layout, test layout, and `Fintype + MeasurableSingletonClass` codomain specialization all match the landed implementation.
- **Superseded.** §PFR and Mathlib API surface used (the landed proof uses `Real.sum_mul_log_div_leq` and PFR's entropy API, not kernel composition), §Design: the single-copy construction, and §Sequencing inside M1.5.
- **Superseded by empirical evidence.** §7.1 (StandardBorelSpace inference risk): PFR's `condIndep_copies` does not require `StandardBorelSpace` at the pin and is the right route for Fintype codomains; the §7.1 mitigation tree never had to be walked. §7.3 (conditional-MI `IdentDistrib` transport): not load-bearing for the KL route. §7.4 (picking the right single-copy construction): the Shannon chase for any single-copy construction is ruled out by Kaced-Romashchenko ([@kaced2013]); see the "Reframing" subsection of the 2026-04-17 status above.

## Context

**Primary reference:** `references/transcriptions/zhangyeung1998.md` (verified 2026-04-16); citation below uses equation numbers from that transcription.

Milestone M1.5 of the Zhang-Yeung roadmap (§6) formalizes the *conditional* information inequality that Zhang and Yeung originally proved in their 1997 paper [39] and restated as Theorem 2 of the 1998 paper. M1.5 is a warm-up for the unconditional result (M3, Theorem 3): it exercises the same kernel-composition and identical-distribution bookkeeping but with one auxiliary random variable instead of two, and on a materially simpler inequality. Landing M1.5 before M2 retires the riskiest open question on the M2 path, which is "can we discharge the measurability and identical-distribution side conditions of a PFR-style single-variable copy construction in our chosen Mathlib idiom?", without the two-copy product-kernel bookkeeping that M2 adds on top.

Theorem 2 states: for any four discrete random variables $X, Y, Z, U$,

$$
I(X ; Y) = I(X ; Y \mid Z) = 0 \qquad \text{(eq. 16)}
$$

implies

$$
I(X ; Y \mid Z, U) \;\le\; I(Z ; U \mid X, Y) + I(X ; Y \mid U). \qquad \text{(eq. 17)}
$$

The paper does not prove Theorem 2; it cites [39]. The proof is not Shannon-type under the given side conditions (if it were, the hypotheses could be dropped and Theorem 2 would already be a basic information inequality), and the 1997 paper discharges it via a single auxiliary variable. M1.5 reconstructs that argument in Lean.

The value of landing M1.5 before M2 is fourfold. First, it forces us to commit, early, to a Lean-level recipe for "copy $V$ given $W$ via the regular conditional distribution," decoupled from the two-copy product-kernel construction that M2 additionally requires. Second, it pins down the measurability and discrete-codomain side conditions we need for `condDistrib` before M2's measurability bill comes due. Third, it yields a Mathlib-idiomatic single-copy helper (inlined in `Theorem2.lean` for now; M2 may generalize it) that validates the kernel-composition approach. Fourth, Theorem 2 is a reusable inequality in its own right: any downstream derivation that assumes $I(X ; Y) = I(X ; Y \mid Z) = 0$ can cite it directly.

## Paper equations this milestone formalizes

Equation (16), the hypothesis:

$$
I(X ; Y) = I(X ; Y \mid Z) = 0.
$$

Equation (17), the conclusion:

$$
I(X ; Y \mid Z, U) \;\le\; I(Z ; U \mid X, Y) + I(X ; Y \mid U).
$$

M1.5 formalizes the implication (16) $\Rightarrow$ (17). It does **not** formalize Theorem 2's role as a stepping-stone to eq. (18), $\Gamma_n^\* \neq \Gamma_n$; that corollary is superseded by M4's direct counterexample to $\bar{\Gamma}_4^\* = \Gamma_4$.

## Prerequisites

M1 delivers (verified in the current worktree, which branches off `main` at `09cceee`):

- `ZhangYeung/Delta.lean` with the `delta` definition, equational lemmas, and the eq. (21)/(22)/(23) form-conversions.
- `ZhangYeungTest/Delta.lean` as the matching API regression suite.
- `lakefile.toml` with the `ZhangYeungTest` library wired as `testDriver` and `defaultTargets = ["ZhangYeung"]`.
- PFR pinned at `80daaf1`, Lean toolchain `leanprover/lean4:v4.28.0-rc1`.

Before starting M1.5 in this worktree, run `bin/bootstrap-worktree`; confirm `make check` (or `lake build ZhangYeung && lake lint && lake test`) passes on the tip of `formalize/1.5-theorem-2` before any Theorem 2 code lands.

The rest of this document assumes M1 is in. If it is not, stop and merge M1 first.

## PFR and Mathlib API surface used

All declarations live under `namespace ProbabilityTheory` unless noted.

**Entropy / information (PFR, `PFR.ForMathlib.Entropy.Basic`):**

- `mutualInfo`, notation `I[X : Y ; μ]`; `condMutualInfo`, notation `I[X : Y | Z ; μ]`.
- `mutualInfo_eq_zero` (`I[X : Y ; μ] = 0 ↔ IndepFun X Y μ`) with side conditions `[IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y]` and `hX : Measurable X`, `hY : Measurable Y`.
- `condMutualInfo_eq_zero` (`I[X : Y | Z ; μ] = 0 ↔ CondIndepFun X Y Z μ`) with side conditions `[IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z]` and analogous measurability.
- `chain_rule`, `entropy_submodular`, `entropy_triple_add_entropy_le`: the Shannon-type algebra M1.5's closing chase will lean on.
- `condMutualInfo_nonneg`, `mutualInfo_nonneg`: sign inputs for `linarith`.
- `IdentDistrib.entropy_congr`, `IdentDistrib.mutualInfo_eq`: transport entropy/mutualInfo across an `IdentDistrib` pair. The conditional-mutual-information analogue is confirmed absent at the pin; see "Risks" §7.3 for the two ways to proceed (default: avoid the transport and work directly on $\nu$).

**Kernel composition (Mathlib, `Mathlib.Probability.Kernel`):**

- `Kernel.compProd` / `κ ⊗ₖ η` (`Kernel α β → Kernel (α × β) γ → Kernel α (β × γ)`).
- `MeasureTheory.Measure.compProd` / `μ ⊗ₘ κ` (`Measure α → Kernel α β → Measure (α × β)`).
- `Measure.fst_compProd : (μ ⊗ₘ κ).map Prod.fst = μ` under `[SFinite μ] [IsMarkovKernel κ]`.
- `condDistrib : (Ω → β) → (Ω → α) → Measure Ω → Kernel α β` under `[IsFiniteMeasure μ]` and `[StandardBorelSpace β] [Nonempty β]` at use sites.
- `map_compProd_condDistrib : μ.map X ⊗ₘ condDistrib Y X μ = μ.map (fun ω ↦ (X ω, Y ω))` in `Mathlib.Probability.Kernel.Disintegration`. Note the name order: `map_compProd_condDistrib`, not `compProd_map_condDistrib`. A `condDistrib_comp_map`-style "second-marginal via `condDistrib` alone" lemma is not available under that name at the pin; if the chase needs it, derive from `map_compProd_condDistrib` + the analogous `Measure.snd_compProd`.
- `Kernel.comap` (pullback of a kernel along a measurable function) is available at the pin in `Mathlib.Probability.Kernel.Basic`; either `Kernel.comap κ π hπ` or composition with a deterministic kernel via `⊗ₘ` is a valid route to the $\Omega$-indexed kernel `κΩ` in the Candidate A sketch below.

**Identical distribution (Mathlib, `Mathlib.Probability.IdentDistrib`):**

- `IdentDistrib f g μ ν` with fields `aemeasurable_fst`, `aemeasurable_snd`, `map_eq : Measure.map f μ = Measure.map g ν`.
- `IdentDistrib.comp : IdentDistrib f g μ ν → Measurable u → IdentDistrib (u ∘ f) (u ∘ g) μ ν`.
- `IdentDistrib.symm`, `IdentDistrib.trans`.

**Conditional independence (Mathlib + PFR):**

- `IndepFun` (`Mathlib.Probability.Independence.Basic`), notation `X ⟂ᵢ[μ] Y`.
- `CondIndepFun` (`PFR.ForMathlib.ConditionalIndependence`): `CondIndepFun f g h μ ↔ ∀ᵐ z ∂(μ.map h), IndepFun f g (μ[|h ← z])`.

**Fintype glue (PFR + Mathlib):**

- `instance : FiniteRange X` when the codomain of `X` is `Finite` (PFR, `ForMathlib/FiniteRange/Defs`). Fintype codomains therefore discharge `FiniteRange` obligations automatically.
- Mathlib's `MeasurableSingletonClass` on Fintype codomains is typically inferred from the default discrete `MeasurableSpace`; add explicit instances only if instance search fails.
- The `StandardBorelSpace` requirement of `condDistrib` for Fintype codomains is the one open question this milestone must resolve (see "Risks" §7.1 below).

## Files

**Create** `ZhangYeung/Theorem2.lean`: the proof code for this milestone.

**Create** `ZhangYeungTest/Theorem2.lean`: the matching API regression tests.

**Modify** `ZhangYeung.lean` to re-export the new module:

```lean
import ZhangYeung.Delta
import ZhangYeung.Prelude
import ZhangYeung.Theorem2
```

**Modify** `ZhangYeungTest.lean` to pull in the new test module:

```lean
import ZhangYeungTest.Delta
import ZhangYeungTest.Theorem2
```

**Modify** `CLAUDE.md`: add a one-line entry under "Module Layout" pointing to `ZhangYeung/Theorem2.lean` and its test.

No changes to `ZhangYeung/Prelude.lean`, `ZhangYeung/Delta.lean`, or `lakefile.toml`. `Prelude.lean` already imports PFR's entropy API; the copy-construction uses Mathlib kernel APIs that transit through PFR's imports, so no additional import surface is required at the `Prelude.lean` level. Any new imports (`Mathlib.Probability.Kernel.CondDistrib`, `Mathlib.Probability.IdentDistrib`, PFR's `ConditionalIndependence`) belong in `Theorem2.lean`'s header, not in `Prelude.lean`, because they are used only here.

## Design: the single-copy construction

### What M1.5 must produce

The core technical content of Theorem 2 is an auxiliary random variable $W$ on an extended probability space, constructed from the original $(X, Y, Z, U)$, such that:

1. **Marginal equality.** The specific tuples that appear in the entropy expansions used in the chase have matching laws across the original and extended spaces. The plan should ask for exactly those tuple-level `IdentDistrib` facts, not for a vague "copy variable has the right marginal" surrogate.
1. **Conditional independence.** $W$ is conditionally independent of some subset of $\{X, Y, Z, U\}$ given another subset, in a way that translates (via `condMutualInfo_eq_zero`) into a zero conditional mutual information term usable inside the Shannon-inequality chase.

The chase that follows --- built from Shannon-type identities, `condMutualInfo_nonneg`, the two hypotheses `I[X : Y ; μ] = 0` and `I[X : Y | Z ; μ] = 0`, and the two facts above --- should discharge the target inequality (17) with `linarith` as the last tactic.

The paper does not spell out the construction; neither does the 1998 transcription. Two candidate constructions cover the natural single-copy degenerations of M3's two-copy $q(x, y, z, u, x_1, y_1) := p(x, y, z, u) \, p(x_1, y_1 \mid z, u)$. Pick one at the construction-selection step in the sequencing below; if the chase does not close under the chosen construction, fall back to the other.

### Candidate A: copy of $Y$ given $(Z, U)$

Define $q(x, y, z, u, y_1) := p(x, y, z, u) \, p(y_1 \mid z, u)$. Under $q$:

- **Marginal equality:** the $(Y_1, Z, U)$ marginal equals the $(Y, Z, U)$ marginal.
- **Conditional independence:** $Y_1 \perp (X, Y) \mid (Z, U)$; in particular $I(Y ; Y_1 \mid Z, U) = I(X ; Y_1 \mid Z, U) = 0$.

These are the immediate structural facts. They do **not** by themselves justify transporting arbitrary mixed terms involving both $X$ and $Y_1$ back to $\mu$; such terms should be handled directly on the auxiliary measure $\nu$, with `aux_condIndep` providing the key zero term.

Lean construction (sketch):

```lean
let π : Ω → S₃ × S₄ := fun ω => (Z ω, U ω)
let κ : Kernel (S₃ × S₄) S₂ := condDistrib Y π μ
-- Pull κ back along π. Two routes exist at the pin: `Kernel.comap κ π hπ`
-- (direct), or composing with a deterministic kernel via `⊗ₘ`. Pick whichever
-- makes the downstream aux_identDistrib lemma shorter.
let κΩ : Kernel Ω S₂ := Kernel.comap κ π (hZ.prodMk hU)
let ν : Measure (Ω × S₂) := μ ⊗ₘ κΩ
```

Advantages: with the pullback expressed via `Kernel.comap`, the needed first-marginal and copied-variable marginal identities come from `map_compProd_condDistrib`, `Measure.fst_compProd`, and `Kernel.comap` map lemmas. The pair measurability `hZ.prodMk hU` discharges the side condition on $\pi$.

Disadvantages: the target inequality (17) does not obviously dissolve after plugging the $Y_1$-based facts in. The chase requires at least one creative step beyond the identities that the construction immediately supplies.

### Candidate B: copy of $X$ given $(Z, U)$

Symmetric to Candidate A: $q(x, y, z, u, x_1) := p(x, y, z, u) \, p(x_1 \mid z, u)$. Gives $(X_1, Z, U)$ marginal equal to $(X, Z, U)$, and $X_1 \perp (X, Y) \mid (Z, U)$.

### Recommended first attempt

**Start with Candidate A.** It is the more natural degeneration of M3's $y_1$ half, and the Shannon chase that M3 runs after Lemma 2 already uses $I(X ; Y_1 \mid Z, U) = 0$ as an input; M1.5's chase can plausibly reuse part of that skeleton. If an honest attempt at the chase under Candidate A does not close the inequality, switch to Candidate B and document the reason in a commit message.

The plan **does not** lock in the specific sequence of Shannon-identity rewrites that closes the chase. That is genuinely a proof-time decision, and overspecifying it here would be wasted work if the chosen construction does not support the prescribed rewrite. Instead, the plan commits to the structural shape of the proof (single kernel composition + `IdentDistrib` transport + `CondIndepFun` use + `linarith`), and the chase steps are to be decided during implementation.

### Signature

The theorem signature mirrors M1's `Delta.lean` conventions (four independent codomains, Fintype + `MeasurableSingletonClass` at module scope). Paper ordering is $X, Y, Z, U$; M1.5 follows the paper's ordering, not M1's `(Z, U, X, Y)` re-ordering, because Theorem 2 is a standalone conditional inequality and the paper-matching signature reads more naturally.

```lean
variable {Ω : Type*} [MeasurableSpace Ω]
variable {S₁ S₂ S₃ S₄ : Type*}
  [Fintype S₁] [Fintype S₂] [Fintype S₃] [Fintype S₄]
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]

theorem theorem2
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h₁ : I[X : Y ; μ] = 0)
    (h₂ : I[X : Y | Z ; μ] = 0) :
    I[X : Y | ⟨Z, U⟩ ; μ] ≤ I[Z : U | ⟨X, Y⟩ ; μ] + I[X : Y | U ; μ] := by
  sorry
```

Design notes:

- **Hypothesis form.** The statement matches the paper's integer-scaled zero-mutual-information form. Inside the proof, use `mutualInfo_eq_zero.mp h₁` and `condMutualInfo_eq_zero.mp h₂` to obtain `IndepFun X Y μ` and `CondIndepFun X Y Z μ` when those are the more convenient inputs. The theorem statement itself stays in terms of `I[... ; μ] = 0` for direct correspondence with eq. (16).
- **Conditioner shape.** `I[X : Y | ⟨Z, U⟩ ; μ]` uses PFR's anonymous-pair notation for $(Z, U)$ --- the same pattern `Delta.lean` uses with `I[X : ⟨Z, U⟩ ; μ]`. Mirror that elaboration path.
- **Symmetric form.** The paper states Theorem 2 in the asymmetric form (17). Do not introduce a symmetric or averaged corollary; (17) is the result the roadmap calls for. If downstream callers want the `X ↔ Y` swap, derive it ad hoc.
- **No notation.** Defer any `ZY[X; Y | Z, U]`-style notation decision until M3, same rationale as M1.
- **`IsProbabilityMeasure`.** Required for `condMutualInfo_eq_zero` and the `condDistrib` identities. The hypothesis is explicit so the theorem is usable off the default measure. Inside the proof, `IsProbabilityMeasure.toIsZeroOrProbabilityMeasure` (instance) lifts to the weaker hypothesis PFR's `..._eq_zero` lemmas actually require.
- **Variable sort.** `S₁, S₂, S₃, S₄` carry `(X, Y, Z, U)` here; `Delta.lean` uses the same `S₁ .. S₄` names for `(Z, U, X, Y)`. Keep them module-local; no cross-module variable reuse, so the naming clash across modules is harmless.
- **Pair measurability.** The conditional mutual information terms `I[X : Y | ⟨Z, U⟩ ; μ]` and `I[Z : U | ⟨X, Y⟩ ; μ]` need `Measurable (fun ω => (Z ω, U ω))` and `Measurable (fun ω => (X ω, Y ω))`. Discharge with `hZ.prodMk hU` (that is, `Measurable.prodMk`); same idiom used in the Candidate A sketch for the pullback $\pi$.
- **Private helpers with `omit`.** `Delta.lean` uses `omit [Fintype S₃] [Fintype S₄] [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄] in` above lemmas whose proofs do not need the full instance bundle. `theorem2` itself will need every instance, but `aux_measure`, `aux_identDistrib`, and `aux_condIndep` may not touch all four codomains symmetrically; mirror the `omit` pattern where it applies, both for readability and to keep PFR's instance search focused.

### Lemma-level skeleton

Inside `Theorem2.lean`, the proof decomposes naturally into four private-ish building blocks. Use `private` or `section`-scoped `lemma`s --- not `theorem`s --- so only `theorem2` is exported.

1. **`aux_measure` (private).** The extended measure is built from $\kappa := \mathrm{condDistrib}\, Y \, \langle Z, U\rangle\, \mu$ by pulling that kernel back along $\pi : \Omega \to S_3 \times S_4$ with `Kernel.comap κ π (hZ.prodMk hU)`, then forming $\nu := \mu \otimes_m \kappa_\Omega$. If `Kernel.comap` proves awkward in practice, the deterministic-kernel-composition route is an equivalent alternative at this pin. Bundle the `Nonempty`/`StandardBorelSpace` side conditions on `S₂` at this lemma (see §7.1 for how those are actually supplied); propagate to downstream building blocks only if needed.
1. **`aux_identDistrib` (private).** Prove only the tuple-law identities the chase actually needs. At minimum, $(Y_1, Z, U)$ under $\nu$ is identically distributed to $(Y, Z, U)$ under $\mu$, and $(X, Z, U)$ under $\nu$ (viewing $X$ pulled back through $\mathrm{fst}$) is identically distributed to $(X, Z, U)$ under $\mu$. Use those to transport one-sided entropy or mutual-information terms whose entropy expansions depend only on these tuples. Do **not** plan around transporting mixed terms involving both $X$ and $Y_1$ by `IdentDistrib`; those belong on the $\nu$ side of the proof and are handled via `aux_condIndep` plus the Shannon chase.
1. **`aux_condIndep` (private).** $I[X : Y_1 \mid \langle Z, U\rangle ; \nu] = 0$, via the `condMutualInfo_eq_zero`/`CondIndepFun` bridge applied to the kernel-level construction.
1. **`theorem2`.** The Shannon-inequality chase: start from the hypotheses and the auxiliary facts, apply Shannon basics (`chain_rule`, submodularity, nonnegativity), close with `linarith`.

If the proof sprawls far beyond the four-lemma skeleton without making progress, stop and reconsider whether the chosen construction is the right one; the fallback is Candidate B, and if that fails, §7.4.

## Sequencing inside M1.5

1. **Bootstrap verification.** Run `bin/bootstrap-worktree`; confirm `make check` passes on the tip of `formalize/1.5-theorem-2` with M1 in place. Halt on any failure; investigate before writing new code.
1. **Create `ZhangYeung/Theorem2.lean` with module docstring and imports, and immediately wire `ZhangYeung.lean` to re-export it.** Imports are: `ZhangYeung.Prelude`, `Mathlib.Probability.Kernel.CondDistrib`, `Mathlib.Probability.IdentDistrib`, `PFR.ForMathlib.ConditionalIndependence`. The module docstring mirrors `ZhangYeung/Delta.lean`'s structure: a short descriptive heading, then `## Main definitions` (if any auxiliary defs land as public), `## Main statements` (naming `theorem2`), `## Implementation notes` (the single-copy construction summary, the finite-alphabet specialization, and the chosen Candidate A/B), `## References` (citing `@zhangyeung1998` and pointing at `references/transcriptions/zhangyeung1998.md` with the same verification date pattern), and `## Tags`. Add the shared `variable` block with the finite-alphabet assumptions. Stub `theorem theorem2` with `sorry`. Confirm `lake build ZhangYeung.Theorem2` and `lake build ZhangYeung` both compile --- this proves the signature, the variable block, the imports, and the public re-export are internally consistent before any real proof work.
1. **Commit the skeleton** as `feat: scaffold theorem 2 module with sorry stub`.
1. **Confirm the `StandardBorelSpace`/`Nonempty` inference path on Fintype codomains.** Write a one-line example or `by exact?` probe to confirm instance search reaches Mathlib's discrete-countable `StandardBorelSpace` instance in the theorem's actual hypothesis shape. If it does, proceed. If not, pick the fallback (see "Risks" §7.1).
1. **Pick a construction (A or B above)**; open a short note in-file documenting the choice. Proceed with Candidate A unless the early proof work shows that Candidate B is the better fit.
1. **Land `aux_measure`.** Define the extended measure and prove it is a probability measure (required for `condMutualInfo_eq_zero` downstream). Expect this to use `Measure.compProd` properties plus `IsMarkovKernel`-ness of `condDistrib`.
1. **Land `aux_identDistrib`.** Prove the exact tuple-level `IdentDistrib` facts the chase uses directly via `map_compProd_condDistrib`, `Measure.fst_compProd`, and `Measure.map` manipulation. Transport only the one-sided entropy or mutual-information identities that really follow from those tuple laws. Keep any needed conditional-mutual-info transport local and specialized; see "Risks" §7.3.
1. **Land `aux_condIndep`.** Prove `I[X : Y₁ | ⟨Z, U⟩ ; ν] = 0` by going through `condMutualInfo_eq_zero` and the structural conditional-independence of the copied variable.
1. **Land `theorem2`.** Run the Shannon chase. The two hypothesis equalities become `IndepFun X Y μ` and `CondIndepFun X Y Z μ` via the `... _eq_zero` iffs, and those in turn give Shannon identities (for instance, the unconditional `I[X : Y ; μ] = 0` gives `H[⟨X, Y⟩ ; μ] = H[X ; μ] + H[Y ; μ]`). Combine with the auxiliary facts, close with `linarith`. If the chase does not close, backtrack to the construction-selection step and try Candidate B.
1. **Commit the core proof** as `feat: prove Theorem 2 (Zhang-Yeung 1997 conditional inequality)`.
1. **Add `ZhangYeungTest/Theorem2.lean` and update `ZhangYeungTest.lean` in the same change.** The test module must import only `ZhangYeung`, and it should start being exercised by `lake test` the moment it lands. Commit as `test: add API regression tests for theorem 2`.
1. **Update `CLAUDE.md`'s Module Layout section** with a one-line entry for `ZhangYeung/Theorem2.lean` and its test. Commit as `docs: document theorem 2 module in CLAUDE.md`.
1. **Run `make check`.** Fix any lint or build failures before opening the PR.
1. **Open the PR.** Title `feat: prove Theorem 2 (Zhang-Yeung 1997 conditional warm-up)`; body links this plan and the roadmap.

Commit at each numbered step; keep commits small and conventional-commit-styled.

## Open questions and known risks

### 7.1: `StandardBorelSpace` on Fintype codomains (moderate)

`condDistrib` requires `[StandardBorelSpace β] [Nonempty β]` on the codomain of the variable being copied. Exploration at the pinned revision found *no* direct instance path from `[Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]` to `[StandardBorelSpace α]`; the instance is not automatic in the Fintype-with-default-discrete-σ-algebra shape this module uses. Expect step 4 of the sequencing (`exact?` probe) to fail, and plan for one of the mitigations below from the start rather than treating step 4 as a rubber stamp.

**Mitigation paths** (try in order):

1. `by exact?`/`Lean.Elab` probe: confirm whether `[Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]` can after all discharge `[StandardBorelSpace α]` in this module's use site. Most likely no; keep the probe to document the result.
1. Supply `StandardBorelSpace` locally via an explicit construction. For Fintype codomains with the default discrete σ-algebra, one standard route is to use `MeasurableEquiv.fintypeOfFintypeEquiv` (or an equivalent Fin-indexed bijection) and transport `StandardBorelSpace` through the equivalence. Add the instance under `section` scope in `Theorem2.lean`; do not change the theorem statement.
1. If that is tedious, fall back to `ProbabilityTheory.Kernel.condKernelCountable` or an explicit PMF-based single-copy construction that bypasses `condDistrib` entirely. For Fintype codomains, `PMF.bind` plus `PMF.toMeasure` is a clean alternative.

If mitigation 2 and 3 both prove fragile, park M1.5 and escalate rather than forcing `sorry`s; this is the single highest-probability blocker on the milestone.

### 7.2: Hypothesis form, equational vs. independence (low)

PFR's `mutualInfo_eq_zero` and `condMutualInfo_eq_zero` require `[IsZeroOrProbabilityMeasure μ]`, `[FiniteRange ...]`, and measurability. All of these follow from the module-level instances plus the explicit `hX, hY, hZ, hU` measurability. No action needed beyond keeping those instance arguments in scope.

If converting hypotheses via these iffs becomes verbose in practice, introduce a one-line private helper lemma at the top of `Theorem2.lean` that packages the conversion.

### 7.3: Conditional-mutual-info transport under `IdentDistrib` (moderate)

PFR exposes `IdentDistrib.entropy_congr` and `IdentDistrib.mutualInfo_eq`. A dedicated conditional analogue `IdentDistrib (⟨X, Z⟩, ⟨Y, Z⟩) ... → I[X : Y | Z ; μ] = I[X' : Y' | Z' ; ν]` is **confirmed absent** at the pinned PFR/Mathlib revision (exploration turned up no `IdentDistrib.condMutualInfo_eq` or an equivalent under a different name). The plan must not rely on such a lemma for mixed original-copy terms. Options, in descending order of preference:

1. **Avoid the transport altogether.** If a target term involves both an original variable and its copy, prove the needed identity or inequality directly on $\nu$ via `aux_condIndep` and Shannon algebra instead of forcing an `IdentDistrib` route. Given the one-sided shape of the tuple laws `aux_identDistrib` supplies, this is almost always the right choice.
1. **Derive the transport in-file, for a specific attainable tuple-law shape.** Expand `condMutualInfo` via `condMutualInfo_eq` (which PFR exposes --- see `Delta.lean`'s `delta_eq_entropy` for precedent), then apply `IdentDistrib.entropy_congr` to each summand and reassemble. Only do this when the concrete term genuinely has matching joint laws on both sides.

Option 1 is the default. Option 2 is escalatory and should be confined to a single local helper if required at all.

### 7.4: Picking the right single-copy construction (moderate)

Candidate A may not close the chase; Candidate B may not either. If both fail, the fallback is a non-degenerate variation (for example, $q(x, y, z, u, u_1) := p(x, y, z, u) \, p(u_1 \mid y, z)$ --- a copy of $U$ given $(Y, Z)$). The 1997 paper's proof used *some* single-variable auxiliary, and the chase is known to close; it is a question of finding the right shape.

If an honest search across Candidates A, B, and the non-degenerate variation does not close the inequality, escalate: either the cited `[39]` proof used a structurally different technique (not a copy) or there is a bookkeeping bug in the construction. In that case, consult [39] directly before continuing rather than multiplying attempts locally.

### 7.5: `condDistrib` and probability-measure preservation (low)

`μ.map X ⊗ₘ condDistrib Y X μ = μ.map (fun ω ↦ (X ω, Y ω))` (lemma `map_compProd_condDistrib`). After pulling the kernel back along $\pi : \Omega \to S_3 \times S_4$ via `Kernel.comap`, the resulting measure on $\Omega \times S_2$ should still have first marginal $\mu$ and preserve total mass. Both facts are required for the chase. Expect to prove them with `Measure.fst_compProd`, `Measure.compProd_apply_univ`, and map-congruence lemmas for `Kernel.comap`.

### 7.6: Namespace pollution (low)

Private helpers `aux_measure`, `aux_identDistrib`, `aux_condIndep` should either be `private def`/`private lemma` or section-scoped `variable` + `lemma` hidden by closing the section before `theorem2`'s statement. Mathlib idiom prefers `private`, but the PFR codebase mixes styles. Pick one and stay consistent within `Theorem2.lean`.

## Verification

Per the roadmap checkpoint: "theorem with all hypotheses explicit, discharged by the single-copy construction and Shannon basics, and the Theorem 2 test module builds." Operationally:

- `lake build ZhangYeung.Theorem2` compiles with no warnings, no `sorry`, no `admit`.
- `lake build ZhangYeung` compiles; `ZhangYeung.lean` re-exports `ZhangYeung.Theorem2` cleanly.
- `lake build ZhangYeungTest.Theorem2` compiles; the test module imports only `ZhangYeung` and not `ZhangYeung.Theorem2` directly, exercising the public API surface.
- `lake build` and `lake test` both succeed on the default targets; CI (`.github/workflows/ci.yml`) goes green.
- `lake lint` passes (batteries linter via the `lintDriver`).
- `make check` passes in full.

**Test module contents** (`ZhangYeungTest/Theorem2.lean`):

1. One `example` restating `theorem2` verbatim --- pinned signature check.
1. One downstream API usage: derive a *Shannon-inequality* corollary that uses `theorem2` as a black box input. For example, given the same hypotheses plus `I[Z : U | ⟨X, Y⟩ ; μ] = 0` (so the auxiliary RHS term vanishes), conclude `I[X : Y | ⟨Z, U⟩ ; μ] ≤ I[X : Y | U ; μ]`. Close with `linarith` after `theorem2` plus `condMutualInfo_nonneg`.
1. One compile-time check that the theorem statement type-checks with concrete `Fin n` codomains --- smoke test that the `Fintype`/`MeasurableSingletonClass` side conditions are supplied by the default instances.

Each `example` lives inside `namespace ZhangYeungTest` with `open ZhangYeung`, following the pattern `ZhangYeungTest/Delta.lean` established.

Land this file in the same commit as the `ZhangYeungTest.lean` import so `lake test` actually exercises it.

Out-of-scope for M1.5 (documented here so M2/M3 can pick them up):

- No generalization of the single-copy helper to arbitrary codomains --- M2 generalizes to the two-copy case and may rename or refactor the single-copy helper at that time.
- No extraction of the single-copy helper into a standalone `ZhangYeung/CopyLemma.lean`. Keep it inlined in `Theorem2.lean` to avoid premature abstraction; if M2 finds itself copying code from this module, the refactor lives in M2.
- No notation macro for Theorem 2.
- No proof of the converse direction of Theorem 2 (the paper does not state one, and there is no obvious reason it would hold).

## Critical files

**This milestone:**

- `ZhangYeung/Theorem2.lean` (new).
- `ZhangYeungTest/Theorem2.lean` (new).
- `ZhangYeung.lean` (modified, add one `import` line).
- `ZhangYeungTest.lean` (modified, add one `import` line).
- `CLAUDE.md` (modified, one-line addition under "Module Layout").

**Read-only references:**

- `ZhangYeung/Delta.lean` (M1 output; the `Fintype`/`MeasurableSingletonClass` specialization pattern to replicate).
- `ZhangYeung/Prelude.lean` (M0 output; entropy API import surface).
- `references/transcriptions/zhangyeung1998.md` (paper transcription, especially eqs. 16-17 on lines 193-207).
- `.lake/packages/PFR/PFR/ForMathlib/Entropy/Basic.lean` (entropy, condEntropy, mutualInfo, condMutualInfo; nonnegativity; `..._eq_zero` iff lemmas; chain rule; submodularity).
- `.lake/packages/PFR/PFR/ForMathlib/ConditionalIndependence.lean` (CondIndepFun).
- `.lake/packages/mathlib/Mathlib/Probability/Kernel/CondDistrib.lean` (condDistrib).
- `.lake/packages/mathlib/Mathlib/Probability/Kernel/Disintegration.lean` (`map_compProd_condDistrib`).
- `.lake/packages/mathlib/Mathlib/Probability/Kernel/Basic.lean` (`Kernel.comap`).
- `.lake/packages/mathlib/Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean` (`μ ⊗ₘ κ`, `fst_compProd`).
- `.lake/packages/mathlib/Mathlib/Probability/IdentDistrib.lean` (IdentDistrib, `.comp`, `.symm`).

Reference: the `write-lean-code` skill is authoritative for Lean naming and proof style; the `write-math` skill governs the module docstring and any mathematical prose inside comments; the `write-pandoc-markdown` skill governs this plan document.
