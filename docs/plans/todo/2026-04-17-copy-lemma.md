---
title: "M2: The copy lemma (Zhang-Yeung 1998, §III, eqs. 44-45)"
created: 2026-04-17
branch: formalize/2-copy-lemma
roadmap: docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md
milestone: M2
depends_on: M1 (`ZhangYeung/Delta.lean`, merged into `main` via PR #4). This branch is currently based on `formalize/1.5-theorem-2` (Theorem 2 / M1.5), which has not yet merged into `main`. M1.5's proof is not a prerequisite for M2: M1.5's final proof took the 1997 KL route and exercises none of the kernel/`condIndep_copies` machinery M2 depends on. The M1.5 branch does, however, pin the same PFR revision and verifies the bootstrap script under the current toolchain; once M1.5 merges, rebase this branch onto `main` rather than keeping it stacked.
---

## Status (2026-04-17): draft

Not yet started. `ZhangYeung/CopyLemma.lean`, `ZhangYeungTest/CopyLemma.lean`, and the associated re-exports from `ZhangYeung.lean` / `ZhangYeungTest.lean` do not exist on this branch.

## Context

**Primary reference:** `references/transcriptions/zhangyeung1998.md` (verified 2026-04-16). Equation numbers below reference that transcription.

Milestone M2 of the Zhang-Yeung roadmap (§6) formalizes the **copy lemma**: the auxiliary-probability construction that §III of the 1998 paper uses to prove Theorem 3 (the Zhang-Yeung inequality). The paper splits the construction into two named artifacts:

1. **Equation (44).** The auxiliary six-variable distribution

    $$
    q(x, y, z, u, x_{1}, y_{1}) \;:=\; \frac{p(x, y, z, u)\,p(x_{1}, y_{1}, z, u)}{p(z, u)}.
    $$

    Under $q$, the triples $(X, Y, Z, U)$ and $(X_{1}, Y_{1}, Z, U)$ each have the original joint law $p$, and the two copies are conditionally independent given $(Z, U)$.

2. **Lemma 2 (eq. 45).** The resulting identity

    $$
    \Delta(Z, U \mid X, Y) \;=\; I(X; Y_{1}) - I(X; Y_{1} \mid U) - I(X; Y_{1} \mid Z) - I(Z; U \mid X, Y_{1}),
    $$

    where the left side is computed under $p$ and the right side under $q$. Equation (45) is an *identity*, not an inequality; the three subtracted conditional mutual informations on the right are each nonnegative, which is what Theorem 3's proof will eventually exploit.

The copy lemma is the single highest-leverage artifact of the project (roadmap §1, §4, §10): non-Shannon information inequalities -- Theorem 3 here, and the larger families of Matus, Dougherty-Freiling-Zeger, Kinser, Chan-Yeung downstream -- all rest on the same two-copy construction. A clean, reusable formalization of the copy lemma is the prerequisite for all of them.

Nothing in PFR or Mathlib currently packages eq. (44) or eq. (45) as a reusable artifact. Mathlib's `ProbabilityTheory.condIndep_copies` (pinned at PFR rev `80daaf1` in `PFR/ForMathlib/ConditionalIndependence.lean:135`) provides a *generic* two-copy existence result: given random variables $X : \Omega \to \alpha$ and $Y : \Omega \to \beta$, it produces an extended probability space $(\Omega', \nu)$ with two conditionally-independent copies $X_{1}, X_{2} : \Omega' \to \alpha$ and a shared $Y' : \Omega' \to \beta$ such that $(X_{1}, Y')$ and $(X_{2}, Y')$ each have the joint law of $(X, Y)$ under $\mu$. Specializing `condIndep_copies` to $\alpha = S_{1} \times S_{2}$ (the codomain of $\langle X, Y \rangle$) and $\beta = S_{3} \times S_{4}$ (the codomain of $\langle Z, U \rangle$) recovers precisely the paper's eq. (44) up to projection onto the six coordinates.

The linking note added to `ZhangYeung/Theorem2.lean`'s module docstring in M1.5 (verified present on the M1.5 base branch at `ZhangYeung/Theorem2.lean:33` on 2026-04-17) makes the connection explicit:

> The auxiliary PMF $\tilde{p}(x, y, z, u) := p(x, z, u)\,p(y, z, u) / p(z, u)$ used in the 1997 KL proof is the $(X', Y_{1}, Z', U')$-marginal of the extended probability measure $\nu$ that `ProbabilityTheory.condIndep_copies`, applied to $\langle X, Y \rangle$ conditioned on $\langle Z, U \rangle$, produces.

M1.5 did not need the kernel construction because Kaced-Romashchenko ([@kaced2013]) showed Theorem 2 is essentially conditional and not derivable from a Shannon chase over any copy. M2 is therefore the **first** milestone in the project that actually builds on `condIndep_copies`, and M3 will be the first milestone to close a Shannon chase over the copy. The M1.5 plan's "Out of scope: M2 copy-construction helpers" list predicted this split.

### Value of M2 landing before M3

1. **Design-first before Shannon-chase-first.** M3's Theorem 3 proof is a six-step Shannon chase once the copy's structural facts are in hand (roadmap §6, M3 summary). Landing the copy structure and Lemma 2 separately forces us to commit early to a clean API -- which seven or eight structural lemmas M3 will cite by name, what their signatures are, which hypotheses they need. If M2 and M3 were combined, the Shannon chase would accrete copy-lemma scaffolding inline.
2. **Modularization before chase code.** The copy lemma is the one part of this project that may later be worth cleaning up for upstreaming, but M2 does not need to optimize for that today. Landing it in its own module, with a reasonably generic signature and no unnecessary Zhang-Yeung-specific naming (the projected coordinate names `X', Y', X_1, Y_1, Z', U'` are standard copy-lemma notation, not paper idioms), keeps later cleanup feasible without forcing the current branch to freeze an API too early. Lemma 2 is stated both in a Zhang-Yeung-flavored form (against the paper's $\Delta$) and in an abstract Shannon-identity form under a generic conditional-independence hypothesis.
3. **Risk isolation.** The three structural uncertainties for M2 -- universe bookkeeping around `condIndep_copies`'s $\Omega' : \mathrm{Type}\, u$, PFR-vs-Mathlib `CondIndepFun` API mismatch, and the missing conditional-mutual-info `IdentDistrib` transport -- all resolve in M2 or fail here. M3 can assume they are resolved.

## Paper equations this milestone formalizes

Equation (44), the auxiliary distribution:

$$
q(x, y, z, u, x_{1}, y_{1}) \;:=\; \frac{p(x, y, z, u)\,p(x_{1}, y_{1}, z, u)}{p(z, u)}.
$$

Equation (45), Lemma 2:

$$
\Delta(Z, U \mid X, Y) \;=\; I(X; Y_{1}) - I(X; Y_{1} \mid U) - I(X; Y_{1} \mid Z) - I(Z; U \mid X, Y_{1}),
$$

where $\Delta(Z, U \mid X, Y)$ is computed under $p$ and the four terms on the right are computed under $q$. The paper's proof of eq. (45) is the five-line chain on p. 1445-1446 combining:

- the marginal equality $I(Z; U \mid Y) = I(Z; U \mid Y_{1})$ (transport via the second-copy identical-distribution);
- a 4-way Shannon expansion $I(Z; U; X; Y_{1}) = I(X; Y_{1}) - I(X; Y_{1} \mid Z) - I(X; Y_{1} \mid U) + I(X; Y_{1} \mid Z, U)$;
- the conditional-independence identity $I(X; Y_{1} \mid Z, U) = 0$, which is the structural fact (iii) of eq. (44).

M2 formalizes (a) the construction of $q$ via `condIndep_copies`, (b) the three structural facts of eq. (44) in their `IdentDistrib` / `CondIndepFun` form, and (c) Lemma 2 as a named theorem under both the Zhang-Yeung $\Delta$ and a generic abstract Shannon-identity presentation.

M2 does **not** formalize Theorem 3's inequality itself. The final Shannon chase that chains two applications of Lemma 2 through the data-processing inequality and `I[X_{1} : Y_{1}] = I[X : Y]` lives in M3.

## Prerequisites

M1 delivers (merged into `main` via PR #4):

- `ZhangYeung/Delta.lean` with the `ZhangYeung.delta` definition, the purely-equational lemmas (`delta_def`, `delta_comm_cond`, `delta_self`), the finite-alphabet lemmas (`delta_comm_main`, `delta_le_mutualInfo`, `delta_eq_entropy`), and the form-conversion equivalences (`delta_form21_iff`, `delta_form22_iff`, `delta_form23_iff`, `delta_form23_of_form21_form22`).
- `ZhangYeungTest/Delta.lean` as the matching API-regression suite.
- `lakefile.toml` with PFR pinned at `80daaf1`, `testDriver = "ZhangYeungTest"`, and `defaultTargets = ["ZhangYeung"]`.

M1.5 (`formalize/1.5-theorem-2`, not yet merged) delivered `ZhangYeung/Theorem2.lean`. Its public surface is the single declaration `theorem2`, and its proof route does not overlap with M2's. Nothing in M2 references Theorem2's private scaffolding. The M2 branch can therefore rebase onto `main` as soon as M1.5 lands.

Before starting M2, run `bin/bootstrap-worktree`, confirm `make check` (build + lint + test) passes on the tip of `formalize/2-copy-lemma` with M1 + M1.5 in place, and verify that `lake env lean --version` reports the same Lean toolchain PFR at `80daaf1` compiles against.

## PFR and Mathlib API surface used

All declarations in this section live under `namespace ProbabilityTheory` unless noted.

**Two-copy construction (PFR, `PFR/ForMathlib/ConditionalIndependence.lean`):**

- `condIndep_copies` (line 135). Signature (abridged):

    ```lean
    lemma condIndep_copies (X : Ω → α) (Y : Ω → β) (hX : Measurable X) (hY : Measurable Y)
        [FiniteRange Y] (μ : Measure Ω) [IsProbabilityMeasure μ] :
        ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (X₁ X₂ : Ω' → α) (Y' : Ω' → β) (ν : Measure Ω'),
          IsProbabilityMeasure ν ∧ Measurable X₁ ∧ Measurable X₂ ∧ Measurable Y' ∧
          CondIndepFun X₁ X₂ Y' ν ∧ IdentDistrib (⟨X₁, Y'⟩) (⟨X, Y⟩) ν μ ∧
          IdentDistrib (⟨X₂, Y'⟩) (⟨X, Y⟩) ν μ
    ```

    Variable block at file scope (lines 126-130): `{α β : Type u} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass β] [Countable β]`. For `α := S₁ × S₂` and `β := S₃ × S₄` with `S_i` finite, `Countable (S₃ × S₄)` and `MeasurableSingletonClass (S₃ × S₄)` both follow from the per-factor instances, and PFR's `instance {Ω G : Type*} (X : Ω → G) [Finite G] : FiniteRange X` discharges the `FiniteRange Y` side condition.

- `CondIndepFun` (line 104): `CondIndepFun f g h μ := ∀ᵐ z ∂(μ.map h), IndepFun f g (μ[|h ← z])`. Note: this is *PFR's* definition conditioning on a random variable `h : Ω → γ`, not Mathlib's `CondIndepFun m' hm' f g μ` which conditions on a sub-σ-algebra. The two are equivalent when `h` is measurable, but they are syntactically distinct and Mathlib's `CondIndepFun.comp` (Mathlib/Probability/Independence/Conditional.lean:707) does not apply to PFR's form without a translation step.

**Entropy and information (PFR, `PFR/ForMathlib/Entropy/Basic.lean`):**

- `entropy`, notation `H[X ; μ]`; `condEntropy`, notation `H[X | Y ; μ]`.
- `mutualInfo`, notation `I[X : Y ; μ]`; `mutualInfo_def : I[X : Y ; μ] = H[X ; μ] + H[Y ; μ] - H[⟨X, Y⟩ ; μ]` (`rfl`).
- `condMutualInfo`, notation `I[X : Y | Z ; μ]`; `condMutualInfo_eq : I[X : Y | Z ; μ] = H[X | Z ; μ] + H[Y | Z ; μ] - H[⟨X, Y⟩ | Z ; μ]` under `[IsZeroOrProbabilityMeasure μ] [FiniteRange Z]` plus measurability (Basic.lean:941).
- `condMutualInfo_eq_zero : I[X : Y | Z ; μ] = 0 ↔ CondIndepFun X Y Z μ` under `[IsZeroOrProbabilityMeasure μ]` plus the usual measurability/`FiniteRange` side conditions (Basic.lean:1042). This is the bridge from PFR's `CondIndepFun` to an algebraic zero, used to turn the copy's conditional-independence fact into an `I[... | ...] = 0` rewrite target.
- `mutualInfo_nonneg`, `condMutualInfo_nonneg`: sign inputs for `linarith` in the nonnegativity half of Lemma 2's corollary inequality.
- `mutualInfo_comm`, `condMutualInfo_comm`, `entropy_comm`, `entropy_assoc`, `chain_rule''`: the Shannon-algebra primitives Lemma 2's entropy-expansion proof will lean on.
- `IdentDistrib.entropy_congr` (Basic.lean:77), `IdentDistrib.condEntropy_eq` (Basic.lean:586), `IdentDistrib.mutualInfo_eq` (Basic.lean:691): the three transport lemmas PFR does expose.

**Conditional mutual information under `IdentDistrib` (derived in-file):**

PFR exposes no `IdentDistrib.condMutualInfo_eq` at the pinned revision (confirmed 2026-04-16; same gap the M1.5 plan §7.3 flagged). The M2 delta transports need this at the concrete **three-variable conditioning shape** -- they transport `I[Z : U | X ; μ] = I[Z' : U' | X' ; ν]` from a triple-level `IdentDistrib ⟨Z, U, X⟩ ⟨Z', U', X'⟩ μ ν`, not at a four-variable shape. Land the helper at exactly that shape:

```lean
lemma IdentDistrib.condMutualInfo_eq
    (h : IdentDistrib (fun ω  => (X ω,  Y ω,  Z ω))
                      (fun ω' => (X' ω', Y' ω', Z' ω')) μ μ') :
    I[X : Y | Z ; μ] = I[X' : Y' | Z' ; μ']
```

(with appropriate measurability / `FiniteRange` / `IsProbabilityMeasure` side conditions). Proof route: apply `condMutualInfo_eq` to expand both sides into the three-term `H[X | Z] + H[Y | Z] - H[⟨X, Y⟩ | Z]` pattern, then transport each `condEntropy` via `IdentDistrib.condEntropy_eq` after extracting the two relevant 2-variable sub-`IdentDistrib`s (for `⟨X, Z⟩` and `⟨Y, Z⟩`) via `IdentDistrib.comp`. Mathlib's `chain_rule''` pattern is the alternative and is what `IdentDistrib.condEntropy_eq`'s own proof uses.

Each of the three triple-level `IdentDistrib`s in the "Delta transport" section below feeds into this helper directly, up to a fixed positional reordering (e.g., transport of `I[Z : U | X ; μ]` instantiates the helper at `(X := Z, Y := U, Z := X)` and consumes the triple `⟨Z, U, X⟩ ∼ ⟨Z', U', X'⟩`). The reordering is a one-line `IdentDistrib.comp` with a measurable permutation, or baked into how the triple is stated; implementation detail for step 6, not a structural obstacle. If a later milestone needs a four-variable shape (e.g., transport of `I[X : Y | ⟨Z, W⟩]` under a single 4-tuple `IdentDistrib`), derive it by packing the two conditioners into a single random variable and reusing this three-variable helper.

**Identical distribution (Mathlib, `Mathlib/Probability/IdentDistrib.lean`):**

- `IdentDistrib f g μ ν` with fields `aemeasurable_fst`, `aemeasurable_snd`, `map_eq`.
- `IdentDistrib.comp : IdentDistrib f g μ ν → Measurable u → IdentDistrib (u ∘ f) (u ∘ g) μ ν`: this is what extracts sub-`IdentDistrib`s from the four-variable one produced by `condIndep_copies`.
- `IdentDistrib.symm`, `IdentDistrib.trans`.

**`CondIndepFun.comp` (derived in-file):**

PFR's `CondIndepFun.comp_right` (ConditionalIndependence.lean:114) post-composes with an *Ω-level* measurable embedding -- the wrong direction for what M2 needs, which is *target-side* post-composition (given `CondIndepFun f g h μ` and measurable `φ, ψ`, conclude `CondIndepFun (φ ∘ f) (ψ ∘ g) h μ`). Mathlib's `CondIndepFun.comp` (Conditional.lean:707) uses the σ-algebra form of `CondIndepFun`, not PFR's random-variable form, so it does not apply directly either.

A private helper `condIndepFun_comp` lands in `ZhangYeung/CopyLemma.lean`. Statement:

```lean
lemma condIndepFun_comp {φ : α → α'} {ψ : β → β'}
    (hφ : Measurable φ) (hψ : Measurable ψ) (h : CondIndepFun f g k μ) :
    CondIndepFun (φ ∘ f) (ψ ∘ g) k μ
```

Proof route: unfold via `condIndepFun_iff` to `∀ᵐ z ∂(μ.map k), IndepFun f g (μ[|k ← z])`, push each fibrewise `IndepFun` through `IndepFun.comp` (Mathlib's post-composition lemma, Mathlib/Probability/Independence/Basic.lean:799), repack via `condIndepFun_iff`. The M1.5 plan's "Out of scope: M2 copy-construction helpers" list named this helper in advance (commit `249da6d` carried a pre-pivot sketch before M1.5 pivoted to KL; that sketch is recoverable from git history if needed).

**`FiniteRange` from `Fintype` (PFR):**

`instance {Ω G : Type*} (X : Ω → G) [Finite G] : FiniteRange X` lives in `PFR/ForMathlib/FiniteRange/Defs.lean`. Combined with the module-scope `Fintype S_i` assumptions, every `Measurable S_i`-valued random variable in M2 -- `X, Y, Z, U, X', Y', X₁, Y₁, Z', U'` -- satisfies `FiniteRange` automatically. No manual `FiniteRange` plumbing is required beyond declaring the module-scope instances.

## Files

**Create** `ZhangYeung/CopyLemma.lean`: the proof code for this milestone.

**Create** `ZhangYeungTest/CopyLemma.lean`: the matching API-regression tests.

**Modify** `ZhangYeung.lean` to re-export the new module:

```lean
import ZhangYeung.Delta
import ZhangYeung.Prelude
import ZhangYeung.Theorem2
import ZhangYeung.CopyLemma
```

**Modify** `ZhangYeungTest.lean` to pull in the new test module:

```lean
import ZhangYeungTest.Delta
import ZhangYeungTest.Theorem2
import ZhangYeungTest.CopyLemma
```

**Modify** `CLAUDE.md` (really `AGENTS.md`): add a one-line entry under "Module Layout" pointing to `ZhangYeung/CopyLemma.lean` and its test.

No changes to `ZhangYeung/Prelude.lean`, `ZhangYeung/Delta.lean`, `ZhangYeung/Theorem2.lean`, or `lakefile.toml`. `Prelude.lean`'s current import surface (`PFR.ForMathlib.Entropy.Basic`) is sufficient for the entropy side; the only new import `CopyLemma.lean` needs on top of `ZhangYeung.Prelude` + `ZhangYeung.Delta` is `PFR.ForMathlib.ConditionalIndependence` (for `condIndep_copies`, `CondIndepFun`, `condMutualInfo_eq_zero`). `IdentDistrib` transits through PFR's existing imports.

## Design: the copy construction

### What M2 must produce

Concretely, the M2 copy lemma is an existential statement that, given four measurable random variables $X, Y, Z, U$ on a probability space $(\Omega, \mu)$, produces an extended probability space $(\Omega', \nu)$ with six projected random variables $X', Y', X_{1}, Y_{1}, Z', U'$ such that:

1. **First-copy marginal equality.** $\langle X', Y', Z', U' \rangle$ under $\nu$ is identically distributed to $\langle X, Y, Z, U \rangle$ under $\mu$.
2. **Second-copy marginal equality.** $\langle X_{1}, Y_{1}, Z', U' \rangle$ under $\nu$ is identically distributed to $\langle X, Y, Z, U \rangle$ under $\mu$.
3. **Conditional independence.** $\langle X', Y' \rangle$ and $\langle X_{1}, Y_{1} \rangle$ are conditionally independent given $\langle Z', U' \rangle$ under $\nu$.

These three facts are the direct Lean encoding of eq. (44). (i) is "summing $q$ over $(x_{1}, y_{1})$ gives $p(x, y, z, u)$", (ii) is "summing over $(x, y)$ gives $p(x_{1}, y_{1}, z, u)$", (iii) is the defining factorization of $q$.

### Construction strategy

Apply `ProbabilityTheory.condIndep_copies` to `⟨X, Y⟩ : Ω → S₁ × S₂` with `⟨Z, U⟩ : Ω → S₃ × S₄` as the shared variable. `condIndep_copies` returns:

- an extended type $\Omega'$ (with a `MeasurableSpace` instance) and a probability measure $\nu$ on it;
- two "copies" $W_{1}, W_{2} : \Omega' \to S_{1} \times S_{2}$ and a shared $V : \Omega' \to S_{3} \times S_{4}$;
- `CondIndepFun W₁ W₂ V ν`;
- `IdentDistrib (⟨W₁, V⟩) (⟨⟨X, Y⟩, ⟨Z, U⟩⟩) ν μ` and `IdentDistrib (⟨W₂, V⟩) (⟨⟨X, Y⟩, ⟨Z, U⟩⟩) ν μ`.

The six projected random variables M2 exposes are

$$
X' := \mathrm{fst} \circ W_{1}, \quad Y' := \mathrm{snd} \circ W_{1}, \quad X_{1} := \mathrm{fst} \circ W_{2}, \quad Y_{1} := \mathrm{snd} \circ W_{2}, \quad Z' := \mathrm{fst} \circ V, \quad U' := \mathrm{snd} \circ V.
$$

Measurability of each projection is immediate from the measurability of `W₁, W₂, V` plus `measurable_fst` / `measurable_snd`.

The two 4-variable `IdentDistrib`s follow from the two $(W_{i}, V)$-level `IdentDistrib`s by composing with the (measurable) rearrangement $(S_{1} \times S_{2}) \times (S_{3} \times S_{4}) \to S_{1} \times S_{2} \times S_{3} \times S_{4}$ on each side. Whether to express the 4-variable output as `⟨X', Y', Z', U'⟩` (right-associated via iterated `Prod.mk`) or `⟨⟨X', Y'⟩, ⟨Z', U'⟩⟩` is a cosmetic choice; PFR's `IdentDistrib.comp` is agnostic. I recommend the right-associated form `⟨X', Y', Z', U'⟩` (matching Theorem 2's `theorem2_shannon_identity` signature and `pJoint`'s tuple layout) so a downstream Theorem 3 proof can reuse the same destructuring patterns.

The conditional-independence fact $\mathrm{CondIndepFun}\,\langle X', Y' \rangle\,\langle X_{1}, Y_{1} \rangle\,\langle Z', U' \rangle\,\nu$ is the returned `CondIndepFun W₁ W₂ V ν` up to the pointwise identity $\langle \mathrm{fst} \circ W_{1}, \mathrm{snd} \circ W_{1} \rangle = W_{1}$ (and similarly for $W_{2}, V$). Lean does **not** close this by `rfl` in general, because `fun ω => (W₁ ω).1, (W₁ ω).2` is not the same term as `W₁`; the rewrite is one line of `funext` + `Prod.mk.eta` (or equivalently `Prod.mk_fst_snd`). Plan for this one-line rewrite at each of the three repackings, not for zero-cost definitional equality. See Risk §7.4 for the fallback if that rewrite proves awkward.

### Bundling the output

For M2, use presentation (A) first. If M3 becomes materially cleaner with bundled data, refactor freely and update the test module in the same change.

**(A) Long existential, direct `condIndep_copies` transform.** Mirrors PFR's presentation of `condIndep_copies`: a single statement with one existential over $\Omega'$, its `MeasurableSpace`, $\nu$, and the six projected random variables, plus a conjunction of `IsProbabilityMeasure ν`, six measurabilities, two 4-variable `IdentDistrib`s, and one `CondIndepFun`. Users apply `obtain ⟨Ω', _, ν, X', Y', X₁, Y₁, Z', U', _, hX', hY', hX₁, hY₁, hZ', hU', ident_first, ident_second, hCond⟩ := copyLemma ...`

Pros: one function, no new datatype, matches `condIndep_copies`'s idiom, minimal packaging overhead.

Cons: long `obtain` patterns on every use site, no named fields.

**(B) `structure CopyData` bundling.** A `structure` with fields for $\Omega'$, its `MeasurableSpace`, $\nu$, its probability-measure instance, the six projected random variables, their measurabilities, the two `IdentDistrib`s, and the `CondIndepFun`. The theorem returns an instance of this structure rather than an existential. Users say `let c := copyLemma ...; have := c.identFirst` and dot-access named fields.

Pros: readable downstream use, named fields are self-documenting, M3's Shannon chase probably reads more linearly.

Cons: the `MeasurableSpace Ω'` and `IsProbabilityMeasure ν` fields are feasible as structure fields (bundle as `[inst : MeasurableSpace Ω']` and similar), but the resulting API is noisier than the bare existential -- each dot-access either requires the bundled instance to be explicitly supplied or relies on `letI`/`haveI` patterns at consumer sites. The cost is readability, not correctness.

**Recommendation: start with (A) for the main `copyLemma` theorem.** It matches `condIndep_copies`'s idiom and avoids instance-class plumbing that (B) forces. The cost is a 16-element `obtain` at the M3 call site, which is unaesthetic but not fragile. If M3's Shannon chase proves hard to read because of that destructuring, refactor to (B) and update the API tests in the same change; no long-term stability commitment is intended here.

### Supporting corollaries under a local `variable` block

Given the destructuring cost, expose the derived facts M3 will need as separate lemmas parametrized by the copy's eight fields (the two `IdentDistrib`s + `CondIndepFun` + six measurabilities) treated as local hypotheses. A single `section` block with a shared `variable` declaration:

```lean
section CopyConsequences
variable {Ω' : Type*} [MeasurableSpace Ω']
  {ν : Measure Ω'} [IsProbabilityMeasure ν]
  {X' : Ω' → S₁} {Y' : Ω' → S₂}
  {X₁ : Ω' → S₁} {Y₁ : Ω' → S₂}
  {Z' : Ω' → S₃} {U' : Ω' → S₄}
  (hX' : Measurable X') (hY' : Measurable Y')
  (hX₁ : Measurable X₁) (hY₁ : Measurable Y₁)
  (hZ' : Measurable Z') (hU' : Measurable U')
  (hFirst : IdentDistrib
      (fun ω' => (X' ω', Y' ω', Z' ω', U' ω'))
      (fun ω  => (X ω,  Y ω,  Z ω,  U ω)) ν μ)
  (hSecond : IdentDistrib
      (fun ω' => (X₁ ω', Y₁ ω', Z' ω', U' ω'))
      (fun ω  => (X ω,  Y ω,  Z ω,  U ω)) ν μ)
  (hCond : CondIndepFun
      (fun ω' => (X' ω', Y' ω'))
      (fun ω' => (X₁ ω', Y₁ ω'))
      (fun ω' => (Z' ω', U' ω')) ν)
```

Derived lemmas in the section take all of these as hypotheses (explicit, so they are visible at use sites); M3 then plugs the outputs of `obtain` into each lemma by name. The `copyLemma` theorem proper lives outside the section.

This is the pattern the M1.5 `theorem2_shannon_identity` / `ptilde_sum_eq_one` / etc. already follow: parametrize over the measurable random variables and their measurabilities, let the caller destructure once and apply lemmas one-by-one.

### Signature of the main theorem

```lean
theorem copyLemma
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
    ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (ν : Measure Ω')
        (X' : Ω' → S₁) (Y' : Ω' → S₂)
        (X₁ : Ω' → S₁) (Y₁ : Ω' → S₂)
        (Z' : Ω' → S₃) (U' : Ω' → S₄),
      IsProbabilityMeasure ν ∧
      Measurable X' ∧ Measurable Y' ∧
      Measurable X₁ ∧ Measurable Y₁ ∧
      Measurable Z' ∧ Measurable U' ∧
      IdentDistrib (fun ω' => (X' ω', Y' ω', Z' ω', U' ω'))
                   (fun ω  => (X ω,  Y ω,  Z ω,  U ω)) ν μ ∧
      IdentDistrib (fun ω' => (X₁ ω', Y₁ ω', Z' ω', U' ω'))
                   (fun ω  => (X ω,  Y ω,  Z ω,  U ω)) ν μ ∧
      CondIndepFun (fun ω' => (X' ω', Y' ω'))
                   (fun ω' => (X₁ ω', Y₁ ω'))
                   (fun ω' => (Z' ω', U' ω')) ν
```

Design notes:

- **Finite-alphabet codomains at module scope.** `[Fintype Sᵢ] [MeasurableSingletonClass Sᵢ]` on all four codomains mirrors M1 and M1.5, and discharges `FiniteRange` / `Countable` / `MeasurableSingletonClass` for both the per-codomain random variables and for the pair codomains `S₁ × S₂` and `S₃ × S₄` via the automatic `Prod` instances.
- **Universe-polymorphic codomains.** `condIndep_copies` binds its two codomains at a single universe `u`. Carrying the codomains at `Type u` (rather than `Type*`) is the smallest possible commitment that makes `condIndep_copies` apply. This is a deviation from M1's `Type*` convention; the reason is `condIndep_copies` itself, not preference. If instance-search or universe-unification issues appear at the call site, see "Risks" §7.1.
- **Hypothesis form.** All four random variables are implicit; measurabilities are explicit positional arguments, mirroring `condIndep_copies`.
- **Variable ordering in the signature.** `(X, Y, Z, U)` across the inputs -- the paper's reading order for eq. (44). Each output's coordinate order follows the tuple pattern `(X', Y', Z', U')` / `(X₁, Y₁, Z', U')` / `(⟨X', Y'⟩, ⟨X₁, Y₁⟩, ⟨Z', U'⟩)` so each name's ordinal in the pair matches the variable it projects from.
- **No notation.** Defer any notation decision to M3 or later. Plain function application `copyLemma hX hY hZ hU μ` is fine; the `obtain` introduces names locally.
- **No dependency on `ZhangYeung.delta`.** The main theorem is stated in pure PFR / Mathlib notation and does not reference `ZhangYeung.delta`. This keeps the construction generic and makes later cleanup or upstreaming easier if we ever want it.

### Lemma 2 (eq. 45) as a Shannon identity

Lemma 2 itself lands in two forms.

**Form A: abstract Shannon identity.** Under the hypothesis `I[A : D | ⟨B, C⟩ ; ν] = 0`, the identity

```lean
lemma delta_of_condMI_vanishes_eq
    {Ω : Type*} [MeasurableSpace Ω]
    {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [MeasurableSingletonClass γ] [MeasurableSingletonClass δ]
    {A : Ω → α} {B : Ω → β} {C : Ω → γ} {D : Ω → δ}
    (hA : Measurable A) (hB : Measurable B) (hC : Measurable C) (hD : Measurable D)
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (hVanish : I[A : D | ⟨B, C⟩ ; ν] = 0) :
    ZhangYeung.delta B C A D ν
      = I[A : D ; ν] - I[A : D | B ; ν] - I[A : D | C ; ν]
        - I[B : C | ⟨A, D⟩ ; ν]
```

holds. This is the paper's eq. (45) abstracted away from the copy construction: any four discrete random variables for which one conditional mutual information vanishes satisfy the delta identity.

Proof route: expand the LHS via `delta_def`, the four subtractors on the RHS via `condMutualInfo_eq` / `mutualInfo_def`, and the hypothesis via `condMutualInfo_eq` on `I[A : D | ⟨B, C⟩]`. The algebra that remains is a linear identity in entropy terms closed by `linarith`, identical in shape to the M1.5 `theorem2_shannon_identity`. The key Shannon combinatorics are: `I[A : D] - I[A : D | B] - I[A : D | C] = (I[A : D] - I[A : D | B]) - I[A : D | C]` expands `I[A : D] - I[A : D | B]` into the four-way $I(A; D; B; C) + I(A; D | B, C)$ identity via two applications of the 3-way identity $I(A; B) - I(A; B | C) = I(A; B; C)$. A search of PFR at the pinned revision (`.lake/packages/pfr/PFR/ForMathlib/Entropy/`) turned up no named lemma for either the 3-way or 4-way form; the proof expands each mutual information into entropy terms via `mutualInfo_eq_entropy_sub_condEntropy` (`PFR/ForMathlib/Entropy/Basic.lean:827`) and `condMutualInfo_eq` (Basic.lean:941), then closes the linear combination by `linarith`. If that route proves unwieldy, introduce the 3-way interaction-information identity as a local helper `private lemma mutualInfo_sub_condMutualInfo_eq` inside `section Helpers`, stated directly in entropy terms; this is ~5-8 tactic lines and is reusable by both `delta_of_condMI_vanishes_eq` and any future Shannon chase. See "Sequencing" §5 below for a concrete proof sketch.

**Form B: Zhang-Yeung-flavored corollary.** Specialized to the copy construction's projections `(X', Y₁, Z', U')` with the already-projected `I[X' : Y₁ | ⟨Z', U'⟩ ; ν] = 0` (a derived corollary of the main `CondIndepFun`):

```lean
lemma copyLemma_delta_identity_Y₁ (hX' : Measurable X') ... (hCond : CondIndepFun ...) :
    ZhangYeung.delta Z' U' X' Y₁ ν
      = I[X' : Y₁ ; ν] - I[X' : Y₁ | Z' ; ν] - I[X' : Y₁ | U' ; ν]
        - I[Z' : U' | ⟨X', Y₁⟩ ; ν]
```

Proof: `delta_of_condMI_vanishes_eq` applied to $(A, B, C, D) = (X', Z', U', Y_{1})$ with the vanishing CMI provided by projecting `hCond`.

### Delta transport: $\Delta_{\mu} = \Delta_{\nu'}$

The bridge identity

```lean
lemma copyLemma_delta_transport_Y_to_Y₁ (hFirst hSecond : ...) :
    ZhangYeung.delta Z U X Y μ = ZhangYeung.delta Z' U' X' Y₁ ν
```

links the LHS of Lemma 2 (computed under $\mu$, the original law) to the RHS of Lemma 2 (computed under $\nu$, the copy). It is a pure `IdentDistrib`-transport: `delta_def` expands each side into three MI terms; `IdentDistrib.mutualInfo_eq` transports `I[Z : U]`; the custom `IdentDistrib.condMutualInfo_eq` helper transports `I[Z : U | X]` and `I[Z : U | Y]`, using triple-level `IdentDistrib`s obtained by composing the full 4-variable first/second copy `IdentDistrib`s with the appropriate projections.

The three triple-level `IdentDistrib`s actually consumed by the two delta transports are:

- `IdentDistrib ⟨X, Z, U⟩ ⟨X', Z', U'⟩ μ ν`, from `hFirst.symm.comp (proj_134 := fun (x, y, z, u) => (x, z, u))`. Used by both transports (shared).
- `IdentDistrib ⟨Y, Z, U⟩ ⟨Y₁, Z', U'⟩ μ ν`, from `hSecond.symm.comp (proj_234 := fun (x, y, z, u) => (y, z, u))`. Used by the `Y_to_Y₁` transport.
- `IdentDistrib ⟨X, Z, U⟩ ⟨X₁, Z', U'⟩ μ ν`, from `hSecond.symm.comp (proj_134)`. Used by the symmetric `X_to_X₁` transport.

No first-copy `Y` triple (`⟨Y, Z, U⟩ ∼ ⟨Y', Z', U'⟩`) is needed: both transports project the second copy into the $Y$-slot to use `Y₁`, not `Y'`. If a later milestone wants a first-copy `Y`-based variant, add it then.

`IdentDistrib.comp` takes `Measurable u`, so each projection needs a one-line measurability proof (chains of `measurable_fst`, `measurable_snd`, and `Measurable.prodMk`).

### The combined Zhang-Yeung bound

Finally, combining Lemma 2 (Form B, identity under $\nu$) with the delta transport (bridge between $\mu$ and $\nu$) and `condMutualInfo_nonneg` yields the inequality the paper reads off at line 683 of the transcription:

```lean
lemma copyLemma_delta_le_mutualInfo_Y₁
    (hX' hY₁ hZ' hU' hFirst hSecond hCond : ...) :
    ZhangYeung.delta Z U X Y μ ≤ I[X' : Y₁ ; ν]
```

Proof: three lines. `rw [copyLemma_delta_transport_Y_to_Y₁, copyLemma_delta_identity_Y₁]`, then `linarith [condMutualInfo_nonneg, condMutualInfo_nonneg, condMutualInfo_nonneg]` for the three subtracted nonnegative terms.

This is precisely the first of the two inequalities Theorem 3's proof opens with ("From Lemma 2, we have $I(Z; U) - I(Z; U \mid X) - I(Z; U \mid Y) \le I(X; Y_{1})$", paper line 683). M3 will also want the symmetric application for $(X, X_{1})$; see the "Symmetric application" sub-section below.

### Symmetric application: $\Delta(Z, U \mid X, X_{1})$

Theorem 3's second inequality ("$I(Z; U) - 2 I(Z; U \mid X) \le I(X; X_{1})$", paper line 689) is the $X \leftrightarrow X_{1}$ swap of the same Lemma 2 machinery. Under $\nu$ and with $X'$ and $X_{1}$ both distributed like $X$ given $(Z', U')$,

$$
\Delta(Z', U' \mid X', X_{1}) = I(Z'; U') - I(Z'; U' \mid X') - I(Z'; U' \mid X_{1}) = I(Z; U)_{\mu} - 2\, I(Z; U \mid X)_{\mu}
$$

via the two triple-level `IdentDistrib`s for $(X, Z, U) \sim (X', Z', U')$ and $(X, Z, U) \sim (X_{1}, Z', U')$.

Applying Lemma 2 Form A to $(A, B, C, D) = (X', Z', U', X_{1})$ with the conditional-independence fact $I[X' : X_{1} \mid \langle Z', U' \rangle ; \nu] = 0$ (derived from the main `CondIndepFun` by projecting each side to its first coordinate) gives

```lean
lemma copyLemma_delta_le_mutualInfo_X_X₁
    (hX' hX₁ hZ' hU' hFirst hSecond hCond : ...) :
    I[Z : U ; μ] - 2 * I[Z : U | X ; μ] ≤ I[X' : X₁ ; ν]
```

M2 ships this symmetric inequality so M3 can open its Shannon chase with both forms in scope. If it turns out to be redundant with a single "Lemma 2 applied twice" lemma, fold them together in a late-pass simplification.

## Lemma-level skeleton

Inside `ZhangYeung/CopyLemma.lean`, the proof decomposes naturally into the blocks below. All non-public declarations are `private`; only the named theorems in the public list are exported.

### Public surface

- `copyLemma`: the main existential. Produces $\Omega', \nu, X', Y', X_{1}, Y_{1}, Z', U'$ plus the three structural facts (two `IdentDistrib`s, one `CondIndepFun`) and six measurabilities.
- `delta_of_condMI_vanishes_eq`: Lemma 2 Form A, the abstract Shannon identity under vanishing conditional MI.
- `copyLemma_delta_transport_Y_to_Y₁`: bridge identity between $\Delta_{\mu}$ and $\Delta_{\nu}$ (first-copy $X$, second-copy $Y_{1}$).
- `copyLemma_delta_transport_X_to_X₁`: bridge identity for the symmetric application.
- `copyLemma_delta_identity_Y₁`: Lemma 2 Form B, specialized to the copy's $(X', Y_{1}, Z', U')$ projections.
- `copyLemma_delta_identity_X_X₁`: Lemma 2 Form B, specialized to $(X', X_{1}, Z', U')$.
- `copyLemma_delta_le_mutualInfo_Y₁`: the inequality-form corollary $\Delta(Z, U \mid X, Y)_{\mu} \le I[X' : Y_{1} ; \nu]$.
- `copyLemma_delta_le_mutualInfo_X_X₁`: the symmetric inequality $I(Z; U) - 2\,I(Z; U \mid X) \le I[X' : X_{1} ; \nu]$.

### Private helpers

- `condIndepFun_comp` (generic): post-composition of `CondIndepFun` on the two measured coordinates. See "PFR and Mathlib API surface used" above for the statement.
- `IdentDistrib.condMutualInfo_eq` (generic): conditional-mutual-information transport under a four-variable `IdentDistrib`. Private for M2; if later modules need it, promote it to `ZhangYeung/Prelude.lean` or refactor at that point.
- `copyLemma_triple_identDistrib_XZU` / `X₁ZU` / `Y₁ZU`: the three triple-level `IdentDistrib`s $(X, Z, U) \sim (X', Z', U')$, $(X, Z, U) \sim (X_{1}, Z', U')$, $(Y, Z, U) \sim (Y_{1}, Z', U')$. Each is a one-line `IdentDistrib.comp` of `hFirst` or `hSecond` with a (measurable) 4-to-3 projection; a shared helper `proj_fst` / `proj_snd_fst` etc. may be useful if the three bodies repeat. (A first-copy `(Y, Z, U) \sim (Y', Z', U')` triple is not included; neither M2 transport consumes it.)
- `copyLemma_condMI_X_Y₁_vanishes`: $I[X' : Y_{1} \mid \langle Z', U' \rangle ; \nu] = 0$. From the main `CondIndepFun` projected through `condIndepFun_comp`, then `condMutualInfo_eq_zero.mpr`.
- `copyLemma_condMI_X_X₁_vanishes`: analogous for the symmetric application.
- Pair measurabilities: `Measurable (fun ω' => (X' ω', Y' ω'))` etc., a handful of `Measurable.prodMk` chains.

### Suggested section structure

```text
ZhangYeung/CopyLemma.lean
├── Module docstring (## Main statements, ## Implementation notes, ## References, ## Tags)
├── Imports: ZhangYeung.Delta, ZhangYeung.Prelude, PFR.ForMathlib.ConditionalIndependence
├── namespace ZhangYeung (keep public surface flat under ZhangYeung)
├── section Helpers
│     - condIndepFun_comp
│     - IdentDistrib.condMutualInfo_eq
├── section MainConstruction
│     - copyLemma
├── section Consequences (local variable block with the eight hypotheses)
│     - triple IdentDistribs (four)
│     - condMI vanishing (two: for (X', Y₁) and (X', X₁))
│     - delta transports (two)
│     - delta identities (two, instantiating delta_of_condMI_vanishes_eq)
│     - delta ≤ mutualInfo corollaries (two)
└── end ZhangYeung
```

The module docstring follows the M1.5 pattern: opening paragraph stating the role of the module, `## Main statements` listing the public theorems with one-sentence descriptions, `## Implementation notes` explaining the `condIndep_copies` wrapper + the derived-corollary section layout + the finite-alphabet specialization, `## References` citing the 1998 paper and pointing at `references/transcriptions/zhangyeung1998.md` (equations 44-45, verified 2026-04-16), and `## Tags`.

## Sequencing: commits

Each commit maintains a green build + lint + test. Each commit is a conventional-commit-styled small unit. Do not batch unrelated commits.

1. **Bootstrap + pre-flight checks.** Run `bin/bootstrap-worktree`; confirm `make check` passes on the tip of `formalize/2-copy-lemma` with M1 (and M1.5 via its base branch) in place. Then, *before writing any module code*, run three pre-flight experiments in a scratch `.lean` file (delete after):

    1. **Universe experiment.** Write an `example` that applies `condIndep_copies` to `⟨X, Y⟩ : Ω → Fin 2 × Fin 2` with shared `⟨Z, U⟩ : Ω → Fin 2 × Fin 2`. Confirm it elaborates without universe errors at the default universe level. This flushes out Risk §7.1 at zero cost before scaffolding lands.
    1. **PFR Shannon-primitive grep.** Confirm `mutualInfo_eq_entropy_sub_condEntropy` (Basic.lean:827), `condMutualInfo_eq` (Basic.lean:941), `condMutualInfo_eq_zero` (Basic.lean:1042), `IdentDistrib.condEntropy_eq` (Basic.lean:586), and `IdentDistrib.mutualInfo_eq` (Basic.lean:691) all exist at the currently-pinned PFR revision. These are the primitives `delta_of_condMI_vanishes_eq` and the transport helper rely on; their absence (due to PFR API churn since the plan was written) is the only way the plan's proof sketches would break.
    1. **Pair-repacking experiment.** Write an `example` proving `(fun ω : Ω => (f ω).1) = Prod.fst ∘ f` and `(fun ω => ((f ω).1, (f ω).2)) = f` for a generic `f : Ω → α × β`, and confirm the one-line `funext` + `Prod.mk.eta` rewrite closes both. This validates the budget in Risk §7.4.

    Halt on any failure; investigate before writing new module code.

1. **Scaffold `ZhangYeung/CopyLemma.lean` with module docstring, imports, and `copyLemma` stubbed with `sorry`.** Wire `ZhangYeung.lean` to re-export the new module. Confirm `lake build ZhangYeung.CopyLemma` and `lake build ZhangYeung` both compile. Commit as `feat: scaffold copy lemma module with sorry stub`.

1. **Scaffold `ZhangYeungTest/CopyLemma.lean` with a single signature-pinning `example` for `copyLemma`.** Wire `ZhangYeungTest.lean` to import it. Confirm `lake test` passes. Commit as `test: scaffold API regression tests for copy lemma`.

1. **Land the two generic helpers.** Add `private lemma condIndepFun_comp` and `private lemma IdentDistrib.condMutualInfo_eq` inside a `section Helpers` block at the top of `CopyLemma.lean`. Each proof body is short (3-5 tactic lines). Commit as `feat(copylemma): add generic CondIndepFun.comp and IdentDistrib.condMutualInfo_eq helpers`.

1. **Prove `copyLemma` itself.** Apply `condIndep_copies` to `⟨X, Y⟩` and `⟨Z, U⟩`, then unpack and repack the output. The heavy lifting is:
    - Projecting $W_{1}, W_{2}, V$ to individual $X', Y', X_{1}, Y_{1}, Z', U'$ (six definitions via `Prod.fst ∘ Wᵢ` etc.).
    - Recasting the returned `IdentDistrib ⟨W_{i}, V⟩ ⟨⟨X, Y⟩, ⟨Z, U⟩⟩ ν μ` into `IdentDistrib ⟨Xᵢ, Yᵢ, Z', U'⟩ ⟨X, Y, Z, U⟩ ν μ` via `IdentDistrib.comp` with a measurable 4-tuple rearrangement.
    - Recasting the returned `CondIndepFun W₁ W₂ V ν` into `CondIndepFun ⟨X', Y'⟩ ⟨X₁, Y₁⟩ ⟨Z', U'⟩ ν`. Since $\langle X', Y' \rangle = W_{1}$ up to definitional equality (because $\langle \mathrm{fst} \circ W_{1}, \mathrm{snd} \circ W_{1} \rangle = W_{1}$ pointwise), this is close to `rfl`; at worst it needs one `fun_prop`-style unfolding.
    - Assembling the final existential.
    Commit as `feat(copylemma): prove main copy construction via condIndep_copies`.

1. **Land the three triple-level `IdentDistrib`s inside `section Consequences`.** One from `hFirst` (the shared $(X, Z, U) \sim (X', Z', U')$ triple) and two from `hSecond` (the $(X, Z, U) \sim (X_{1}, Z', U')$ and $(Y, Z, U) \sim (Y_{1}, Z', U')$ triples); each is a one-line `IdentDistrib.comp` with a 4-to-3 projection. Commit as `feat(copylemma): add triple IdentDistribs for projection pairs`.

1. **Land the two conditional-MI vanishing lemmas.** `copyLemma_condMI_X_Y₁_vanishes` uses `condIndepFun_comp` to project `hCond` to the `⟨X' ⟂ Y₁ | ⟨Z', U'⟩⟩` shape, then `condMutualInfo_eq_zero.mpr`. Symmetric companion for `(X', X₁)`. Commit as `feat(copylemma): prove projected conditional-independence facts`.

1. **Land `delta_of_condMI_vanishes_eq` (Lemma 2 Form A).** Pure Shannon algebra. Proof sketch: expand both sides into entropy terms via `delta_def`, `condMutualInfo_eq` (four times), `mutualInfo_def` (once); rewrite the hypothesis `I[A : D | ⟨B, C⟩ ; ν] = 0` as an entropy identity (`H[A | ⟨B, C⟩] + H[D | ⟨B, C⟩] = H[⟨A, D⟩ | ⟨B, C⟩]`); apply `entropy_comm` and `chain_rule''` to align all entropy triples to a canonical ordering; close with `linarith`. This is the highest-risk step in M2 for heartbeat budget; plan for the proof to be ~30-40 tactic lines and to potentially need a `set_option maxHeartbeats` bump (see "Risks" §7.3 and the empirically-validated split-before-bump guidance in `feedback_lean_split_before_bump.md`).

    Commit as `feat(copylemma): prove Lemma 2 as abstract Shannon identity`.

1. **Add a signature-pin test for `delta_of_condMI_vanishes_eq`.** Extend `ZhangYeungTest/CopyLemma.lean` with a single `example` restating Form A's signature verbatim. This pins the hypothesis order, the `I[A : D | ⟨B, C⟩ ; ν] = 0` shape, and the conclusion's argument order to `ZhangYeung.delta B C A D ν` against accidental drift during the Form-B / transport work in steps 10-12. Commit as `test: pin Lemma 2 Form A signature`.

1. **Land the two delta-identity Form-B corollaries.** Each instantiates `delta_of_condMI_vanishes_eq` at a specific copy-projection tuple and plugs in the vanishing-CMI lemma from step 7. One-line bodies (effectively). Commit as `feat(copylemma): specialize Lemma 2 to copy projections`.

1. **Land the two delta-transport lemmas.** Each is ~8-12 tactic lines: expand `delta_def` twice, transport the three MI terms via `IdentDistrib.mutualInfo_eq` (for the unconditional $I[Z:U]$) and `IdentDistrib.condMutualInfo_eq` (for the two conditional terms), close with `ring` or `linarith`. Commit as `feat(copylemma): prove delta transport between µ and ν`.

1. **Land the two delta-≤-mutualInfo inequality corollaries.** Three-line proofs combining the previous two lemmas with `condMutualInfo_nonneg` via `linarith`. Commit as `feat(copylemma): derive delta ≤ mutualInfo inequalities`.

1. **Expand `ZhangYeungTest/CopyLemma.lean` to cover the public API.** Steps 3 and 9 have established `example`s for `copyLemma` and `delta_of_condMI_vanishes_eq` respectively; expand to cover:
    - The signature of `copyLemma` (already there from step 3).
    - The signature of `delta_of_condMI_vanishes_eq` (already there from step 9).
    - The signature of each of the six `copyLemma_delta_*` theorems.
    - A downstream-usage `example`: given a concrete `Fin n`-valued $X, Y, Z, U$ setup, apply `copyLemma`, `obtain` the projection, apply `copyLemma_delta_le_mutualInfo_Y₁`, and conclude the compact inequality-form expected by the M1 delta scaffolding. This compile-time test catches breakage in the current M2-to-M3 workflow; if the API is refactored later, update this example in the same change.
    - One smoke test that `copyLemma_delta_le_mutualInfo_Y₁` + `copyLemma_delta_le_mutualInfo_X_X₁` together prove $2 I(Z; U) - 3 I(Z; U \mid X) - I(Z; U \mid Y) \le I[X' : Y_{1} ; \nu] + I[X' : X_{1} ; \nu]$, routed through M1's `ZhangYeung.delta_form21_iff` (or `delta_form23_of_form21_form22` for the symmetric average) rather than a raw `linarith`. This is the M1-to-M2 bridge made concrete: the M1 form-conversion lemmas package the compact `delta`-algebra shape into the paper's form (21), so the test both exercises the role M2 plays for M3's Shannon chase and verifies that the M2 inequality-form corollaries compose cleanly with M1's form-conversion machinery.

    Commit as `test: cover copy lemma API surface`.

1. **Update `CLAUDE.md` Module Layout.** Add one line pointing to `ZhangYeung/CopyLemma.lean` and one line pointing to `ZhangYeungTest/CopyLemma.lean`. Commit as `docs: document copy lemma module in CLAUDE.md`.

1. **Run `make check`.** Address any remaining lint or build issues, and cspell-update any newly-introduced tokens (likely `condIndepFun_comp`, `condMI`, `X_1`, `Y_1` if the source uses subscripted forms in docstrings). Commit any cspell / lint adjustments as `chore: address lint feedback`.

1. **Open the PR.** Title: `feat: prove the copy lemma (Zhang-Yeung 1998, §III, eqs. 44-45)`. Body links this plan and the roadmap, summarizes the three deliverables (copy structure, Lemma 2 identity, Lemma 2 inequality corollaries), and calls out the two generic helpers that may have future Mathlib interest (`condIndepFun_comp`, `IdentDistrib.condMutualInfo_eq`).

If the `delta_of_condMI_vanishes_eq` proof in step 8 sprawls past 60 lines without closing, halt and reconsider: either split into sub-lemmas (one for the 4-way Shannon expansion, one for the conditioning collapse, one for reassembly), or fall back to a direct proof on the expanded entropy terms similar to Theorem2's `theorem2_shannon_identity`.

## Open questions and known risks

### 7.1 Universe bookkeeping around `condIndep_copies` (low-moderate)

`condIndep_copies` binds $\alpha, \beta : \mathrm{Type}\, u$ at a single universe. Instantiating with $\alpha := S_{1} \times S_{2}$ and $\beta := S_{3} \times S_{4}$ requires that all four $S_{i}$ are in the same universe. M2's `copyLemma` signature therefore binds $S_{i} : \mathrm{Type}\, u$ rather than M1's $\mathrm{Type}\,*$. Expected to just work; flag at the bootstrap step (step 1) if it doesn't.

**Mitigation paths** (try in order):

1. Check that an `example` applying `condIndep_copies` to concrete `Fin n`-valued pair codomains elaborates successfully at the default universe, before writing the main theorem.
1. If instance search fails because of universe mismatch, insert explicit `ULift` wrappers at the test layer and document in the module docstring.

### 7.2 PFR vs Mathlib `CondIndepFun` form (low-moderate)

PFR defines `CondIndepFun f g h μ` by conditioning on a random variable `h : Ω → γ`; Mathlib's `CondIndepFun m' hm' f g μ` conditions on a sub-σ-algebra `m'`. The two are equivalent when `h` is measurable (via `MeasurableSpace.comap`), but Mathlib's `CondIndepFun.comp` takes the σ-algebra form and does not apply directly to the random-variable form.

**Mitigation:** write `condIndepFun_comp` for PFR's form by unfolding through `condIndepFun_iff` (Mathlib/PFR syntactic equivalence), applying Mathlib's fibrewise `IndepFun.comp` at each conditioning fibre, and repacking. The proof is ~5-8 lines and does not depend on σ-algebra ↔ random-variable bridging.

### 7.3 Heartbeat budget for `delta_of_condMI_vanishes_eq` (moderate)

Lemma 2's Shannon expansion rewrites 5 mutual informations (one unconditional, four conditional) into 13-15 entropy terms (each `I[A : B | C]` expanding to three `H[_|_]` terms; each `H[⟨A, B⟩ | C]` potentially needing `entropy_comm` alignment). The `theorem2_shannon_identity` in M1.5 is the closest precedent (18-20 entropy terms) and landed in ~30 tactic lines without a heartbeat bump after the M1.5 refactor-polish branch reduced its `maxHeartbeats = 3200000` to the default.

**Mitigation:** apply the split-before-bump lesson from `feedback_lean_split_before_bump.md`. If the proof body does not close at the default `maxHeartbeats` (200000), factor it into sub-lemmas:

1. A helper that expands the hypothesis `I[A : D | ⟨B, C⟩ ; ν] = 0` into a specific entropy identity.
1. A helper that rewrites `I[A : D] - I[A : D | B] - I[A : D | C]` as `I[A : D ; B, C] - I[A : D | B, C]` (a "four-way" identity).
1. The final close via `linarith` over the sub-lemmas.

Extraction gives order-of-magnitude heartbeat speedups (per `feedback_lean_split_before_bump.md`); tactical rewriting only shaves tens of percent.

### 7.4 Recasting `⟨fst ∘ W₁, snd ∘ W₁⟩` vs `W₁` (low)

The main-theorem step that repacks `CondIndepFun W₁ W₂ V ν` as `CondIndepFun ⟨X', Y'⟩ ⟨X₁, Y₁⟩ ⟨Z', U'⟩ ν` hinges on `⟨fst ∘ W₁, snd ∘ W₁⟩ = W₁` and similar. For `f : Ω → α × β`, `fun ω => (fst (f ω), snd (f ω))` and `f` are *pointwise* equal but not definitionally equal as Lean terms; the rewrite is `funext ω; exact (Prod.mk.eta).symm` (or equivalently `Prod.mk_fst_snd`, or `Prod.mk_fst_snd_apply`), expected to be one line per repacking. Budget three such rewrites: one each for $W_{1}, W_{2}, V$.

Mitigation if the rewrite proves awkward in context (for example, if instance synthesis fires on the unrepacked form): avoid the repacking entirely -- keep the `CondIndepFun` output statement in terms of $W_{1}, W_{2}, V$ and treat the projections as internal definitions downstream consumers unfold as needed. This is uglier but always works, and is a clean refactor target if later milestones find it worth cleaning up.

### 7.5 `IdentDistrib.condMutualInfo_eq` correctness vs generality (low)

The helper's statement is settled at the three-variable shape `IdentDistrib ⟨X, Y, Z⟩ ⟨X', Y', Z'⟩ μ μ'` → `I[X : Y | Z] = I[X' : Y' | Z']` (see "Conditional mutual information under `IdentDistrib`" above). This is exactly what the M2 delta transports consume: each transports a `condMutualInfo` conditioned on a single random variable, not on a pair.

**Mitigation if M3 needs a four-variable conditioning shape:** pack the two conditioners into a single random variable via `Measurable.prodMk` and reuse the three-variable helper unchanged. If that pattern repeats enough to warrant its own name, promote it to `ZhangYeung/Prelude.lean` when the concrete need appears -- don't pre-generalize in M2.

### 7.6 PFR API churn (low, documented)

This project treats PFR as a permanent pinned dependency (roadmap §3). M2 may surface PFR API issues -- missing lemmas, awkward signatures -- that the M1.5 KL route sidestepped. Log them; any upstream cleanup is optional follow-up work, not part of this PR.

### 7.7 Namespace pollution (low)

The `IdentDistrib.condMutualInfo_eq` helper is a candidate for later cleanup or upstreaming, but M2 does not need to decide that. Keep it `private` inside `ZhangYeung/CopyLemma.lean` for now. If another Zhang-Yeung module wants to consume it, promote it to `ZhangYeung/Prelude.lean` when that concrete need appears. `condIndepFun_comp` is in the same category.

## Verification

Per the roadmap M2 checkpoint: "compiles with all measure-theoretic side conditions discharged, and the copy-lemma test module builds cleanly." Operationally:

- `lake build ZhangYeung.CopyLemma` compiles with no warnings, no `sorry`, no `admit`.
- `lake build ZhangYeung` compiles with `ZhangYeung.lean` re-exporting `ZhangYeung.CopyLemma` cleanly.
- `lake build ZhangYeungTest.CopyLemma` compiles; the test module imports only `ZhangYeung` and not `ZhangYeung.CopyLemma` directly, exercising the public API surface.
- `lake build` and `lake test` both succeed on the default targets; CI (`.github/workflows/ci.yml`) goes green.
- `lake lint` passes (batteries linter via the `lintDriver`).
- `make check` passes in full.

**Test module contents** (`ZhangYeungTest/CopyLemma.lean`, established incrementally in sequencing steps 3, 9, and 13):

1. One `example` per public theorem restating the current signature verbatim. This is a snapshot test for the M2 branch, and catches accidental drift in hypothesis order, universe bindings, or conclusion shape while the module is under active construction. Eight such `example`s for the eight public theorems enumerated in the "Public surface" section above. If the API is intentionally refactored later, update these examples in the same change.
1. One downstream-usage `example`: given concrete `Fin n`-valued $X, Y, Z, U$ on a probability space, apply `copyLemma`, `obtain` the projections, apply `copyLemma_delta_le_mutualInfo_Y₁` to close a `delta Z U X Y μ ≤ _`. Exercises the full flow M3 will follow.
1. One Shannon-chase `example` exercising both inequality corollaries simultaneously: derive $2 I(Z; U) - 3 I(Z; U \mid X) - I(Z; U \mid Y) \le I[X' : Y_{1} ; \nu] + I[X' : X_{1} ; \nu]$ as a single `linarith` over the two copies' outputs. This is literally the first line of M3's Shannon chase, so if it doesn't type-check, the API is wrong.
1. One concrete-`Fin` smoke test for the main theorem's signature. Confirms that the `Fintype` / `MeasurableSingletonClass` / universe side conditions elaborate cleanly on concrete types.

Each `example` lives inside `namespace ZhangYeungTest` with `open ZhangYeung`, following `ZhangYeungTest/Delta.lean` and `ZhangYeungTest/Theorem2.lean`.

Land these in the same commits as the corresponding public surface (tests in step 3, Form-A signature pin in step 9, expanded tests in step 13, same branch), so `lake test` exercises the public API continuously through the milestone.

Out-of-scope for M2 (documented here so M3 can pick them up):

- No proof of Theorem 3's final inequality. The Shannon chase combining `copyLemma_delta_le_mutualInfo_Y₁` + `copyLemma_delta_le_mutualInfo_X_X₁` with the data-processing inequality and the $I[X_{1} : Y_{1}] = I[X : Y]$ transport is M3's core work.
- No data-processing inequality for conditional mutual information under a Markov chain (needed by M3's step $I[X : \langle X_{1}, Y_{1} \rangle ; \nu] \le I[X : \langle Z', U' \rangle ; \nu]$). PFR does not currently expose this as a named lemma; if M3 finds the natural derivation awkward, that derivation lives in M3, not M2.
- No `IdentDistrib` helpers beyond the one conditional-MI transport that Lemma 2's proof actually requires. Further transports (for example, transport of $I[X : \langle X_{1}, Y_{1} \rangle]$ across the two-copy distinction) land in M3 when and if M3 needs them.
- No notation macro for the copy construction.

## Critical files

**This milestone:**

- `ZhangYeung/CopyLemma.lean` (new).
- `ZhangYeungTest/CopyLemma.lean` (new).
- `ZhangYeung.lean` (modified, add one `import` line).
- `ZhangYeungTest.lean` (modified, add one `import` line).
- `CLAUDE.md` (modified, two-line addition under "Module Layout").

**Read-only references:**

- `ZhangYeung/Delta.lean` (M1 output; `ZhangYeung.delta` definition and form-conversion lemmas).
- `ZhangYeung/Prelude.lean` (M0 output; entropy API import surface).
- `ZhangYeung/Theorem2.lean` (M1.5 output; structural precedent for module layout, variable blocks, and the `IdentDistrib` transport pattern that the `condMutualInfo` helper extends).
- `references/transcriptions/zhangyeung1998.md` (paper transcription; equations 44-45 on lines 645-678, proof of Lemma 2 on lines 664-678, application to Theorem 3 on lines 680-709).
- `.lake/packages/pfr/PFR/ForMathlib/ConditionalIndependence.lean` (`condIndep_copies` at line 135, `CondIndepFun` at line 104, `condIndepFun_iff` at line 108, `CondIndepFun.comp_right` at line 114).
- `.lake/packages/pfr/PFR/ForMathlib/Entropy/Basic.lean` (`IdentDistrib.entropy_congr` at line 77, `IdentDistrib.condEntropy_eq` at line 586, `IdentDistrib.mutualInfo_eq` at line 691, `condMutualInfo_eq` at line 941, `condMutualInfo_eq_zero` at line 1042, `condMutualInfo_nonneg` at line 924, `condMutualInfo_comm` at line 933).
- `.lake/packages/mathlib/Mathlib/Probability/IdentDistrib.lean` (`IdentDistrib`, `IdentDistrib.comp`, `IdentDistrib.symm`).
- `.lake/packages/mathlib/Mathlib/Probability/Independence/Basic.lean` (`IndepFun.comp` at line 799, the target-side post-composition lemma that `condIndepFun_comp` dispatches to fibrewise).

Reference: the `write-lean-code` skill is authoritative for Lean naming and proof style; the `write-math` skill governs the module docstring and any mathematical prose inside comments; the `write-pandoc-markdown` skill governs this plan document.
