---
title: "M1.5: Theorem 2 Conditional Warm-Up"
created: 2026-04-16
branch: formalize/1.5-theorem-2
roadmap: docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md
milestone: M1.5
depends_on: M1 (`ZhangYeung/Delta.lean`, merged into `main` via PR #4)
---

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
- `IdentDistrib.entropy_congr`, `IdentDistrib.mutualInfo_eq`: transport entropy/mutualInfo across an `IdentDistrib` pair. The conditional-mutual-information analogue is not published under a stable name; if needed, derive it in-file via the entropy and chain-rule versions (see "Risks" §7.3 below).

**Kernel composition (Mathlib, `Mathlib.Probability.Kernel`):**

- `Kernel.compProd` / `κ ⊗ₖ η` (`Kernel α β → Kernel (α × β) γ → Kernel α (β × γ)`).
- `MeasureTheory.Measure.compProd` / `μ ⊗ₘ κ` (`Measure α → Kernel α β → Measure (α × β)`).
- `Measure.fst_compProd : (μ ⊗ₘ κ).map Prod.fst = μ` under `[SFinite μ] [IsMarkovKernel κ]`.
- `condDistrib : (Ω → β) → (Ω → α) → Measure Ω → Kernel α β` under `[IsFiniteMeasure μ]` and `[StandardBorelSpace β] [Nonempty β]` at use sites.
- `compProd_map_condDistrib : (μ.map X) ⊗ₘ condDistrib Y X μ = μ.map (fun a ↦ (X a, Y a))`.
- `condDistrib_comp_map : condDistrib Y X μ ∘ₘ (μ.map X) = μ.map Y`.

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

1. **Marginal equality.** Some tuple that includes $W$ has the same distribution on the extended space as a corresponding tuple that includes the $W$-analogue does on the original space; equivalently, there is an `IdentDistrib` pair that transports entropy/mutual-information terms between the two sides.
1. **Conditional independence.** $W$ is conditionally independent of some subset of $\{X, Y, Z, U\}$ given another subset, in a way that translates (via `condMutualInfo_eq_zero`) into a zero conditional mutual information term usable inside the Shannon-inequality chase.

The chase that follows --- built from Shannon-type identities, `condMutualInfo_nonneg`, the two hypotheses `I[X : Y ; μ] = 0` and `I[X : Y | Z ; μ] = 0`, and the two facts above --- should discharge the target inequality (17) with `linarith` as the last tactic.

The paper does not spell out the construction; neither does the 1998 transcription. Two candidate constructions cover the natural single-copy degenerations of M3's two-copy $q(x, y, z, u, x_1, y_1) := p(x, y, z, u) \, p(x_1, y_1 \mid z, u)$. Pick one at step 3 of the sequencing below; if the chase does not close under the chosen construction, fall back to the other.

### Candidate A: copy of $Y$ given $(Z, U)$

Define $q(x, y, z, u, y_1) := p(x, y, z, u) \, p(y_1 \mid z, u)$. Under $q$:

- **Marginal equality:** the $(Y_1, Z, U)$ marginal equals the $(Y, Z, U)$ marginal.
- **Conditional independence:** $Y_1 \perp (X, Y) \mid (Z, U)$; in particular $I(Y ; Y_1 \mid Z, U) = I(X ; Y_1 \mid Z, U) = 0$.

Lean construction (sketch):

```lean
-- extended sample space Ω × S₂
-- (S₂ is the codomain of Y)
let κ : Kernel (S₃ × S₄) S₂ := condDistrib Y (fun ω => (Z ω, U ω)) μ
let ν : Measure (Ω × S₂) := μ ⊗ₘ Kernel.comap κ (fun ω => (Z ω, U ω))
```

Advantages: the needed marginal and conditional-independence facts fall out directly from `compProd_map_condDistrib` and the kernel-compose lemmas.

Disadvantages: the target inequality (17) does not obviously dissolve after plugging the $Y_1$-based facts in. The chase requires at least one creative step beyond the identities that the construction immediately supplies.

### Candidate B: copy of $X$ given $(Z, U)$

Symmetric to Candidate A: $q(x, y, z, u, x_1) := p(x, y, z, u) \, p(x_1 \mid z, u)$. Gives $(X_1, Z, U)$ marginal equal to $(X, Z, U)$, and $X_1 \perp (X, Y) \mid (Z, U)$.

### Recommended first attempt

**Start with Candidate A.** It is the more natural degeneration of M3's $y_1$ half, and the Shannon chase that M3 runs after Lemma 2 already uses $I(X ; Y_1 \mid Z, U) = 0$ as an input; M1.5's chase can plausibly reuse part of that skeleton. If after two to three hours of attempting the chase the chosen construction does not close the inequality, switch to Candidate B and document the reason in a commit message.

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
- **`IsProbabilityMeasure`.** Required for `condMutualInfo_eq_zero` and the `condDistrib` identities. The hypothesis is explicit so the theorem is usable off the default measure.
- **Variable sort.** `S₁, S₂, S₃, S₄` carry `(X, Y, Z, U)` here; `Delta.lean` uses the same `S₁ .. S₄` names for `(Z, U, X, Y)`. Keep them module-local; no cross-module variable reuse, so the naming clash across modules is harmless.

### Lemma-level skeleton

Inside `Theorem2.lean`, the proof decomposes naturally into four private-ish building blocks. Use `private` or `section`-scoped `lemma`s --- not `theorem`s --- so only `theorem2` is exported.

1. **`aux_measure` (private).** The extended measure $\nu := \mu \otimes_m (\kappa \circ \pi)$ where $\kappa := \mathrm{condDistrib}\, Y \, \langle Z, U\rangle\, \mu$ and $\pi : \Omega \to S_3 \times S_4$ is the $(Z, U)$ projection. Bundle the `Nonempty`/`StandardBorelSpace` side conditions on `S₂` at this lemma; propagate to downstream building blocks only if needed.
1. **`aux_identDistrib` (private).** The `IdentDistrib` facts the chase needs: $(Y_1, Z, U)$ under $\nu$ is identically distributed to $(Y, Z, U)$ under $\mu$, and $(X, Z, U)$ under $\nu$ (viewing $X$ pulled back through $\mathrm{fst}$) is identically distributed to $(X, Z, U)$ under $\mu$. Transport to the required information-identity lemmas using `IdentDistrib.mutualInfo_eq` and the conditional-mutual-information analogue.
1. **`aux_condIndep` (private).** $I[X : Y_1 \mid \langle Z, U\rangle ; \nu] = 0$, via the `condMutualInfo_eq_zero`/`CondIndepFun` bridge applied to the kernel-level construction.
1. **`theorem2`.** The Shannon-inequality chase: start from the hypotheses and the auxiliary facts, apply Shannon basics (`chain_rule`, submodularity, nonnegativity), close with `linarith`.

The total proof is expected to be roughly 60-120 lines. If it runs to 200+, stop and reconsider whether the chosen construction is the right one.

## Sequencing inside M1.5

1. **Bootstrap verification.** Run `bin/bootstrap-worktree`; confirm `make check` passes on the tip of `formalize/1.5-theorem-2` with M1 in place. Halt on any failure; investigate before writing new code.
1. **Create `ZhangYeung/Theorem2.lean` with module docstring and imports.** Imports are: `ZhangYeung.Prelude`, `Mathlib.Probability.Kernel.CondDistrib`, `Mathlib.Probability.IdentDistrib`, `PFR.ForMathlib.ConditionalIndependence`. Add the shared `variable` block with the finite-alphabet assumptions. Stub `theorem theorem2` with `sorry`. Confirm the file compiles --- this proves the signature, the variable block, and the imports are internally consistent before any real proof work.
1. **Commit the skeleton** as `feat: scaffold theorem 2 module with sorry stub`.
1. **Resolve the `StandardBorelSpace`/`Nonempty` question on Fintype codomains.** Write a one-line example or `by exact?` probe to confirm Mathlib provides (or does not provide) a `StandardBorelSpace` instance for a `Fintype` codomain with `MeasurableSingletonClass` and the default discrete `MeasurableSpace`. If it does, proceed. If not, pick the fallback (see "Risks" §7.1).
1. **Pick a construction (A or B above)**; open a short note in-file documenting the choice. Proceed with Candidate A unless step 4's outcome forces B.
1. **Land `aux_measure`.** Define the extended measure and prove it is a probability measure (required for `condMutualInfo_eq_zero` downstream). Expect this to use `Measure.compProd` properties plus `IsMarkovKernel`-ness of `condDistrib`.
1. **Land `aux_identDistrib`.** Prove the two `IdentDistrib` facts directly via `compProd_map_condDistrib` and `Measure.map` manipulation; transport them to `I[... ; ν] = I[... ; μ]` identities via `IdentDistrib.mutualInfo_eq`. Keep conditional-mutual-info transport in-file if PFR does not expose it; see "Risks" §7.3.
1. **Land `aux_condIndep`.** Prove `I[X : Y₁ | ⟨Z, U⟩ ; ν] = 0` by going through `condMutualInfo_eq_zero` and the structural conditional-independence of the copied variable.
1. **Land `theorem2`.** Run the Shannon chase. The two hypothesis equalities become `IndepFun X Y μ` and `CondIndepFun X Y Z μ` via the `... _eq_zero` iffs, and those in turn give Shannon identities (for instance, the unconditional `I[X : Y ; μ] = 0` gives `H[⟨X, Y⟩ ; μ] = H[X ; μ] + H[Y ; μ]`). Combine with the auxiliary facts, close with `linarith`. If the chase does not close, backtrack to step 5 and try Candidate B.
1. **Commit the core proof** as `feat: prove Theorem 2 (Zhang-Yeung 1997 conditional inequality)`.
1. **Add `ZhangYeungTest/Theorem2.lean`** with API regression tests (see Verification §8 below). Commit as `test: add API regression tests for theorem 2`.
1. **Update `ZhangYeung.lean`** to re-export `ZhangYeung.Theorem2`, and **`ZhangYeungTest.lean`** to re-export the matching test module. Commit as `chore: wire theorem 2 into entrypoints`.
1. **Update `CLAUDE.md`'s Module Layout section** with a one-line entry for `ZhangYeung/Theorem2.lean` and its test. Commit as `docs: document theorem 2 module in CLAUDE.md`.
1. **Run `make check`.** Fix any lint or build failures before opening the PR.
1. **Open the PR.** Title `feat: prove Theorem 2 (Zhang-Yeung 1997 conditional warm-up)`; body links this plan and the roadmap.

Commit at each numbered step; keep commits small and conventional-commit-styled.

## Open questions and known risks

### 7.1: `StandardBorelSpace` on Fintype codomains (moderate)

`condDistrib` requires `[StandardBorelSpace β] [Nonempty β]` on the codomain of the variable being copied. Mathlib provides `StandardBorelSpace` for standard concrete types (`ℝ`, `PolishSpace` + `BorelSpace`, etc.) but it is not immediately obvious whether the default discrete `MeasurableSpace` on a `Fintype` type carries a `StandardBorelSpace` instance.

**Mitigation paths** (try in order):

1. `by exact?`/`Lean.Elab` probe: does `[Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]` already imply `StandardBorelSpace α` in Mathlib?
1. If not, look for `Mathlib.MeasureTheory.Constructions.BorelSpace.Basic` or `Mathlib.Topology.MetricSpace.Polish` entries that bridge discrete Fintype types.
1. If still not, fall back to `ProbabilityTheory.condKernelCountable` or an explicit PMF-based single-copy construction that bypasses `condDistrib` entirely. For Fintype codomains, `PMF.bind` plus `PMF.toMeasure` is a clean alternative, and PFR has precedent for `PMF`-level constructions elsewhere.

Budget up to half a day for this; if unresolved, park M1.5 and escalate rather than forcing `sorry`s.

### 7.2: Hypothesis form, equational vs. independence (low)

PFR's `mutualInfo_eq_zero` and `condMutualInfo_eq_zero` require `[IsZeroOrProbabilityMeasure μ]`, `[FiniteRange ...]`, and measurability. All of these follow from the module-level instances plus the explicit `hX, hY, hZ, hU` measurability. No action needed beyond keeping those instance arguments in scope.

If converting hypotheses via these iffs becomes verbose in practice, introduce a one-line private helper lemma at the top of `Theorem2.lean` that packages the conversion.

### 7.3: Conditional-mutual-info transport under `IdentDistrib` (moderate)

PFR exposes `IdentDistrib.entropy_congr` and `IdentDistrib.mutualInfo_eq`, but a dedicated conditional analogue `IdentDistrib (⟨X, Z⟩, ⟨Y, Z⟩) ... → I[X : Y | Z ; μ] = I[X' : Y' | Z' ; ν]` may not be published under a stable name. Options, in descending order of preference:

1. **Find it in PFR.** Grep `condMutualInfo`/`condEntropy` congruence lemmas; PFR is active enough that such a lemma likely exists under a slightly different name.
1. **Derive it in-file.** Expand `condMutualInfo` via `condMutualInfo_eq` (which PFR exposes --- see `Delta.lean`'s `delta_eq_entropy` for precedent), then apply `IdentDistrib.entropy_congr` to each summand and reassemble. This is approximately ten lines.
1. **Specialize to what M1.5 actually needs.** If only one shape of transport is required, a direct proof against that shape can be shorter than a general lemma.

Prefer option 2 if option 1 fails: it keeps the chase local and avoids introducing a public lemma that belongs in Mathlib.

### 7.4: Picking the right single-copy construction (moderate)

Candidate A may not close the chase; Candidate B may not either. If both fail, the fallback is a non-degenerate variation (for example, $q(x, y, z, u, u_1) := p(x, y, z, u) \, p(u_1 \mid y, z)$ --- a copy of $U$ given $(Y, Z)$). The 1997 paper's proof used *some* single-variable auxiliary, and the chase is known to close; it is a question of finding the right shape.

If after a full day of searching the chase still does not close under any of these, escalate: either the cited `[39]` proof used a structurally different technique (not a copy) or there is a bookkeeping bug in the construction. In that case, consult [39] directly before continuing.

### 7.5: `condDistrib` and probability-measure preservation (low)

`μ ⊗ₘ condDistrib Y X μ = μ.map (fun ω ↦ (X ω, Y ω))` (lemma `compProd_map_condDistrib`). When we extend this to $\mu \otimes_m (\kappa \circ \pi)$ where $\pi$ is a measurable projection, the resulting measure is a probability measure on $\Omega \times S_W$ and its first marginal is $\mu$. Both facts are required for the chase and should fall out directly from Mathlib's `IsMarkovKernel`/`IsProbabilityMeasure` instance chains, but confirm them early rather than assuming.

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
1. One `example` showing the $X \leftrightarrow Y$ symmetry at the hypothesis level: given both `I[X : Y ; μ] = 0` hypotheses, the conclusion can be obtained from `theorem2` applied once. No new theorem is introduced --- the example just exercises the public API under hypothesis permutation.
1. One downstream API usage: derive a *Shannon-inequality* corollary that uses `theorem2` as a black box input. For example, given the same hypotheses plus `I[Z : U | X, Y ; μ] = 0` (so the auxiliary RHS term vanishes), conclude `I[X : Y | ⟨Z, U⟩ ; μ] ≤ I[X : Y | U ; μ]`. Close with `linarith` after `theorem2` plus `condMutualInfo_nonneg`.
1. One compile-time check that the theorem statement type-checks with concrete `Fin n` codomains --- smoke test that the `Fintype`/`MeasurableSingletonClass` side conditions are supplied by the default instances.

Each `example` lives inside `namespace ZhangYeungTest` with `open ZhangYeung`, following the pattern `ZhangYeungTest/Delta.lean` established.

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
- `.lake/packages/mathlib/Mathlib/Probability/Kernel/CondDistrib.lean` (condDistrib, `compProd_map_condDistrib`).
- `.lake/packages/mathlib/Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean` (`μ ⊗ₘ κ`, `fst_compProd`).
- `.lake/packages/mathlib/Mathlib/Probability/IdentDistrib.lean` (IdentDistrib, `.comp`, `.symm`).

Reference: the `write-lean-code` skill is authoritative for Lean naming and proof style; the `write-math` skill governs the module docstring and any mathematical prose inside comments; the `write-pandoc-markdown` skill governs this plan document.
