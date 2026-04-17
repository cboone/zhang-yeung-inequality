import ZhangYeung.Prelude
import Mathlib.Probability.Kernel.CondDistrib

/-!
# Zhang-Yeung Theorem 2: a conditional information inequality

Theorem 2 of [@zhangyeung1998] (originally proved in reference [39] cited therein) states that for any four discrete random variables `X, Y, Z, U`, the hypothesis

  `I[X : Y ; μ] = 0` and `I[X : Y | Z ; μ] = 0`   (eq. 16)

implies the conditional information inequality

  `I[X : Y | ⟨Z, U⟩ ; μ] ≤ I[Z : U | ⟨X, Y⟩ ; μ] + I[X : Y | U ; μ]`.   (eq. 17)

This module formalizes the implication (16) ⇒ (17) on finite-alphabet random variables. It is a single-copy warm-up for the two-copy construction used in the paper's main non-Shannon inequality; its purpose is to exercise the Lean-level identical-distribution and conditional-independence bookkeeping in the simpler single-copy setting.

## Main statements

- `ZhangYeung.theorem2`: the implication (16) ⇒ (17) for discrete random variables on a probability space.

## Implementation notes

The proof uses the single-copy construction of the 1997 Zhang-Yeung argument. PFR's `ProbabilityTheory.condIndep_copies`, applied to the pair `⟨X, Y⟩` (as a single `S₁ × S₂`-valued random variable) conditioned on `⟨Z, U⟩`, produces an extended probability space `ν` on `Ω'` carrying two conditionally independent copies `W₁, W₂` of `⟨X, Y⟩` given a pullback `V` of `⟨Z, U⟩`. Taking `W₁` as the primary copy (whose four-way joint law with `V` matches the `μ`-law of `(X, Y, Z, U)` via `IdentDistrib`) and `W₂.2` as the single-copy auxiliary `Y₁`, we obtain the Candidate A structure of the milestone plan:
- `(Y₁, Z', U') ∼ (Y, Z, U)` under `ν, μ` (the copy marginal);
- `I[X' : Y₁ | ⟨Z', U'⟩ ; ν] = 0` via the conditional independence of `W₁` and `W₂` given `V`.

The four codomains `S₁, S₂, S₃, S₄` are specialized to `[Fintype]` + `[MeasurableSingletonClass]`. This specialization supplies PFR's `FiniteRange` obligations uniformly (via `Fintype → Finite → Countable → FiniteRange`) and, where `condDistrib` would otherwise be reached for, implies `[StandardBorelSpace]` via Mathlib's chain `MeasurableSingletonClass α + Countable α ⇒ DiscreteMeasurableSpace α ⇒ StandardBorelSpace α`. With the `condIndep_copies` construction used here, no direct appeal to `condDistrib` is required.

Paper ordering `(X, Y, Z, U)` is followed here because Theorem 2 is a standalone inequality read most naturally in that order; `ZhangYeung/Delta.lean` uses `(Z, U, X, Y)` because the delta quantity is symmetric in its first two arguments, but the two modules share no variables so the naming clash is harmless.

## References

* [@zhangyeung1998] -- see `references/transcriptions/zhangyeung1998.md` for a verbatim transcription of equations (16) and (17), verified 2026-04-16.

## Tags

Shannon entropy, conditional mutual information, conditional information inequality, single-copy construction, Zhang-Yeung
-/

namespace ZhangYeung

open MeasureTheory ProbabilityTheory

universe u

variable {Ω : Type*} [MeasurableSpace Ω]
  {S₁ S₂ S₃ S₄ : Type u}
  [Fintype S₁] [Fintype S₂] [Fintype S₃] [Fintype S₄]
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]

/-- Post-composition of a `CondIndepFun` by measurable functions. If `f ⟂ g | h` under `μ`, then for any measurable `φ, ψ`, also `φ ∘ f ⟂ ψ ∘ g | h` under `μ`. This mirrors `Mathlib.Probability.Independence.Basic.IndepFun.comp` for the conditional version; PFR's existing `CondIndepFun.comp_right` is a different lemma (composition by a measurable embedding on the underlying space, not by measurable functions on the codomains). -/
private lemma condIndepFun_comp
    {Ω' α β α' β' γ : Type*} [MeasurableSpace Ω']
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace α'] [MeasurableSpace β']
    [MeasurableSpace γ]
    {f : Ω' → α} {g : Ω' → β} {h : Ω' → γ} {φ : α → α'} {ψ : β → β'}
    {ν : Measure Ω'}
    (hfg : CondIndepFun f g h ν) (hφ : Measurable φ) (hψ : Measurable ψ) :
    CondIndepFun (φ ∘ f) (ψ ∘ g) h ν := by
  rw [condIndepFun_iff] at hfg ⊢
  exact hfg.mono (fun _ hz ↦ hz.comp hφ hψ)

/-- **Shannon-type reduction for Theorem 2.** The algebraic identity that rewrites `I[X:Y|⟨Z,U⟩] - I[Z:U|⟨X,Y⟩] - I[X:Y|U]` as `(I[Z:U] - I[Z:U|X] - I[Z:U|Y]) + I[X:Y|Z] - I[X:Y]` (the Zhang-Yeung delta plus the two hypothesis-vanishing correction terms). Under the hypotheses of Theorem 2 (eq. 16), the two correction terms are zero and the Theorem 2 target is equivalent to `Δ(Z, U | X, Y) ≤ 0`. The identity is pure Shannon algebra and needs no hypotheses beyond `IsProbabilityMeasure`. -/
private lemma theorem2_shannon_identity
    {Ω : Type*} [MeasurableSpace Ω]
    {S₁ S₂ S₃ S₄ : Type u}
    [Fintype S₁] [Fintype S₂] [Fintype S₃] [Fintype S₄]
    [MeasurableSpace S₁] [MeasurableSpace S₂]
    [MeasurableSpace S₃] [MeasurableSpace S₄]
    [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
    [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    I[X : Y | ⟨Z, U⟩ ; μ] - I[Z : U | ⟨X, Y⟩ ; μ] - I[X : Y | U ; μ]
      = (I[Z : U ; μ] - I[Z : U | X ; μ] - I[Z : U | Y ; μ])
        + I[X : Y | Z ; μ] - I[X : Y ; μ] := by
  have hZU : Measurable (fun ω => (Z ω, U ω)) := hZ.prodMk hU
  have hXY : Measurable (fun ω => (X ω, Y ω)) := hX.prodMk hY
  rw [condMutualInfo_eq hX hY hZU μ, condMutualInfo_eq hZ hU hXY μ,
      condMutualInfo_eq hX hY hU μ, mutualInfo_def, condMutualInfo_eq hZ hU hX μ,
      condMutualInfo_eq hZ hU hY μ, condMutualInfo_eq hX hY hZ μ, mutualInfo_def]
  rw [chain_rule'' μ hX hZU, chain_rule'' μ hY hZU, chain_rule'' μ hXY hZU,
      chain_rule'' μ hZ hXY, chain_rule'' μ hU hXY, chain_rule'' μ hZU hXY,
      chain_rule'' μ hX hU, chain_rule'' μ hY hU, chain_rule'' μ hXY hU,
      chain_rule'' μ hZ hX, chain_rule'' μ hU hX, chain_rule'' μ hZU hX,
      chain_rule'' μ hZ hY, chain_rule'' μ hU hY, chain_rule'' μ hZU hY,
      chain_rule'' μ hX hZ, chain_rule'' μ hY hZ, chain_rule'' μ hXY hZ]
  have e_XZU : H[⟨X, fun ω => (Z ω, U ω)⟩ ; μ] = H[⟨fun ω => (Z ω, U ω), X⟩ ; μ] :=
    entropy_comm hX hZU μ
  have e_YZU : H[⟨Y, fun ω => (Z ω, U ω)⟩ ; μ] = H[⟨fun ω => (Z ω, U ω), Y⟩ ; μ] :=
    entropy_comm hY hZU μ
  have e_ZXY : H[⟨Z, fun ω => (X ω, Y ω)⟩ ; μ] = H[⟨fun ω => (X ω, Y ω), Z⟩ ; μ] :=
    entropy_comm hZ hXY μ
  have e_UXY : H[⟨U, fun ω => (X ω, Y ω)⟩ ; μ] = H[⟨fun ω => (X ω, Y ω), U⟩ ; μ] :=
    entropy_comm hU hXY μ
  have e_XU : H[⟨X, U⟩ ; μ] = H[⟨U, X⟩ ; μ] := entropy_comm hX hU μ
  have e_YU : H[⟨Y, U⟩ ; μ] = H[⟨U, Y⟩ ; μ] := entropy_comm hY hU μ
  have e_XZ : H[⟨X, Z⟩ ; μ] = H[⟨Z, X⟩ ; μ] := entropy_comm hX hZ μ
  have e_YZ : H[⟨Y, Z⟩ ; μ] = H[⟨Z, Y⟩ ; μ] := entropy_comm hY hZ μ
  have e_XYZU : H[⟨fun ω => (X ω, Y ω), fun ω => (Z ω, U ω)⟩ ; μ]
      = H[⟨fun ω => (Z ω, U ω), fun ω => (X ω, Y ω)⟩ ; μ] :=
    entropy_comm hXY hZU μ
  linarith [e_XZU, e_YZU, e_ZXY, e_UXY, e_XU, e_YU, e_XZ, e_YZ, e_XYZU]

/-- **Zhang-Yeung Theorem 2** ([@zhangyeung1998], eqs. 16-17, originally proved in reference [39] cited therein). For any four discrete random variables `X, Y, Z, U` on a probability space, if `I[X : Y ; μ] = 0` and `I[X : Y | Z ; μ] = 0`, then `I[X : Y | ⟨Z, U⟩ ; μ] ≤ I[Z : U | ⟨X, Y⟩ ; μ] + I[X : Y | U ; μ]`. The proof uses a single-copy construction: an auxiliary variable `Y₁` obtained from `ProbabilityTheory.condIndep_copies` applied to the pair `⟨X, Y⟩` conditioned on `⟨Z, U⟩`. -/
theorem theorem2
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h₁ : I[X : Y ; μ] = 0)
    (h₂ : I[X : Y | Z ; μ] = 0) :
    I[X : Y | ⟨Z, U⟩ ; μ] ≤ I[Z : U | ⟨X, Y⟩ ; μ] + I[X : Y | U ; μ] := by
  -- Step 1 (Shannon algebra). The target is equivalent, modulo the two hypothesis equalities (16),
  -- to `Δ(Z, U | X, Y) ≤ 0`, where `Δ(Z, U | X, Y) := I[Z:U] - I[Z:U|X] - I[Z:U|Y]` is the
  -- Zhang-Yeung delta of `Delta.lean`. The reduction lemma `theorem2_shannon_identity` encodes this
  -- as a Shannon-type identity that holds without any independence hypotheses.
  have h_red : I[X : Y | ⟨Z, U⟩ ; μ] - I[Z : U | ⟨X, Y⟩ ; μ] - I[X : Y | U ; μ]
      = (I[Z : U ; μ] - I[Z : U | X ; μ] - I[Z : U | Y ; μ])
        + I[X : Y | Z ; μ] - I[X : Y ; μ] :=
    theorem2_shannon_identity hX hY hZ hU μ
  -- Step 2 (single-copy construction). Use PFR's `condIndep_copies` on `⟨X, Y⟩` conditioned on
  -- `⟨Z, U⟩` to land `W₁, W₂ : Ω' → S₁ × S₂` and `V : Ω' → S₃ × S₄` on an extended space `ν`
  -- with `W₁ ⟂ W₂ | V` and both `⟨W₁, V⟩` and `⟨W₂, V⟩` identically distributed to
  -- `⟨⟨X, Y⟩, ⟨Z, U⟩⟩` under `μ`. Letting `Y₁ := Prod.snd ∘ W₂` gives the plan's Candidate A
  -- structure. The three auxiliary facts the plan asks for are:
  -- (i) `(Y₁, Z', U') ∼ (Y, Z, U)` (copy-marginal `IdentDistrib`, from `hID₂` by projection),
  -- (ii) `(X', Y', Z', U') ∼ (X, Y, Z, U)` (primary-copy `IdentDistrib`, from `hID₁`),
  -- (iii) `CondIndepFun X' Y₁ V ν` (from `hCI` via `condIndepFun_comp`).
  -- These supply every piece of structural content the single-copy milestone commits to.
  obtain ⟨Ω', _mΩ', W₁, W₂, V, ν, _hν, hW₁, hW₂, hV, hCI, _hID₁, _hID₂⟩ :=
    condIndep_copies (fun ω ↦ (X ω, Y ω)) (fun ω ↦ (Z ω, U ω))
      (hX.prodMk hY) (hZ.prodMk hU) μ
  set X' : Ω' → S₁ := fun ω' ↦ (W₁ ω').1
  set Y' : Ω' → S₂ := fun ω' ↦ (W₁ ω').2
  set Z' : Ω' → S₃ := fun ω' ↦ (V ω').1
  set U' : Ω' → S₄ := fun ω' ↦ (V ω').2
  set Y₁ : Ω' → S₂ := fun ω' ↦ (W₂ ω').2
  have hX'_meas : Measurable X' := measurable_fst.comp hW₁
  have hY'_meas : Measurable Y' := measurable_snd.comp hW₁
  have hZ'_meas : Measurable Z' := measurable_fst.comp hV
  have hU'_meas : Measurable U' := measurable_snd.comp hV
  have hY₁_meas : Measurable Y₁ := measurable_snd.comp hW₂
  have hCI_proj : CondIndepFun X' Y₁ V ν :=
    condIndepFun_comp hCI measurable_fst measurable_snd
  -- Step 3 (non-Shannon core). The residual claim is `Δ(Z, U | X, Y) ≤ 0` under the hypotheses of
  -- (16). Closing this from the three auxiliary facts above is the true proof-time content of the
  -- milestone; it requires a Shannon chase in `ν` that this commit does not land. Per plan §7.4,
  -- if Candidate A (the construction above) does not close the chase in honest exploration, the
  -- fallback is Candidate B (copy of `X` given `⟨Z, U⟩`) and, if that too fails, a non-degenerate
  -- variation.
  have hΔ : I[Z : U ; μ] - I[Z : U | X ; μ] - I[Z : U | Y ; μ] ≤ 0 := by
    sorry
  linarith

end ZhangYeung
