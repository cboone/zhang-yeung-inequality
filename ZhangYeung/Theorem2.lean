import ZhangYeung.Delta
import ZhangYeung.Prelude

/-!
# Zhang-Yeung Theorem 2: a conditional information inequality

Theorem 2 of [@zhangyeung1998], originally proved as Theorem 3 of [@zhangyeung1997], states that for any four discrete random variables `X, Y, Z, U`, the hypothesis

  `I[X : Y ; μ] = 0` and `I[X : Y | Z ; μ] = 0`   (eq. 16)

implies the conditional information inequality

  `I[X : Y | ⟨Z, U⟩ ; μ] ≤ I[Z : U | ⟨X, Y⟩ ; μ] + I[X : Y | U ; μ]`.   (eq. 17)

This module formalizes the implication (16) ⇒ (17) on finite-alphabet random variables. It is a single-auxiliary-distribution warm-up for the two-copy construction used in the paper's main non-Shannon inequality; its purpose is to land the Shannon-algebra reduction and the non-Shannon-type core lemma in Lean before M2/M3's two-copy `condIndep_copies` bookkeeping comes due.

## Main statements

- `ZhangYeung.theorem2`: the implication (16) ⇒ (17) for discrete random variables on a probability space.

## Implementation notes

The proof has two structurally distinct layers. The first is a Shannon-type algebraic identity (`theorem2_shannon_identity`) that rewrites `I[X:Y|⟨Z,U⟩] - I[Z:U|⟨X,Y⟩] - I[X:Y|U]` as `Δ(Z, U | X, Y) + I[X:Y|Z] - I[X:Y]`, where `Δ` is `ZhangYeung.delta` from the M1 module. Under (16) the two correction terms `I[X:Y|Z]` and `I[X:Y]` vanish, so Theorem 2 reduces to `Δ(Z, U | X, Y) ≤ 0`. The identity is pure Shannon algebra and needs no hypotheses beyond `IsProbabilityMeasure`.

The second layer (`theorem2_delta_le_zero`) discharges the reduced inequality via the [@zhangyeung1997] argument: construct two auxiliary *probability distributions* on `S₁ × S₂ × S₃ × S₄`,

  `p̃(x, y, z, u) := p(x, z, u) p(y, z, u) / p(z, u)`
  `p̂(x, y, z, u) := p(x, z) p(x, u) p(y, z) p(y, u) / [p(z) p(u) p(x) p(y)]`

(both vanishing on the appropriate zero-measure diagonals). Both sum to one -- `p̃` unconditionally, `p̂` by way of the two hypotheses `I[X:Y] = 0` and `I[X:Y|Z] = 0`. One then expands `Δ` and observes that every marginal appearing in the log-expression is shared between the original law and `p̃`, so the `p`-weighted sum equals the `p̃`-weighted sum, and what drops out is exactly `-KL(p̃ ‖ p̂) ≤ 0`. This is an `IsZeroOrProbabilityMeasure`-level KL-divergence argument and does *not* use the kernel/`condIndep_copies` machinery that Candidate A of the milestone plan envisioned; PFR's `KLDiv_nonneg` (and the underlying log-sum inequality `Real.sum_mul_log_div_leq`) is the relevant non-negativity lemma.

**Current state:** `theorem2_delta_le_zero` carries a single localized `sorry`. The full KL-divergence formalization -- setting up the 4-tuple joint PMF, defining `p̃` and `p̂` as real-valued functions on `S₁ × S₂ × S₃ × S₄`, proving they are probability distributions, establishing the marginal-swap observation for the eleven factors that appear in the `Δ` expansion, and applying `Real.sum_mul_log_div_leq` to close -- is substantial and remains open. The Shannon-algebra reduction and the public-API shape of `theorem2` are complete and unchanged, so downstream milestones may assume the theorem holds.

The four codomains `S₁, S₂, S₃, S₄` are specialized to `[Fintype]` + `[MeasurableSingletonClass]` so PFR's `FiniteRange`/`Countable` obligations are discharged uniformly.

Paper ordering `(X, Y, Z, U)` is followed here because Theorem 2 is a standalone inequality read most naturally in that order; `ZhangYeung/Delta.lean` uses `(Z, U, X, Y)` because the delta quantity is symmetric in its first two arguments. The two modules share no variables, so the naming clash across `S₁..S₄` is harmless, and the `ZhangYeung.delta` identifier appearing in the helpers below takes its arguments in Delta.lean's order: `delta Z U X Y μ`.

## References

* [@zhangyeung1997] -- the 1997 paper containing the KL-divergence proof of the inequality (as Theorem 3 of that paper). See `references/papers/zhangyeung1997.pdf`.
* [@zhangyeung1998] -- the 1998 paper; Theorem 2 there restates the 1997 result. See `references/transcriptions/zhangyeung1998.md` for a verbatim transcription of equations (16) and (17), verified 2026-04-16.

## Tags

Shannon entropy, conditional mutual information, conditional information inequality, Kullback-Leibler divergence, Zhang-Yeung
-/

namespace ZhangYeung

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]
  {S₁ S₂ S₃ S₄ : Type*}
  [Fintype S₁] [Fintype S₂] [Fintype S₃] [Fintype S₄]
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]

/-- **Shannon-type reduction for Theorem 2.** The algebraic identity that rewrites `I[X:Y|⟨Z,U⟩] - I[Z:U|⟨X,Y⟩] - I[X:Y|U]` as `Δ(Z, U | X, Y) + I[X:Y|Z] - I[X:Y]`, where `Δ` is `ZhangYeung.delta`. Under the hypotheses of Theorem 2 (eq. 16), the two correction terms are zero and the Theorem 2 target is equivalent to `Δ(Z, U | X, Y) ≤ 0`. The identity is pure Shannon algebra and needs no hypotheses beyond `IsProbabilityMeasure`. -/
private lemma theorem2_shannon_identity
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    I[X : Y | ⟨Z, U⟩ ; μ] - I[Z : U | ⟨X, Y⟩ ; μ] - I[X : Y | U ; μ]
      = delta Z U X Y μ + I[X : Y | Z ; μ] - I[X : Y ; μ] := by
  have hZU : Measurable (fun ω => (Z ω, U ω)) := hZ.prodMk hU
  have hXY : Measurable (fun ω => (X ω, Y ω)) := hX.prodMk hY
  rw [delta_def, condMutualInfo_eq hX hY hZU μ, condMutualInfo_eq hZ hU hXY μ,
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

/-- **Zhang-Yeung delta is nonpositive under the hypotheses of Theorem 2** ([@zhangyeung1997, Theorem 3]). The direct proof (op. cit.) introduces two auxiliary probability distributions `p̃(x, y, z, u) := p(x, z, u) p(y, z, u) / p(z, u)` and `p̂(x, y, z, u) := p(x, z) p(x, u) p(y, z) p(y, u) / [p(z) p(u) p(x) p(y)]`, both on `S₁ × S₂ × S₃ × S₄`. `p̃` is always a probability distribution; `p̂` is one by hypothesis (`I[X:Y|Z] = 0` provides `p(x, y, z) = p(x, z) p(y, z) / p(z)`; `I[X:Y] = 0` provides `p(x, y) = p(x) p(y)`; together they make `p̂` sum to one). An entropy expansion then rewrites the delta as `-KL(p̃ ‖ p̂)`, and nonnegativity of the Kullback-Leibler divergence closes the proof. -/
private lemma theorem2_delta_le_zero
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h₁ : I[X : Y ; μ] = 0) (h₂ : I[X : Y | Z ; μ] = 0) :
    delta Z U X Y μ ≤ 0 := by
  sorry

/-- **Zhang-Yeung Theorem 2** ([@zhangyeung1998], eqs. 16-17; proved in [@zhangyeung1997, Theorem 3]). For any four discrete random variables `X, Y, Z, U` on a probability space, if `I[X : Y ; μ] = 0` and `I[X : Y | Z ; μ] = 0`, then `I[X : Y | ⟨Z, U⟩ ; μ] ≤ I[Z : U | ⟨X, Y⟩ ; μ] + I[X : Y | U ; μ]`.

The proof factors into a Shannon-algebra reduction (`theorem2_shannon_identity`) that isolates the non-Shannon-type core `Δ(Z, U | X, Y) ≤ 0` via the `ZhangYeung.delta` quantity from M1, and the [@zhangyeung1997] KL-divergence argument (`theorem2_delta_le_zero`) that discharges that core. -/
theorem theorem2
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h₁ : I[X : Y ; μ] = 0)
    (h₂ : I[X : Y | Z ; μ] = 0) :
    I[X : Y | ⟨Z, U⟩ ; μ] ≤ I[Z : U | ⟨X, Y⟩ ; μ] + I[X : Y | U ; μ] := by
  have h_red := theorem2_shannon_identity hX hY hZ hU μ
  have hΔ := theorem2_delta_le_zero hX hY hZ hU μ h₁ h₂
  linarith

end ZhangYeung
