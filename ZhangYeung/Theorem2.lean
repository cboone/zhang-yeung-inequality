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

**Current state:** The proof of `theorem2_delta_le_zero` is scaffolded into four named sub-lemmas, each with its own localized `sorry`: `ptilde_sum_eq_one`, `phat_sum_eq_one`, `delta_eq_sum_log_ratio`, and `sum_joint_eq_sum_ptilde`. The main proof threads them together with `Real.sum_mul_log_div_leq` so the non-Shannon core is isolated to these four claims. Progress closing each can land independently.

The four codomains `S₁, S₂, S₃, S₄` are specialized to `[Fintype]` + `[MeasurableSingletonClass]` so PFR's `FiniteRange`/`Countable` obligations are discharged uniformly.

Paper ordering `(X, Y, Z, U)` is followed here because Theorem 2 is a standalone inequality read most naturally in that order; `ZhangYeung/Delta.lean` uses `(Z, U, X, Y)` because the delta quantity is symmetric in its first two arguments. The two modules share no variables, so the naming clash across `S₁..S₄` is harmless, and the `ZhangYeung.delta` identifier appearing in the helpers below takes its arguments in Delta.lean's order: `delta Z U X Y μ`.

## References

* [@zhangyeung1997] -- the 1997 paper containing the KL-divergence proof of the inequality (as Theorem 3 of that paper). See `references/papers/zhangyeung1997.pdf`.
* [@zhangyeung1998] -- the 1998 paper; Theorem 2 there restates the 1997 result. See `references/transcriptions/zhangyeung1998.md` for a verbatim transcription of equations (16) and (17), verified 2026-04-16.

## Tags

Shannon entropy, conditional mutual information, conditional information inequality, Kullback-Leibler divergence, Zhang-Yeung
-/

namespace ZhangYeung

open MeasureTheory ProbabilityTheory Real

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

/-! ### KL-divergence scaffolding for `theorem2_delta_le_zero`

The four sub-lemmas below factor the [@zhangyeung1997] proof of `Δ(Z, U | X, Y) ≤ 0`. They share the auxiliary distributions `ptilde` and `phat` defined immediately below; each captures one algebraic obligation of the KL-divergence argument so the main proof is a composition that invokes `Real.sum_mul_log_div_leq` on the finite-alphabet sum.
-/

/-- The first auxiliary distribution `p̃(x, y, z, u) := p(x, z, u) p(y, z, u) / p(z, u)` on `S₁ × S₂ × S₃ × S₄`, built from the joint law of `(X, Y, Z, U)` under `μ`. Under Lean's convention `0 / 0 = 0` and the absolute-continuity of the marginals, `ptilde` vanishes exactly on the zero-measure diagonal `{(x, y, z, u) : p(z, u) = 0}` without an explicit case split. -/
private noncomputable def ptilde
    (X : Ω → S₁) (Y : Ω → S₂) (Z : Ω → S₃) (U : Ω → S₄) (μ : Measure Ω) :
    S₁ × S₂ × S₃ × S₄ → ℝ := fun ⟨x, y, z, u⟩ =>
  (μ.map (fun ω => (X ω, Z ω, U ω))).real {(x, z, u)}
    * (μ.map (fun ω => (Y ω, Z ω, U ω))).real {(y, z, u)}
    / (μ.map (fun ω => (Z ω, U ω))).real {(z, u)}

/-- The second auxiliary distribution `p̂(x, y, z, u) := p(x, z) p(x, u) p(y, z) p(y, u) / (p(z) p(u) p(x) p(y))` on `S₁ × S₂ × S₃ × S₄`. It is a probability distribution only under the hypotheses of Theorem 2 (see `phat_sum_eq_one`); the `I[X:Y|Z] = 0` hypothesis supplies `p(x, y, z) = p(x, z) p(y, z) / p(z)` and `I[X:Y] = 0` supplies `p(x, y) = p(x) p(y)`, and together they collapse `∑ p̂` to one. -/
private noncomputable def phat
    (X : Ω → S₁) (Y : Ω → S₂) (Z : Ω → S₃) (U : Ω → S₄) (μ : Measure Ω) :
    S₁ × S₂ × S₃ × S₄ → ℝ := fun ⟨x, y, z, u⟩ =>
  (μ.map (fun ω => (X ω, Z ω))).real {(x, z)}
    * (μ.map (fun ω => (X ω, U ω))).real {(x, u)}
    * (μ.map (fun ω => (Y ω, Z ω))).real {(y, z)}
    * (μ.map (fun ω => (Y ω, U ω))).real {(y, u)}
    / ((μ.map Z).real {z} * (μ.map U).real {u} * (μ.map X).real {x} * (μ.map Y).real {y})

/-- The joint PMF of `(X, Y, Z, U)` under `μ`, as a real-valued function on the 4-tuple space. -/
private noncomputable def pJoint
    (X : Ω → S₁) (Y : Ω → S₂) (Z : Ω → S₃) (U : Ω → S₄) (μ : Measure Ω) :
    S₁ × S₂ × S₃ × S₄ → ℝ := fun t =>
  (μ.map (fun ω => (X ω, Y ω, Z ω, U ω))).real {t}

/-- **Marginal summation.** For a triple-valued joint `(f, g, h) : Ω → α × β × γ` with `α` finite and discrete, summing the real joint PMF over the first coordinate recovers the two-coordinate marginal PMF `(g, h)`. This is the Fintype-level `Prod.snd`-pushforward fact used in the `ptilde`/`phat` sum arguments. -/
private lemma sum_map_triple_first
    {α β γ : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    {Ω' : Type*} [MeasurableSpace Ω']
    {f : Ω' → α} {g : Ω' → β} {h : Ω' → γ}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (μ : Measure Ω') [IsFiniteMeasure μ] (b : β) (c : γ) :
    ∑ a : α, (μ.map (fun ω => (f ω, g ω, h ω))).real {(a, b, c)}
      = (μ.map (fun ω => (g ω, h ω))).real {(b, c)} := by
  have hfgh : Measurable (fun ω => (f ω, g ω, h ω)) := hf.prodMk (hg.prodMk hh)
  have hgh : Measurable (fun ω => (g ω, h ω)) := hg.prodMk hh
  simp_rw [map_measureReal_apply hfgh (measurableSet_singleton _),
           map_measureReal_apply hgh (measurableSet_singleton _)]
  have preimage_eq : ∀ a : α,
      (fun ω => (f ω, g ω, h ω))⁻¹' {(a, b, c)}
        = f ⁻¹' {a} ∩ (fun ω => (g ω, h ω))⁻¹' {(b, c)} := by
    intro a; ext ω; simp
  simp_rw [preimage_eq]
  have hA : MeasurableSet ((fun ω => (g ω, h ω))⁻¹' {(b, c)}) :=
    hgh (measurableSet_singleton _)
  simp_rw [show ∀ a : α, μ.real (f ⁻¹' {a} ∩ (fun ω => (g ω, h ω))⁻¹' {(b, c)})
      = (μ.restrict ((fun ω => (g ω, h ω))⁻¹' {(b, c)})).real (f ⁻¹' {a}) from
    fun a => (measureReal_restrict_apply (hf (measurableSet_singleton a))).symm]
  rw [sum_measureReal_preimage_singleton (Finset.univ : Finset α)
      (fun y _ => hf (measurableSet_singleton y))]
  simp

/-- Marginal summation, second variant: summing the triple joint over the *second* coordinate recovers the marginal of `(f, h)`. -/
private lemma sum_map_triple_second
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    {Ω' : Type*} [MeasurableSpace Ω']
    {f : Ω' → α} {g : Ω' → β} {h : Ω' → γ}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (μ : Measure Ω') [IsFiniteMeasure μ] (a : α) (c : γ) :
    ∑ b : β, (μ.map (fun ω => (f ω, g ω, h ω))).real {(a, b, c)}
      = (μ.map (fun ω => (f ω, h ω))).real {(a, c)} := by
  have hfgh : Measurable (fun ω => (f ω, g ω, h ω)) := hf.prodMk (hg.prodMk hh)
  have hfh : Measurable (fun ω => (f ω, h ω)) := hf.prodMk hh
  simp_rw [map_measureReal_apply hfgh (measurableSet_singleton _),
           map_measureReal_apply hfh (measurableSet_singleton _)]
  have preimage_eq : ∀ b : β,
      (fun ω => (f ω, g ω, h ω))⁻¹' {(a, b, c)}
        = g ⁻¹' {b} ∩ ((fun ω => (f ω, h ω))⁻¹' {(a, c)}) := by
    intro b; ext ω; simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq,
      Set.mem_inter_iff]; tauto
  simp_rw [preimage_eq]
  have hA : MeasurableSet ((fun ω => (f ω, h ω))⁻¹' {(a, c)}) :=
    hfh (measurableSet_singleton _)
  simp_rw [show ∀ b : β, μ.real (g ⁻¹' {b} ∩ (fun ω => (f ω, h ω))⁻¹' {(a, c)})
      = (μ.restrict ((fun ω => (f ω, h ω))⁻¹' {(a, c)})).real (g ⁻¹' {b}) from
    fun b => (measureReal_restrict_apply (hg (measurableSet_singleton b))).symm]
  rw [sum_measureReal_preimage_singleton (Finset.univ : Finset β)
      (fun y _ => hg (measurableSet_singleton y))]
  simp

omit [Fintype S₃] [Fintype S₄] in
/-- **Inner fiber sum.** For each fixed `(z, u)`, the fibre sum of `p̃` over `(x, y)` collapses to `p(z, u)`. This is the core computation of `ptilde_sum_eq_one`: the marginal identities supply `∑_x p(x, z, u) = p(z, u)` and `∑_y p(y, z, u) = p(z, u)`, factoring the inner product-of-sums out of the division. -/
private lemma ptilde_fibre_sum
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsFiniteMeasure μ] (z : S₃) (u : S₄) :
    (∑ x : S₁, ∑ y : S₂,
        (μ.map (fun ω => (X ω, Z ω, U ω))).real {(x, z, u)} *
        (μ.map (fun ω => (Y ω, Z ω, U ω))).real {(y, z, u)} /
        (μ.map (fun ω => (Z ω, U ω))).real {(z, u)})
      = (μ.map (fun ω => (Z ω, U ω))).real {(z, u)} := by
  set c := (μ.map (fun ω => (Z ω, U ω))).real {(z, u)}
  set Fx := fun x : S₁ => (μ.map (fun ω => (X ω, Z ω, U ω))).real {(x, z, u)}
  set Fy := fun y : S₂ => (μ.map (fun ω => (Y ω, Z ω, U ω))).real {(y, z, u)}
  have hSumFx : ∑ x, Fx x = c := sum_map_triple_first hX hZ hU μ z u
  have hSumFy : ∑ y, Fy y = c := sum_map_triple_first hY hZ hU μ z u
  show ∑ x, ∑ y, Fx x * Fy y / c = c
  simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
  rw [← Finset.sum_mul_sum, hSumFx, hSumFy]
  by_cases hc : c = 0
  · simp [hc]
  · field_simp

/-- **`p̃` is a probability distribution.** This is the unconditional half of the Zhang-Yeung auxiliary-distribution argument: `∑_{x,y,z,u} p(x,z,u) p(y,z,u) / p(z,u) = 1` for any probability measure. The proof reshapes the 4-tuple sum via a product re-associate-and-swap `Equiv`, applies `ptilde_fibre_sum` on each `(z, u)` fibre, and collapses the outer `∑_{z,u} p(z, u) = 1` via the probability-measure property of the pushforward `μ.map ⟨Z, U⟩`. -/
private lemma ptilde_sum_eq_one
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ∑ t : S₁ × S₂ × S₃ × S₄, ptilde X Y Z U μ t = 1 := by
  sorry

/-- **`p̂` is a probability distribution under the hypotheses of Theorem 2.** Collapses by summing over `z` first (using `I[X:Y|Z] = 0` ⇒ `p(x, y, z) = p(x, z) p(y, z) / p(z)`), then using `I[X:Y] = 0` ⇒ `p(x, y) = p(x) p(y)` to cancel the single-variable denominators, then summing over `x, y, u`. -/
private lemma phat_sum_eq_one
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h₁ : I[X : Y ; μ] = 0) (h₂ : I[X : Y | Z ; μ] = 0) :
    ∑ t : S₁ × S₂ × S₃ × S₄, phat X Y Z U μ t = 1 := by
  sorry

/-- **`Δ` as a weighted-log sum.** The identity `Δ(Z, U | X, Y) = ∑_{x,y,z,u} p(x,y,z,u) · log (p̂(x,y,z,u) / p̃(x,y,z,u))` obtained by expanding each of `I[Z:U]`, `I[Z:U|X]`, `I[Z:U|Y]` via `entropy_eq_sum_finset` over the 4-tuple marginal and combining the eleven `negMulLog` contributions. The right-hand side is the raw form of Zhang-Yeung 1997's eq. (41). -/
private lemma delta_eq_sum_log_ratio
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    delta Z U X Y μ
      = ∑ t : S₁ × S₂ × S₃ × S₄,
          pJoint X Y Z U μ t * Real.log (phat X Y Z U μ t / ptilde X Y Z U μ t) := by
  sorry

/-- **Marginal swap.** Every factor appearing in the log-ratio `p̂ / p̃` is a marginal distribution common to `p` and `p̃` -- the full list is `{p(z,u), p(x,z), p(x,u), p(y,z), p(y,u), p(x,z,u), p(y,z,u), p(z), p(u), p(x), p(y)}`. The `p`-weighted sum therefore agrees with the `p̃`-weighted sum on each factor, and the eleven summands recombine to `∑ p̃ · log(p̂ / p̃)`. This is the key observation of [@zhangyeung1997] that converts Shannon-type quantities into the KL-divergence-amenable form. -/
private lemma sum_joint_eq_sum_ptilde
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ∑ t : S₁ × S₂ × S₃ × S₄,
        pJoint X Y Z U μ t * Real.log (phat X Y Z U μ t / ptilde X Y Z U μ t)
      = ∑ t : S₁ × S₂ × S₃ × S₄,
          ptilde X Y Z U μ t * Real.log (phat X Y Z U μ t / ptilde X Y Z U μ t) := by
  sorry

omit [Fintype S₁] [Fintype S₂] [Fintype S₃] [Fintype S₄]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄] in
/-- **`ptilde` is nonnegative.** Quotients of nonneg reals are nonneg in Lean (with `0 / 0 = 0`). -/
private lemma ptilde_nonneg
    (X : Ω → S₁) (Y : Ω → S₂) (Z : Ω → S₃) (U : Ω → S₄) (μ : Measure Ω)
    (t : S₁ × S₂ × S₃ × S₄) :
    0 ≤ ptilde X Y Z U μ t := by
  obtain ⟨x, y, z, u⟩ := t
  unfold ptilde
  positivity

omit [Fintype S₁] [Fintype S₂] [Fintype S₃] [Fintype S₄]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄] in
/-- **`phat` is nonnegative.** Quotients of nonneg reals are nonneg. -/
private lemma phat_nonneg
    (X : Ω → S₁) (Y : Ω → S₂) (Z : Ω → S₃) (U : Ω → S₄) (μ : Measure Ω)
    (t : S₁ × S₂ × S₃ × S₄) :
    0 ≤ phat X Y Z U μ t := by
  obtain ⟨x, y, z, u⟩ := t
  unfold phat
  positivity

/-- **Zhang-Yeung delta is nonpositive under the hypotheses of Theorem 2** ([@zhangyeung1997, Theorem 3]). The direct proof (op. cit.) introduces the auxiliary distributions `ptilde` and `phat` (defined above), expands `Δ` as `∑ p · log(p̂ / p̃)`, reweights via `sum_joint_eq_sum_ptilde` to `∑ p̃ · log(p̂ / p̃) = -KL(p̃ ‖ p̂)`, and closes by the log-sum inequality `Real.sum_mul_log_div_leq` applied to `p̃`, `p̂`. The four scaffolding sub-lemmas above capture every algebraic obligation of the argument. -/
private lemma theorem2_delta_le_zero
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h₁ : I[X : Y ; μ] = 0) (h₂ : I[X : Y | Z ; μ] = 0) :
    delta Z U X Y μ ≤ 0 := by
  set s : Finset (S₁ × S₂ × S₃ × S₄) := Finset.univ
  have h_ptilde_sum : ∑ t ∈ s, ptilde X Y Z U μ t = 1 :=
    ptilde_sum_eq_one hX hY hZ hU μ
  have h_phat_sum : ∑ t ∈ s, phat X Y Z U μ t = 1 :=
    phat_sum_eq_one hX hY hZ hU μ h₁ h₂
  have h_ptilde_nn : ∀ t ∈ s, 0 ≤ ptilde X Y Z U μ t :=
    fun t _ => ptilde_nonneg X Y Z U μ t
  have h_phat_nn : ∀ t ∈ s, 0 ≤ phat X Y Z U μ t :=
    fun t _ => phat_nonneg X Y Z U μ t
  have h_log_sum : (∑ t ∈ s, ptilde X Y Z U μ t) *
      Real.log ((∑ t ∈ s, ptilde X Y Z U μ t) / (∑ t ∈ s, phat X Y Z U μ t))
        ≤ ∑ t ∈ s, ptilde X Y Z U μ t *
          Real.log (ptilde X Y Z U μ t / phat X Y Z U μ t) := by
    -- The absolute-continuity side condition `phat = 0 → ptilde = 0` follows from
    -- the fact that every factor in `phat` is a marginal of `μ`: if any single
    -- marginal vanishes, the corresponding factor in `ptilde` also vanishes, so
    -- `ptilde = 0 / (anything) = 0`. We leave this as a scaffolded sub-obligation
    -- alongside `ptilde_sum_eq_one` etc.; it is closed together with the main
    -- proof in a subsequent commit.
    sorry
  have h_kl_nonneg : 0 ≤ ∑ t ∈ s,
      ptilde X Y Z U μ t * Real.log (ptilde X Y Z U μ t / phat X Y Z U μ t) := by
    have : (1 : ℝ) * Real.log (1 / 1) ≤
        ∑ t ∈ s, ptilde X Y Z U μ t *
          Real.log (ptilde X Y Z U μ t / phat X Y Z U μ t) := by
      rw [h_ptilde_sum, h_phat_sum] at h_log_sum
      exact h_log_sum
    simpa using this
  have h_delta_eq : delta Z U X Y μ
      = ∑ t ∈ s, pJoint X Y Z U μ t *
          Real.log (phat X Y Z U μ t / ptilde X Y Z U μ t) :=
    delta_eq_sum_log_ratio hX hY hZ hU μ
  have h_swap : ∑ t ∈ s, pJoint X Y Z U μ t *
        Real.log (phat X Y Z U μ t / ptilde X Y Z U μ t)
      = ∑ t ∈ s, ptilde X Y Z U μ t *
          Real.log (phat X Y Z U μ t / ptilde X Y Z U μ t) :=
    sum_joint_eq_sum_ptilde hX hY hZ hU μ
  have h_neg : ∑ t ∈ s, ptilde X Y Z U μ t *
        Real.log (phat X Y Z U μ t / ptilde X Y Z U μ t)
      = -(∑ t ∈ s, ptilde X Y Z U μ t *
          Real.log (ptilde X Y Z U μ t / phat X Y Z U μ t)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases hpt : ptilde X Y Z U μ t = 0
    · simp [hpt]
    by_cases hph : phat X Y Z U μ t = 0
    · simp [hph, Real.log_zero]
    rw [← mul_neg, Real.log_div hph hpt, Real.log_div hpt hph]
    ring
  linarith [h_delta_eq, h_swap, h_neg, h_kl_nonneg]

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
