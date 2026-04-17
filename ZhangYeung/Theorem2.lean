import ZhangYeung.Delta
import ZhangYeung.Prelude
import PFR.Mathlib.Analysis.SpecialFunctions.NegMulLog

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

**Current state:** `theorem2_delta_le_zero` is wired end-to-end, with the main proof body assembled around `Real.sum_mul_log_div_leq` and its absolute-continuity side condition (closed inline via marginal bounds). `ptilde_sum_eq_one` is closed. Three scaffolded sub-lemmas remain `sorry`:

- `phat_sum_eq_one` (requires extracting `p(x,y) = p(x)p(y)` from `IndepFun X Y` and `p(x,y,z) = p(x,z)p(y,z)/p(z)` from `CondIndepFun X Y Z`),
- `delta_eq_sum_log_ratio` (entropy expansion over the 4-tuple space), and
- `sum_joint_eq_sum_ptilde` (the 11-factor marginal-swap observation).

Each closes independently of the others. The file is organized into the following sections:

1. `theorem2_shannon_identity` -- Shannon-algebra reduction to `Δ ≤ 0`.
2. Auxiliary distributions `p̃`, `p̂` (plus `pJoint`) and their nonnegativity.
3. Generic finite-alphabet utilities (marginal summations, marginal bounds, `IndepFun` product formula, fibrewise-swap helper).
4. The eleven marginal-match facts for `p̃`.
5. Sum-to-one facts (`ptilde_sum_eq_one` closed; `phat_sum_eq_one` sorry).
6. Δ-to-log-ratio identities (`delta_eq_sum_log_ratio`, `sum_joint_eq_sum_ptilde` -- both sorry).
7. `theorem2_delta_le_zero` + `theorem2`.

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

/-! ### Shannon-algebra reduction -/

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

/-! ### Auxiliary distributions `p̃`, `p̂`, and the joint PMF -/

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

omit [Fintype S₁] [Fintype S₂] [Fintype S₃] [Fintype S₄]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄] in
/-- **`p̃` is nonnegative.** Quotients of nonneg reals are nonneg in Lean (with `0 / 0 = 0`). -/
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
/-- **`p̂` is nonnegative.** Quotients of nonneg reals are nonneg. -/
private lemma phat_nonneg
    (X : Ω → S₁) (Y : Ω → S₂) (Z : Ω → S₃) (U : Ω → S₄) (μ : Measure Ω)
    (t : S₁ × S₂ × S₃ × S₄) :
    0 ≤ phat X Y Z U μ t := by
  obtain ⟨x, y, z, u⟩ := t
  unfold phat
  positivity

/-! ### Generic finite-alphabet utilities

Pair and triple pushforward helpers -- marginal summation over each coordinate, pointwise marginal bounds, the `IndepFun` product formula, and the fibrewise-swap identity. All are stated generically (on abstract `Ω' / α / β / γ`) so they apply independently of this module's `X, Y, Z, U` variables. -/

/-- Marginal summation for pairs: summing the pair-joint over the *first* coordinate recovers the marginal of `g`. -/
private lemma sum_map_pair_first
    {α β : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    {Ω' : Type*} [MeasurableSpace Ω']
    {f : Ω' → α} {g : Ω' → β}
    (hf : Measurable f) (hg : Measurable g)
    (μ : Measure Ω') [IsFiniteMeasure μ] (b : β) :
    ∑ a : α, (μ.map (fun ω => (f ω, g ω))).real {(a, b)}
      = (μ.map g).real {b} := by
  have hfg : Measurable (fun ω => (f ω, g ω)) := hf.prodMk hg
  simp_rw [map_measureReal_apply hfg (measurableSet_singleton _),
           map_measureReal_apply hg (measurableSet_singleton _)]
  have preimage_eq : ∀ a : α,
      (fun ω => (f ω, g ω))⁻¹' {(a, b)}
        = f ⁻¹' {a} ∩ (g ⁻¹' {b}) := by
    intro a; ext ω; simp
  simp_rw [preimage_eq]
  simp_rw [show ∀ a : α, μ.real (f ⁻¹' {a} ∩ g ⁻¹' {b})
      = (μ.restrict (g ⁻¹' {b})).real (f ⁻¹' {a}) from
    fun a => (measureReal_restrict_apply (hf (measurableSet_singleton a))).symm]
  rw [sum_measureReal_preimage_singleton (Finset.univ : Finset α)
      (fun y _ => hf (measurableSet_singleton y))]
  simp

/-- Marginal summation for pairs: summing the pair-joint over the *second* coordinate recovers the marginal of `f`. -/
private lemma sum_map_pair_second
    {α β : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    {Ω' : Type*} [MeasurableSpace Ω']
    {f : Ω' → α} {g : Ω' → β}
    (hf : Measurable f) (hg : Measurable g)
    (μ : Measure Ω') [IsFiniteMeasure μ] (a : α) :
    ∑ b : β, (μ.map (fun ω => (f ω, g ω))).real {(a, b)}
      = (μ.map f).real {a} := by
  have hfg : Measurable (fun ω => (f ω, g ω)) := hf.prodMk hg
  simp_rw [map_measureReal_apply hfg (measurableSet_singleton _),
           map_measureReal_apply hf (measurableSet_singleton _)]
  have preimage_eq : ∀ b : β,
      (fun ω => (f ω, g ω))⁻¹' {(a, b)}
        = g ⁻¹' {b} ∩ (f ⁻¹' {a}) := by
    intro b; ext ω; simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq,
      Set.mem_inter_iff]; tauto
  simp_rw [preimage_eq]
  simp_rw [show ∀ b : β, μ.real (g ⁻¹' {b} ∩ f ⁻¹' {a})
      = (μ.restrict (f ⁻¹' {a})).real (g ⁻¹' {b}) from
    fun b => (measureReal_restrict_apply (hg (measurableSet_singleton b))).symm]
  rw [sum_measureReal_preimage_singleton (Finset.univ : Finset β)
      (fun y _ => hg (measurableSet_singleton y))]
  simp

/-- Marginal summation for triples: summing over the *first* coordinate recovers the `(g, h)` marginal. -/
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
  have h_fgh : Measurable (fun ω => (f ω, g ω, h ω)) := hf.prodMk (hg.prodMk hh)
  have hgh : Measurable (fun ω => (g ω, h ω)) := hg.prodMk hh
  simp_rw [map_measureReal_apply h_fgh (measurableSet_singleton _),
           map_measureReal_apply hgh (measurableSet_singleton _)]
  have preimage_eq : ∀ a : α,
      (fun ω => (f ω, g ω, h ω))⁻¹' {(a, b, c)}
        = f ⁻¹' {a} ∩ (fun ω => (g ω, h ω))⁻¹' {(b, c)} := by
    intro a; ext ω; simp
  simp_rw [preimage_eq]
  simp_rw [show ∀ a : α, μ.real (f ⁻¹' {a} ∩ (fun ω => (g ω, h ω))⁻¹' {(b, c)})
      = (μ.restrict ((fun ω => (g ω, h ω))⁻¹' {(b, c)})).real (f ⁻¹' {a}) from
    fun a => (measureReal_restrict_apply (hf (measurableSet_singleton a))).symm]
  rw [sum_measureReal_preimage_singleton (Finset.univ : Finset α)
      (fun y _ => hf (measurableSet_singleton y))]
  simp

/-- Marginal summation for triples: summing over the *second* coordinate recovers the `(f, h)` marginal. -/
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
  have h_fgh : Measurable (fun ω => (f ω, g ω, h ω)) := hf.prodMk (hg.prodMk hh)
  have hfh : Measurable (fun ω => (f ω, h ω)) := hf.prodMk hh
  simp_rw [map_measureReal_apply h_fgh (measurableSet_singleton _),
           map_measureReal_apply hfh (measurableSet_singleton _)]
  have preimage_eq : ∀ b : β,
      (fun ω => (f ω, g ω, h ω))⁻¹' {(a, b, c)}
        = g ⁻¹' {b} ∩ ((fun ω => (f ω, h ω))⁻¹' {(a, c)}) := by
    intro b; ext ω; simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq,
      Set.mem_inter_iff]; tauto
  simp_rw [preimage_eq]
  simp_rw [show ∀ b : β, μ.real (g ⁻¹' {b} ∩ (fun ω => (f ω, h ω))⁻¹' {(a, c)})
      = (μ.restrict ((fun ω => (f ω, h ω))⁻¹' {(a, c)})).real (g ⁻¹' {b}) from
    fun b => (measureReal_restrict_apply (hg (measurableSet_singleton b))).symm]
  rw [sum_measureReal_preimage_singleton (Finset.univ : Finset β)
      (fun y _ => hg (measurableSet_singleton y))]
  simp

/-- Marginal summation for triples: summing over the *third* coordinate recovers the `(f, g)` marginal. -/
private lemma sum_map_triple_third
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    [Fintype γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
    {Ω' : Type*} [MeasurableSpace Ω']
    {f : Ω' → α} {g : Ω' → β} {h : Ω' → γ}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (μ : Measure Ω') [IsFiniteMeasure μ] (a : α) (b : β) :
    ∑ c : γ, (μ.map (fun ω => (f ω, g ω, h ω))).real {(a, b, c)}
      = (μ.map (fun ω => (f ω, g ω))).real {(a, b)} := by
  have h_fgh : Measurable (fun ω => (f ω, g ω, h ω)) := hf.prodMk (hg.prodMk hh)
  have hfg : Measurable (fun ω => (f ω, g ω)) := hf.prodMk hg
  simp_rw [map_measureReal_apply h_fgh (measurableSet_singleton _),
           map_measureReal_apply hfg (measurableSet_singleton _)]
  have preimage_eq : ∀ c : γ,
      (fun ω => (f ω, g ω, h ω))⁻¹' {(a, b, c)}
        = h ⁻¹' {c} ∩ ((fun ω => (f ω, g ω))⁻¹' {(a, b)}) := by
    intro c; ext ω; simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq,
      Set.mem_inter_iff]; tauto
  simp_rw [preimage_eq]
  simp_rw [show ∀ c : γ, μ.real (h ⁻¹' {c} ∩ (fun ω => (f ω, g ω))⁻¹' {(a, b)})
      = (μ.restrict ((fun ω => (f ω, g ω))⁻¹' {(a, b)})).real (h ⁻¹' {c}) from
    fun c => (measureReal_restrict_apply (hh (measurableSet_singleton c))).symm]
  rw [sum_measureReal_preimage_singleton (Finset.univ : Finset γ)
      (fun y _ => hh (measurableSet_singleton y))]
  simp

/-- **Marginal bound (pair, first).** The pair mass is bounded by the first projection. Used for the absolute-continuity claim `p̂ = 0 → p̃ = 0`. -/
private lemma measureReal_map_pair_le_map_fst
    {α β : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    {Ω' : Type*} [MeasurableSpace Ω']
    {f : Ω' → α} {g : Ω' → β}
    (hf : Measurable f) (hg : Measurable g)
    (μ : Measure Ω') [IsFiniteMeasure μ] (a : α) (b : β) :
    (μ.map (fun ω => (f ω, g ω))).real {(a, b)} ≤ (μ.map f).real {a} := by
  rw [map_measureReal_apply (hf.prodMk hg) (measurableSet_singleton _),
      map_measureReal_apply hf (measurableSet_singleton _)]
  apply measureReal_mono _ (measure_ne_top _ _)
  intro ω hω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq] at hω ⊢
  exact hω.1

/-- **Marginal bound (pair, second).** The pair mass is bounded by the second projection. -/
private lemma measureReal_map_pair_le_map_snd
    {α β : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    {Ω' : Type*} [MeasurableSpace Ω']
    {f : Ω' → α} {g : Ω' → β}
    (hf : Measurable f) (hg : Measurable g)
    (μ : Measure Ω') [IsFiniteMeasure μ] (a : α) (b : β) :
    (μ.map (fun ω => (f ω, g ω))).real {(a, b)} ≤ (μ.map g).real {b} := by
  rw [map_measureReal_apply (hf.prodMk hg) (measurableSet_singleton _),
      map_measureReal_apply hg (measurableSet_singleton _)]
  apply measureReal_mono _ (measure_ne_top _ _)
  intro ω hω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq] at hω ⊢
  exact hω.2

/-- **Marginal bound (triple, forget third).** `p(a, b, c) ≤ p(a, b)`. -/
private lemma measureReal_map_triple_le_map_pair_12
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    {Ω' : Type*} [MeasurableSpace Ω']
    {f : Ω' → α} {g : Ω' → β} {h : Ω' → γ}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (μ : Measure Ω') [IsFiniteMeasure μ] (a : α) (b : β) (c : γ) :
    (μ.map (fun ω => (f ω, g ω, h ω))).real {(a, b, c)}
      ≤ (μ.map (fun ω => (f ω, g ω))).real {(a, b)} := by
  rw [map_measureReal_apply (hf.prodMk (hg.prodMk hh)) (measurableSet_singleton _),
      map_measureReal_apply (hf.prodMk hg) (measurableSet_singleton _)]
  apply measureReal_mono _ (measure_ne_top _ _)
  intro ω hω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq] at hω ⊢
  exact ⟨hω.1, hω.2.1⟩

/-- **Marginal bound (triple, forget second).** `p(a, b, c) ≤ p(a, c)`. -/
private lemma measureReal_map_triple_le_map_pair_13
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    {Ω' : Type*} [MeasurableSpace Ω']
    {f : Ω' → α} {g : Ω' → β} {h : Ω' → γ}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (μ : Measure Ω') [IsFiniteMeasure μ] (a : α) (b : β) (c : γ) :
    (μ.map (fun ω => (f ω, g ω, h ω))).real {(a, b, c)}
      ≤ (μ.map (fun ω => (f ω, h ω))).real {(a, c)} := by
  rw [map_measureReal_apply (hf.prodMk (hg.prodMk hh)) (measurableSet_singleton _),
      map_measureReal_apply (hf.prodMk hh) (measurableSet_singleton _)]
  apply measureReal_mono _ (measure_ne_top _ _)
  intro ω hω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq] at hω ⊢
  exact ⟨hω.1, hω.2.2⟩

/-- **IndepFun product formula.** If `f, g` are independent, the joint singleton mass factors: `(μ.map ⟨f, g⟩).real {(a, b)} = (μ.map f).real {a} * (μ.map g).real {b}`. This extracts the product identity from `IndepFun.measure_inter_preimage_eq_mul` in the shape used by `phat_sum_eq_one`. -/
private lemma indepFun_map_pair_real_singleton
    {α β : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    {Ω' : Type*} [MeasurableSpace Ω'] {f : Ω' → α} {g : Ω' → β}
    (hf : Measurable f) (hg : Measurable g)
    {μ : Measure Ω'} (h_indep : IndepFun f g μ) (a : α) (b : β) :
    (μ.map (fun ω => (f ω, g ω))).real {(a, b)}
      = (μ.map f).real {a} * (μ.map g).real {b} := by
  rw [map_measureReal_apply (hf.prodMk hg) (measurableSet_singleton _),
      map_measureReal_apply hf (measurableSet_singleton _),
      map_measureReal_apply hg (measurableSet_singleton _)]
  have h_pre : (fun ω => (f ω, g ω)) ⁻¹' {(a, b)} = f ⁻¹' {a} ∩ g ⁻¹' {b} := by
    ext ω; simp
  rw [h_pre, measureReal_def, measureReal_def, measureReal_def,
      h_indep.measure_inter_preimage_eq_mul {a} {b}
        (measurableSet_singleton a) (measurableSet_singleton b),
      ENNReal.toReal_mul]

/-- **Fibrewise marginal-swap.** If two weight functions `f, g : α → ℝ` agree on every fibre of a projection `proj : α → β` (i.e., share the same `proj`-marginal), then their weighted sums of any `proj`-composed function agree. This is the abstract kernel of the 11-factor marginal-swap argument used in `sum_joint_eq_sum_ptilde`. -/
private lemma sum_mul_proj_eq_of_marginal_eq
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f g : α → ℝ) (proj : α → β) (φ : β → ℝ)
    (h_marg : ∀ b : β, (∑ a ∈ Finset.univ.filter (fun a => proj a = b), f a)
                     = (∑ a ∈ Finset.univ.filter (fun a => proj a = b), g a)) :
    ∑ a : α, f a * φ (proj a) = ∑ a : α, g a * φ (proj a) := by
  conv_lhs => rw [← Finset.sum_fiberwise (s := Finset.univ) (g := proj)
    (f := fun a => f a * φ (proj a))]
  conv_rhs => rw [← Finset.sum_fiberwise (s := Finset.univ) (g := proj)
    (f := fun a => g a * φ (proj a))]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hf : (∑ a ∈ Finset.univ.filter (fun a => proj a = b), f a * φ (proj a))
      = (∑ a ∈ Finset.univ.filter (fun a => proj a = b), f a) * φ b := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [(Finset.mem_filter.mp ha).2]
  have hg : (∑ a ∈ Finset.univ.filter (fun a => proj a = b), g a * φ (proj a))
      = (∑ a ∈ Finset.univ.filter (fun a => proj a = b), g a) * φ b := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [(Finset.mem_filter.mp ha).2]
  rw [hf, hg, h_marg]

/-! ### Marginal structure of `p̃`

The eleven marginal-match facts: each of `p̃`'s projection-marginals agrees with `pJoint`'s. `ptilde_fibre_sum` handles the `(x, y)` fibre at the 2-tuple level; the rest cascade from `sum_ptilde_over_y`/`sum_ptilde_over_x` plus `sum_map_triple_*` / `sum_map_pair_*` to descend through the other projections. -/

omit [Fintype S₃] [Fintype S₄] in
/-- **Inner fibre sum.** For each fixed `(z, u)`, the fibre sum of `p̃` over `(x, y)` collapses to `p(z, u)`. This is the core computation of `ptilde_sum_eq_one`: the marginal identities supply `∑_x p(x, z, u) = p(z, u)` and `∑_y p(y, z, u) = p(z, u)`, factoring the inner product-of-sums out of the division. -/
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

omit [Fintype S₁] [Fintype S₃] [Fintype S₄] in
/-- **`p̃` marginal over `y` is `pXZU`.** Summing `p̃(x, y, z, u)` over `y ∈ S₂` gives `pXZU(x, z, u)`. -/
private lemma sum_ptilde_over_y
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsFiniteMeasure μ] (x : S₁) (z : S₃) (u : S₄) :
    (∑ y : S₂, ptilde X Y Z U μ (x, y, z, u))
      = (μ.map (fun ω => (X ω, Z ω, U ω))).real {(x, z, u)} := by
  simp only [ptilde]
  rw [← Finset.sum_div, ← Finset.mul_sum]
  rw [sum_map_triple_first hY hZ hU μ z u]
  set a := (μ.map (fun ω => (X ω, Z ω, U ω))).real {(x, z, u)}
  set b := (μ.map (fun ω => (Z ω, U ω))).real {(z, u)}
  by_cases hb : b = 0
  · have h_le : a ≤ b := measureReal_map_pair_le_map_snd hX (hZ.prodMk hU) μ x (z, u)
    have ha : a = 0 := le_antisymm (hb ▸ h_le) measureReal_nonneg
    simp [ha, hb]
  · field_simp

omit [Fintype S₂] [Fintype S₃] [Fintype S₄] in
/-- **`p̃` marginal over `x` is `pYZU`.** Symmetric to `sum_ptilde_over_y`. -/
private lemma sum_ptilde_over_x
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsFiniteMeasure μ] (y : S₂) (z : S₃) (u : S₄) :
    (∑ x : S₁, ptilde X Y Z U μ (x, y, z, u))
      = (μ.map (fun ω => (Y ω, Z ω, U ω))).real {(y, z, u)} := by
  simp only [ptilde]
  rw [← Finset.sum_div]
  simp_rw [mul_comm _ ((μ.map (fun ω => (Y ω, Z ω, U ω))).real {(y, z, u)})]
  rw [← Finset.mul_sum]
  rw [sum_map_triple_first hX hZ hU μ z u]
  set a := (μ.map (fun ω => (Y ω, Z ω, U ω))).real {(y, z, u)}
  set b := (μ.map (fun ω => (Z ω, U ω))).real {(z, u)}
  by_cases hb : b = 0
  · have h_le : a ≤ b := measureReal_map_pair_le_map_snd hY (hZ.prodMk hU) μ y (z, u)
    have ha : a = 0 := le_antisymm (hb ▸ h_le) measureReal_nonneg
    simp [ha, hb]
  · field_simp

omit [Fintype S₁] [Fintype S₃] in
/-- **`p̃` marginal over `(y, u)` is `pXZ`.** Derived from `sum_ptilde_over_y` (collapse `y`, leaving pXZU) and `sum_map_triple_third` (collapse `u`, leaving pXZ). -/
private lemma sum_ptilde_over_y_u
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsFiniteMeasure μ] (x : S₁) (z : S₃) :
    (∑ y : S₂, ∑ u : S₄, ptilde X Y Z U μ (x, y, z, u))
      = (μ.map (fun ω => (X ω, Z ω))).real {(x, z)} := by
  rw [Finset.sum_comm]
  simp_rw [sum_ptilde_over_y hX hY hZ hU μ]
  exact sum_map_triple_third hX hZ hU μ x z

omit [Fintype S₁] [Fintype S₄] in
/-- **`p̃` marginal over `(y, z)` is `pXU`.** Derived from `sum_ptilde_over_y` and `sum_map_triple_second`. -/
private lemma sum_ptilde_over_y_z
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsFiniteMeasure μ] (x : S₁) (u : S₄) :
    (∑ y : S₂, ∑ z : S₃, ptilde X Y Z U μ (x, y, z, u))
      = (μ.map (fun ω => (X ω, U ω))).real {(x, u)} := by
  rw [Finset.sum_comm]
  simp_rw [sum_ptilde_over_y hX hY hZ hU μ]
  exact sum_map_triple_second hX hZ hU μ x u

omit [Fintype S₂] [Fintype S₃] in
/-- **`p̃` marginal over `(x, u)` is `pYZ`.** Derived from `sum_ptilde_over_x` and `sum_map_triple_third`. -/
private lemma sum_ptilde_over_x_u
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsFiniteMeasure μ] (y : S₂) (z : S₃) :
    (∑ x : S₁, ∑ u : S₄, ptilde X Y Z U μ (x, y, z, u))
      = (μ.map (fun ω => (Y ω, Z ω))).real {(y, z)} := by
  rw [Finset.sum_comm]
  simp_rw [sum_ptilde_over_x hX hY hZ hU μ]
  exact sum_map_triple_third hY hZ hU μ y z

omit [Fintype S₂] [Fintype S₄] in
/-- **`p̃` marginal over `(x, z)` is `pYU`.** Derived from `sum_ptilde_over_x` and `sum_map_triple_second`. -/
private lemma sum_ptilde_over_x_z
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsFiniteMeasure μ] (y : S₂) (u : S₄) :
    (∑ x : S₁, ∑ z : S₃, ptilde X Y Z U μ (x, y, z, u))
      = (μ.map (fun ω => (Y ω, U ω))).real {(y, u)} := by
  rw [Finset.sum_comm]
  simp_rw [sum_ptilde_over_x hX hY hZ hU μ]
  exact sum_map_triple_second hY hZ hU μ y u

omit [Fintype S₁] in
/-- **`p̃` marginal over `(y, z, u)` is `pX`.** Derived from `sum_ptilde_over_y_z` and `sum_map_pair_second`. -/
private lemma sum_ptilde_over_y_z_u
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsFiniteMeasure μ] (x : S₁) :
    (∑ y : S₂, ∑ z : S₃, ∑ u : S₄, ptilde X Y Z U μ (x, y, z, u))
      = (μ.map X).real {x} := by
  have step1 : (∑ y : S₂, ∑ z : S₃, ∑ u : S₄, ptilde X Y Z U μ (x, y, z, u))
      = ∑ y : S₂, ∑ u : S₄, ∑ z : S₃, ptilde X Y Z U μ (x, y, z, u) :=
    Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have step2 : (∑ y : S₂, ∑ u : S₄, ∑ z : S₃, ptilde X Y Z U μ (x, y, z, u))
      = ∑ u : S₄, ∑ y : S₂, ∑ z : S₃, ptilde X Y Z U μ (x, y, z, u) :=
    Finset.sum_comm
  rw [step1, step2]
  simp_rw [sum_ptilde_over_y_z hX hY hZ hU μ]
  exact sum_map_pair_second hX hU μ x

omit [Fintype S₂] in
/-- **`p̃` marginal over `(x, z, u)` is `pY`.** Derived from `sum_ptilde_over_x_z` and `sum_map_pair_second`. -/
private lemma sum_ptilde_over_x_z_u
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsFiniteMeasure μ] (y : S₂) :
    (∑ x : S₁, ∑ z : S₃, ∑ u : S₄, ptilde X Y Z U μ (x, y, z, u))
      = (μ.map Y).real {y} := by
  have step1 : (∑ x : S₁, ∑ z : S₃, ∑ u : S₄, ptilde X Y Z U μ (x, y, z, u))
      = ∑ x : S₁, ∑ u : S₄, ∑ z : S₃, ptilde X Y Z U μ (x, y, z, u) :=
    Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have step2 : (∑ x : S₁, ∑ u : S₄, ∑ z : S₃, ptilde X Y Z U μ (x, y, z, u))
      = ∑ u : S₄, ∑ x : S₁, ∑ z : S₃, ptilde X Y Z U μ (x, y, z, u) :=
    Finset.sum_comm
  rw [step1, step2]
  simp_rw [sum_ptilde_over_x_z hX hY hZ hU μ]
  exact sum_map_pair_second hY hU μ y

omit [Fintype S₃] in
/-- **`p̃` marginal over `(x, y, u)` is `pZ`.** Derived from `ptilde_fibre_sum` and `sum_map_pair_second`. -/
private lemma sum_ptilde_over_x_y_u
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsFiniteMeasure μ] (z : S₃) :
    (∑ x : S₁, ∑ y : S₂, ∑ u : S₄, ptilde X Y Z U μ (x, y, z, u))
      = (μ.map Z).real {z} := by
  have step1 : (∑ x : S₁, ∑ y : S₂, ∑ u : S₄, ptilde X Y Z U μ (x, y, z, u))
      = ∑ x : S₁, ∑ u : S₄, ∑ y : S₂, ptilde X Y Z U μ (x, y, z, u) :=
    Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have step2 : (∑ x : S₁, ∑ u : S₄, ∑ y : S₂, ptilde X Y Z U μ (x, y, z, u))
      = ∑ u : S₄, ∑ x : S₁, ∑ y : S₂, ptilde X Y Z U μ (x, y, z, u) :=
    Finset.sum_comm
  rw [step1, step2]
  have hFibre : ∀ u : S₄, (∑ x : S₁, ∑ y : S₂, ptilde X Y Z U μ (x, y, z, u))
      = (μ.map (fun ω => (Z ω, U ω))).real {(z, u)} :=
    fun u => ptilde_fibre_sum hX hY hZ hU μ z u
  simp_rw [hFibre]
  exact sum_map_pair_second hZ hU μ z

omit [Fintype S₄] in
/-- **`p̃` marginal over `(x, y, z)` is `pU`.** Derived from `ptilde_fibre_sum` and `sum_map_pair_first`. -/
private lemma sum_ptilde_over_x_y_z
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsFiniteMeasure μ] (u : S₄) :
    (∑ x : S₁, ∑ y : S₂, ∑ z : S₃, ptilde X Y Z U μ (x, y, z, u))
      = (μ.map U).real {u} := by
  have step1 : (∑ x : S₁, ∑ y : S₂, ∑ z : S₃, ptilde X Y Z U μ (x, y, z, u))
      = ∑ x : S₁, ∑ z : S₃, ∑ y : S₂, ptilde X Y Z U μ (x, y, z, u) :=
    Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have step2 : (∑ x : S₁, ∑ z : S₃, ∑ y : S₂, ptilde X Y Z U μ (x, y, z, u))
      = ∑ z : S₃, ∑ x : S₁, ∑ y : S₂, ptilde X Y Z U μ (x, y, z, u) :=
    Finset.sum_comm
  rw [step1, step2]
  have hFibre : ∀ z : S₃, (∑ x : S₁, ∑ y : S₂, ptilde X Y Z U μ (x, y, z, u))
      = (μ.map (fun ω => (Z ω, U ω))).real {(z, u)} :=
    fun z => ptilde_fibre_sum hX hY hZ hU μ z u
  simp_rw [hFibre]
  exact sum_map_pair_first hZ hU μ u

/-! ### Sum-to-one -/

/-- **`p̃` is a probability distribution.** This is the unconditional half of the Zhang-Yeung auxiliary-distribution argument: `∑_{x,y,z,u} p(x,z,u) p(y,z,u) / p(z,u) = 1` for any probability measure. The proof reshapes the 4-tuple sum via an `Equiv` `S₃ × S₄ × S₁ × S₂ ≃ S₁ × S₂ × S₃ × S₄`, uses `ptilde_fibre_sum` to collapse each `(z, u)` fibre, and reassembles the outer `∑_{z,u} p(z, u) = 1` via the probability-measure property of the pushforward `μ.map ⟨Z, U⟩`. -/
private lemma ptilde_sum_eq_one
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ∑ t : S₁ × S₂ × S₃ × S₄, ptilde X Y Z U μ t = 1 := by
  have hZU_meas : Measurable (fun ω => (Z ω, U ω)) := hZ.prodMk hU
  haveI : IsProbabilityMeasure (μ.map (fun ω => (Z ω, U ω))) :=
    Measure.isProbabilityMeasure_map hZU_meas.aemeasurable
  let e : S₃ × S₄ × S₁ × S₂ ≃ S₁ × S₂ × S₃ × S₄ :=
    { toFun := fun ⟨z, u, x, y⟩ => (x, y, z, u)
      invFun := fun ⟨x, y, z, u⟩ => (z, u, x, y)
      left_inv := fun ⟨_, _, _, _⟩ => rfl
      right_inv := fun ⟨_, _, _, _⟩ => rfl }
  rw [← Equiv.sum_comp e (ptilde X Y Z U μ)]
  simp_rw [Fintype.sum_prod_type]
  have hFibre : ∀ z : S₃, ∀ u : S₄,
      (∑ x : S₁, ∑ y : S₂, ptilde X Y Z U μ (e (z, u, x, y)))
        = (μ.map (fun ω => (Z ω, U ω))).real {(z, u)} :=
    fun z u => ptilde_fibre_sum hX hY hZ hU μ z u
  simp_rw [hFibre]
  have hSingletonSum : (∑ p : S₃ × S₄, (μ.map (fun ω => (Z ω, U ω))).real {p}) = 1 := by
    rw [sum_measureReal_singleton (Finset.univ : Finset (S₃ × S₄))]
    simp
  have hCollapse :
      (∑ z : S₃, ∑ u : S₄, (μ.map (fun ω => (Z ω, U ω))).real {(z, u)}) = 1 := by
    rw [show (∑ z : S₃, ∑ u : S₄, (μ.map (fun ω => (Z ω, U ω))).real {(z, u)})
          = ∑ p : S₃ × S₄, (μ.map (fun ω => (Z ω, U ω))).real {p} from
        (Fintype.sum_prod_type
          (fun p : S₃ × S₄ => (μ.map (fun ω => (Z ω, U ω))).real {p})).symm]
    exact hSingletonSum
  exact hCollapse

/-- **`p̂` is a probability distribution under the hypotheses of Theorem 2.** Collapses by summing over `z` first (using `I[X:Y|Z] = 0` ⇒ `p(x, y, z) = p(x, z) p(y, z) / p(z)`), then using `I[X:Y] = 0` ⇒ `p(x, y) = p(x) p(y)` to cancel the single-variable denominators, then summing over `x, y, u`. -/
private lemma phat_sum_eq_one
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h₁ : I[X : Y ; μ] = 0) (h₂ : I[X : Y | Z ; μ] = 0) :
    ∑ t : S₁ × S₂ × S₃ × S₄, phat X Y Z U μ t = 1 := by
  sorry

/-! ### Δ-to-log-ratio identities -/

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

/-! ### Main proof -/

/-- **Zhang-Yeung delta is nonpositive under the hypotheses of Theorem 2** ([@zhangyeung1997, Theorem 3]). The direct proof (op. cit.) introduces the auxiliary distributions `ptilde` and `phat` (defined above), expands `Δ` as `∑ p · log(p̂ / p̃)`, reweights via `sum_joint_eq_sum_ptilde` to `∑ p̃ · log(p̂ / p̃) = -KL(p̃ ‖ p̂)`, and closes by the log-sum inequality `Real.sum_mul_log_div_leq` applied to `p̃`, `p̂`. The main proof body here is complete and wires `ptilde_sum_eq_one`, `phat_sum_eq_one`, `delta_eq_sum_log_ratio`, `sum_joint_eq_sum_ptilde`, plus the inline absolute-continuity claim, into the final inequality via `linarith`. -/
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
  -- Absolute-continuity side condition for `Real.sum_mul_log_div_leq`:
  -- whenever a factor of `p̂` vanishes, the corresponding marginal of `p̃`
  -- also vanishes (by the pair- and triple-projection bounds), so `p̃ = 0`.
  have h_abs : ∀ t ∈ s, phat X Y Z U μ t = 0 → ptilde X Y Z U μ t = 0 := by
    rintro ⟨x, y, z, u⟩ _ hphat
    simp only [phat, div_eq_zero_iff, mul_eq_zero] at hphat
    have h_XZU_le_XZ := measureReal_map_triple_le_map_pair_12 hX hZ hU μ x z u
    have h_XZU_le_XU := measureReal_map_triple_le_map_pair_13 hX hZ hU μ x z u
    have h_YZU_le_YZ := measureReal_map_triple_le_map_pair_12 hY hZ hU μ y z u
    have h_YZU_le_YU := measureReal_map_triple_le_map_pair_13 hY hZ hU μ y z u
    have h_XZU_le_X := measureReal_map_pair_le_map_fst hX (hZ.prodMk hU) μ x (z, u)
    have h_YZU_le_Y := measureReal_map_pair_le_map_fst hY (hZ.prodMk hU) μ y (z, u)
    have h_ZU_le_Z := measureReal_map_pair_le_map_fst hZ hU μ z u
    have h_ZU_le_U := measureReal_map_pair_le_map_snd hZ hU μ z u
    have hXZU_nn : 0 ≤ (μ.map (fun ω => (X ω, Z ω, U ω))).real {(x, z, u)} := measureReal_nonneg
    have hYZU_nn : 0 ≤ (μ.map (fun ω => (Y ω, Z ω, U ω))).real {(y, z, u)} := measureReal_nonneg
    have hZU_nn : 0 ≤ (μ.map (fun ω => (Z ω, U ω))).real {(z, u)} := measureReal_nonneg
    have kill : (μ.map (fun ω => (X ω, Z ω, U ω))).real {(x, z, u)} = 0
              ∨ (μ.map (fun ω => (Y ω, Z ω, U ω))).real {(y, z, u)} = 0
              ∨ (μ.map (fun ω => (Z ω, U ω))).real {(z, u)} = 0 := by
      rcases hphat with (((h1 | h2) | h3) | h4) | (((h5 | h6) | h7) | h8)
      · left; exact le_antisymm (h_XZU_le_XZ.trans h1.le) hXZU_nn
      · left; exact le_antisymm (h_XZU_le_XU.trans h2.le) hXZU_nn
      · right; left; exact le_antisymm (h_YZU_le_YZ.trans h3.le) hYZU_nn
      · right; left; exact le_antisymm (h_YZU_le_YU.trans h4.le) hYZU_nn
      · right; right; exact le_antisymm (h_ZU_le_Z.trans h5.le) hZU_nn
      · right; right; exact le_antisymm (h_ZU_le_U.trans h6.le) hZU_nn
      · left; exact le_antisymm (h_XZU_le_X.trans h7.le) hXZU_nn
      · right; left; exact le_antisymm (h_YZU_le_Y.trans h8.le) hYZU_nn
    simp only [ptilde]
    rcases kill with hXZU | hYZU | hZU
    · simp [hXZU]
    · simp [hYZU]
    · simp [hZU]
  have h_log_sum : (∑ t ∈ s, ptilde X Y Z U μ t) *
      Real.log ((∑ t ∈ s, ptilde X Y Z U μ t) / (∑ t ∈ s, phat X Y Z U μ t))
        ≤ ∑ t ∈ s, ptilde X Y Z U μ t *
          Real.log (ptilde X Y Z U μ t / phat X Y Z U μ t) :=
    Real.sum_mul_log_div_leq h_ptilde_nn h_phat_nn h_abs
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
