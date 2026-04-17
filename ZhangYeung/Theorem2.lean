import ZhangYeung.Delta
import ZhangYeung.Prelude
import PFR.Mathlib.Analysis.SpecialFunctions.NegMulLog

/-!
# Zhang-Yeung Theorem 2: a conditional information inequality

Theorem 2 of [@zhangyeung1998], originally proved as Theorem 3 of [@zhangyeung1997], states that for any four discrete random variables `X, Y, Z, U`, the hypothesis

  `I[X : Y ; μ] = 0` and `I[X : Y | Z ; μ] = 0`   (eq. 16)

implies the conditional information inequality

  `I[X : Y | ⟨Z, U⟩ ; μ] ≤ I[Z : U | ⟨X, Y⟩ ; μ] + I[X : Y | U ; μ]`.   (eq. 17)

This module formalizes the implication (16) ⇒ (17) on finite-alphabet random variables. It is a standalone formalization of the first known non-Shannon-type conditional information inequality, originally proved in [@zhangyeung1997, Theorem 3]. Kaced and Romashchenko classify it as $(\mathcal{I}_1)$ in their family of essentially conditional inequalities ([@kaced2013]): it holds on the set $\Gamma^*_4$ of constructible entropy functions but fails on its closure $\overline{\Gamma}^*_4$ (loc. cit., Theorem 5), so it is not derivable from the basic Shannon inequalities under any Lagrange combination of the hypotheses.

## Main statements

- `ZhangYeung.theorem2`: the implication (16) ⇒ (17) for discrete random variables on a probability space.

## Implementation notes

The proof has two structurally distinct layers. The first is a Shannon-type algebraic identity (`theorem2_shannon_identity`) that rewrites `I[X:Y|⟨Z,U⟩] - I[Z:U|⟨X,Y⟩] - I[X:Y|U]` as `Δ(Z, U | X, Y) + I[X:Y|Z] - I[X:Y]`, where `Δ` is `ZhangYeung.delta` from the M1 module. Under (16) the two correction terms `I[X:Y|Z]` and `I[X:Y]` vanish, so Theorem 2 reduces to `Δ(Z, U | X, Y) ≤ 0`. The identity is pure Shannon algebra and needs no hypotheses beyond `IsProbabilityMeasure`.

The second layer (`theorem2_delta_le_zero`) discharges the reduced inequality via the [@zhangyeung1997] argument: construct two auxiliary *probability distributions* on `S₁ × S₂ × S₃ × S₄`,

  `p̃(x, y, z, u) := p(x, z, u) p(y, z, u) / p(z, u)`
  `p̂(x, y, z, u) := p(x, z) p(x, u) p(y, z) p(y, u) / [p(z) p(u) p(x) p(y)]`

(both vanishing on the appropriate zero-measure diagonals). Both sum to one -- `p̃` unconditionally, `p̂` by way of the two hypotheses `I[X:Y] = 0` and `I[X:Y|Z] = 0`. One then expands `Δ` and observes that every marginal appearing in the log-expression is shared between the original law and `p̃`, so the `p`-weighted sum equals the `p̃`-weighted sum, and what drops out is exactly `-KL(p̃ ‖ p̂) ≤ 0`. This is an `IsZeroOrProbabilityMeasure`-level KL-divergence argument and does *not* use the kernel/`condIndep_copies` machinery that Candidate A of the milestone plan envisioned; PFR's `KLDiv_nonneg` (and the underlying log-sum inequality `Real.sum_mul_log_div_leq`) is the relevant non-negativity lemma.

**Connection to the 1998 copy construction.** The auxiliary PMF `p̃(x, y, z, u) := p(x, z, u) p(y, z, u) / p(z, u)` defined above is precisely the `(X', Y₁, Z', U')`-marginal of the extended probability measure `ν` that PFR's `ProbabilityTheory.condIndep_copies`, applied to `⟨X, Y⟩` conditioned on `⟨Z, U⟩`, would produce. Projecting the copy -- set `X' := Prod.fst ∘ W₁`, `Y₁ := Prod.snd ∘ W₂`, `⟨Z', U'⟩ := V` -- the conditional independence `X' ⟂ Y₁ | ⟨Z', U'⟩` plus the marginal identities `(X', Z', U') ∼ (X, Z, U)` and `(Y₁, Z', U') ∼ (Y, Z, U)` force `p_ν(x, y, z, u) = p(x, z, u) p(y, z, u) / p(z, u) = p̃(x, y, z, u)`. So the 1997 KL proof and the 1998 two-copy copy-lemma framework reach the same object from two directions: the 1997 paper constructs `p̃` as a PMF and closes via `Real.sum_mul_log_div_leq`; the 1998 paper (Lemma 2 in §III, eq. 44-45) constructs `ν` via kernel composition and closes Theorem 3 (the unconditional inequality) via a Shannon chase on the copy joint. For Theorem 2 specifically a pure copy + Shannon-chase close is ruled out: [@kaced2013, Theorem 3 + Claim 1, Theorem 5] show this inequality is essentially conditional and fails on the closure of the entropic region, so no combination of basic Shannon inequalities plus Lagrange multiples of the premises can derive it. This module follows the 1997 KL route rather than attempting the copy-construction framing.

**Current state:** `theorem2_delta_le_zero` is wired end-to-end, with the main proof body assembled around `Real.sum_mul_log_div_leq` and its absolute-continuity side condition (closed inline via marginal bounds). `ptilde_sum_eq_one`, `phat_sum_eq_one`, and `sum_joint_eq_sum_ptilde` are closed. The `phat_sum_eq_one` closure uses the module-level helpers `condIndepFun_map_triple_real_singleton` (extracting `p(x,y,z) · p(z) = p(x,z) · p(y,z)` from `CondIndepFun X Y Z`), `condIndep_normalized_pair_eq_triple`, and `indepFun_map_pair_real_singleton` (extracting `p(x,y) = p(x) · p(y)` from `IndepFun X Y`); the `sum_joint_eq_sum_ptilde` closure is the 11-factor marginal-swap closing argument, factored through the `marg_swap_helper` helper. One scaffolded sub-lemma remains `sorry`:

- `delta_eq_sum_log_ratio` (entropy expansion over the 4-tuple space; the `entropy_eq_sum_joint` helper lifts each entropy `H[f ; μ]` to a 4-tuple weighted sum, after which the eleven signed entropy contributions recombine into `∑ p · log (p̂/p̃)`; the algebraic recombination step is the residual work).

The file is organized into the following sections:

1. `theorem2_shannon_identity` -- Shannon-algebra reduction to `Δ ≤ 0`.
2. Auxiliary distributions `p̃`, `p̂` (plus `pJoint`) and their nonnegativity.
3. Generic finite-alphabet utilities (marginal summations, marginal bounds, `IndepFun` product formula, fibrewise-swap helper).
4. The eleven marginal-match facts for `p̃`.
5. Sum-to-one facts (`ptilde_sum_eq_one` and `phat_sum_eq_one` closed).
6. Δ-to-log-ratio identities (`delta_eq_sum_log_ratio` sorry; `sum_joint_eq_sum_ptilde` closed).
7. `theorem2_delta_le_zero` + `theorem2`.

The four codomains `S₁, S₂, S₃, S₄` are specialized to `[Fintype]` + `[MeasurableSingletonClass]` so PFR's `FiniteRange`/`Countable` obligations are discharged uniformly.

Paper ordering `(X, Y, Z, U)` is followed here because Theorem 2 is a standalone inequality read most naturally in that order; `ZhangYeung/Delta.lean` uses `(Z, U, X, Y)` because the delta quantity is symmetric in its first two arguments. The two modules share no variables, so the naming clash across `S₁..S₄` is harmless, and the `ZhangYeung.delta` identifier appearing in the helpers below takes its arguments in Delta.lean's order: `delta Z U X Y μ`.

## References

* [@zhangyeung1997] -- the 1997 paper containing the KL-divergence proof of the inequality (as Theorem 3 of that paper). See `references/papers/zhangyeung1997.pdf`.
* [@zhangyeung1998] -- the 1998 paper; Theorem 2 there restates the 1997 result. See `references/transcriptions/zhangyeung1998.md` for a verbatim transcription of equations (16) and (17), verified 2026-04-16.
* [@kaced2013] -- Kaced and Romashchenko classify the inequality as $(\mathcal{I}_1)$ in a family of essentially conditional inequalities. Theorem 3 + Claim 1 prove essential conditionality; Theorem 5 shows $(\mathcal{I}_1)$ fails on $\overline{\Gamma}^*_n$. Available as arXiv:1207.5742.

## Tags

Shannon entropy, conditional mutual information, conditional information inequality, Kullback-Leibler divergence, Zhang-Yeung, essentially conditional inequality
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

/-- **Pushforward marginal via fibre sum.** For a measurable `F : Ω' → α` and a measurable projection `proj : α → γ`, the sum of `(μ.map F).real {t}` over the fibre of `proj` at `b` equals the image-measure at `b` of the composite pushforward `proj ∘ F`. This is the generic "marginalize a pushforward by composing with a projection" identity, used to derive the pJoint fibre-sum identities for each of the eleven projections in `sum_joint_eq_sum_ptilde`. -/
private lemma sum_filter_map_real_eq_map_comp
    {α γ : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace γ] [MeasurableSingletonClass γ] [DecidableEq γ]
    {Ω' : Type*} [MeasurableSpace Ω']
    {F : Ω' → α} {proj : α → γ} (hF : Measurable F) (hproj : Measurable proj)
    (μ : Measure Ω') [IsFiniteMeasure μ] (b : γ) :
    (∑ t ∈ (Finset.univ : Finset α).filter (fun t => proj t = b), (μ.map F).real {t})
      = (μ.map (fun ω => proj (F ω))).real {b} := by
  have hcomp : Measurable (fun ω => proj (F ω)) := hproj.comp hF
  simp_rw [map_measureReal_apply hF (measurableSet_singleton _)]
  rw [map_measureReal_apply hcomp (measurableSet_singleton _)]
  have hUnion : (fun ω => proj (F ω)) ⁻¹' {b}
      = ⋃ t ∈ (Finset.univ.filter (fun t : α => proj t = b) : Finset α), F ⁻¹' {t} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion,
               Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨F ω, h, rfl⟩, fun ⟨_, ht, hωt⟩ => hωt ▸ ht⟩
  rw [hUnion]
  refine (measureReal_biUnion_finset ?_ ?_).symm
  · rintro t₁ - t₂ - hne
    rw [Function.onFun, Set.disjoint_left]
    intro ω hω₁ hω₂
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω₁ hω₂
    exact hne (hω₁.symm.trans hω₂)
  · exact fun _ _ => hF (measurableSet_singleton _)

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

/-- **CondIndepFun at singletons: the pointwise product formula.** The conditional analogue of `indepFun_map_pair_real_singleton`. Under `CondIndepFun f g h μ` with a probability measure, the three-way marginal factorizes as `p(a, b, c) · p(c) = p(a, c) · p(b, c)`. The zero-measure branch (when `p(c) = 0`) closes via the `measureReal_map_pair_le_map_snd` bound; the positive branch unpacks `CondIndepFun` at `c` via `ae_iff_of_countable`, applies the unconditional product formula on the fibre `(μ[|h ← c])`, and multiplies through by `p(c)` in ENNReal to clear the two conditional denominators. -/
private lemma condIndepFun_map_triple_real_singleton
    {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    [Fintype γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
    {Ω' : Type*} [MeasurableSpace Ω']
    {f : Ω' → α} {g : Ω' → β} {h : Ω' → γ}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    {μ : Measure Ω'} [IsProbabilityMeasure μ]
    (h_cond : CondIndepFun f g h μ) (a : α) (b : β) (c : γ) :
    (μ.map (fun ω => (f ω, g ω, h ω))).real {(a, b, c)} * (μ.map h).real {c}
      = (μ.map (fun ω => (f ω, h ω))).real {(a, c)}
        * (μ.map (fun ω => (g ω, h ω))).real {(b, c)} := by
  by_cases hc_zero : (μ.map h).real {c} = 0
  · rw [hc_zero, mul_zero,
        le_antisymm (hc_zero ▸ measureReal_map_pair_le_map_snd hf hh μ a c) measureReal_nonneg,
        zero_mul]
  · -- Positive case.
    have h_map_c_ne : (μ.map h) {c} ≠ 0 := fun heq => hc_zero (by
      rw [measureReal_def, heq]; rfl)
    have h_h_pre_ne : μ (h ⁻¹' {c}) ≠ 0 := by
      rw [← Measure.map_apply hh (measurableSet_singleton c)]; exact h_map_c_ne
    have h_h_pre_top : μ (h ⁻¹' {c}) ≠ ⊤ := measure_ne_top _ _
    have h_Xinv_ne : (μ (h ⁻¹' {c}))⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr h_h_pre_top
    have h_Xinv_top : (μ (h ⁻¹' {c}))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr h_h_pre_ne
    have h_cancel : μ (h ⁻¹' {c}) * (μ (h ⁻¹' {c}))⁻¹ = 1 :=
      ENNReal.mul_inv_cancel h_h_pre_ne h_h_pre_top
    -- Extract IndepFun on the conditional.
    have h_cond' : ∀ᵐ z ∂(μ.map h), IndepFun f g (μ[|h ← z]) := h_cond
    rw [ae_iff_of_countable] at h_cond'
    have h_indep : IndepFun f g (μ[|h ← c]) := h_cond' c h_map_c_ne
    have h_prod_cond : (μ[|h ← c]) (f ⁻¹' {a} ∩ g ⁻¹' {b})
        = (μ[|h ← c]) (f ⁻¹' {a}) * (μ[|h ← c]) (g ⁻¹' {b}) :=
      (indepFun_iff_measure_inter_preimage_eq_mul).mp h_indep {a} {b}
        (measurableSet_singleton a) (measurableSet_singleton b)
    simp_rw [cond_apply (hh (measurableSet_singleton c))] at h_prod_cond
    -- `h_prod_cond : X⁻¹ * μ(h⁻¹{c} ∩ (f⁻¹{a} ∩ g⁻¹{b}))
    --                = X⁻¹ * μ(h⁻¹{c} ∩ f⁻¹{a}) * (X⁻¹ * μ(h⁻¹{c} ∩ g⁻¹{b}))`
    -- Rearrange the right-hand side via `mul_mul_mul_comm`, then cancel `X⁻¹` on the left.
    rw [mul_mul_mul_comm, mul_assoc] at h_prod_cond
    -- Now `h_prod_cond : X⁻¹ * P = X⁻¹ * (X⁻¹ * (F * G))`. Multiply both by `X` twice.
    have h_step1 : μ (h ⁻¹' {c} ∩ (f ⁻¹' {a} ∩ g ⁻¹' {b}))
        = (μ (h ⁻¹' {c}))⁻¹ * (μ (h ⁻¹' {c} ∩ f ⁻¹' {a}) * μ (h ⁻¹' {c} ∩ g ⁻¹' {b})) := by
      have := congrArg (fun y => μ (h ⁻¹' {c}) * y) h_prod_cond
      simp only at this
      rw [← mul_assoc (μ (h ⁻¹' {c})) _ (μ (h ⁻¹' {c} ∩ (f ⁻¹' {a} ∩ g ⁻¹' {b}))),
          h_cancel, one_mul,
          ← mul_assoc (μ (h ⁻¹' {c})) _ (_ * (_ * _)),
          h_cancel, one_mul] at this
      exact this
    -- `h_step1 : P = X⁻¹ * (F * G)`. Multiply by `X` to clear.
    have h_step2 : μ (h ⁻¹' {c}) * μ (h ⁻¹' {c} ∩ (f ⁻¹' {a} ∩ g ⁻¹' {b}))
        = μ (h ⁻¹' {c} ∩ f ⁻¹' {a}) * μ (h ⁻¹' {c} ∩ g ⁻¹' {b}) := by
      rw [h_step1, ← mul_assoc, h_cancel, one_mul]
    -- Translate to target form.
    have h_T_eq : (fun ω => (f ω, g ω, h ω)) ⁻¹' {(a, b, c)}
        = h ⁻¹' {c} ∩ (f ⁻¹' {a} ∩ g ⁻¹' {b}) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Prod.mk.injEq]
      tauto
    have h_A_eq : (fun ω => (f ω, h ω)) ⁻¹' {(a, c)} = h ⁻¹' {c} ∩ f ⁻¹' {a} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Prod.mk.injEq]
      tauto
    have h_B_eq : (fun ω => (g ω, h ω)) ⁻¹' {(b, c)} = h ⁻¹' {c} ∩ g ⁻¹' {b} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Prod.mk.injEq]
      tauto
    rw [map_measureReal_apply (hf.prodMk (hg.prodMk hh)) (measurableSet_singleton _),
        map_measureReal_apply (hf.prodMk hh) (measurableSet_singleton _),
        map_measureReal_apply (hg.prodMk hh) (measurableSet_singleton _),
        map_measureReal_apply hh (measurableSet_singleton _),
        h_T_eq, h_A_eq, h_B_eq]
    -- Convert ENNReal → Real.
    rw [show μ.real (h ⁻¹' {c} ∩ (f ⁻¹' {a} ∩ g ⁻¹' {b}))
          = (μ (h ⁻¹' {c} ∩ (f ⁻¹' {a} ∩ g ⁻¹' {b}))).toReal from rfl,
        show μ.real (h ⁻¹' {c}) = (μ (h ⁻¹' {c})).toReal from rfl,
        show μ.real (h ⁻¹' {c} ∩ f ⁻¹' {a}) = (μ (h ⁻¹' {c} ∩ f ⁻¹' {a})).toReal from rfl,
        show μ.real (h ⁻¹' {c} ∩ g ⁻¹' {b}) = (μ (h ⁻¹' {c} ∩ g ⁻¹' {b})).toReal from rfl]
    rw [← ENNReal.toReal_mul, ← ENNReal.toReal_mul, mul_comm (μ (h ⁻¹' {c} ∩ _)) _]
    exact congrArg ENNReal.toReal h_step2

/-- **Pointwise conditional factorization of `p̃`-style fibre.** Under `CondIndepFun f g h μ` (with `μ` a probability measure on a Fintype `h`-codomain), the "normalized pair" `(μ.map ⟨f, h⟩).real {(a, c)} · (μ.map ⟨g, h⟩).real {(b, c)} / (μ.map h).real {c}` equals the triple marginal `(μ.map ⟨f, g, h⟩).real {(a, b, c)}`. On the null support of `(μ.map h).real {c}`, both sides vanish (via the pair/triple marginal bounds). -/
private lemma condIndep_normalized_pair_eq_triple
    {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    [Fintype γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
    {Ω' : Type*} [MeasurableSpace Ω']
    {f : Ω' → α} {g : Ω' → β} {h : Ω' → γ}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    {μ : Measure Ω'} [IsProbabilityMeasure μ]
    (h_cond : CondIndepFun f g h μ) (a : α) (b : β) (c : γ) :
    (μ.map (fun ω => (f ω, h ω))).real {(a, c)}
        * (μ.map (fun ω => (g ω, h ω))).real {(b, c)} / (μ.map h).real {c}
      = (μ.map (fun ω => (f ω, g ω, h ω))).real {(a, b, c)} := by
  by_cases hc_zero : (μ.map h).real {c} = 0
  · rw [hc_zero, div_zero]
    have h_fgh_le : (μ.map (fun ω => (f ω, g ω, h ω))).real {(a, b, c)}
        ≤ (μ.map h).real {c} := by
      rw [map_measureReal_apply (hf.prodMk (hg.prodMk hh)) (measurableSet_singleton _),
          map_measureReal_apply hh (measurableSet_singleton _)]
      apply measureReal_mono _ (measure_ne_top _ _)
      intro ω hω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq] at hω ⊢
      exact hω.2.2
    exact (le_antisymm (hc_zero ▸ h_fgh_le) measureReal_nonneg).symm
  · have h_prod := condIndepFun_map_triple_real_singleton hf hg hh h_cond a b c
    rw [div_eq_iff hc_zero]
    linarith

/-- **`p̂` is a probability distribution under the hypotheses of Theorem 2.** Collapses by summing over `z` first (using `I[X:Y|Z] = 0` ⇒ `p(x, y, z) · p(z) = p(x, z) · p(y, z)` via `condIndepFun_map_triple_real_singleton`), then using `I[X:Y] = 0` ⇒ `p(x, y) = p(x) · p(y)` (via `indepFun_map_pair_real_singleton`) to cancel the single-variable denominators, then summing over `x, y, u`. -/
private lemma phat_sum_eq_one
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h₁ : I[X : Y ; μ] = 0) (h₂ : I[X : Y | Z ; μ] = 0) :
    ∑ t : S₁ × S₂ × S₃ × S₄, phat X Y Z U μ t = 1 := by
  have h_indep : IndepFun X Y μ := (mutualInfo_eq_zero hX hY).mp h₁
  have h_cond : CondIndepFun X Y Z μ := (condMutualInfo_eq_zero hX hY).mp h₂
  -- **Pointwise identity (h_phat_mul).** `phat(x, y, z, u) * pZ pU pX pY = pXZ * pXU * pYZ * pYU`.
  -- Clearing the denominator in the definition of phat (works universally via 0/0 = 0 and marginal bounds on the numerator).
  have h_phat_mul : ∀ (x : S₁) (y : S₂) (z : S₃) (u : S₄),
      phat X Y Z U μ (x, y, z, u)
        * ((μ.map Z).real {z} * (μ.map U).real {u} * (μ.map X).real {x} * (μ.map Y).real {y})
      = (μ.map (fun ω => (X ω, Z ω))).real {(x, z)}
        * (μ.map (fun ω => (X ω, U ω))).real {(x, u)}
        * (μ.map (fun ω => (Y ω, Z ω))).real {(y, z)}
        * (μ.map (fun ω => (Y ω, U ω))).real {(y, u)} := by
    intros x y z u
    by_cases hD : (μ.map Z).real {z} * (μ.map U).real {u} * (μ.map X).real {x} * (μ.map Y).real {y} = 0
    · -- Denom = 0: need to show num = 0 using marginal bounds, then phat * 0 = 0 = num.
      rw [hD, mul_zero]
      have h_or : (μ.map Z).real {z} = 0 ∨ (μ.map U).real {u} = 0 ∨
                  (μ.map X).real {x} = 0 ∨ (μ.map Y).real {y} = 0 := by
        simp only [mul_eq_zero] at hD; tauto
      rcases h_or with hZ0 | hU0 | hX0 | hY0
      · have : (μ.map (fun ω => (X ω, Z ω))).real {(x, z)} = 0 :=
          le_antisymm (hZ0 ▸ measureReal_map_pair_le_map_snd hX hZ μ x z) measureReal_nonneg
        rw [this]; ring
      · have : (μ.map (fun ω => (X ω, U ω))).real {(x, u)} = 0 :=
          le_antisymm (hU0 ▸ measureReal_map_pair_le_map_snd hX hU μ x u) measureReal_nonneg
        rw [this]; ring
      · have : (μ.map (fun ω => (X ω, Z ω))).real {(x, z)} = 0 :=
          le_antisymm (hX0 ▸ measureReal_map_pair_le_map_fst hX hZ μ x z) measureReal_nonneg
        rw [this]; ring
      · have : (μ.map (fun ω => (Y ω, Z ω))).real {(y, z)} = 0 :=
          le_antisymm (hY0 ▸ measureReal_map_pair_le_map_fst hY hZ μ y z) measureReal_nonneg
        rw [this]; ring
    · -- Denom ≠ 0: cancel directly.
      show phat X Y Z U μ (x, y, z, u) * _ = _
      change (_ / _) * _ = _
      rw [div_mul_cancel₀ _ hD]
  -- **Pointwise identity (h_point).** Applying condIndepFun to the above:
  -- `phat * pU pX pY = pXYZ * pXU * pYU`.
  have h_point : ∀ (x : S₁) (y : S₂) (z : S₃) (u : S₄),
      phat X Y Z U μ (x, y, z, u)
        * ((μ.map U).real {u} * (μ.map X).real {x} * (μ.map Y).real {y})
      = (μ.map (fun ω => (X ω, Y ω, Z ω))).real {(x, y, z)}
        * (μ.map (fun ω => (X ω, U ω))).real {(x, u)}
        * (μ.map (fun ω => (Y ω, U ω))).real {(y, u)} := by
    intros x y z u
    have h_helper := condIndepFun_map_triple_real_singleton hX hY hZ h_cond x y z
    -- h_helper : pXYZ * pZ = pXZ * pYZ. Multiply `h_phat_mul x y z u` identity through by pZ:
    -- LHS * pZ (of h_point): phat * (pU pX pY) * pZ = phat * (pZ pU pX pY) = pXZ pXU pYZ pYU.
    -- RHS * pZ (of h_point): pXYZ pXU pYU * pZ = (pXYZ pZ) * pXU pYU = (pXZ pYZ) pXU pYU = pXZ pXU pYZ pYU.
    -- Both equal, so LHS = RHS after cancelling pZ (case: pZ > 0) or directly in pZ = 0 case.
    by_cases hZ_zero : (μ.map Z).real {z} = 0
    · have hphat_zero : phat X Y Z U μ (x, y, z, u) = 0 := by
        unfold phat
        simp [hZ_zero]
      have hXYZ_zero : (μ.map (fun ω => (X ω, Y ω, Z ω))).real {(x, y, z)} = 0 := by
        have h1 : (μ.map (fun ω => (X ω, Y ω, Z ω))).real {(x, y, z)}
            ≤ (μ.map (fun ω => (X ω, Z ω))).real {(x, z)} :=
          measureReal_map_triple_le_map_pair_13 hX hY hZ μ x y z
        have h2 : (μ.map (fun ω => (X ω, Z ω))).real {(x, z)} ≤ (μ.map Z).real {z} :=
          measureReal_map_pair_le_map_snd hX hZ μ x z
        linarith [measureReal_nonneg (μ := μ.map (fun ω => (X ω, Y ω, Z ω))) (s := ({(x, y, z)} : Set _))]
      rw [hphat_zero, zero_mul, hXYZ_zero, zero_mul, zero_mul]
    · -- pZ > 0: multiply both sides by pZ and use h_phat_mul, h_helper.
      have h_muled : (phat X Y Z U μ (x, y, z, u)
          * ((μ.map U).real {u} * (μ.map X).real {x} * (μ.map Y).real {y})) * (μ.map Z).real {z}
        = ((μ.map (fun ω => (X ω, Y ω, Z ω))).real {(x, y, z)}
            * (μ.map (fun ω => (X ω, U ω))).real {(x, u)}
            * (μ.map (fun ω => (Y ω, U ω))).real {(y, u)}) * (μ.map Z).real {z} := by
        have h_lhs : (phat X Y Z U μ (x, y, z, u)
            * ((μ.map U).real {u} * (μ.map X).real {x} * (μ.map Y).real {y})) * (μ.map Z).real {z}
          = phat X Y Z U μ (x, y, z, u)
            * ((μ.map Z).real {z} * (μ.map U).real {u} * (μ.map X).real {x} * (μ.map Y).real {y}) := by
          ring
        rw [h_lhs, h_phat_mul x y z u]
        have h_rhs : ((μ.map (fun ω => (X ω, Y ω, Z ω))).real {(x, y, z)}
            * (μ.map (fun ω => (X ω, U ω))).real {(x, u)}
            * (μ.map (fun ω => (Y ω, U ω))).real {(y, u)}) * (μ.map Z).real {z}
          = ((μ.map (fun ω => (X ω, Y ω, Z ω))).real {(x, y, z)} * (μ.map Z).real {z})
            * ((μ.map (fun ω => (X ω, U ω))).real {(x, u)} * (μ.map (fun ω => (Y ω, U ω))).real {(y, u)}) := by
          ring
        rw [h_rhs, h_helper]; ring
      exact mul_right_cancel₀ hZ_zero h_muled
  -- **Sum over z:** `∑ z, phat(x, y, z, u) = pXU(x, u) * pYU(y, u) / pU(u)`.
  have h_indep_pair : ∀ x y, (μ.map (fun ω => (X ω, Y ω))).real {(x, y)}
      = (μ.map X).real {x} * (μ.map Y).real {y} :=
    fun x y => indepFun_map_pair_real_singleton hX hY h_indep x y
  have h_sum_z : ∀ (x : S₁) (y : S₂) (u : S₄),
      (∑ z : S₃, phat X Y Z U μ (x, y, z, u))
        * ((μ.map U).real {u} * (μ.map X).real {x} * (μ.map Y).real {y})
      = (μ.map (fun ω => (X ω, U ω))).real {(x, u)}
        * (μ.map (fun ω => (Y ω, U ω))).real {(y, u)}
        * ((μ.map X).real {x} * (μ.map Y).real {y}) := by
    intros x y u
    rw [Finset.sum_mul]
    simp_rw [h_point x y _ u]
    rw [show (∑ z : S₃, (μ.map (fun ω => (X ω, Y ω, Z ω))).real {(x, y, z)}
              * (μ.map (fun ω => (X ω, U ω))).real {(x, u)}
              * (μ.map (fun ω => (Y ω, U ω))).real {(y, u)})
           = (μ.map (fun ω => (X ω, U ω))).real {(x, u)}
             * (μ.map (fun ω => (Y ω, U ω))).real {(y, u)}
             * (∑ z : S₃, (μ.map (fun ω => (X ω, Y ω, Z ω))).real {(x, y, z)}) from by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun z _ => by ring]
    rw [sum_map_triple_third hX hY hZ μ x y, h_indep_pair]
  -- **Normalize.** `∑ z, phat(x, y, z, u) = pXU(x, u) * pYU(y, u) / pU(u)` even at zeros.
  have h_sum_z_eq : ∀ (x : S₁) (y : S₂) (u : S₄),
      (∑ z : S₃, phat X Y Z U μ (x, y, z, u))
        = (μ.map (fun ω => (X ω, U ω))).real {(x, u)}
          * (μ.map (fun ω => (Y ω, U ω))).real {(y, u)}
          / (μ.map U).real {u} := by
    intros x y u
    have h := h_sum_z x y u
    by_cases hU_zero : (μ.map U).real {u} = 0
    · have h_phat_zero : ∀ z, phat X Y Z U μ (x, y, z, u) = 0 := by
        intro z; unfold phat; simp [hU_zero]
      rw [Finset.sum_congr rfl (fun z _ => h_phat_zero z), Finset.sum_const_zero, hU_zero, div_zero]
    by_cases hX_zero : (μ.map X).real {x} = 0
    · have hXU_zero : (μ.map (fun ω => (X ω, U ω))).real {(x, u)} = 0 :=
        le_antisymm (hX_zero ▸ measureReal_map_pair_le_map_fst hX hU μ x u) measureReal_nonneg
      have h_phat_zero : ∀ z, phat X Y Z U μ (x, y, z, u) = 0 := by
        intro z; unfold phat; simp [hX_zero]
      rw [Finset.sum_congr rfl (fun z _ => h_phat_zero z), Finset.sum_const_zero, hXU_zero, zero_mul, zero_div]
    by_cases hY_zero : (μ.map Y).real {y} = 0
    · have hYU_zero : (μ.map (fun ω => (Y ω, U ω))).real {(y, u)} = 0 :=
        le_antisymm (hY_zero ▸ measureReal_map_pair_le_map_fst hY hU μ y u) measureReal_nonneg
      have h_phat_zero : ∀ z, phat X Y Z U μ (x, y, z, u) = 0 := by
        intro z; unfold phat; simp [hY_zero]
      rw [Finset.sum_congr rfl (fun z _ => h_phat_zero z), Finset.sum_const_zero, hYU_zero, mul_zero, zero_div]
    -- All positive.
    have h_denom_ne : (μ.map U).real {u} * (μ.map X).real {x} * (μ.map Y).real {y} ≠ 0 := by
      intro heq; simp only [mul_eq_zero] at heq
      rcases heq with (h | h) | h
      exacts [hU_zero h, hX_zero h, hY_zero h]
    have hXY_ne : (μ.map X).real {x} * (μ.map Y).real {y} ≠ 0 := by
      intro heq; simp only [mul_eq_zero] at heq
      rcases heq with h | h
      exacts [hX_zero h, hY_zero h]
    -- From h: (∑_z phat) * (pU pX pY) = pXU pYU * (pX pY)
    -- Divide by (pU pX pY):
    have h' : ∑ z, phat X Y Z U μ (x, y, z, u)
            = (μ.map (fun ω => (X ω, U ω))).real {(x, u)}
              * (μ.map (fun ω => (Y ω, U ω))).real {(y, u)}
              * ((μ.map X).real {x} * (μ.map Y).real {y})
              / ((μ.map U).real {u} * (μ.map X).real {x} * (μ.map Y).real {y}) := by
      rw [eq_div_iff h_denom_ne]; exact h
    rw [h']
    field_simp
  -- **Outer telescope:** reshape the 4-tuple sum via an `Equiv`, collapse ∑_z
  -- using h_sum_z_eq, then telescope ∑_y, ∑_x, ∑_u.
  let e : S₄ × S₁ × S₂ × S₃ ≃ S₁ × S₂ × S₃ × S₄ :=
    { toFun := fun ⟨u, x, y, z⟩ => (x, y, z, u)
      invFun := fun ⟨x, y, z, u⟩ => (u, x, y, z)
      left_inv := fun ⟨_, _, _, _⟩ => rfl
      right_inv := fun ⟨_, _, _, _⟩ => rfl }
  rw [← Equiv.sum_comp e (phat X Y Z U μ)]
  show ∑ p : S₄ × S₁ × S₂ × S₃, phat X Y Z U μ (p.2.1, p.2.2.1, p.2.2.2, p.1) = 1
  simp_rw [Fintype.sum_prod_type]
  -- Goal: ∑ u, ∑ x, ∑ y, ∑ z, phat(x, y, z, u) = 1.
  simp_rw [h_sum_z_eq]
  -- Goal: ∑ u, ∑ x, ∑ y, pXU(x, u) * pYU(y, u) / pU(u) = 1.
  -- ∑_y pYU(y, u) / pU = pU / pU = 1 (when pU > 0).
  have h_sum_y : ∀ (x : S₁) (u : S₄),
      (∑ y : S₂, (μ.map (fun ω => (X ω, U ω))).real {(x, u)}
          * (μ.map (fun ω => (Y ω, U ω))).real {(y, u)} / (μ.map U).real {u})
        = (μ.map (fun ω => (X ω, U ω))).real {(x, u)} := by
    intros x u
    by_cases hU_zero : (μ.map U).real {u} = 0
    · have hXU_zero : (μ.map (fun ω => (X ω, U ω))).real {(x, u)} = 0 :=
        le_antisymm (hU_zero ▸ measureReal_map_pair_le_map_snd hX hU μ x u) measureReal_nonneg
      simp [hXU_zero]
    -- pU > 0. Factor out pXU/pU and use sum_map_pair_first on pYU to get pU.
    rw [show (∑ y : S₂, (μ.map (fun ω => (X ω, U ω))).real {(x, u)}
                * (μ.map (fun ω => (Y ω, U ω))).real {(y, u)} / (μ.map U).real {u})
            = ((μ.map (fun ω => (X ω, U ω))).real {(x, u)} / (μ.map U).real {u})
              * ∑ y : S₂, (μ.map (fun ω => (Y ω, U ω))).real {(y, u)} from by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring]
    rw [sum_map_pair_first hY hU μ u]
    field_simp
  simp_rw [h_sum_y]
  -- Goal: ∑ u, ∑ x, pXU(x, u) = 1.
  simp_rw [sum_map_pair_first hX hU μ]
  -- Goal: ∑ u, pU u = 1.
  haveI : IsProbabilityMeasure (μ.map U) := Measure.isProbabilityMeasure_map hU.aemeasurable
  rw [sum_measureReal_singleton (Finset.univ : Finset S₄)]
  simp

/-! ### Δ-to-log-ratio identities -/

/-- **Entropy as a 4-tuple weighted log sum.** For a measurable `F : Ω' → α` and a measurable projection `proj : α → β`, `H[proj ∘ F ; μ]` can be written as a sum over the full range of `F` weighted by `(μ.map F).real`. This follows from `entropy_eq_sum` (a sum over the projected range) by fibrewise decomposition along `proj`, using `sum_filter_map_real_eq_map_comp` to identify the fibre sum of `μ.map F` with `(μ.map (proj ∘ F)).real {b}`. Used to lift each of the eleven entropy terms in the expansion of `delta Z U X Y μ` to a common 4-tuple weighted sum. -/
private lemma entropy_eq_sum_joint
    {α β : Type*}
    [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β] [DecidableEq β]
    {Ω' : Type*} [MeasurableSpace Ω']
    (F : Ω' → α) (proj : α → β)
    (hF : Measurable F) (hproj : Measurable proj)
    (μ : Measure Ω') [IsProbabilityMeasure μ] :
    H[fun ω => proj (F ω) ; μ]
      = -∑ t : α, (μ.map F).real {t}
          * Real.log ((μ.map (fun ω => proj (F ω))).real {proj t}) := by
  have hcomp : Measurable (fun ω => proj (F ω)) := hproj.comp hF
  have hA : (μ.map (fun ω => proj (F ω))) ((Finset.univ : Finset β) : Set β)ᶜ = 0 := by simp
  rw [entropy_eq_sum_finset hA]
  -- Goal: (∑ b : β, negMulLog (p_f b)) = -∑ t : α, p_F(t) * log (p_f (π t))
  simp_rw [Real.negMulLog, neg_mul]
  rw [Finset.sum_neg_distrib]
  congr 1
  classical
  rw [← Finset.sum_fiberwise (Finset.univ : Finset α) proj
      (fun t => (μ.map F).real {t} * Real.log ((μ.map (fun ω => proj (F ω))).real {proj t}))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [show (∑ t ∈ (Finset.univ : Finset α).filter (fun t => proj t = b),
              (μ.map F).real {t} * Real.log ((μ.map (fun ω => proj (F ω))).real {proj t}))
         = (∑ t ∈ (Finset.univ : Finset α).filter (fun t => proj t = b), (μ.map F).real {t})
           * Real.log ((μ.map (fun ω => proj (F ω))).real {b}) from by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [(Finset.mem_filter.mp ht).2]]
  rw [sum_filter_map_real_eq_map_comp hF hproj μ b]

/-- **`Δ` as a weighted-log sum.** The identity `Δ(Z, U | X, Y) = ∑_{x,y,z,u} p(x,y,z,u) · log (p̂(x,y,z,u) / p̃(x,y,z,u))` obtained by expanding each of `I[Z:U]`, `I[Z:U|X]`, `I[Z:U|Y]` via `entropy_eq_sum_joint` over the 4-tuple marginal and combining the eleven lifted contributions. The right-hand side is the raw form of Zhang-Yeung 1997's eq. (41). -/
private lemma delta_eq_sum_log_ratio
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    delta Z U X Y μ
      = ∑ t : S₁ × S₂ × S₃ × S₄,
          pJoint X Y Z U μ t * Real.log (phat X Y Z U μ t / ptilde X Y Z U μ t) := by
  sorry

/-- **Marginal-swap helper.** Given a measurable projection `proj : S₁ × S₂ × S₃ × S₄ → γ` of the 4-tuple alphabet, and given that `p̃` agrees with the μ-pushforward of `proj ∘ ⟨X, Y, Z, U⟩` on every fibre, the sum of `pJoint · φ(proj ·)` equals the sum of `p̃ · φ(proj ·)` for any `φ`. The pJoint half of the filter-sum identity is automatic from `sum_filter_map_real_eq_map_comp` (since `pJoint` is a pushforward singleton value); the `p̃` half is the `h_pt_marg` hypothesis. This helper factors out the shared bookkeeping of the eleven projection-specific applications in `sum_joint_eq_sum_ptilde`. -/
private lemma marg_swap_helper
    {γ : Type*} [Fintype γ] [MeasurableSpace γ] [MeasurableSingletonClass γ] [DecidableEq γ]
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (proj : S₁ × S₂ × S₃ × S₄ → γ) (hproj : Measurable proj) (φ : γ → ℝ)
    (h_pt_marg : ∀ b : γ,
        (∑ t ∈ (Finset.univ : Finset (S₁ × S₂ × S₃ × S₄)).filter
            (fun t => proj t = b), ptilde X Y Z U μ t)
          = (μ.map (fun ω => proj (X ω, Y ω, Z ω, U ω))).real {b}) :
    ∑ t : S₁ × S₂ × S₃ × S₄, pJoint X Y Z U μ t * φ (proj t)
      = ∑ t : S₁ × S₂ × S₃ × S₄, ptilde X Y Z U μ t * φ (proj t) := by
  have hF : Measurable (fun ω => (X ω, Y ω, Z ω, U ω)) :=
    hX.prodMk (hY.prodMk (hZ.prodMk hU))
  refine sum_mul_proj_eq_of_marginal_eq (pJoint X Y Z U μ) (ptilde X Y Z U μ) proj φ ?_
  intro b
  have h_pJ : (∑ t ∈ (Finset.univ : Finset (S₁ × S₂ × S₃ × S₄)).filter
        (fun t => proj t = b), pJoint X Y Z U μ t)
      = (μ.map (fun ω => proj (X ω, Y ω, Z ω, U ω))).real {b} := by
    simp only [pJoint]
    exact sum_filter_map_real_eq_map_comp hF hproj μ b
  rw [h_pJ, h_pt_marg b]

set_option maxHeartbeats 2400000 in
/-- **Marginal swap.** Every factor appearing in the log-ratio `p̂ / p̃` is a marginal distribution common to `p` and `p̃` -- the full list is `{p(z,u), p(x,z), p(x,u), p(y,z), p(y,u), p(x,z,u), p(y,z,u), p(z), p(u), p(x), p(y)}`. The `p`-weighted sum therefore agrees with the `p̃`-weighted sum on each factor, and the eleven summands recombine to `∑ p̃ · log(p̂ / p̃)`. This is the key observation of [@zhangyeung1997] that converts Shannon-type quantities into the KL-divergence-amenable form. -/
private lemma sum_joint_eq_sum_ptilde
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ∑ t : S₁ × S₂ × S₃ × S₄,
        pJoint X Y Z U μ t * Real.log (phat X Y Z U μ t / ptilde X Y Z U μ t)
      = ∑ t : S₁ × S₂ × S₃ × S₄,
          ptilde X Y Z U μ t * Real.log (phat X Y Z U μ t / ptilde X Y Z U μ t) := by
  classical
  -- Abbreviations for the eleven μ-marginals appearing in the log-ratio decomposition.
  set pXZ  : S₁ × S₃        → ℝ := fun p => (μ.map (fun ω => (X ω, Z ω))).real {p}
    with hpXZ_def
  set pXU  : S₁ × S₄        → ℝ := fun p => (μ.map (fun ω => (X ω, U ω))).real {p}
    with hpXU_def
  set pYZ  : S₂ × S₃        → ℝ := fun p => (μ.map (fun ω => (Y ω, Z ω))).real {p}
    with hpYZ_def
  set pYU  : S₂ × S₄        → ℝ := fun p => (μ.map (fun ω => (Y ω, U ω))).real {p}
    with hpYU_def
  set pZU  : S₃ × S₄        → ℝ := fun p => (μ.map (fun ω => (Z ω, U ω))).real {p}
    with hpZU_def
  set pX   : S₁             → ℝ := fun x => (μ.map X).real {x}
    with hpX_def
  set pY   : S₂             → ℝ := fun y => (μ.map Y).real {y}
    with hpY_def
  set pZ   : S₃             → ℝ := fun z => (μ.map Z).real {z}
    with hpZ_def
  set pU   : S₄             → ℝ := fun u => (μ.map U).real {u}
    with hpU_def
  set pXZU : S₁ × S₃ × S₄   → ℝ := fun p => (μ.map (fun ω => (X ω, Z ω, U ω))).real {p}
    with hpXZU_def
  set pYZU : S₂ × S₃ × S₄   → ℝ := fun p => (μ.map (fun ω => (Y ω, Z ω, U ω))).real {p}
    with hpYZU_def
  -- The 11-term additive decomposition of `log (p̂ / p̃)` that holds on the common support.
  set L : S₁ × S₂ × S₃ × S₄ → ℝ := fun t =>
    Real.log (pXZ (t.1, t.2.2.1)) + Real.log (pXU (t.1, t.2.2.2))
    + Real.log (pYZ (t.2.1, t.2.2.1)) + Real.log (pYU (t.2.1, t.2.2.2))
    + Real.log (pZU t.2.2)
    - Real.log (pZ t.2.2.1) - Real.log (pU t.2.2.2)
    - Real.log (pX t.1) - Real.log (pY t.2.1)
    - Real.log (pXZU (t.1, t.2.2)) - Real.log (pYZU (t.2.1, t.2.2))
    with hL_def
  -- Measurability of the full joint function and every projection we use.
  have hF : Measurable (fun ω => (X ω, Y ω, Z ω, U ω)) :=
    hX.prodMk (hY.prodMk (hZ.prodMk hU))
  -- **Step 1.** Show the pointwise identity `log (p̂ / p̃) = L` on the support of `p̃`.
  have h_log_eq_L : ∀ t : S₁ × S₂ × S₃ × S₄, 0 < ptilde X Y Z U μ t →
      Real.log (phat X Y Z U μ t / ptilde X Y Z U μ t) = L t := by
    rintro ⟨x, y, z, u⟩ h_pt_pos
    -- Extract positivity of the three triple marginals from `ptilde > 0`.
    have h_ptilde_form : ptilde X Y Z U μ (x, y, z, u) = pXZU (x, z, u) * pYZU (y, z, u) / pZU (z, u) :=
      rfl
    rw [h_ptilde_form] at h_pt_pos
    have hXZU_nn : 0 ≤ pXZU (x, z, u) := measureReal_nonneg
    have hYZU_nn : 0 ≤ pYZU (y, z, u) := measureReal_nonneg
    have hZU_nn : 0 ≤ pZU (z, u) := measureReal_nonneg
    have hZU_pos : 0 < pZU (z, u) := by
      rcases hZU_nn.lt_or_eq with h | h
      · exact h
      · exfalso; rw [← h] at h_pt_pos; simp at h_pt_pos
    have hProd_pos : 0 < pXZU (x, z, u) * pYZU (y, z, u) := by
      have := h_pt_pos
      have h_num : pXZU (x, z, u) * pYZU (y, z, u) / pZU (z, u) > 0 := h_pt_pos
      by_contra h_neg
      push_neg at h_neg
      have : pXZU (x, z, u) * pYZU (y, z, u) = 0 :=
        le_antisymm h_neg (mul_nonneg hXZU_nn hYZU_nn)
      rw [this, zero_div] at h_num
      exact lt_irrefl _ h_num
    have hXZU_pos : 0 < pXZU (x, z, u) := by
      rcases (mul_pos_iff.mp hProd_pos) with ⟨hp1, _⟩ | ⟨hn1, _⟩
      · exact hp1
      · exact absurd hn1 ((not_lt.mpr) hXZU_nn)
    have hYZU_pos : 0 < pYZU (y, z, u) := by
      rcases (mul_pos_iff.mp hProd_pos) with ⟨_, hp2⟩ | ⟨_, hn2⟩
      · exact hp2
      · exact absurd hn2 ((not_lt.mpr) hYZU_nn)
    -- From the triple marginals, derive positivity of all 11 factors.
    have hXZ_pos : 0 < pXZ (x, z) := lt_of_lt_of_le hXZU_pos
      (measureReal_map_triple_le_map_pair_12 hX hZ hU μ x z u)
    have hXU_pos : 0 < pXU (x, u) := lt_of_lt_of_le hXZU_pos
      (measureReal_map_triple_le_map_pair_13 hX hZ hU μ x z u)
    have hYZ_pos : 0 < pYZ (y, z) := lt_of_lt_of_le hYZU_pos
      (measureReal_map_triple_le_map_pair_12 hY hZ hU μ y z u)
    have hYU_pos : 0 < pYU (y, u) := lt_of_lt_of_le hYZU_pos
      (measureReal_map_triple_le_map_pair_13 hY hZ hU μ y z u)
    have hX_pos : 0 < pX x := lt_of_lt_of_le hXZU_pos
      (measureReal_map_pair_le_map_fst hX (hZ.prodMk hU) μ x (z, u))
    have hY_pos : 0 < pY y := lt_of_lt_of_le hYZU_pos
      (measureReal_map_pair_le_map_fst hY (hZ.prodMk hU) μ y (z, u))
    have hZ_pos : 0 < pZ z := lt_of_lt_of_le hZU_pos
      (measureReal_map_pair_le_map_fst hZ hU μ z u)
    have hU_pos : 0 < pU u := lt_of_lt_of_le hZU_pos
      (measureReal_map_pair_le_map_snd hZ hU μ z u)
    -- Rewrite `p̂ / p̃` as a single fraction and take logs.
    have hphat_form : phat X Y Z U μ (x, y, z, u)
        = pXZ (x, z) * pXU (x, u) * pYZ (y, z) * pYU (y, u) / (pZ z * pU u * pX x * pY y) := rfl
    rw [hphat_form, h_ptilde_form]
    -- Combine the two fractions into a single one with positive denominator.
    rw [show pXZ (x, z) * pXU (x, u) * pYZ (y, z) * pYU (y, u) / (pZ z * pU u * pX x * pY y)
            / (pXZU (x, z, u) * pYZU (y, z, u) / pZU (z, u))
          = pXZ (x, z) * pXU (x, u) * pYZ (y, z) * pYU (y, u) * pZU (z, u)
            / (pZ z * pU u * pX x * pY y * pXZU (x, z, u) * pYZU (y, z, u)) from by
        field_simp]
    rw [Real.log_div (by positivity) (by positivity)]
    rw [show pXZ (x, z) * pXU (x, u) * pYZ (y, z) * pYU (y, u) * pZU (z, u)
          = pXZ (x, z) * (pXU (x, u) * (pYZ (y, z) * (pYU (y, u) * pZU (z, u)))) from by ring]
    rw [Real.log_mul hXZ_pos.ne' (by positivity),
        Real.log_mul hXU_pos.ne' (by positivity),
        Real.log_mul hYZ_pos.ne' (by positivity),
        Real.log_mul hYU_pos.ne' hZU_pos.ne']
    rw [show pZ z * pU u * pX x * pY y * pXZU (x, z, u) * pYZU (y, z, u)
          = pZ z * (pU u * (pX x * (pY y * (pXZU (x, z, u) * pYZU (y, z, u))))) from by ring]
    rw [Real.log_mul hZ_pos.ne' (by positivity),
        Real.log_mul hU_pos.ne' (by positivity),
        Real.log_mul hX_pos.ne' (by positivity),
        Real.log_mul hY_pos.ne' (by positivity),
        Real.log_mul hXZU_pos.ne' hYZU_pos.ne']
    show _ = L (x, y, z, u)
    simp only [hL_def]
    ring
  -- **Step 2.** Pointwise: `pJoint t * log (p̂ / p̃) = pJoint t * L` and same for `p̃`.
  -- Use that the support of `pJoint` is contained in the support of `p̃`.
  have h_supp : ∀ t : S₁ × S₂ × S₃ × S₄,
      0 < pJoint X Y Z U μ t → 0 < ptilde X Y Z U μ t := by
    rintro ⟨x, y, z, u⟩ h_pJ
    simp only [pJoint] at h_pJ
    -- From pJoint > 0, all three triple marginals are positive (marginal bounds).
    have hXZU_pos : 0 < pXZU (x, z, u) := by
      apply lt_of_lt_of_le h_pJ
      -- (μ.map ⟨X,Y,Z,U⟩).real {(x,y,z,u)} ≤ (μ.map ⟨X,⟨Z,U⟩⟩).real {(x, (z,u))}
      -- Using the pair-projection marginal bound: view ⟨X,Y,Z,U⟩ as a pair ⟨X, ⟨Y, ⟨Z, U⟩⟩⟩
      -- and drop the middle Y. Simpler: use iterated triple-marginal bound.
      have h1 := measureReal_map_triple_le_map_pair_13 hX hY (hZ.prodMk hU) μ x y (z, u)
      exact h1
    have hYZU_pos : 0 < pYZU (y, z, u) := by
      apply lt_of_lt_of_le h_pJ
      -- View ⟨X, Y, Z, U⟩ as pair ⟨X, ⟨Y, Z, U⟩⟩ and drop the first coord.
      exact measureReal_map_pair_le_map_snd hX (hY.prodMk (hZ.prodMk hU)) μ x (y, z, u)
    have hZU_pos : 0 < pZU (z, u) :=
      lt_of_lt_of_le hXZU_pos (measureReal_map_pair_le_map_snd hX (hZ.prodMk hU) μ x (z, u))
    -- ptilde = pXZU * pYZU / pZU > 0.
    show 0 < pXZU (x, z, u) * pYZU (y, z, u) / pZU (z, u)
    exact div_pos (mul_pos hXZU_pos hYZU_pos) hZU_pos
  have h_pJ_mul : ∀ t : S₁ × S₂ × S₃ × S₄,
      pJoint X Y Z U μ t * Real.log (phat X Y Z U μ t / ptilde X Y Z U μ t)
        = pJoint X Y Z U μ t * L t := by
    intro t
    by_cases h : pJoint X Y Z U μ t = 0
    · rw [h, zero_mul, zero_mul]
    · have h_pos : 0 < pJoint X Y Z U μ t :=
        lt_of_le_of_ne measureReal_nonneg (Ne.symm h)
      rw [h_log_eq_L t (h_supp t h_pos)]
  have h_pt_mul : ∀ t : S₁ × S₂ × S₃ × S₄,
      ptilde X Y Z U μ t * Real.log (phat X Y Z U μ t / ptilde X Y Z U μ t)
        = ptilde X Y Z U μ t * L t := by
    intro t
    by_cases h : ptilde X Y Z U μ t = 0
    · rw [h, zero_mul, zero_mul]
    · have h_pos : 0 < ptilde X Y Z U μ t :=
        lt_of_le_of_ne (ptilde_nonneg X Y Z U μ t) (Ne.symm h)
      rw [h_log_eq_L t h_pos]
  -- Rewrite both sums in L-form.
  rw [Finset.sum_congr rfl (fun t _ => h_pJ_mul t)]
  rw [Finset.sum_congr rfl (fun t _ => h_pt_mul t)]
  -- **Step 3.** `∑ pJoint * L = ∑ ptilde * L` via 11 marginal-swap applications.
  -- Each of the eleven log terms in `L` depends only on a projection of the 4-tuple;
  -- `sum_mul_proj_eq_of_marginal_eq` closes the match once we verify that `pJoint` and
  -- `p̃` agree on the corresponding fibre sums (i.e., share the μ-marginal at that projection).
  -- `sum_filter_map_real_eq_map_comp` gives the pJoint side; a bijective reindex to the
  -- nested form recorded in `sum_ptilde_over_*` / `ptilde_fibre_sum` gives the `p̃` side.
  -- **Shared bookkeeping.** `F` := the full joint random variable `⟨X, Y, Z, U⟩`.
  -- Abbreviations for the eleven μ-pushforward measures (as `.real` applied at a singleton).
  -- Define the eleven marginal-swap identities, one per log term in L.
  -- Each has shape `∑ t, pJoint(t) * log (marginal (proj t)) = ∑ t, ptilde(t) * log (...)`.
  -- Step 3a: `log p(x, z)` term (projection: `(x, y, z, u) ↦ (x, z)`, complement: `(y, u)`).
  have hEq_xz : ∑ t : S₁ × S₂ × S₃ × S₄,
        pJoint X Y Z U μ t * Real.log (pXZ (t.1, t.2.2.1))
      = ∑ t : S₁ × S₂ × S₃ × S₄,
        ptilde X Y Z U μ t * Real.log (pXZ (t.1, t.2.2.1)) := by
    apply marg_swap_helper hX hY hZ hU μ (fun t => (t.1, t.2.2.1)) (by measurability)
      (fun p => Real.log (pXZ p))
    rintro ⟨x, z⟩
    have h_reindex : (∑ t ∈ (Finset.univ : Finset (S₁ × S₂ × S₃ × S₄)).filter
          (fun t => (t.1, t.2.2.1) = (x, z)), ptilde X Y Z U μ t)
        = ∑ p : S₂ × S₄, ptilde X Y Z U μ (x, p.1, z, p.2) := by
      refine (Finset.sum_nbij' (fun p : S₂ × S₄ => (x, p.1, z, p.2))
        (fun t : S₁ × S₂ × S₃ × S₄ => (t.2.1, t.2.2.2)) ?_ ?_ ?_ ?_ ?_).symm
      · intro _ _; simp [Finset.mem_filter]
      · intro _ _; exact Finset.mem_univ _
      · rintro ⟨_, _⟩ _; rfl
      · rintro ⟨_, _, _, _⟩ ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at ht
        obtain ⟨rfl, rfl⟩ := ht
        rfl
      · intro _ _; rfl
    rw [h_reindex, Fintype.sum_prod_type]
    exact sum_ptilde_over_y_u hX hY hZ hU μ x z
  -- Step 3b–3k: the remaining 10 projections follow the same template, factored through
  -- the module-level `marg_swap_helper` that bundles the shared pJoint filter-sum argument.
  -- 2-coordinate projections: (y, u), (y, z), (x, u), (x, z), (x, y)-complement → S₁×S₃, etc.
  have hEq_xu : ∑ t : S₁ × S₂ × S₃ × S₄,
        pJoint X Y Z U μ t * Real.log (pXU (t.1, t.2.2.2))
      = ∑ t : S₁ × S₂ × S₃ × S₄,
        ptilde X Y Z U μ t * Real.log (pXU (t.1, t.2.2.2)) := by
    apply marg_swap_helper hX hY hZ hU μ (fun t => (t.1, t.2.2.2)) (by measurability)
      (fun p => Real.log (pXU p))
    rintro ⟨x, u⟩
    have h_reindex : (∑ t ∈ (Finset.univ : Finset (S₁ × S₂ × S₃ × S₄)).filter
          (fun t => (t.1, t.2.2.2) = (x, u)), ptilde X Y Z U μ t)
        = ∑ p : S₂ × S₃, ptilde X Y Z U μ (x, p.1, p.2, u) := by
      refine (Finset.sum_nbij' (fun p : S₂ × S₃ => (x, p.1, p.2, u))
        (fun t : S₁ × S₂ × S₃ × S₄ => (t.2.1, t.2.2.1)) ?_ ?_ ?_ ?_ ?_).symm
      · intro _ _; simp [Finset.mem_filter]
      · intro _ _; exact Finset.mem_univ _
      · rintro ⟨_, _⟩ _; rfl
      · rintro ⟨_, _, _, _⟩ ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at ht
        obtain ⟨rfl, rfl⟩ := ht
        rfl
      · intro _ _; rfl
    rw [h_reindex, Fintype.sum_prod_type]
    exact sum_ptilde_over_y_z hX hY hZ hU μ x u
  have hEq_yz : ∑ t : S₁ × S₂ × S₃ × S₄,
        pJoint X Y Z U μ t * Real.log (pYZ (t.2.1, t.2.2.1))
      = ∑ t : S₁ × S₂ × S₃ × S₄,
        ptilde X Y Z U μ t * Real.log (pYZ (t.2.1, t.2.2.1)) := by
    apply marg_swap_helper hX hY hZ hU μ (fun t => (t.2.1, t.2.2.1)) (by measurability)
      (fun p => Real.log (pYZ p))
    rintro ⟨y, z⟩
    have h_reindex : (∑ t ∈ (Finset.univ : Finset (S₁ × S₂ × S₃ × S₄)).filter
          (fun t => (t.2.1, t.2.2.1) = (y, z)), ptilde X Y Z U μ t)
        = ∑ p : S₁ × S₄, ptilde X Y Z U μ (p.1, y, z, p.2) := by
      refine (Finset.sum_nbij' (fun p : S₁ × S₄ => (p.1, y, z, p.2))
        (fun t : S₁ × S₂ × S₃ × S₄ => (t.1, t.2.2.2)) ?_ ?_ ?_ ?_ ?_).symm
      · intro _ _; simp [Finset.mem_filter]
      · intro _ _; exact Finset.mem_univ _
      · rintro ⟨_, _⟩ _; rfl
      · rintro ⟨_, _, _, _⟩ ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at ht
        obtain ⟨rfl, rfl⟩ := ht
        rfl
      · intro _ _; rfl
    rw [h_reindex, Fintype.sum_prod_type]
    exact sum_ptilde_over_x_u hX hY hZ hU μ y z
  have hEq_yu : ∑ t : S₁ × S₂ × S₃ × S₄,
        pJoint X Y Z U μ t * Real.log (pYU (t.2.1, t.2.2.2))
      = ∑ t : S₁ × S₂ × S₃ × S₄,
        ptilde X Y Z U μ t * Real.log (pYU (t.2.1, t.2.2.2)) := by
    apply marg_swap_helper hX hY hZ hU μ (fun t => (t.2.1, t.2.2.2)) (by measurability)
      (fun p => Real.log (pYU p))
    rintro ⟨y, u⟩
    have h_reindex : (∑ t ∈ (Finset.univ : Finset (S₁ × S₂ × S₃ × S₄)).filter
          (fun t => (t.2.1, t.2.2.2) = (y, u)), ptilde X Y Z U μ t)
        = ∑ p : S₁ × S₃, ptilde X Y Z U μ (p.1, y, p.2, u) := by
      refine (Finset.sum_nbij' (fun p : S₁ × S₃ => (p.1, y, p.2, u))
        (fun t : S₁ × S₂ × S₃ × S₄ => (t.1, t.2.2.1)) ?_ ?_ ?_ ?_ ?_).symm
      · intro _ _; simp [Finset.mem_filter]
      · intro _ _; exact Finset.mem_univ _
      · rintro ⟨_, _⟩ _; rfl
      · rintro ⟨_, _, _, _⟩ ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at ht
        obtain ⟨rfl, rfl⟩ := ht
        rfl
      · intro _ _; rfl
    rw [h_reindex, Fintype.sum_prod_type]
    exact sum_ptilde_over_x_z hX hY hZ hU μ y u
  have hEq_zu : ∑ t : S₁ × S₂ × S₃ × S₄,
        pJoint X Y Z U μ t * Real.log (pZU t.2.2)
      = ∑ t : S₁ × S₂ × S₃ × S₄,
        ptilde X Y Z U μ t * Real.log (pZU t.2.2) := by
    apply marg_swap_helper hX hY hZ hU μ (fun t => t.2.2) (by measurability)
      (fun p => Real.log (pZU p))
    rintro ⟨z, u⟩
    have h_reindex : (∑ t ∈ (Finset.univ : Finset (S₁ × S₂ × S₃ × S₄)).filter
          (fun t => t.2.2 = (z, u)), ptilde X Y Z U μ t)
        = ∑ p : S₁ × S₂, ptilde X Y Z U μ (p.1, p.2, z, u) := by
      refine (Finset.sum_nbij' (fun p : S₁ × S₂ => (p.1, p.2, z, u))
        (fun t : S₁ × S₂ × S₃ × S₄ => (t.1, t.2.1)) ?_ ?_ ?_ ?_ ?_).symm
      · intro _ _; simp [Finset.mem_filter]
      · intro _ _; exact Finset.mem_univ _
      · rintro ⟨_, _⟩ _; rfl
      · rintro ⟨_, _, _, _⟩ ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at ht
        obtain ⟨rfl, rfl⟩ := ht
        rfl
      · intro _ _; rfl
    rw [h_reindex, Fintype.sum_prod_type]
    -- Inner sum ∑ y ptilde(x, y, z, u) over y for each fixed x (via ptilde_fibre_sum)
    simp only [ptilde]
    exact ptilde_fibre_sum hX hY hZ hU μ z u
  -- Single-coordinate projections.
  have hEq_x : ∑ t : S₁ × S₂ × S₃ × S₄,
        pJoint X Y Z U μ t * Real.log (pX t.1)
      = ∑ t : S₁ × S₂ × S₃ × S₄,
        ptilde X Y Z U μ t * Real.log (pX t.1) := by
    apply marg_swap_helper hX hY hZ hU μ (fun t => t.1) measurable_fst
      (fun x => Real.log (pX x))
    intro x
    have h_reindex : (∑ t ∈ (Finset.univ : Finset (S₁ × S₂ × S₃ × S₄)).filter
          (fun t => t.1 = x), ptilde X Y Z U μ t)
        = ∑ p : S₂ × S₃ × S₄, ptilde X Y Z U μ (x, p.1, p.2.1, p.2.2) := by
      refine (Finset.sum_nbij' (fun p : S₂ × S₃ × S₄ => (x, p.1, p.2.1, p.2.2))
        (fun t : S₁ × S₂ × S₃ × S₄ => (t.2.1, t.2.2.1, t.2.2.2)) ?_ ?_ ?_ ?_ ?_).symm
      · intro _ _; simp [Finset.mem_filter]
      · intro _ _; exact Finset.mem_univ _
      · rintro ⟨_, _, _⟩ _; rfl
      · rintro ⟨_, _, _, _⟩ ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
        subst ht; rfl
      · intro _ _; rfl
    rw [h_reindex]
    simp_rw [Fintype.sum_prod_type]
    exact sum_ptilde_over_y_z_u hX hY hZ hU μ x
  have hEq_y : ∑ t : S₁ × S₂ × S₃ × S₄,
        pJoint X Y Z U μ t * Real.log (pY t.2.1)
      = ∑ t : S₁ × S₂ × S₃ × S₄,
        ptilde X Y Z U μ t * Real.log (pY t.2.1) := by
    apply marg_swap_helper hX hY hZ hU μ (fun t => t.2.1) (measurable_fst.comp measurable_snd)
      (fun y => Real.log (pY y))
    intro y
    have h_reindex : (∑ t ∈ (Finset.univ : Finset (S₁ × S₂ × S₃ × S₄)).filter
          (fun t => t.2.1 = y), ptilde X Y Z U μ t)
        = ∑ p : S₁ × S₃ × S₄, ptilde X Y Z U μ (p.1, y, p.2.1, p.2.2) := by
      refine (Finset.sum_nbij' (fun p : S₁ × S₃ × S₄ => (p.1, y, p.2.1, p.2.2))
        (fun t : S₁ × S₂ × S₃ × S₄ => (t.1, t.2.2.1, t.2.2.2)) ?_ ?_ ?_ ?_ ?_).symm
      · intro _ _; simp [Finset.mem_filter]
      · intro _ _; exact Finset.mem_univ _
      · rintro ⟨_, _, _⟩ _; rfl
      · rintro ⟨_, _, _, _⟩ ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
        subst ht; rfl
      · intro _ _; rfl
    rw [h_reindex]
    simp_rw [Fintype.sum_prod_type]
    exact sum_ptilde_over_x_z_u hX hY hZ hU μ y
  have hEq_z : ∑ t : S₁ × S₂ × S₃ × S₄,
        pJoint X Y Z U μ t * Real.log (pZ t.2.2.1)
      = ∑ t : S₁ × S₂ × S₃ × S₄,
        ptilde X Y Z U μ t * Real.log (pZ t.2.2.1) := by
    apply marg_swap_helper hX hY hZ hU μ (fun t => t.2.2.1)
      (measurable_fst.comp (measurable_snd.comp measurable_snd)) (fun z => Real.log (pZ z))
    intro z
    have h_reindex : (∑ t ∈ (Finset.univ : Finset (S₁ × S₂ × S₃ × S₄)).filter
          (fun t => t.2.2.1 = z), ptilde X Y Z U μ t)
        = ∑ p : S₁ × S₂ × S₄, ptilde X Y Z U μ (p.1, p.2.1, z, p.2.2) := by
      refine (Finset.sum_nbij' (fun p : S₁ × S₂ × S₄ => (p.1, p.2.1, z, p.2.2))
        (fun t : S₁ × S₂ × S₃ × S₄ => (t.1, t.2.1, t.2.2.2)) ?_ ?_ ?_ ?_ ?_).symm
      · intro _ _; simp [Finset.mem_filter]
      · intro _ _; exact Finset.mem_univ _
      · rintro ⟨_, _, _⟩ _; rfl
      · rintro ⟨_, _, _, _⟩ ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
        subst ht; rfl
      · intro _ _; rfl
    rw [h_reindex]
    simp_rw [Fintype.sum_prod_type]
    exact sum_ptilde_over_x_y_u hX hY hZ hU μ z
  have hEq_u : ∑ t : S₁ × S₂ × S₃ × S₄,
        pJoint X Y Z U μ t * Real.log (pU t.2.2.2)
      = ∑ t : S₁ × S₂ × S₃ × S₄,
        ptilde X Y Z U μ t * Real.log (pU t.2.2.2) := by
    apply marg_swap_helper hX hY hZ hU μ (fun t => t.2.2.2)
      (measurable_snd.comp (measurable_snd.comp measurable_snd)) (fun u => Real.log (pU u))
    intro u
    have h_reindex : (∑ t ∈ (Finset.univ : Finset (S₁ × S₂ × S₃ × S₄)).filter
          (fun t => t.2.2.2 = u), ptilde X Y Z U μ t)
        = ∑ p : S₁ × S₂ × S₃, ptilde X Y Z U μ (p.1, p.2.1, p.2.2, u) := by
      refine (Finset.sum_nbij' (fun p : S₁ × S₂ × S₃ => (p.1, p.2.1, p.2.2, u))
        (fun t : S₁ × S₂ × S₃ × S₄ => (t.1, t.2.1, t.2.2.1)) ?_ ?_ ?_ ?_ ?_).symm
      · intro _ _; simp [Finset.mem_filter]
      · intro _ _; exact Finset.mem_univ _
      · rintro ⟨_, _, _⟩ _; rfl
      · rintro ⟨_, _, _, _⟩ ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
        subst ht; rfl
      · intro _ _; rfl
    rw [h_reindex]
    simp_rw [Fintype.sum_prod_type]
    exact sum_ptilde_over_x_y_z hX hY hZ hU μ u
  -- 3-coordinate projections.
  have hEq_xzu : ∑ t : S₁ × S₂ × S₃ × S₄,
        pJoint X Y Z U μ t * Real.log (pXZU (t.1, t.2.2))
      = ∑ t : S₁ × S₂ × S₃ × S₄,
        ptilde X Y Z U μ t * Real.log (pXZU (t.1, t.2.2)) := by
    apply marg_swap_helper hX hY hZ hU μ (fun t => (t.1, t.2.2)) (by measurability)
      (fun p => Real.log (pXZU p))
    rintro ⟨x, z, u⟩
    have h_reindex : (∑ t ∈ (Finset.univ : Finset (S₁ × S₂ × S₃ × S₄)).filter
          (fun t => (t.1, t.2.2) = (x, z, u)), ptilde X Y Z U μ t)
        = ∑ y : S₂, ptilde X Y Z U μ (x, y, z, u) := by
      refine (Finset.sum_nbij' (fun y : S₂ => (x, y, z, u))
        (fun t : S₁ × S₂ × S₃ × S₄ => t.2.1) ?_ ?_ ?_ ?_ ?_).symm
      · intro _ _; simp [Finset.mem_filter]
      · intro _ _; exact Finset.mem_univ _
      · intro _ _; rfl
      · rintro ⟨_, _, _, _⟩ ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at ht
        obtain ⟨rfl, rfl, rfl⟩ := ht
        rfl
      · intro _ _; rfl
    rw [h_reindex]
    exact sum_ptilde_over_y hX hY hZ hU μ x z u
  have hEq_yzu : ∑ t : S₁ × S₂ × S₃ × S₄,
        pJoint X Y Z U μ t * Real.log (pYZU (t.2.1, t.2.2))
      = ∑ t : S₁ × S₂ × S₃ × S₄,
        ptilde X Y Z U μ t * Real.log (pYZU (t.2.1, t.2.2)) := by
    apply marg_swap_helper hX hY hZ hU μ (fun t => (t.2.1, t.2.2)) (by measurability)
      (fun p => Real.log (pYZU p))
    rintro ⟨y, z, u⟩
    have h_reindex : (∑ t ∈ (Finset.univ : Finset (S₁ × S₂ × S₃ × S₄)).filter
          (fun t => (t.2.1, t.2.2) = (y, z, u)), ptilde X Y Z U μ t)
        = ∑ x : S₁, ptilde X Y Z U μ (x, y, z, u) := by
      refine (Finset.sum_nbij' (fun x : S₁ => (x, y, z, u))
        (fun t : S₁ × S₂ × S₃ × S₄ => t.1) ?_ ?_ ?_ ?_ ?_).symm
      · intro _ _; simp [Finset.mem_filter]
      · intro _ _; exact Finset.mem_univ _
      · intro _ _; rfl
      · rintro ⟨_, _, _, _⟩ ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at ht
        obtain ⟨rfl, rfl, rfl⟩ := ht
        rfl
      · intro _ _; rfl
    rw [h_reindex]
    exact sum_ptilde_over_x hX hY hZ hU μ y z u
  -- **Step 4.** Combine the eleven `hEq_*` identities via the 11-term additive decomposition of L.
  -- Distribute the multiplication pointwise and split the sum into eleven pieces.
  have h_split : ∀ (w : S₁ × S₂ × S₃ × S₄ → ℝ),
      (∑ t : S₁ × S₂ × S₃ × S₄, w t * L t)
        = (∑ t, w t * Real.log (pXZ (t.1, t.2.2.1)))
          + (∑ t, w t * Real.log (pXU (t.1, t.2.2.2)))
          + (∑ t, w t * Real.log (pYZ (t.2.1, t.2.2.1)))
          + (∑ t, w t * Real.log (pYU (t.2.1, t.2.2.2)))
          + (∑ t, w t * Real.log (pZU t.2.2))
          - (∑ t, w t * Real.log (pZ t.2.2.1))
          - (∑ t, w t * Real.log (pU t.2.2.2))
          - (∑ t, w t * Real.log (pX t.1))
          - (∑ t, w t * Real.log (pY t.2.1))
          - (∑ t, w t * Real.log (pXZU (t.1, t.2.2)))
          - (∑ t, w t * Real.log (pYZU (t.2.1, t.2.2))) := fun w => by
    simp only [hL_def, mul_add, mul_sub]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [h_split (pJoint X Y Z U μ), h_split (ptilde X Y Z U μ),
      hEq_xz, hEq_xu, hEq_yz, hEq_yu, hEq_zu,
      hEq_z, hEq_u, hEq_x, hEq_y, hEq_xzu, hEq_yzu]

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
