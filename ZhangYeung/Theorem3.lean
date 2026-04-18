import ZhangYeung.CopyLemma
import ZhangYeung.Delta
import ZhangYeung.Prelude

/-!
# The Zhang-Yeung inequality (Theorem 3)

Theorem 3 of [@zhangyeung1998, §III, eqs. 21-23] is the headline non-Shannon-type information inequality of the paper: the first known instance of a linear inequality on the entropies of four discrete random variables that does not follow from Shannon's basic inequalities. This module closes the Shannon chase that takes the two copy-lemma inputs of M2 (`copyLemma_delta_le_mutualInfo_Y₁` and `copyLemma_delta_le_mutualInfo_X_X₁`) to the three equivalent forms of the paper's conclusion (eqs. 21, 22, 23).

Statement of eq. (21):

  `Δ(Z, U | X, Y) ≤ (1/2)·(I(X; Y) + I(X; ⟨Z, U⟩) + I(Z; U | X) - I(Z; U | Y))`.

Its `X ↔ Y` symmetric partner (eq. 22) and their average (eq. 23) follow by mechanical algebra on `delta_form22_iff`, `delta_form23_iff`, and `delta_form23_of_form21_form22` from `ZhangYeung/Delta.lean`.

## Main statements

- `ZhangYeung.zhangYeung`: paper eq. (21), the asymmetric form the copy-lemma chase naturally produces.
- `ZhangYeung.zhangYeung_dual`: paper eq. (22), the `X ↔ Y` swap of eq. (21).
- `ZhangYeung.zhangYeung_averaged`: paper eq. (23), the symmetric headline form obtained by averaging (21) and (22).

## Implementation notes

The cleanest proof produces the integer-scaled form first (because the chase naturally closes at `2·I[Z:U] - 3·I[Z:U|X] - I[Z:U|Y] ≤ I[X:Y] + I[X:⟨Z, U⟩]`) and converts to the paper's `(1/2)`-scaled form at the end via the M1 `delta_form21_iff` lemma. A private theorem `zhangYeung_integer` captures this intermediate shape, and the three public theorems are thin wrappers that route through the form-conversion lemmas of `ZhangYeung/Delta.lean`.

Two generic Shannon helpers land `private` at the top of the module: `mutualInfo_add_three_way_identity` (the "peeling chain rule twice" identity `I[X:Y] + I[X:Z] = I[X:⟨Y,Z⟩] + I[Y:Z] - I[Y:Z|X]`), and `mutualInfo_le_of_condIndepFun` (the data-processing inequality `CondIndepFun X Y Z μ → I[X:Y] ≤ I[X:Z]`). Neither references the copy construction; both are candidates for later promotion to `ZhangYeung/Prelude.lean` or upstreaming to PFR if a subsequent milestone uses them.

Two measurable projection helpers (`measurable_pairXZU`, `measurable_pairXY`) package the specific 4-tuple projections the main chase invokes through `IdentDistrib.comp` to extract the pair-level `IdentDistrib`s consumed by `IdentDistrib.mutualInfo_eq`. They are `private` and local to this file; their specific shapes are tied to the chase.

The four codomains `S₁, S₂, S₃, S₄` of the measured random variables are bound at a common universe `u`, inherited from the `copyLemma` existential (`ZhangYeung/CopyLemma.lean`).

## References

* [@zhangyeung1998, §III, Theorem 3, eqs. 21-23] -- see `references/transcriptions/zhangyeung1998.md` for a verbatim transcription of the theorem statement (line 290) and the proof (lines 680-709), verified 2026-04-16.

## Tags

Shannon entropy, mutual information, non-Shannon information inequality, Zhang-Yeung, data processing
-/

namespace ZhangYeung

open MeasureTheory ProbabilityTheory

universe u

/-! ### Generic Shannon helpers

Two pure-Shannon-algebra identities (no reference to the copy construction) and two projection-measurability facts local to the Theorem 3 chase. Promoted to `ZhangYeung/Prelude.lean` only if a later milestone needs them. -/

section Helpers

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The three-way interaction identity

  `I[X : Y] + I[X : Z] = I[X : ⟨Y, Z⟩] + I[Y : Z] - I[Y : Z | X]`.

Equivalent to a pair of chain-rule applications on `I[X : ⟨Y, Z⟩]`, together with the defining identity `I[Y : Z | X] = I[Y : Z] - I[X : Y : Z]` for the three-way interaction information. Consumed inside `zhangYeung_integer` at step 2 of the chase (paper line 700). -/
private lemma mutualInfo_add_three_way_identity
    {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    {X : Ω → α} {Y : Ω → β} {Z : Ω → γ}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    I[X : Y ; μ] + I[X : Z ; μ]
      = I[X : ⟨Y, Z⟩ ; μ] + I[Y : Z ; μ] - I[Y : Z | X ; μ] := by
  have hYZ : Measurable (fun ω => (Y ω, Z ω)) := hY.prodMk hZ
  simp only [mutualInfo_def]
  rw [condMutualInfo_eq hY hZ hX μ,
      chain_rule'' μ hY hX, chain_rule'' μ hZ hX, chain_rule'' μ hYZ hX]
  have e_XY : H[⟨X, Y⟩ ; μ] = H[⟨Y, X⟩ ; μ] := entropy_comm hX hY μ
  have e_XZ : H[⟨X, Z⟩ ; μ] = H[⟨Z, X⟩ ; μ] := entropy_comm hX hZ μ
  have e_X_YZ : H[⟨X, ⟨Y, Z⟩⟩ ; μ] = H[⟨⟨Y, Z⟩, X⟩ ; μ] := entropy_comm hX hYZ μ
  linarith [e_XY, e_XZ, e_X_YZ]

/-- Data processing for PFR's random-variable form of `CondIndepFun`: if `X` and `Y` are conditionally independent given `Z`, then `I[X : Y] ≤ I[X : Z]`. Consumed inside `zhangYeung_integer` at step 4 of the chase (paper line 708). -/
private lemma mutualInfo_le_of_condIndepFun
    {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    {X : Ω → α} {Y : Ω → β} {Z : Ω → γ}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : CondIndepFun X Y Z μ) :
    I[X : Y ; μ] ≤ I[X : Z ; μ] := by
  have h_ent : H[⟨X, ⟨Y, Z⟩⟩ ; μ] = H[⟨X, Z⟩ ; μ] + H[⟨Y, Z⟩ ; μ] - H[Z ; μ] :=
    ent_of_cond_indep μ hX hY hZ h
  have h_sub : H[⟨X, ⟨Z, Y⟩⟩ ; μ] + H[Y ; μ] ≤ H[⟨X, Y⟩ ; μ] + H[⟨Z, Y⟩ ; μ] :=
    entropy_triple_add_entropy_le μ hX hZ hY
  have e_inner : H[⟨X, ⟨Z, Y⟩⟩ ; μ] = H[⟨X, ⟨Y, Z⟩⟩ ; μ] := by
    rw [chain_rule' μ hX (hZ.prodMk hY), chain_rule' μ hX (hY.prodMk hZ),
        condEntropy_comm hZ hY]
  have e_ZY : H[⟨Z, Y⟩ ; μ] = H[⟨Y, Z⟩ ; μ] := entropy_comm hZ hY μ
  simp only [mutualInfo_def]
  linarith [h_ent, h_sub, e_inner, e_ZY]

/-- Measurability of the `(a, b, c, d) ↦ (a, (c, d))` projection, extracting the `(X, ⟨Z, U⟩)` pair from a right-associated 4-tuple. Consumed by `zhangYeung_integer` for the first marginal-equality transport. -/
private lemma measurable_pairXZU
    {S₁ S₂ S₃ S₄ : Type*}
    [MeasurableSpace S₁] [MeasurableSpace S₂] [MeasurableSpace S₃] [MeasurableSpace S₄] :
    Measurable (fun p : S₁ × S₂ × S₃ × S₄ => (p.1, (p.2.2.1, p.2.2.2))) := by
  fun_prop

/-- Measurability of the `(a, b, c, d) ↦ (a, b)` projection, extracting the `(X, Y)` pair from a right-associated 4-tuple. Consumed by `zhangYeung_integer` for the second marginal-equality transport. -/
private lemma measurable_pairXY
    {S₁ S₂ S₃ S₄ : Type*}
    [MeasurableSpace S₁] [MeasurableSpace S₂] [MeasurableSpace S₃] [MeasurableSpace S₄] :
    Measurable (fun p : S₁ × S₂ × S₃ × S₄ => (p.1, p.2.1)) := by
  fun_prop

end Helpers

/-! ### Main theorems

Module-scope fixtures for the three public theorems. The four codomains are bound at a single universe `u` because the `copyLemma` existential consumed by `zhangYeung_integer` is universe-bound. -/

section MainTheorems

variable {Ω : Type*} [MeasurableSpace Ω]
  {S₁ S₂ S₃ S₄ : Type u}
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
  [Fintype S₁] [Fintype S₂] [Fintype S₃] [Fintype S₄]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]

/-- The integer-scaled form of Theorem 3 (paper line 705, the shape the Shannon chase naturally closes at before rescaling):

  `2·I[Z : U] - 3·I[Z : U | X] - I[Z : U | Y] ≤ I[X : Y] + I[X : ⟨Z, U⟩]`.

The three public wrappers `zhangYeung`, `zhangYeung_dual`, `zhangYeung_averaged` route their `(1/2)`- and `(1/4)`-scaled conclusions through this integer form via the M1 form-conversion lemmas. -/
private theorem zhangYeung_integer
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    2 * I[Z : U ; μ] - 3 * I[Z : U | X ; μ] - I[Z : U | Y ; μ]
      ≤ I[X : Y ; μ] + I[X : ⟨Z, U⟩ ; μ] := by
  obtain ⟨Ω', _, ν, X', Y', X₁, Y₁, Z', U',
      _, hX', _, hX₁, hY₁, hZ', hU', hFirst, hSecond, hCond⟩ :=
    copyLemma hX hY hZ hU μ
  -- Step 1: two copy-lemma inequalities (paper lines 683, 689).
  have h1 : delta Z U X Y μ ≤ I[X' : Y₁ ; ν] :=
    copyLemma_delta_le_mutualInfo_Y₁ hX hY hZ hU hX' hY₁ hZ' hU' hFirst hSecond hCond
  have h2 : I[Z : U ; μ] - 2 * I[Z : U | X ; μ] ≤ I[X' : X₁ ; ν] :=
    copyLemma_delta_le_mutualInfo_X_X₁ hX hZ hU hX' hX₁ hZ' hU' hFirst hSecond hCond
  rw [delta_def] at h1
  -- Step 2: three-way interaction identity on ν (paper line 700).
  have h_three :
      I[X' : X₁ ; ν] + I[X' : Y₁ ; ν]
        = I[X' : ⟨X₁, Y₁⟩ ; ν] + I[X₁ : Y₁ ; ν] - I[X₁ : Y₁ | X' ; ν] :=
    mutualInfo_add_three_way_identity hX' hX₁ hY₁ ν
  -- Step 3: drop the nonneg CMI term.
  have h_nonneg : 0 ≤ I[X₁ : Y₁ | X' ; ν] := condMutualInfo_nonneg hX₁ hY₁
  -- Step 4: data processing (paper line 708).
  have hCond_proj : CondIndepFun X' (fun ω' => (X₁ ω', Y₁ ω'))
                      (fun ω' => (Z' ω', U' ω')) ν :=
    ZhangYeung.condIndepFun_comp (φ := Prod.fst) (ψ := id)
      measurable_fst measurable_id hCond
  have h_dp : I[X' : ⟨X₁, Y₁⟩ ; ν] ≤ I[X' : ⟨Z', U'⟩ ; ν] :=
    mutualInfo_le_of_condIndepFun hX' (hX₁.prodMk hY₁) (hZ'.prodMk hU') ν hCond_proj
  -- Step 5: transport `I[X' : ⟨Z', U'⟩ ; ν] = I[X : ⟨Z, U⟩ ; μ]` via `hFirst`.
  have hPairXZU : IdentDistrib
      (fun ω' => (X' ω', (Z' ω', U' ω'))) (fun ω => (X ω, (Z ω, U ω))) ν μ :=
    hFirst.comp measurable_pairXZU
  have h_marg_XZU : I[X' : ⟨Z', U'⟩ ; ν] = I[X : ⟨Z, U⟩ ; μ] :=
    hPairXZU.mutualInfo_eq
  -- Step 6: transport `I[X₁ : Y₁ ; ν] = I[X : Y ; μ]` via `hSecond`.
  have hPairXY : IdentDistrib
      (fun ω' => (X₁ ω', Y₁ ω')) (fun ω => (X ω, Y ω)) ν μ :=
    hSecond.comp measurable_pairXY
  have h_marg_XY : I[X₁ : Y₁ ; ν] = I[X : Y ; μ] :=
    hPairXY.mutualInfo_eq
  linarith [h1, h2, h_three, h_nonneg, h_dp, h_marg_XZU, h_marg_XY]

/-- **Theorem 3 of [@zhangyeung1998, §III, eq. 21]** -- the Zhang-Yeung inequality in the asymmetric form the copy-lemma proof naturally produces:

  `Δ(Z, U | X, Y) ≤ (1/2)·(I(X; Y) + I(X; ⟨Z, U⟩) + I(Z; U | X) - I(Z; U | Y))`.

This is the first known non-Shannon-type information inequality, in the form paper eq. (21) states. -/
theorem zhangYeung
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    delta Z U X Y μ
      ≤ (1 / 2) * (I[X : Y ; μ] + I[X : ⟨Z, U⟩ ; μ]
        + I[Z : U | X ; μ] - I[Z : U | Y ; μ]) := by
  sorry

/-- **The `X ↔ Y` dual of Theorem 3** [@zhangyeung1998, §III, eq. 22]:

  `Δ(Z, U | X, Y) ≤ (1/2)·(I(X; Y) + I(Y; ⟨Z, U⟩) - I(Z; U | X) + I(Z; U | Y))`.

Obtained from `zhangYeung` by swapping `X` and `Y` in the hypotheses, using `delta_comm_cond` to rewrite the left-hand side back to the original delta, and `mutualInfo_comm` to rewrite `I[Y : X]` as `I[X : Y]`. -/
theorem zhangYeung_dual
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    delta Z U X Y μ
      ≤ (1 / 2) * (I[X : Y ; μ] + I[Y : ⟨Z, U⟩ ; μ]
        - I[Z : U | X ; μ] + I[Z : U | Y ; μ]) := by
  sorry

/-- **The averaged symmetric form of Theorem 3** [@zhangyeung1998, §III, eq. 23]:

  `Δ(Z, U | X, Y) ≤ (1/2)·I(X; Y) + (1/4)·(I(X; ⟨Z, U⟩) + I(Y; ⟨Z, U⟩))`.

The paper highlights this as Theorem 3's headline statement; it follows by averaging eqs. (21) and (22) via the M1 `delta_form23_of_form21_form22` averaging lemma. -/
theorem zhangYeung_averaged
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    delta Z U X Y μ
      ≤ (1 / 2) * I[X : Y ; μ]
        + (1 / 4) * (I[X : ⟨Z, U⟩ ; μ] + I[Y : ⟨Z, U⟩ ; μ]) := by
  sorry

end MainTheorems

end ZhangYeung
