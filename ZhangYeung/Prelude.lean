/-
SPDX-FileCopyrightText: 2026 Christopher Boone
SPDX-License-Identifier: Apache-2.0
-/

/- Import surface for PFR's Shannon entropy API. Brings entropy notation (H[X], I[X:Y], I[X:Y|Z]) into scope for downstream modules, and hosts generic helpers reusable across the `ZhangYeung` hierarchy. -/
import PFR.ForMathlib.Entropy.Basic

open MeasureTheory ProbabilityTheory

namespace ZhangYeung

/-! ### Generic Shannon helpers -/

/-- Substituting variables for identically-distributed ones leaves the conditional mutual information unchanged. PFR exposes `IdentDistrib.condEntropy_eq` and `IdentDistrib.mutualInfo_eq` but not this conditional-mutual-information transport. The three sub-`IdentDistrib`s for `⟨X, Z⟩`, `⟨Y, Z⟩`, and `⟨⟨X, Y⟩, Z⟩` are extracted from the triple by one `IdentDistrib.comp` with a measurable projection each. Promoted from `ZhangYeung/CopyLemma.lean` as of M5. -/
lemma IdentDistrib.condMutualInfo_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {S T U : Type*}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
    [Finite S] [Finite T] [Finite U]
    {μ : Measure Ω} {μ' : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {X : Ω → S} {Y : Ω → T} {Z : Ω → U}
    {X' : Ω' → S} {Y' : Ω' → T} {Z' : Ω' → U}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hX' : Measurable X') (hY' : Measurable Y') (hZ' : Measurable Z')
    (h : IdentDistrib (fun ω => (X ω, Y ω, Z ω))
                      (fun ω' => (X' ω', Y' ω', Z' ω')) μ μ') :
    I[X : Y | Z ; μ] = I[X' : Y' | Z' ; μ'] := by
  have hXZ : IdentDistrib (fun ω => (X ω, Z ω)) (fun ω' => (X' ω', Z' ω')) μ μ' :=
    h.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hYZ : IdentDistrib (fun ω => (Y ω, Z ω)) (fun ω' => (Y' ω', Z' ω')) μ μ' :=
    h.comp ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd))
  have hXYZ : IdentDistrib (fun ω => ((X ω, Y ω), Z ω))
      (fun ω' => ((X' ω', Y' ω'), Z' ω')) μ μ' :=
    h.comp ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd))
  have eHX : H[X | Z ; μ] = H[X' | Z' ; μ'] :=
    IdentDistrib.condEntropy_eq hX hZ hX' hZ' hXZ
  have eHY : H[Y | Z ; μ] = H[Y' | Z' ; μ'] :=
    IdentDistrib.condEntropy_eq hY hZ hY' hZ' hYZ
  have eHXY : H[⟨X, Y⟩ | Z ; μ] = H[⟨X', Y'⟩ | Z' ; μ'] :=
    IdentDistrib.condEntropy_eq (hX.prodMk hY) hZ (hX'.prodMk hY') hZ' hXYZ
  calc I[X : Y | Z ; μ]
      = H[X | Z ; μ] + H[Y | Z ; μ] - H[⟨X, Y⟩ | Z ; μ] :=
        ProbabilityTheory.condMutualInfo_eq hX hY hZ μ
    _ = H[X' | Z' ; μ'] + H[Y' | Z' ; μ'] - H[⟨X', Y'⟩ | Z' ; μ'] := by rw [eHX, eHY, eHXY]
    _ = I[X' : Y' | Z' ; μ'] := (ProbabilityTheory.condMutualInfo_eq hX' hY' hZ' μ').symm

/-- The three-way interaction identity

  `I[X : Y] + I[X : Z] = I[X : ⟨Y, Z⟩] + I[Y : Z] - I[Y : Z | X]`.

Equivalent to a pair of chain-rule applications on `I[X : ⟨Y, Z⟩]`, together with the defining identity `I[Y : Z | X] = I[Y : Z] - I[X : Y : Z]` for the three-way interaction information. Promoted from `ZhangYeung/Theorem3.lean` as of M5. -/
lemma mutualInfo_add_three_way_identity
    {Ω : Type*} [MeasurableSpace Ω]
    {α β γ : Type*}
    [Finite α] [Finite β] [Finite γ]
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

/-- Data processing for PFR's random-variable form of `CondIndepFun`: if `X` and `Y` are conditionally independent given `Z`, then `I[X : Y] ≤ I[X : Z]`. Promoted from `ZhangYeung/Theorem3.lean` as of M5. -/
lemma mutualInfo_le_of_condIndepFun
    {Ω : Type*} [MeasurableSpace Ω]
    {α β γ : Type*}
    [Finite α] [Finite β] [Finite γ]
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

/-- Post-composition of a `CondIndepFun` statement on its two measured coordinates by independent measurable functions `φ` and `ψ`. The conditioner `k` is unchanged. Mathlib's `CondIndepFun.comp` uses the σ-algebra form of conditional independence and does not apply to PFR's random-variable form; this lemma fills that gap by unfolding through `condIndepFun_iff` to a fibrewise `∀ᵐ`-family of `IndepFun` statements, applying Mathlib's `IndepFun.comp` inside each fibre, and repackaging. Promoted from `ZhangYeung/CopyLemma.lean` as of M3 (the second consumer). -/
lemma condIndepFun_comp
    {Ω α α' β β' γ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace α']
    [MeasurableSpace β] [MeasurableSpace β'] [MeasurableSpace γ]
    {μ : Measure Ω} {f : Ω → α} {g : Ω → β} {k : Ω → γ}
    {φ : α → α'} {ψ : β → β'}
    (hφ : Measurable φ) (hψ : Measurable ψ) (h : CondIndepFun f g k μ) :
    CondIndepFun (φ ∘ f) (ψ ∘ g) k μ := by
  rw [condIndepFun_iff] at h ⊢
  filter_upwards [h] with z hfg
  exact hfg.comp hφ hψ

end ZhangYeung
