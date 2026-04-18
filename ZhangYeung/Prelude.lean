/- Import surface for PFR's Shannon entropy API. Brings entropy notation (H[X], I[X:Y], I[X:Y|Z]) into scope for downstream modules, and hosts generic helpers reusable across the `ZhangYeung` hierarchy. -/
import PFR.ForMathlib.Entropy.Basic

open MeasureTheory ProbabilityTheory

namespace ZhangYeung

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
