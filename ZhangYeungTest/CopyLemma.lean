import ZhangYeung

namespace ZhangYeungTest

open MeasureTheory ProbabilityTheory
open ZhangYeung

universe u

section Signature

variable {Ω : Type*} [MeasurableSpace Ω]
  {S₁ S₂ S₃ S₄ : Type u}
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
  [Fintype S₁] [Fintype S₂] [Fintype S₃] [Fintype S₄]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]

/- Pinned signature: re-state `copyLemma` verbatim, exercising the six
projected random variables, the two `IdentDistrib` marginal-equality facts,
and the `CondIndepFun` conditional-independence fact. This guards against
silent drifts in the existential shape or the hypothesis order. -/
example
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
                   (fun ω' => (Z' ω', U' ω')) ν :=
  copyLemma hX hY hZ hU μ

end Signature

section LemmaTwoFormA

variable {Ω : Type*} [MeasurableSpace Ω]
  {α β γ δ : Type*}
  [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  [MeasurableSingletonClass γ] [MeasurableSingletonClass δ]

/- Pinned signature: re-state `delta_of_condMI_vanishes_eq` verbatim. Pins the
hypothesis order, the vanishing-CMI shape `I[A : D | ⟨B, C⟩ ; ν] = 0`, and the
right-hand-side argument order `delta B C A D` vs `I[A : D] - I[A : D | B] -
I[A : D | C] - I[B : C | ⟨A, D⟩]`. -/
example
    {A : Ω → α} {B : Ω → β} {C : Ω → γ} {D : Ω → δ}
    (hA : Measurable A) (hB : Measurable B) (hC : Measurable C) (hD : Measurable D)
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (hVanish : I[A : D | ⟨B, C⟩ ; ν] = 0) :
    delta B C A D ν
      = I[A : D ; ν] - I[A : D | B ; ν] - I[A : D | C ; ν]
        - I[B : C | ⟨A, D⟩ ; ν] :=
  delta_of_condMI_vanishes_eq hA hB hC hD ν hVanish

end LemmaTwoFormA

end ZhangYeungTest
