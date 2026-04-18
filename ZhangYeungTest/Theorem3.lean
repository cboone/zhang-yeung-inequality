import ZhangYeung

namespace ZhangYeungTest

open MeasureTheory ProbabilityTheory
open ZhangYeung

universe u

section Signatures

variable {Ω : Type*} [MeasurableSpace Ω]
  {S₁ S₂ S₃ S₄ : Type u}
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
  [Fintype S₁] [Fintype S₂] [Fintype S₃] [Fintype S₄]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]

/- Pinned signature: re-state `zhangYeung` verbatim, pinning the paper's
`(1/2)`-scaled right-hand side and the hypothesis order. -/
example
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    delta Z U X Y μ
      ≤ (1 / 2) * (I[X : Y ; μ] + I[X : ⟨Z, U⟩ ; μ]
        + I[Z : U | X ; μ] - I[Z : U | Y ; μ]) :=
  zhangYeung hX hY hZ hU μ

/- Pinned signature: re-state `zhangYeung_dual` verbatim, pinning the
`X ↔ Y` dual (paper eq. 22) and the sign flips on the two conditional
MI terms. -/
example
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    delta Z U X Y μ
      ≤ (1 / 2) * (I[X : Y ; μ] + I[Y : ⟨Z, U⟩ ; μ]
        - I[Z : U | X ; μ] + I[Z : U | Y ; μ]) :=
  zhangYeung_dual hX hY hZ hU μ

/- Pinned signature: re-state `zhangYeung_averaged` verbatim, pinning
the `(1/2)`- and `(1/4)`-scaled averaged symmetric form of paper
eq. (23). -/
example
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    delta Z U X Y μ
      ≤ (1 / 2) * I[X : Y ; μ]
        + (1 / 4) * (I[X : ⟨Z, U⟩ ; μ] + I[Y : ⟨Z, U⟩ ; μ]) :=
  zhangYeung_averaged hX hY hZ hU μ

end Signatures

end ZhangYeungTest
