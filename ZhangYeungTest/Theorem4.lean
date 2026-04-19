import ZhangYeung

namespace ZhangYeungTest

open MeasureTheory ProbabilityTheory
open ZhangYeung

universe u

/-! ### Signature pins for the set-function calculus and cone predicates -/

section SetFunctionCalculus

/- Pinned signature: `I_F` is a three-argument real-valued function of `F` and two `Finset (Fin 4)` arguments. -/
example (F : Finset (Fin 4) → ℝ) (α β : Finset (Fin 4)) :
    I_F F α β = F α + F β - F (α ∪ β) :=
  rfl

/- Pinned signature: `condI_F` is a four-argument real-valued function of `F` and three `Finset (Fin 4)` arguments. -/
example (F : Finset (Fin 4) → ℝ) (α β γ : Finset (Fin 4)) :
    condI_F F α β γ = F (α ∪ γ) + F (β ∪ γ) - F (α ∪ β ∪ γ) - F γ :=
  rfl

/- Pinned signature: `delta_F` is a five-argument real-valued function of `F` and four `Fin 4` indices. -/
example (F : Finset (Fin 4) → ℝ) (i j k l : Fin 4) :
    delta_F F i j k l = I_F F {i} {j} - condI_F F {i} {j} {k} - condI_F F {i} {j} {l} :=
  rfl

end SetFunctionCalculus

section Predicates

/- Pinned signature: `shannonCone` is a three-clause conjunction (zero, monotone, submodular). -/
example (F : Finset (Fin 4) → ℝ) :
    shannonCone F ↔
      F ∅ = 0 ∧
      (∀ α β : Finset (Fin 4), α ⊆ β → F α ≤ F β) ∧
      (∀ α β : Finset (Fin 4), F (α ∪ β) + F (α ∩ β) ≤ F α + F β) :=
  Iff.rfl

/- Pinned signature: `zhangYeungAt F i j k l` is paper eq. (21) at the labeling `(i, j, k, l)`. -/
example (F : Finset (Fin 4) → ℝ) (i j k l : Fin 4) :
    zhangYeungAt F i j k l ↔
      delta_F F i j k l ≤ (1 / 2) * (I_F F {k} {l} + I_F F {k} ({i} ∪ {j})
        + condI_F F {i} {j} {k} - condI_F F {i} {j} {l}) :=
  Iff.rfl

/- Pinned signature: `zhangYeungHolds F` quantifies over `Equiv.Perm (Fin 4)`. -/
example (F : Finset (Fin 4) → ℝ) :
    zhangYeungHolds F ↔ ∀ π : Equiv.Perm (Fin 4), zhangYeungAt F (π 0) (π 1) (π 2) (π 3) :=
  Iff.rfl

end Predicates

/-! ### Witness signature pins -/

section Witness

/- Pinned signature: `F_witness_ℚ` is a `Finset (Fin 4) → ℚ` five-case function. -/
example : F_witness_ℚ (∅ : Finset (Fin 4)) = 0 := rfl

/- Pinned signature: `F_witness` is the `ℝ`-cast of `F_witness_ℚ`. -/
example (S : Finset (Fin 4)) : F_witness S = (F_witness_ℚ S : ℝ) :=
  F_witness_eq_cast S

end Witness

/-! ### Main statement pins -/

section MainStatements

example : shannonCone F_witness := shannonCone_of_witness

example : ¬ zhangYeungHolds F_witness := not_zhangYeungHolds_witness

example : ∃ F : Finset (Fin 4) → ℝ, shannonCone F ∧ ¬ zhangYeungHolds F :=
  shannon_incomplete

example
    {Ω : Type*} [MeasurableSpace Ω]
    {S : Fin 4 → Type u}
    [∀ i, MeasurableSpace (S i)] [∀ i, Fintype (S i)]
    [∀ i, MeasurableSingletonClass (S i)]
    {X : ∀ i : Fin 4, Ω → S i} (hX : ∀ i, Measurable (X i))
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    zhangYeungHolds (entropyFn X μ) :=
  zhangYeungHolds_of_entropy hX μ

example :
    ∃ F : Finset (Fin 4) → ℝ,
      shannonCone F ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        {S : Fin 4 → Type u}
        [∀ i, MeasurableSpace (S i)] [∀ i, Fintype (S i)]
        [∀ i, MeasurableSingletonClass (S i)]
        (X : ∀ i : Fin 4, Ω → S i) (_ : ∀ i, Measurable (X i)),
        F ≠ entropyFn X μ :=
  theorem4

end MainStatements

/-! ### Concrete evaluation of the `ℚ`-valued witness

The witness values at the 16 subsets of `Fin 4`, as a compile-time regression
against accidental edits to `F_witness_ℚ`. Each value follows the paper's
table on lines 368-377 at `a = 1`. -/

section WitnessEvaluation

example : F_witness_ℚ ({0} : Finset (Fin 4)) = 2 := by native_decide
example : F_witness_ℚ ({1} : Finset (Fin 4)) = 2 := by native_decide
example : F_witness_ℚ ({2} : Finset (Fin 4)) = 2 := by native_decide
example : F_witness_ℚ ({3} : Finset (Fin 4)) = 2 := by native_decide
example : F_witness_ℚ ({0, 1} : Finset (Fin 4)) = 4 := by native_decide
example : F_witness_ℚ ({0, 2} : Finset (Fin 4)) = 3 := by native_decide
example : F_witness_ℚ ({0, 3} : Finset (Fin 4)) = 3 := by native_decide
example : F_witness_ℚ ({1, 2} : Finset (Fin 4)) = 3 := by native_decide
example : F_witness_ℚ ({1, 3} : Finset (Fin 4)) = 3 := by native_decide
example : F_witness_ℚ ({2, 3} : Finset (Fin 4)) = 3 := by native_decide
example : F_witness_ℚ ({0, 1, 2} : Finset (Fin 4)) = 4 := by native_decide
example : F_witness_ℚ ({0, 1, 3} : Finset (Fin 4)) = 4 := by native_decide
example : F_witness_ℚ ({0, 2, 3} : Finset (Fin 4)) = 4 := by native_decide
example : F_witness_ℚ ({1, 2, 3} : Finset (Fin 4)) = 4 := by native_decide
example : F_witness_ℚ ({0, 1, 2, 3} : Finset (Fin 4)) = 4 := by native_decide

end WitnessEvaluation

/-! ### Downstream usage

`shannon_incomplete` composes Parts (a) and (b) into a single existential;
`theorem4` composes (a), (b), and the bridge (c) into the separation
`Γ_4 ∖ (entropy functions)`. Both are the intended public consequences. -/

section DownstreamUsage

/- Extracting the separating set function from `shannon_incomplete`. -/
example : ∃ F : Finset (Fin 4) → ℝ, shannonCone F ∧ ¬ zhangYeungHolds F :=
  shannon_incomplete

/- From `zhangYeungHolds_of_entropy`, every permutation of a four-variable
entropy family satisfies `zhangYeungAt`. Exercising the composition on the
identity permutation pins the bridge's downstream shape. -/
example {Ω : Type*} [MeasurableSpace Ω]
    {X : ∀ _ : Fin 4, Ω → Fin 2} (hX : ∀ i, Measurable (X i))
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    zhangYeungAt (entropyFn X μ) 0 1 2 3 :=
  zhangYeungHolds_of_entropy hX μ (Equiv.refl _)

end DownstreamUsage

/-! ### Stretch: closure form pins -/

section ClosureStretch

open scoped Topology

/- Pinned signature: `zhangYeungHolds_of_tendsto` closes the Zhang-Yeung cone
under pointwise convergence. -/
example {F_seq : ℕ → Finset (Fin 4) → ℝ} {F : Finset (Fin 4) → ℝ}
    (h_seq : ∀ k, zhangYeungHolds (F_seq k))
    (h_lim : ∀ α, Filter.Tendsto (fun k => F_seq k α) Filter.atTop (𝓝 (F α))) :
    zhangYeungHolds F :=
  zhangYeungHolds_of_tendsto h_seq h_lim

/- Pinned signature: `theorem4_closure` shows `F_witness` is not even a
pointwise limit of `tildeΓ_4` members. -/
example :
    ∃ F : Finset (Fin 4) → ℝ, shannonCone F ∧
      ∀ (F_seq : ℕ → Finset (Fin 4) → ℝ),
        (∀ k, zhangYeungHolds (F_seq k)) →
        (∀ α, Filter.Tendsto (fun k => F_seq k α) Filter.atTop (𝓝 (F α))) →
        False :=
  theorem4_closure

end ClosureStretch

end ZhangYeungTest
