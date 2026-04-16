/-
Copyright (c) 2023 Rémy Degenne, Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Terence Tao
-/
module

public import ZhangYeung.Entropy.Basic
public import ZhangYeung.ForMathlib.ConditionalIndependence

/-!
# Mutual information and conditional mutual information

## Main definitions

* `mutualInfo`: mutual information of two random variables, denoted by `I[X : Y ; μ]`
* `condMutualInfo`: conditional mutual information `I[X : Y | Z ; μ]`

## Main statements

* `mutualInfo_nonneg`, `condMutualInfo_nonneg`: nonnegativity of mutual information.
* `mutualInfo_eq_zero`: `I[X : Y] = 0` iff `X` and `Y` are independent.
* `condMutualInfo_eq_zero`: `I[X : Y | Z] = 0` iff `X` and `Y` are conditionally independent over
  `Z`.
* `ent_of_cond_indep`: if `X, Y` are conditionally independent over `Z`, then
  `H[X, Y, Z] = H[X, Z] + H[Y, Z] - H[Z]`.
* `condEntropy_le_entropy`, `entropy_submodular`, `entropy_triple_add_entropy_le`: classical
  entropy inequalities.
* `mutual_comp_le`, `mutual_comp_comp_le`, `condMutual_comp_comp_le`: data-processing inequalities
  for mutual and conditional mutual information.

## Notations

* `I[X : Y ; μ] = mutualInfo X Y μ`
* `I[X : Y | Z ; μ] = condMutualInfo X Y Z μ`

## References

* [teorth/pfr](https://github.com/teorth/pfr) at rev `80daaf1` — file
  `PFR/ForMathlib/Entropy/Basic.lean`, whose second half (sections `mutualInfo` and
  `dataProcessing`) this file is forked from. The `iIndepFun.entropy_eq_add` lemma is omitted
  because it depends on PFR patches that are not needed elsewhere in Zhang-Yeung.
-/

@[expose] public section

open Function MeasureTheory Measure Real
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace ProbabilityTheory
variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}

section mutualInfo

variable [MeasurableSpace T]

/-- The mutual information `I[X : Y]` of two random variables
is defined to be `H[X] + H[Y] - H[X ; Y]`. -/
noncomputable
def mutualInfo (X : Ω → S) (Y : Ω → T) (μ : Measure Ω := by volume_tac) : ℝ :=
  H[X ; μ] + H[Y ; μ] - H[⟨X, Y⟩ ; μ]

@[inherit_doc mutualInfo] notation3:max "I[" X " : " Y " ; " μ "]" => mutualInfo X Y μ
@[inherit_doc mutualInfo] notation3:max "I[" X " : " Y "]" => mutualInfo X Y volume

lemma mutualInfo_def (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) :
  I[X : Y ; μ] = H[X ; μ] + H[Y ; μ] - H[⟨X, Y⟩ ; μ] := rfl

lemma entropy_add_entropy_sub_mutualInfo (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) :
    H[X ; μ] + H[Y ; μ] - I[X : Y ; μ] = H[⟨X, Y⟩ ; μ] := sub_sub_self _ _

/-- Substituting variables for ones with the same distributions doesn't change the mutual
information. -/
lemma IdentDistrib.mutualInfo_eq {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    {X' : Ω' → S} {Y' : Ω' → T} (hXY : IdentDistrib (⟨X, Y⟩) (⟨X', Y'⟩) μ μ') :
      I[X : Y ; μ] = I[X' : Y' ; μ'] := by
  have hX : IdentDistrib X X' μ μ' := hXY.comp measurable_fst
  have hY : IdentDistrib Y Y' μ μ' := hXY.comp measurable_snd
  simp_rw [mutualInfo_def,hX.entropy_congr,hY.entropy_congr,hXY.entropy_congr]

/-- The conditional mutual information `I[X : Y| Z]` is the mutual information of `X| Z=z` and
`Y| Z=z`, integrated over `z`. -/
noncomputable
def condMutualInfo (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (μ : Measure Ω := by volume_tac) :
    ℝ := (μ.map Z)[fun z ↦ H[X | Z ← z ; μ] + H[Y | Z ← z ; μ] - H[⟨X, Y⟩ | Z ← z ; μ]]

lemma condMutualInfo_def (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (μ : Measure Ω) :
    condMutualInfo X Y Z μ = (μ.map Z)[fun z ↦
      H[X | Z ← z ; μ] + H[Y | Z ← z ; μ] - H[⟨X, Y⟩ | Z ← z ; μ]] := rfl

@[inherit_doc condMutualInfo]
notation3:max "I[" X " : " Y "|" Z ";" μ "]" => condMutualInfo X Y Z μ
@[inherit_doc condMutualInfo]
notation3:max "I[" X " : " Y "|" Z "]" => condMutualInfo X Y Z volume

lemma condMutualInfo_eq_integral_mutualInfo :
    I[X : Y | Z ; μ] = (μ.map Z)[fun z ↦ I[X : Y ; μ[| Z ⁻¹' {z}]]] := rfl

@[simp] lemma condMutualInfo_zero_measure : I[X : Y | Z ; 0] = 0 := by
  simp [condMutualInfo]

section

variable [MeasurableSingletonClass S] [MeasurableSingletonClass T]

/-- Mutual information is non-negative. -/
lemma mutualInfo_nonneg (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [FiniteRange X] [FiniteRange Y] :
    0 ≤ I[X : Y ; μ] := by
  simp_rw [mutualInfo_def, entropy_def]
  have h_fst : μ.map X = (μ.map (⟨X, Y⟩)).map Prod.fst := by
    rw [Measure.map_map measurable_fst (hX.prodMk hY)]
    congr
  have h_snd : μ.map Y = (μ.map (⟨X, Y⟩)).map Prod.snd := by
    rw [Measure.map_map measurable_snd (hX.prodMk hY)]
    congr
  rw [h_fst, h_snd]
  exact measureMutualInfo_nonneg

/-- Subadditivity of entropy. -/
lemma entropy_pair_le_add (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) [FiniteRange X]
    [FiniteRange Y] : H[⟨X, Y⟩ ; μ] ≤ H[X ; μ] + H[Y ; μ] :=
  sub_nonneg.1 <| mutualInfo_nonneg hX hY _

/-- `I[X : Y] = 0` iff `X, Y` are independent. -/
lemma mutualInfo_eq_zero (hX : Measurable X) (hY : Measurable Y) {μ : Measure Ω}
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    I[X : Y ; μ] = 0 ↔ IndepFun X Y μ := by
  simp_rw [mutualInfo_def, entropy_def]
  have h_fst : μ.map X = (μ.map (⟨X, Y⟩)).map Prod.fst := by
    rw [Measure.map_map measurable_fst (hX.prodMk hY)]
    congr
  have h_snd : μ.map Y = (μ.map (⟨X, Y⟩)).map Prod.snd := by
    rw [Measure.map_map measurable_snd (hX.prodMk hY)]
    congr
  rw [h_fst, h_snd]
  convert measureMutualInfo_eq_zero_iff (μ := μ.map (⟨X, Y⟩))
  rw [indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable,
    Measure.ext_iff_measureReal_singleton_finiteSupport]
  congr! with p
  convert measureReal_prod_prod (μ := μ.map X) (ν := μ.map Y) {p.1} {p.2}
  · simp
  · exact Measure.map_map measurable_fst (hX.prodMk hY)
  · exact Measure.map_map measurable_snd (hX.prodMk hY)

protected alias ⟨_, IndepFun.mutualInfo_eq_zero⟩ := mutualInfo_eq_zero

/-- `H[X, Y] = H[X] + H[Y]` if and only if `X, Y` are independent. -/
lemma entropy_pair_eq_add (hX : Measurable X) (hY : Measurable Y) {μ : Measure Ω}
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    H[⟨X, Y⟩ ; μ] = H[X ; μ] + H[Y ; μ] ↔ IndepFun X Y μ := by
  rw [eq_comm, ← sub_eq_zero, ← mutualInfo_eq_zero hX hY]; rfl

/-- If `X, Y` are independent, then `H[X, Y] = H[X] + H[Y]`. -/
protected alias ⟨_, IndepFun.entropy_pair_eq_add⟩ := entropy_pair_eq_add

variable [Countable S] [Countable T]

/-- `I[X : Y] = I[Y : X]`. -/
lemma mutualInfo_comm (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    I[X : Y ; μ] = I[Y : X ; μ] := by simp_rw [mutualInfo, add_comm, entropy_comm hX hY]

/-- `I[X : Y] = H[X] - H[X|Y]`. -/
lemma mutualInfo_eq_entropy_sub_condEntropy
    (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    I[X : Y ; μ] = H[X ; μ] - H[X | Y ; μ] := by
  rw [mutualInfo_def, chain_rule μ hX hY]
  abel

/-- `I[X : Y] = H[Y] - H[Y | X]`. -/
lemma mutualInfo_eq_entropy_sub_condEntropy' (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    I[X : Y ; μ] = H[Y ; μ] - H[Y | X ; μ] := by
  rw [mutualInfo_comm hX hY, mutualInfo_eq_entropy_sub_condEntropy hY hX]

/-- `H[X] - I[X : Y] = H[X | Y]`. -/
lemma entropy_sub_mutualInfo_eq_condEntropy (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    H[X ; μ] - I[X : Y ; μ] = H[X | Y ; μ] := by
  rw [mutualInfo_eq_entropy_sub_condEntropy hX hY, sub_sub_self]

/-- `H[Y] - I[X : Y] = H[Y | X]`. -/
lemma entropy_sub_mutualInfo_eq_condEntropy' (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    H[Y ; μ] - I[X : Y ; μ] = H[Y | X ; μ] := by
  rw [mutualInfo_eq_entropy_sub_condEntropy' hX hY, sub_sub_self]

lemma IndepFun.condEntropy_eq_entropy {μ : Measure Ω} (h : IndepFun X Y μ)
    (hX : Measurable X) (hY : Measurable Y) [IsZeroOrProbabilityMeasure μ]
    [FiniteRange X] [FiniteRange Y] :
    H[X | Y ; μ] = H[X ; μ] := by
  have := h.mutualInfo_eq_zero hX hY
  rw [mutualInfo_eq_entropy_sub_condEntropy hX hY] at this
  linarith

variable [Countable U] [MeasurableSingletonClass U] [Nonempty S] [Nonempty T]

/-- The conditional mutual information agrees with the information of the conditional kernel.
-/
lemma condMutualInfo_eq_kernel_mutualInfo
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] [FiniteRange Z] :
    I[X : Y | Z ; μ] = Ik[condDistrib (⟨X, Y⟩) Z μ, μ.map Z] := by
  rcases finiteSupport_of_finiteRange (μ := μ) (X := Z) with ⟨A, hA⟩
  simp_rw [condMutualInfo_def, entropy_def, Kernel.mutualInfo, Kernel.entropy,
    integral_eq_setIntegral hA, integral_finset _ _ IntegrableOn.finset, smul_eq_mul, mul_sub,
    mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  congr with x
  · have h := condDistrib_fst_ae_eq hX hY hZ μ
    rw [Filter.EventuallyEq, ae_iff_of_countable] at h
    specialize h x
    by_cases hx : (μ.map Z) {x} = 0
    · simp [hx, Measure.real]
    rw [h hx, condDistrib_apply hX hZ]
    rwa [Measure.map_apply hZ (.singleton _)] at hx
  · have h := condDistrib_snd_ae_eq hX hY hZ μ
    rw [Filter.EventuallyEq, ae_iff_of_countable] at h
    specialize h x
    by_cases hx : (μ.map Z) {x} = 0
    · simp [hx, Measure.real]
    rw [h hx, condDistrib_apply hY hZ]
    rwa [Measure.map_apply hZ (.singleton _)] at hx
  · by_cases hx : (μ.map Z) {x} = 0
    · simp [hx, Measure.real]
    rw [condDistrib_apply (hX.prodMk hY) hZ]
    rwa [Measure.map_apply hZ (.singleton _)] at hx

end

lemma condMutualInfo_eq_sum [MeasurableSingletonClass U] [IsFiniteMeasure μ]
    (hZ : Measurable Z) [FiniteRange Z] :
    I[X : Y | Z ; μ] = ∑ z ∈ FiniteRange.toFinset Z,
      μ.real (Z ⁻¹' {z}) * I[X : Y ; μ[|Z ← z]] := by
  rw [condMutualInfo_eq_integral_mutualInfo,
    integral_eq_setIntegral (FiniteRange.null_of_compl _ Z),
    integral_finset _ _ IntegrableOn.finset]
  congr 1 with z
  rw [map_measureReal_apply hZ (MeasurableSet.singleton z)]
  rfl

/-- A variant of `condMutualInfo_eq_sum` when `Z` has finite codomain. -/
lemma condMutualInfo_eq_sum' [MeasurableSingletonClass U] [IsFiniteMeasure μ]
    (hZ : Measurable Z) [Fintype U] :
    I[X : Y | Z ; μ] = ∑ z, μ.real (Z ⁻¹' {z}) * I[X : Y ; (μ[|Z ← z])] := by
  rw [condMutualInfo_eq_sum hZ]
  apply Finset.sum_subset
  · simp
  intro z _ hz
  have : Z ⁻¹' {z} = ∅ := by
    ext ω
    simp at hz
    simp [hz]
  simp [this]

section

variable [MeasurableSingletonClass S] [MeasurableSingletonClass T]

/-- Conditional information is non-nonegative. -/
lemma condMutualInfo_nonneg (hX : Measurable X) (hY : Measurable Y) {Z : Ω → U} {μ : Measure Ω}
    [FiniteRange X] [FiniteRange Y] :
    0 ≤ I[X : Y | Z ; μ] := by
  refine integral_nonneg (fun z ↦ ?_)
  exact mutualInfo_nonneg hX hY _

variable [Countable S] [Countable T]

/-- `I[X : Y | Z] = I[Y : X | Z]`. -/
lemma condMutualInfo_comm
    (hX : Measurable X) (hY : Measurable Y) (Z : Ω → U) (μ : Measure Ω) :
    I[X : Y | Z ; μ] = I[Y : X | Z ; μ] := by
  simp_rw [condMutualInfo_def, add_comm, entropy_comm hX hY]

variable [MeasurableSingletonClass U]

/-- `I[X : Y| Z] = H[X| Z] + H[Y| Z] - H[X, Y| Z]`. -/
lemma condMutualInfo_eq [Countable U]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] [FiniteRange Z] :
    I[X : Y | Z ; μ] = H[X | Z ; μ] + H[Y | Z; μ] - H[⟨X, Y⟩ | Z ; μ] := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  have : Nonempty S := Nonempty.map X (μ.nonempty_of_neZero)
  have : Nonempty T := Nonempty.map Y (μ.nonempty_of_neZero)
  rw [condMutualInfo_eq_kernel_mutualInfo hX hY hZ, Kernel.mutualInfo,
    Kernel.entropy_congr (condDistrib_fst_ae_eq hX hY hZ _),
    Kernel.entropy_congr (condDistrib_snd_ae_eq hX hY hZ _),
    condEntropy_eq_kernel_entropy hX hZ, condEntropy_eq_kernel_entropy hY hZ,
    condEntropy_eq_kernel_entropy (hX.prodMk hY) hZ]

/-- `I[X : Y| Z] = H[X| Z] - H[X|Y, Z]`. -/
lemma condMutualInfo_eq' [Countable U]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    I[X : Y | Z ; μ] = H[X | Z ; μ] - H[X | ⟨Y, Z⟩ ; μ] := by
  rw [condMutualInfo_eq hX hY hZ, cond_chain_rule _ hX hY hZ]
  ring

/-- If `f(Z, X)` is injective for each fixed `Z`, then `I[f(Z, X) : Y| Z] = I[X : Y| Z]`. -/
lemma condMutualInfo_of_inj_map [Countable U] [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
    (f : U → S → V) (hf : ∀ t, Function.Injective (f t)) [FiniteRange Z] :
    I[fun ω ↦ f (Z ω) (X ω) : Y | Z ; μ] =
    I[X : Y | Z ; μ] := by
  have hM : Measurable (Function.uncurry f ∘ ⟨Z, X⟩) := by fun_prop
  have hM : Measurable fun ω ↦ f (Z ω) (X ω) := hM
  rw [condMutualInfo_eq hM hY hZ, condMutualInfo_eq hX hY hZ]
  let g : U → (S × T) → (V × T) := fun z (x, y) ↦ (f z x, y)
  have hg : ∀ t, Function.Injective (g t) :=
    fun _ _ _ h ↦ Prod.ext_iff.2 ⟨hf _ (Prod.ext_iff.1 h).1, (Prod.ext_iff.1 h).2⟩
  rw [← condEntropy_of_injective μ (hX.prodMk hY) hZ g hg, ← condEntropy_of_injective μ hX hZ _ hf]

lemma condMutualInfo_of_inj [Countable U]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z]
    {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
    {f : U → V} (hf : Function.Injective f) :
    I[X : Y | f ∘ Z; μ] = I[X : Y | Z; μ] := by
  have hfZ : Measurable (f ∘ Z) := by fun_prop
  rw [condMutualInfo_eq hX hY hZ, condMutualInfo_eq hX hY hfZ,
    condEntropy_of_injective' _ hX hZ _ hf hfZ, condEntropy_of_injective' _ hY hZ _ hf hfZ,
    condEntropy_of_injective' _ (hX.prodMk hY) hZ _ hf hfZ]


lemma condMutualInfo_of_inj' {S T U S' T' U' Ω : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T]
    [MeasurableSpace U] [MeasurableSingletonClass U] [Countable U]
    [MeasurableSpace S'] [MeasurableSingletonClass S'] [Countable S']
    [MeasurableSpace T'] [MeasurableSingletonClass T'] [Countable T']
    [MeasurableSpace U'] [MeasurableSingletonClass U'] [Countable U']
    {X : Ω → S} {Y : Ω → T} {Z : Ω → U} (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z]
    {f : S → S'} (hf : Function.Injective f)
    {g : T → T'} (hg : Function.Injective g)
    {h : U → U'} (hh : Function.Injective h)
    : I[f ∘ X : g ∘ Y | h ∘ Z; μ] = I[X : Y | Z; μ] := calc
    _ = I[f ∘ X : g ∘ Y | Z; μ] := by rw [condMutualInfo_of_inj _ _ _ _ hh] <;> try fun_prop
    _ = I[X : g ∘ Y | Z; μ] := by
      convert condMutualInfo_of_inj_map hX _ hZ (fun _ ↦ f) (fun _ ↦ hf) <;> try infer_instance
      fun_prop
    _ = I[g ∘ Y : X | Z; μ] := by apply condMutualInfo_comm <;> fun_prop
    _ = I[Y : X | Z; μ] := by
      convert condMutualInfo_of_inj_map hY _ hZ (fun _ ↦ g) (fun _ ↦ hg) <;> try infer_instance
      fun_prop
    _ = _ := by apply condMutualInfo_comm <;> fun_prop


lemma condEntropy_prod_eq_of_indepFun [Finite T] [Finite U] [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) [FiniteRange X]
    (h : IndepFun (⟨X, Y⟩) Z μ) :
    H[X | ⟨Y, Z⟩ ; μ] = H[X | Y ; μ] := by
  cases nonempty_fintype U
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  rw [condEntropy_prod_eq_sum _ hY hZ]
  have : H[X | Y ; μ] = ∑ z, (μ.real (Z ⁻¹' {z})) * H[X | Y ; μ] := by
    rw [← Finset.sum_mul, sum_measureReal_preimage_singleton _ fun z _ ↦ hZ <| .singleton z]; simp
  rw [this]
  congr with w
  rcases eq_or_ne (μ (Z ⁻¹' {w})) 0 with hw|hw
  · simp [hw, Measure.real]
  congr 1
  have : IsProbabilityMeasure (μ[|Z ⁻¹' {w}]) := cond_isProbabilityMeasure hw
  apply IdentDistrib.condEntropy_eq hX hY hX hY
  exact (h.identDistrib_cond (MeasurableSet.singleton w) (hX.prodMk hY) hZ hw).symm

end

section IsProbabilityMeasure

variable [MeasurableSingletonClass S] [MeasurableSingletonClass T]

variable [Countable U] [MeasurableSingletonClass U]

/-- `I[X : Y| Z]=0` iff `X, Y` are conditionally independent over `Z`. -/
lemma condMutualInfo_eq_zero (hX : Measurable X) (hY : Measurable Y)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    I[X : Y | Z ; μ] = 0 ↔ CondIndepFun X Y Z μ := by
  rw [condIndepFun_iff, condMutualInfo_eq_integral_mutualInfo, integral_eq_zero_iff_of_nonneg]
  · have : (fun x ↦ I[X : Y;μ[| Z ⁻¹' {x}]]) =ᵐ[μ.map Z] 0 ↔
      ∀ᵐ z ∂(μ.map Z), I[X : Y ; μ[| Z ⁻¹' {z}]] = 0 := by rfl
    rw [this]
    apply Filter.eventually_congr
    rw [ae_iff_of_countable]
    intro z _hz
    exact mutualInfo_eq_zero hX hY
  · intro z
    by_cases hz : μ (Z ⁻¹' {z}) = 0
    · simp [cond_eq_zero_of_meas_eq_zero hz, mutualInfo_def]
    · exact mutualInfo_nonneg hX hY _
  · exact integrable_of_finiteSupport _

variable (μ)
variable [Countable S] [Countable T]

/-- If `X, Y` are conditionally independent over `Z`, then `H[X, Y, Z] = H[X, Z] + H[Y, Z] - H[Z]`.
-/
lemma ent_of_cond_indep (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
     (h : CondIndepFun X Y Z μ) [IsZeroOrProbabilityMeasure μ]
     [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
     H[⟨X, ⟨Y, Z⟩⟩ ; μ] = H[⟨X, Z⟩; μ] + H[⟨Y, Z⟩; μ] - H[Z; μ] := by
  have hI : I[X : Y | Z ; μ] = 0 := (condMutualInfo_eq_zero hX hY).mpr h
  rw [condMutualInfo_eq hX hY hZ] at hI
  rw [entropy_assoc hX hY hZ, chain_rule _ (hX.prodMk hY) hZ, chain_rule _ hX hZ,
    chain_rule _ hY hZ]
  linarith [hI]

variable [IsZeroOrProbabilityMeasure μ]

/-- `H[X] - H[X|Y] = I[X : Y]` -/
lemma entropy_sub_condEntropy (hX : Measurable X) (hY : Measurable Y) [FiniteRange X]
    [FiniteRange Y] : H[X ; μ] - H[X | Y ; μ] = I[X : Y ; μ] := by
  rw [mutualInfo_def, chain_rule _ hX hY, add_comm, add_sub_add_left_eq_sub]

/-- `H[X | Y] ≤ H[X]`. -/
lemma condEntropy_le_entropy (hX : Measurable X) (hY : Measurable Y) [FiniteRange X]
    [FiniteRange Y] : H[X | Y ; μ] ≤ H[X ; μ] :=
  sub_nonneg.1 <| by rw [entropy_sub_condEntropy _ hX hY]; exact mutualInfo_nonneg hX hY _

/-- `H[X | Y, Z] ≤ H[X | Z]`. -/
lemma entropy_submodular (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    H[X | ⟨Y, Z⟩ ; μ] ≤ H[X | Z ; μ] := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  have : Nonempty S := Nonempty.map X (μ.nonempty_of_neZero)
  have : Nonempty T := Nonempty.map Y (μ.nonempty_of_neZero)
  rw [condEntropy_eq_kernel_entropy hX hZ, condEntropy_two_eq_kernel_entropy hX hY hZ]
  refine (Kernel.entropy_condKernel_le_entropy_snd ?_).trans_eq ?_
  · apply Kernel.aefiniteKernelSupport_condDistrib
    all_goals fun_prop
  exact Kernel.entropy_congr (condDistrib_snd_ae_eq hY hX hZ _)

/-- Data-processing inequality for the conditional entropy: `H[Y|f(X)] ≥ H[Y|X]`
To upgrade this to equality, see `condEntropy_of_injective'` -/
lemma condEntropy_comp_ge
    [FiniteRange X] [FiniteRange Y] (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (f : S → U) : H[Y | f ∘ X ; μ] ≥ H[Y | X; μ] := by
  have h_joint : H[⟨Y, ⟨X, f ∘ X⟩⟩ ; μ] = H[⟨Y, X⟩ ; μ] := by
    let g : T × S → T × S × U := fun (y, x) ↦ (y, (x, f x))
    change H[g ∘ ⟨Y, X⟩ ; μ] = H[⟨Y, X⟩ ; μ]
    refine entropy_comp_of_injective μ (by exact Measurable.prod hY hX) g (fun _ _ h => ?_)
    repeat rewrite [Prod.mk.injEq] at h
    exact Prod.ext h.1 h.2.1
  have hZ : Measurable (f ∘ X) := by fun_prop
  rewrite [chain_rule'' μ hY hX, ← entropy_prod_comp hX μ f, ← h_joint,
    ← chain_rule'' μ hY (Measurable.prod (by exact hX) (by exact hZ))]
  exact entropy_submodular μ hY hX hZ

/-- The submodularity inequality: `H[X, Y, Z] + H[Z] ≤ H[X, Z] + H[Y, Z]`. -/
lemma entropy_triple_add_entropy_le (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    H[⟨X, ⟨Y, Z⟩⟩ ; μ] + H[Z ; μ] ≤ H[⟨X, Z⟩ ; μ] + H[⟨Y, Z⟩ ; μ] := by
  rw [chain_rule _ hX (hY.prodMk hZ), chain_rule _ hX hZ, chain_rule _ hY hZ]
  ring_nf
  exact add_le_add le_rfl (entropy_submodular _ hX hY hZ)

end IsProbabilityMeasure
end mutualInfo
end ProbabilityTheory


section dataProcessing

open Function MeasureTheory Measure Real
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace ProbabilityTheory

universe uΩ uS uT uU uV uW

variable {Ω : Type uΩ} {S : Type uS} {T : Type uT} {U : Type uU} {V : Type uV} {W : Type uW}
  [mΩ : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
  [MeasurableSpace V] [MeasurableSpace W]
  [Countable S] [Countable T] [Countable V] [Countable W]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
  [MeasurableSingletonClass V] [MeasurableSingletonClass W]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U}
  {μ : Measure Ω}

/--
Let `X, Y`be random variables. For any function `f, g` on the range of `X`, we have
`I[f(X) : Y] ≤ I[X : Y]`.
-/
lemma mutual_comp_le [Countable U] (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (f : S → U) [FiniteRange X] [FiniteRange Y] :
    I[f ∘ X : Y ; μ] ≤ I[X : Y ; μ] := by
  have h_meas : Measurable (f ∘ X) := by fun_prop
  rw [mutualInfo_comm h_meas hY, mutualInfo_comm hX hY,
    mutualInfo_eq_entropy_sub_condEntropy hY h_meas, mutualInfo_eq_entropy_sub_condEntropy hY hX]
  gcongr
  exact condEntropy_comp_ge μ hX hY f

/-- Let `X, Y` be random variables. For any functions `f, g` on the ranges of `X, Y` respectively,
we have `I[f ∘ X : g ∘ Y ; μ] ≤ I[X : Y ; μ]`. -/
lemma mutual_comp_comp_le [Countable U] (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (f : S → U) (g : T → V) (hg : Measurable g)
    [FiniteRange X] [FiniteRange Y] :
    I[f ∘ X : g ∘ Y ; μ] ≤ I[X : Y ; μ] :=
  calc
    _ ≤ I[X : g ∘ Y ; μ] := mutual_comp_le μ hX (Measurable.comp hg hY) f
    _ = I[g ∘ Y : X ; μ] := mutualInfo_comm hX (Measurable.comp hg hY) μ
    _ ≤ I[Y : X ; μ] := mutual_comp_le μ hY hX g
    _ = I[X : Y ; μ] := mutualInfo_comm hY hX μ

/-- Let `X, Y, Z`. For any functions `f, g` on the ranges of `X, Y` respectively,
we have `I[f ∘ X : g ∘ Y | Z ; μ] ≤ I[X : Y | Z ; μ]`. -/
lemma condMutual_comp_comp_le (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (hZ : Measurable Z) (f : S → V) (g : T → W) (hg : Measurable g)
    [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    I[f ∘ X : g ∘ Y | Z ; μ] ≤ I[X : Y | Z ; μ] := by
  rw [condMutualInfo_eq_sum hZ, condMutualInfo_eq_sum hZ]
  apply Finset.sum_le_sum
  intro i _
  rcases eq_or_lt_of_le (measureReal_nonneg (μ := μ) (s := (Z ⁻¹' {i}))) with h | h
  · simp [← h]
  · gcongr
    have : IsProbabilityMeasure (μ[|Z ← i]) := by
      apply cond_isProbabilityMeasure_of_finite
      · exact (ENNReal.toReal_ne_zero.mp (ne_of_gt h)).left
      · exact (ENNReal.toReal_ne_zero.mp (ne_of_gt h)).right
    apply mutual_comp_comp_le _ hX hY f g hg

end ProbabilityTheory
end dataProcessing
