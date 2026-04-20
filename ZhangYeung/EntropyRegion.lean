import ZhangYeung.Prelude

/-!
# Entropy-region infrastructure for Theorem 4

This module packages the generic `Fin n` set-function surface used by the exact entropic-region closure form of Theorem 4: the `n`-ary entropy function `entropyFn_n`, the Shannon and entropic region sets, and the restriction map from `Fin n` down to the first four coordinates.
-/

namespace ZhangYeung

open MeasureTheory ProbabilityTheory
open scoped Topology

universe u

/-- `I_F` generalized to `Finset (Fin n)`. -/
def I_F_n {n : ℕ} (F : Finset (Fin n) → ℝ) (α β : Finset (Fin n)) : ℝ :=
  F α + F β - F (α ∪ β)

/-- `condI_F` generalized to `Finset (Fin n)`. -/
def condI_F_n {n : ℕ} (F : Finset (Fin n) → ℝ) (α β γ : Finset (Fin n)) : ℝ :=
  F (α ∪ γ) + F (β ∪ γ) - F (α ∪ β ∪ γ) - F γ

/-- `delta_F` generalized to `Finset (Fin n)`. -/
def delta_F_n {n : ℕ} (F : Finset (Fin n) → ℝ) (i j k l : Fin n) : ℝ :=
  I_F_n F {i} {j} - condI_F_n F {i} {j} {k} - condI_F_n F {i} {j} {l}

/-- `Γ_n` (paper eq. 11) as a predicate on `Finset (Fin n) → ℝ`. -/
def shannonCone_n {n : ℕ} (F : Finset (Fin n) → ℝ) : Prop :=
  F ∅ = 0 ∧
  (∀ α β : Finset (Fin n), α ⊆ β → F α ≤ F β) ∧
  (∀ α β : Finset (Fin n), F (α ∪ β) + F (α ∩ β) ≤ F α + F β)

/-- The entropy function of an `n`-variable random-variable family `X : ∀ i : Fin n, Ω → S i`, expressed as a set function on `Finset (Fin n)`. -/
noncomputable def entropyFn_n
    {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} {S : Fin n → Type u}
    [∀ i, MeasurableSpace (S i)]
    (X : ∀ i : Fin n, Ω → S i) (μ : Measure Ω) : Finset (Fin n) → ℝ :=
  fun α => H[(fun ω : Ω => fun i : α => X i.1 ω) ; μ]

/-- The original four-variable entropy function surface, now as the `n = 4` specialization of `entropyFn_n`. -/
noncomputable abbrev entropyFn
    {Ω : Type*} [MeasurableSpace Ω]
    {S : Fin 4 → Type u}
    [∀ i, MeasurableSpace (S i)]
    (X : ∀ i : Fin 4, Ω → S i) (μ : Measure Ω) : Finset (Fin 4) → ℝ :=
  entropyFn_n X μ

/-- The Shannon outer bound `Γ_n`, packaged as a set. Membership is definitionally `shannonCone_n`. -/
def shannonRegion_n (n : ℕ) : Set (Finset (Fin n) → ℝ) :=
  {F | shannonCone_n F}

/-- The entropic region `Γ_n^*`, packaged as the set of actual entropy functions of `n` discrete random variables. The quantified probability space and codomain family are pinned to `Type` to keep the carrier in `Type`. -/
def entropyRegion_n (n : ℕ) : Set (Finset (Fin n) → ℝ) :=
  {F | ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (S : Fin n → Type) (_ : ∀ i, MeasurableSpace (S i)) (_ : ∀ i, Fintype (S i))
      (_ : ∀ i, MeasurableSingletonClass (S i))
      (X : ∀ i : Fin n, Ω → S i),
      (∀ i, Measurable (X i)) ∧ F = entropyFn_n X μ}

/-- The almost-entropic region `closure (Γ_n^*)`. -/
def almostEntropicRegion_n (n : ℕ) : Set (Finset (Fin n) → ℝ) :=
  closure (entropyRegion_n n)

/-- Restrict a set function on `Fin n` to its first four coordinates. -/
def restrictFirstFour {n : ℕ} (hn : 4 ≤ n) :
    (Finset (Fin n) → ℝ) → (Finset (Fin 4) → ℝ) :=
  fun F α => F (α.map (Fin.castLEEmb hn))

/-- `restrictFirstFour` is continuous in the pointwise topology. -/
theorem restrictFirstFour_continuous {n : ℕ} (hn : 4 ≤ n) : Continuous (restrictFirstFour hn) := by
  refine continuous_pi fun α => ?_
  simpa [restrictFirstFour] using (continuous_apply (α.map (Fin.castLEEmb hn)))

/-- Restricting an `n`-variable entropy function to the first four coordinates agrees with taking the entropy function of the restricted family. -/
theorem entropyFn_n_restrictFirstFour
    {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} {S : Fin n → Type u}
    [∀ i, MeasurableSpace (S i)] [∀ i, Fintype (S i)]
    [∀ i, MeasurableSingletonClass (S i)]
    {X : ∀ i : Fin n, Ω → S i} (hX : ∀ i, Measurable (X i))
    (μ : Measure Ω) (hn : 4 ≤ n) :
    restrictFirstFour hn (entropyFn_n X μ) = entropyFn_n (fun i : Fin 4 => X (Fin.castLE hn i)) μ := by
  ext α
  let e : Fin 4 ↪ Fin n := Fin.castLEEmb hn
  let π : (∀ j : α.map e, S j.1) → (∀ i : α, S (e i.1)) :=
    fun g i => g ⟨e i.1, by exact (Finset.mem_map' e).2 i.2⟩
  have hπ : Function.Injective π := by
    intro g₁ g₂ hMapEq
    funext j
    obtain ⟨i, hi, hij⟩ := Finset.mem_map.mp j.2
    have hValueEq : g₁ ⟨e i, by simpa using (Finset.mem_map' e).2 hi⟩ =
        g₂ ⟨e i, by simpa using (Finset.mem_map' e).2 hi⟩ :=
      congrFun hMapEq ⟨i, hi⟩
    have hj : j = ⟨e i, by simpa using (Finset.mem_map' e).2 hi⟩ := by
      apply Subtype.ext
      exact hij.symm
    cases hj
    simpa using hValueEq
  have h_meas : Measurable (fun ω : Ω => fun j : α.map e => X j.1 ω) :=
    measurable_pi_lambda _ (fun j => hX j.1)
  have h_ent := entropy_comp_of_injective μ h_meas π hπ
  simpa [restrictFirstFour, entropyFn_n, π] using h_ent.symm

/-- Entropic points remain entropic after restriction to the first four coordinates. -/
theorem restrictFirstFour_mem_entropyRegion_n
    {n : ℕ} (hn : 4 ≤ n) {F : Finset (Fin n) → ℝ}
    (hF : F ∈ entropyRegion_n n) :
    restrictFirstFour hn F ∈ entropyRegion_n 4 := by
  rcases hF with ⟨Ω, hΩ, μ, hμ, S, hS, hFin, hMSC, X, hX, rfl⟩
  letI : MeasurableSpace Ω := hΩ
  letI : IsProbabilityMeasure μ := hμ
  letI : ∀ i, MeasurableSpace (S i) := hS
  letI : ∀ i, Fintype (S i) := hFin
  letI : ∀ i, MeasurableSingletonClass (S i) := hMSC
  refine ⟨Ω, inferInstance, μ, inferInstance, (fun i : Fin 4 => S (Fin.castLE hn i)), inferInstance,
    inferInstance, inferInstance, (fun i : Fin 4 => X (Fin.castLE hn i)), ?_, ?_⟩
  · intro i
    exact hX (Fin.castLE hn i)
  · simpa using entropyFn_n_restrictFirstFour hX μ hn

/-- Almost-entropic points remain almost entropic after restriction to the first four coordinates. -/
theorem restrictFirstFour_mem_almostEntropicRegion_n
    {n : ℕ} (hn : 4 ≤ n) {F : Finset (Fin n) → ℝ}
    (hF : F ∈ almostEntropicRegion_n n) :
    restrictFirstFour hn F ∈ almostEntropicRegion_n 4 := by
  have h_map : Set.MapsTo (restrictFirstFour hn) (entropyRegion_n n) (entropyRegion_n 4) :=
    fun _ h_mem => restrictFirstFour_mem_entropyRegion_n hn h_mem
  simpa [almostEntropicRegion_n] using h_map.closure (restrictFirstFour_continuous hn) hF

end ZhangYeung
