/-
SPDX-FileCopyrightText: 2026 Christopher Boone
SPDX-License-Identifier: Apache-2.0
-/

import ZhangYeung.EntropyRegion
import ZhangYeung.Theorem4

namespace ZhangYeungTest

open MeasureTheory ProbabilityTheory
open scoped Topology
open ZhangYeung

universe u

section EntropyFunction

example {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {S : Fin n → Type u}
    [∀ i, MeasurableSpace (S i)] (X : ∀ i : Fin n, Ω → S i) (μ : Measure Ω) :
    entropyFn_n X μ = fun α : Finset (Fin n) => H[(fun ω : Ω => fun i : α => X i.1 ω) ; μ] :=
  rfl

example {Ω : Type*} [MeasurableSpace Ω] {S : Fin 4 → Type u}
    [∀ i, MeasurableSpace (S i)] (X : ∀ i : Fin 4, Ω → S i) (μ : Measure Ω) :
    entropyFn X μ = entropyFn_n X μ :=
  rfl

end EntropyFunction

section Regions

example (n : ℕ) : shannonRegion_n n = {F | shannonCone_n F} :=
  rfl

example (n : ℕ) : Set (Finset (Fin n) → ℝ) :=
  entropyRegion_n.{u} n

example (n : ℕ) :
    almostEntropicRegion_n.{u} n = closure (entropyRegion_n.{u} n) :=
  rfl

example
    {Ω : Type u} [MeasurableSpace Ω]
    {n : ℕ} {S : Fin n → Type u}
    [∀ i, MeasurableSpace (S i)] [∀ i, Fintype (S i)]
    [∀ i, MeasurableSingletonClass (S i)]
    (X : ∀ i : Fin n, Ω → S i) (hX : ∀ i, Measurable (X i))
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    entropyFn_n X μ ∈ entropyRegion_n.{u} n := by
  exact ⟨Ω, inferInstance, μ, inferInstance, S, inferInstance, inferInstance, inferInstance, X, hX, rfl⟩

example {n : ℕ} (hn : 4 ≤ n) :
    restrictFirstFour hn = fun F α => F (α.map (Fin.castLEEmb hn)) :=
  rfl

example (F : Finset (Fin 4) → ℝ) :
    shannonCone_n F ↔ shannonCone F :=
  Iff.rfl

end Regions

section Restriction

example {n : ℕ} (hn : 4 ≤ n) :
    restrictFirstFour hn (F_witness_n hn) = F_witness :=
  restrictFirstFour_witness_n hn

end Restriction

end ZhangYeungTest
