/-
Copyright (c) 2024 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Tactic.Finiteness

/-!
# Conditional independence of functions

Defines `CondIndepFun f g h μ`, the assertion that two random variables `f` and `g` are
conditionally independent given a third random variable `h`. This is the function-indexed
conditional independence used by PFR and required by the Shannon-entropy API, distinct from
Mathlib's `CondIndepFun` which takes a σ-algebra.

Forked from `PFR.ForMathlib.ConditionalIndependence` in
[teorth/pfr](https://github.com/teorth/pfr) at rev `80daaf1`, retaining only the minimal set of
declarations required for the Zhang-Yeung entropy API (the existence lemmas for conditionally
independent copies from PFR are omitted).
-/

public section

open MeasureTheory Measure Set
open scoped ENNReal

namespace ProbabilityTheory

section
variable {Ω α β : Type*} {_ : MeasurableSpace Ω} {_ : MeasurableSpace α} {_ : MeasurableSpace β}
  {μ : Measure Ω} {A : Ω → α} {B : Ω → β}

/-- If `A` is independent from `B`, then conditioning on an event given by `B` does not change
the distribution of `A`. -/
theorem IndepFun.identDistrib_cond [IsProbabilityMeasure μ]
    (hi : IndepFun A B μ) {s : Set β}
    (hs : MeasurableSet s) (hA : Measurable A) (hB : Measurable B)
    (h : μ (B ⁻¹' s) ≠ 0) :
    IdentDistrib A A μ (μ[|B ⁻¹' s]) := by
  refine ⟨hA.aemeasurable, hA.aemeasurable, ?_⟩
  ext t ht
  rw [Measure.map_apply hA ht, Measure.map_apply hA ht, cond_apply (hB hs), Set.inter_comm,
    hi.measure_inter_preimage_eq_mul _ _ ht hs, mul_comm, mul_assoc,
    ENNReal.mul_inv_cancel h (by finiteness), mul_one]

end

section defs
variable {Ω Ω' α β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace α]
  [MeasurableSpace β] [MeasurableSpace γ] {μ : Measure Ω} {f : Ω → α} {g : Ω → β} {h : Ω → γ}

/-- The assertion that `f` and `g` are conditionally independent relative to `h`. -/
def CondIndepFun (f : Ω → α) (g : Ω → β) (h : Ω → γ) (μ : Measure Ω := by volume_tac) : Prop :=
  ∀ᵐ z ∂ (μ.map h), IndepFun f g (μ[|h ← z])

lemma condIndepFun_iff : CondIndepFun f g h μ ↔ ∀ᵐ z ∂ (μ.map h), IndepFun f g (μ[|h ← z]) := by rfl

end defs

end ProbabilityTheory
