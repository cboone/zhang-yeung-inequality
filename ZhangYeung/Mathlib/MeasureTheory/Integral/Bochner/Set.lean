/-
Copyright (c) 2024 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Patches to `MeasureTheory.Integral.Bochner.Set`

Forked from `PFR.Mathlib.MeasureTheory.Integral.Bochner.Set` in
[teorth/pfr](https://github.com/teorth/pfr) at rev `80daaf1`. To be upstreamed to Mathlib.
-/

public section

open scoped ENNReal

namespace MeasureTheory
variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma integral_eq_setIntegral {μ : Measure α} {s : Set α} (hs : μ sᶜ = 0) (f : α → E) :
    ∫ x, f x ∂μ = ∫ x in s, f x ∂μ := by
  rw [← setIntegral_univ, ← setIntegral_congr_set]; rwa [ae_eq_univ]

end MeasureTheory
