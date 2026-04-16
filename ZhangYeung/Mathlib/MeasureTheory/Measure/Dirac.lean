/-
Copyright (c) 2024 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import Mathlib.MeasureTheory.Measure.Dirac

/-!
# Patches to `MeasureTheory.Measure.Dirac`

A small addition expressing `(dirac a).real s` via the indicator function. Forked from
`PFR.Mathlib.MeasureTheory.Measure.Dirac` in [teorth/pfr](https://github.com/teorth/pfr) at rev
`80daaf1`. This should eventually be upstreamed to Mathlib.
-/

public section

namespace MeasureTheory.Measure
variable {α : Type*} [MeasurableSpace α] {s : Set α} {a : α}

@[simp]
lemma dirac_real_apply' (a : α) (hs : MeasurableSet s) : (dirac a).real s = s.indicator 1 a := by
  by_cases ha : a ∈ s <;> simp [Measure.real, *]

end MeasureTheory.Measure
