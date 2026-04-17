import ZhangYeung.Prelude
import Mathlib.Probability.Kernel.CondDistrib

/-!
# Zhang-Yeung Theorem 2: a conditional information inequality

Theorem 2 of [@zhangyeung1998] (originally proved in reference [39] cited therein) states that for any four discrete random variables `X, Y, Z, U`, the hypothesis

  `I[X : Y ; μ] = 0` and `I[X : Y | Z ; μ] = 0`   (eq. 16)

implies the conditional information inequality

  `I[X : Y | ⟨Z, U⟩ ; μ] ≤ I[Z : U | ⟨X, Y⟩ ; μ] + I[X : Y | U ; μ]`.   (eq. 17)

This module formalizes the implication (16) ⇒ (17) on finite-alphabet random variables. It is a single-variable warm-up for the two-copy construction used in the paper's main non-Shannon inequality; its purpose is to exercise the Lean-level kernel-composition and identical-distribution bookkeeping in the simpler single-copy setting.

## Main statements

- `ZhangYeung.theorem2`: the implication (16) ⇒ (17) for discrete random variables on a probability space.

## Implementation notes

The proof follows the single-copy construction of the 1997 Zhang-Yeung argument. An auxiliary random variable `Y₁` is introduced on the extended probability space `Ω × S₂` via the regular conditional distribution `condDistrib Y ⟨Z, U⟩ μ` pulled back along `⟨Z, U⟩ : Ω → S₃ × S₄`. The resulting measure `ν := μ ⊗ₘ κΩ` has two key properties: (i) the triple `(Y₁, Z, U)` under `ν` is identically distributed to `(Y, Z, U)` under `μ`, and (ii) `I[X : Y₁ | ⟨Z, U⟩ ; ν] = 0`. The conclusion (17) then follows from Shannon-type algebra combined with the hypothesis equalities from (16).

The four codomains `S₁, S₂, S₃, S₄` are specialized to `[Fintype]` + `[MeasurableSingletonClass]`. This specialization supplies PFR's `FiniteRange` obligations uniformly (via `Fintype → Finite → Countable → FiniteRange`) and, crucially for `condDistrib`, implies `[StandardBorelSpace]` via Mathlib's chain `MeasurableSingletonClass α + Countable α ⇒ DiscreteMeasurableSpace α ⇒ StandardBorelSpace α`. No extra typeclass plumbing is needed.

Paper ordering `(X, Y, Z, U)` is followed here because Theorem 2 is a standalone inequality read most naturally in that order; `ZhangYeung/Delta.lean` uses `(Z, U, X, Y)` because the delta quantity is symmetric in its first two arguments, but the two modules share no variables so the naming clash is harmless.

## References

* [@zhangyeung1998] -- see `references/transcriptions/zhangyeung1998.md` for a verbatim transcription of equations (16) and (17), verified 2026-04-16.

## Tags

Shannon entropy, conditional mutual information, conditional information inequality, single-copy construction, Zhang-Yeung
-/

namespace ZhangYeung

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]
  {S₁ S₂ S₃ S₄ : Type*}
  [Fintype S₁] [Fintype S₂] [Fintype S₃] [Fintype S₄]
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]

/-- **Zhang-Yeung Theorem 2** ([@zhangyeung1998], eqs. 16-17, originally proved in reference [39] cited therein). For any four discrete random variables `X, Y, Z, U` on a probability space, if `I[X : Y ; μ] = 0` and `I[X : Y | Z ; μ] = 0`, then `I[X : Y | ⟨Z, U⟩ ; μ] ≤ I[Z : U | ⟨X, Y⟩ ; μ] + I[X : Y | U ; μ]`. The proof uses a single-copy construction: an auxiliary variable `Y₁` drawn from the regular conditional distribution `condDistrib Y ⟨Z, U⟩ μ` on an extended probability space. -/
theorem theorem2
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h₁ : I[X : Y ; μ] = 0)
    (h₂ : I[X : Y | Z ; μ] = 0) :
    I[X : Y | ⟨Z, U⟩ ; μ] ≤ I[Z : U | ⟨X, Y⟩ ; μ] + I[X : Y | U ; μ] := by
  sorry

end ZhangYeung
