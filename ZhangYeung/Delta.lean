import ZhangYeung.Prelude

/-!
# The Zhang-Yeung delta quantity

The Zhang-Yeung delta

  `Δ(Z, U | X, Y) := I(Z; U) - I(Z; U | X) - I(Z; U | Y)`

is the central quantity of the Zhang-Yeung conditional information inequality [ZhangYeung1998]. The main theorem of the paper states an upper bound on this quantity; that bound is a non-Shannon information inequality whose proof rests on the copy lemma and lives in a later milestone. This module only captures the *equational* content: the definition, the symmetries induced by commutativity of mutual information, the expansion into raw entropy terms, and the linear-arithmetic interrelation of the three shapes in which the paper presents the main inequality (equations 21, 22, and 23).

## Main definitions

- `ZhangYeung.delta`: the quantity `Δ(Z, U | X, Y)`.

## Implementation notes

The four codomains `S₁ S₂ S₃ S₄` of the random variables live under a shared finite-alphabet specialization `[Fintype Sᵢ]` + `[MeasurableSingletonClass Sᵢ]`. That specialization discharges PFR's discrete/countable side conditions uniformly (via `Fintype → Finite → Countable`) and supplies the `FiniteRange` obligations PFR's commutativity and entropy-expansion lemmas impose on the measured and conditioning variables. The `variable` block is staged: the definition and the purely algebraic lemmas only need `[MeasurableSpace Sᵢ]`; lemmas downstream of PFR's discrete API are collected after a later `variable` block introducing the `Fintype`/`MeasurableSingletonClass` instances.

No notation `Δ[Z : U | X, Y ; μ]` is introduced; plain function application `delta Z U X Y μ` suffices for the uses anticipated in the current milestone. The decision to introduce notation is deferred until a later milestone whose proofs exercise `delta` heavily enough to warrant it.

## References

Zhang, Zhen and Yeung, Raymond W., "On characterization of entropy function via information inequalities", IEEE Trans. Inform. Theory 44 (1998), 1440-1452.

## Tags

Shannon entropy, mutual information, non-Shannon information inequality, Zhang-Yeung
-/

namespace ZhangYeung

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]
  {S₁ S₂ S₃ S₄ : Type*}
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]

/-- The Zhang-Yeung delta `Δ(Z, U | X, Y) := I(Z; U) - I(Z; U | X) - I(Z; U | Y)`. This is the central quantity of Zhang-Yeung (1998); the main inequality of the paper bounds it from above by a Shannon-type expression in the four random variables, but that bound is a non-Shannon information inequality proved via the copy lemma and is not part of this definition. -/
noncomputable def delta
    (Z : Ω → S₁) (U : Ω → S₂) (X : Ω → S₃) (Y : Ω → S₄)
    (μ : Measure Ω := by volume_tac) : ℝ :=
  I[Z : U ; μ] - I[Z : U | X ; μ] - I[Z : U | Y ; μ]

end ZhangYeung
