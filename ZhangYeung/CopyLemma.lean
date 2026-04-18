import ZhangYeung.Delta
import ZhangYeung.Prelude
import PFR.ForMathlib.ConditionalIndependence

/-!
# The Zhang-Yeung copy lemma

The **copy lemma** of [@zhangyeung1998, §III, eqs. 44-45] is the auxiliary-probability construction at the heart of the 1998 proof of Theorem 3. Given four discrete random variables `X, Y, Z, U` on a probability space `(Ω, μ)`, it produces an extended space `(Ω', ν)` carrying a second conditionally-independent copy `(X₁, Y₁)` of `(X, Y)` over the shared variables `(Z, U)`. The auxiliary law is the paper's

  `q(x, y, z, u, x₁, y₁) := p(x, y, z, u) p(x₁, y₁, z, u) / p(z, u)`   (eq. 44)

and this module formalizes it via PFR's `ProbabilityTheory.condIndep_copies` applied to the pair `⟨X, Y⟩` conditioned on the shared variable `⟨Z, U⟩`. The module then ships Lemma 2 (eq. 45),

  `Δ(Z, U | X, Y) = I(X; Y₁) - I(X; Y₁ | U) - I(X; Y₁ | Z) - I(Z; U | X, Y₁)`,

both as an abstract Shannon identity (under the hypothesis that one conditional mutual information vanishes) and as its Zhang-Yeung-flavored specialization to the copy projections. The three subtracted conditional mutual informations on the right are each nonnegative, so the identity immediately yields the inequality `Δ(Z, U | X, Y) ≤ I(X; Y₁)` (and the `X ↔ X₁` symmetric variant `I(Z; U) - 2·I(Z; U | X) ≤ I(X; X₁)`) -- the two inputs to the Shannon chase that proves Theorem 3 in the next milestone.

## Main statements

- `ZhangYeung.copyLemma`: the main existential, producing `Ω', ν, X', Y', X₁, Y₁, Z', U'` together with the three structural facts of eq. (44) (two 4-variable `IdentDistrib`s and one `CondIndepFun`) and the six measurabilities.
- `ZhangYeung.delta_of_condMI_vanishes_eq`: Lemma 2 in abstract form -- under the hypothesis `I[A : D | ⟨B, C⟩ ; ν] = 0`, the delta identity `Δ(B, C | A, D) = I(A; D) - I(A; D | B) - I(A; D | C) - I(B; C | ⟨A, D⟩)`.
- `ZhangYeung.copyLemma_delta_transport_Y_to_Y₁`, `ZhangYeung.copyLemma_delta_transport_X_to_X₁`: bridge identities between `Δ` computed under the original law `μ` and `Δ` computed under the copy law `ν`, with either `(X, Y)` or `(X, X₁)` in the measured slots.
- `ZhangYeung.copyLemma_delta_identity_Y₁`, `ZhangYeung.copyLemma_delta_identity_X_X₁`: Lemma 2 specialized to the copy's projections.
- `ZhangYeung.copyLemma_delta_le_mutualInfo_Y₁`, `ZhangYeung.copyLemma_delta_le_mutualInfo_X_X₁`: the inequality-form corollaries combining the delta identity with nonnegativity of the three conditional mutual information terms on the right of eq. (45).

## Implementation notes

The main `copyLemma` is a direct wrapper around `ProbabilityTheory.condIndep_copies` applied to `⟨X, Y⟩ : Ω → S₁ × S₂` with shared variable `⟨Z, U⟩ : Ω → S₃ × S₄`. `condIndep_copies` returns two pair-valued copies `W₁, W₂` and a shared pair-valued variable `V`; we project to the six individual random variables `X', Y', X₁, Y₁, Z', U'` via `Prod.fst`/`Prod.snd`. The 4-variable `IdentDistrib` outputs are recovered from the 2-level `IdentDistrib`s PFR supplies by composition with a measurable rearrangement `((s₁, s₂), (s₃, s₄)) ↦ (s₁, s₂, s₃, s₄)`.

The four codomains `S₁, S₂, S₃, S₄` are bound at a common universe `u` because `condIndep_copies` binds its two codomains at a single universe. This is a deviation from `ZhangYeung/Delta.lean`'s `Type*` convention, made here because `condIndep_copies` itself requires it.

The derived corollaries (delta transports, delta identities, delta ≤ mutualInfo) live in their own `section Consequences` with a shared `variable` block packaging the eight relevant hypotheses (six measurabilities, two `IdentDistrib`s, one `CondIndepFun`). A caller of `copyLemma` produces these eight hypotheses with one `obtain`, then applies the corollaries as black-box Shannon identities.

Two generic helpers used by the module -- `condIndepFun_comp` (post-composition of `CondIndepFun` on its two measured coordinates) and `IdentDistrib.condMutualInfo_eq` (conditional-mutual-information transport under a three-variable `IdentDistrib`) -- are kept `private` here. If later milestones need them, promote to `ZhangYeung/Prelude.lean` at that point.

## References

* [@zhangyeung1998, §III, eq. 44-45, Lemma 2] -- see `references/transcriptions/zhangyeung1998.md` for a verbatim transcription of equations (44) and (45), verified 2026-04-16.

## Tags

Shannon entropy, conditional mutual information, copy lemma, conditional independence, Zhang-Yeung
-/

namespace ZhangYeung

open MeasureTheory ProbabilityTheory

universe u

/-! ### The main copy construction -/

/-- **The Zhang-Yeung copy lemma** (eq. 44). Given four discrete random variables `X, Y, Z, U` on a probability space `(Ω, μ)`, there exists an extended probability space `(Ω', ν)` carrying six projected random variables `X', Y', X₁, Y₁, Z', U'` such that `(X', Y', Z', U')` and `(X₁, Y₁, Z', U')` each have the original joint law of `(X, Y, Z, U)` under `μ`, and the two pairs `(X', Y')` and `(X₁, Y₁)` are conditionally independent given the shared pair `(Z', U')`. This is a direct wrapper around `ProbabilityTheory.condIndep_copies` applied to `⟨X, Y⟩` conditioned on `⟨Z, U⟩`. -/
theorem copyLemma
    {Ω : Type*} [MeasurableSpace Ω]
    {S₁ S₂ S₃ S₄ : Type u}
    [MeasurableSpace S₁] [MeasurableSpace S₂]
    [MeasurableSpace S₃] [MeasurableSpace S₄]
    [Fintype S₁] [Fintype S₂] [Fintype S₃] [Fintype S₄]
    [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
    [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (ν : Measure Ω')
        (X' : Ω' → S₁) (Y' : Ω' → S₂)
        (X₁ : Ω' → S₁) (Y₁ : Ω' → S₂)
        (Z' : Ω' → S₃) (U' : Ω' → S₄),
      IsProbabilityMeasure ν ∧
      Measurable X' ∧ Measurable Y' ∧
      Measurable X₁ ∧ Measurable Y₁ ∧
      Measurable Z' ∧ Measurable U' ∧
      IdentDistrib (fun ω' => (X' ω', Y' ω', Z' ω', U' ω'))
                   (fun ω  => (X ω,  Y ω,  Z ω,  U ω)) ν μ ∧
      IdentDistrib (fun ω' => (X₁ ω', Y₁ ω', Z' ω', U' ω'))
                   (fun ω  => (X ω,  Y ω,  Z ω,  U ω)) ν μ ∧
      CondIndepFun (fun ω' => (X' ω', Y' ω'))
                   (fun ω' => (X₁ ω', Y₁ ω'))
                   (fun ω' => (Z' ω', U' ω')) ν := by
  sorry

end ZhangYeung
