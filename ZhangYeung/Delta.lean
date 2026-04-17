import ZhangYeung.Prelude

/-!
# The Zhang-Yeung delta quantity

The Zhang-Yeung delta

  `Δ(Z, U | X, Y) := I(Z; U) - I(Z; U | X) - I(Z; U | Y)`

is the central quantity of the Zhang-Yeung conditional information inequality [@zhangyeung1998]. The main theorem of the paper states an upper bound on this quantity; that bound is a non-Shannon information inequality whose proof rests on the copy lemma and lives in a later milestone. This module only captures the *equational* content: the definition, the symmetries induced by commutativity of mutual information, the expansion into raw entropy terms, and the linear-arithmetic interrelation of the three shapes in which the paper presents the main inequality (equations 21, 22, and 23).

## Main definitions

- `ZhangYeung.delta`: the quantity `Δ(Z, U | X, Y)`.

## Main statements

- `ZhangYeung.delta_def`: definitional unfolding.
- `ZhangYeung.delta_comm_cond`: the two conditioning arguments commute.
- `ZhangYeung.delta_comm_main`: the two measured arguments commute (uses `mutualInfo_comm` and `condMutualInfo_comm`).
- `ZhangYeung.delta_self`: the case `X = Y`.
- `ZhangYeung.delta_eq_entropy`: expansion into raw entropy terms.
- `ZhangYeung.delta_form21_iff`, `ZhangYeung.delta_form22_iff`, `ZhangYeung.delta_form23_iff`: iff-equivalences between the integer-scaled shape produced by a copy-lemma proof and the shape the paper states.
- `ZhangYeung.delta_form23_of_form21_form22`: the symmetric form (23) follows from (21) and (22) by averaging.
- `ZhangYeung.delta_le_mutualInfo`: `Δ ≤ I[Z : U]`, from nonnegativity of conditional mutual information.

## Implementation notes

The four codomains `S₁ S₂ S₃ S₄` of the random variables live under a shared finite-alphabet specialization `[Fintype Sᵢ]` + `[MeasurableSingletonClass Sᵢ]`. That specialization discharges PFR's discrete/countable side conditions uniformly (via `Fintype → Finite → Countable`) and supplies the `FiniteRange` obligations PFR's commutativity and entropy-expansion lemmas impose on the measured and conditioning variables. The `variable` block is staged: the definition and the purely algebraic lemmas only need `[MeasurableSpace Sᵢ]`; lemmas downstream of PFR's discrete API are collected after a later `variable` block introducing the `Fintype`/`MeasurableSingletonClass` instances.

No notation `Δ[Z : U | X, Y ; μ]` is introduced; plain function application `delta Z U X Y μ` suffices for the uses anticipated in the current milestone. The decision to introduce notation is deferred until a later milestone whose proofs exercise `delta` heavily enough to warrant it.

The `delta_self` lemma handles only the *literal* repeated-conditioner case `X = Y`. Bridging `Δ(Z, U | X, X₁)` where `X₁` is merely a copy of `X` requires a separate transport lemma for `condMutualInfo` (under the copy construction's `IdentDistrib` hypotheses), which is out of scope for this module.

## References

* [@zhangyeung1998] -- see `references/transcriptions/zhangyeung1998.md` for a verbatim transcription of the paper's equations (20)-(23), verified 2026-04-16.

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

/-- Definitional unfolding of `delta`. -/
lemma delta_def (Z : Ω → S₁) (U : Ω → S₂) (X : Ω → S₃) (Y : Ω → S₄) (μ : Measure Ω) :
    delta Z U X Y μ
      = I[Z : U ; μ] - I[Z : U | X ; μ] - I[Z : U | Y ; μ] := rfl

/-- Swapping the two conditioning arguments leaves `delta` unchanged. -/
lemma delta_comm_cond (Z : Ω → S₁) (U : Ω → S₂) (X : Ω → S₃) (Y : Ω → S₄) (μ : Measure Ω) :
    delta Z U X Y μ = delta Z U Y X μ := by
  simp only [delta_def]; ring

/-- The case `X = Y`: `Δ(Z, U | X, X) = I(Z; U) - 2·I(Z; U | X)`. -/
lemma delta_self (Z : Ω → S₁) (U : Ω → S₂) (X : Ω → S₃) (μ : Measure Ω) :
    delta Z U X X μ = I[Z : U ; μ] - 2 * I[Z : U | X ; μ] := by
  simp only [delta_def]; ring

/-- Paper eq. (21): the inequality `2·Δ(Z, U | X, Y) ≤ I(X;Y) + I(X;ZU) + I(Z;U|X) - I(Z;U|Y)` is equivalent to the compact form `2·I(Z;U) - 3·I(Z;U|X) - I(Z;U|Y) ≤ I(X;Y) + I(X;ZU)`, which is the shape a copy-lemma proof naturally produces. -/
lemma delta_form21_iff
    (Z : Ω → S₁) (U : Ω → S₂) (X : Ω → S₃) (Y : Ω → S₄) (μ : Measure Ω) :
    2 * delta Z U X Y μ
        ≤ I[X : Y ; μ] + I[X : ⟨Z, U⟩ ; μ] + I[Z : U | X ; μ] - I[Z : U | Y ; μ]
      ↔ 2 * I[Z : U ; μ] - 3 * I[Z : U | X ; μ] - I[Z : U | Y ; μ]
          ≤ I[X : Y ; μ] + I[X : ⟨Z, U⟩ ; μ] := by
  constructor <;> intro h <;> linarith [delta_def Z U X Y μ]

/-- Paper eq. (22): the `X ↔ Y` swap of `delta_form21_iff`. -/
lemma delta_form22_iff
    (Z : Ω → S₁) (U : Ω → S₂) (X : Ω → S₃) (Y : Ω → S₄) (μ : Measure Ω) :
    2 * delta Z U X Y μ
        ≤ I[X : Y ; μ] + I[Y : ⟨Z, U⟩ ; μ] - I[Z : U | X ; μ] + I[Z : U | Y ; μ]
      ↔ 2 * I[Z : U ; μ] - I[Z : U | X ; μ] - 3 * I[Z : U | Y ; μ]
          ≤ I[X : Y ; μ] + I[Y : ⟨Z, U⟩ ; μ] := by
  constructor <;> intro h <;> linarith [delta_def Z U X Y μ]

/-- Paper eq. (23), the symmetric form of Theorem 3, follows from eqs. (21) and (22) by averaging. This lemma contains no measure-theoretic content; the inequalities (21) and (22) are the nontrivial inputs and are proved in a later milestone via the copy lemma. -/
lemma delta_form23_of_form21_form22
    {Z : Ω → S₁} {U : Ω → S₂} {X : Ω → S₃} {Y : Ω → S₄} {μ : Measure Ω}
    (h21 : 2 * delta Z U X Y μ
        ≤ I[X : Y ; μ] + I[X : ⟨Z, U⟩ ; μ] + I[Z : U | X ; μ] - I[Z : U | Y ; μ])
    (h22 : 2 * delta Z U X Y μ
        ≤ I[X : Y ; μ] + I[Y : ⟨Z, U⟩ ; μ] - I[Z : U | X ; μ] + I[Z : U | Y ; μ]) :
    4 * delta Z U X Y μ
      ≤ 2 * I[X : Y ; μ] + I[X : ⟨Z, U⟩ ; μ] + I[Y : ⟨Z, U⟩ ; μ] := by
  linarith

/-- The integer-scaled conclusion of `delta_form23_of_form21_form22` is equivalent to the paper's `1/2` and `1/4` statement. -/
lemma delta_form23_iff
    (Z : Ω → S₁) (U : Ω → S₂) (X : Ω → S₃) (Y : Ω → S₄) (μ : Measure Ω) :
    4 * delta Z U X Y μ
        ≤ 2 * I[X : Y ; μ] + I[X : ⟨Z, U⟩ ; μ] + I[Y : ⟨Z, U⟩ ; μ]
      ↔ delta Z U X Y μ
          ≤ (1 / 2) * I[X : Y ; μ] + (1 / 4) * (I[X : ⟨Z, U⟩ ; μ] + I[Y : ⟨Z, U⟩ ; μ]) := by
  constructor <;> intro h <;> linarith

/-! ### Lemmas requiring finite-alphabet structure

The remaining lemmas rely on PFR's commutativity and entropy-expansion results, which are stated under discrete/countable hypotheses on the codomains of the measured random variables. Extending the shared `variable` block with `[Fintype Sᵢ]` and `[MeasurableSingletonClass Sᵢ]` supplies those hypotheses uniformly: `Fintype → Finite → Countable` closes the discrete side, and the same `Fintype` instances discharge PFR's `FiniteRange` obligations via the instance `{Ω G : Type*} (X : Ω → G) [Finite G] : FiniteRange X`. -/

variable [Fintype S₁] [Fintype S₂] [Fintype S₃] [Fintype S₄]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]

omit [Fintype S₃] [Fintype S₄] [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄] in
/-- Swapping the two measured arguments leaves `delta` unchanged, via `mutualInfo_comm` and `condMutualInfo_comm`. -/
lemma delta_comm_main
    {Z : Ω → S₁} {U : Ω → S₂} (hZ : Measurable Z) (hU : Measurable U)
    (X : Ω → S₃) (Y : Ω → S₄) (μ : Measure Ω) :
    delta Z U X Y μ = delta U Z X Y μ := by
  simp only [delta_def, mutualInfo_comm hZ hU, condMutualInfo_comm hZ hU]

/-- Expand `delta` all the way down to raw entropy terms, using `mutualInfo_def` and `condMutualInfo_eq`. This is the bridge to any reasoning at the entropy layer directly (for example, evaluating `delta` on a concrete four-variable distribution when checking bounds or building counterexamples). -/
lemma delta_eq_entropy
    {Z : Ω → S₁} {U : Ω → S₂} {X : Ω → S₃} {Y : Ω → S₄}
    (hZ : Measurable Z) (hU : Measurable U) (hX : Measurable X) (hY : Measurable Y)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    delta Z U X Y μ
      = (H[Z ; μ] + H[U ; μ] - H[⟨Z, U⟩ ; μ])
        - (H[Z | X ; μ] + H[U | X ; μ] - H[⟨Z, U⟩ | X ; μ])
        - (H[Z | Y ; μ] + H[U | Y ; μ] - H[⟨Z, U⟩ | Y ; μ]) := by
  rw [delta_def, mutualInfo_def, condMutualInfo_eq hZ hU hX, condMutualInfo_eq hZ hU hY]

omit [Fintype S₃] [Fintype S₄] [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄] in
/-- `Δ(Z, U | X, Y) ≤ I(Z; U)`: the delta is bounded above by the unconditional mutual information, since conditional mutual information is non-negative. -/
lemma delta_le_mutualInfo
    {Z : Ω → S₁} {U : Ω → S₂} (hZ : Measurable Z) (hU : Measurable U)
    (X : Ω → S₃) (Y : Ω → S₄) (μ : Measure Ω) :
    delta Z U X Y μ ≤ I[Z : U ; μ] := by
  have h₁ : 0 ≤ I[Z : U | X ; μ] := condMutualInfo_nonneg hZ hU
  have h₂ : 0 ≤ I[Z : U | Y ; μ] := condMutualInfo_nonneg hZ hU
  rw [delta_def]; linarith

end ZhangYeung
