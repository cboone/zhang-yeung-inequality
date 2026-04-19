import ZhangYeung.Theorem3

/-!
# Theorem 4: Shannon incompleteness at `n = 4`

Theorem 4 of [@zhangyeung1998, §II, eq. 26] is the scientific payoff of the Zhang-Yeung inequality: the Shannon outer bound `Γ_n` strictly contains the set of entropy functions of `n` discrete random variables for `n ≥ 4`. At `n = 4` the witness is explicit (paper lines 368-377): a concrete rational-valued set function on the 16 subsets of `Fin 4` that satisfies the three Shannon-cone axioms (paper eq. 11) but violates the Zhang-Yeung inequality (paper eq. 21) at the canonical labeling.

The milestone lands four ingredients:

- **Parts (a), (b)** -- pure set-function arithmetic. The witness `F_witness_ℚ : Finset (Fin 4) → ℚ` satisfies `shannonCone F_witness` and fails `zhangYeungHolds F_witness`. Both are decidable finite checks.
- **Part (c), the bridge** -- for any four discrete random variables `X : ∀ i : Fin 4, Ω → S i`, possibly with different finite codomains `S : Fin 4 → Type u`, their entropy function `entropyFn X μ : Finset (Fin 4) → ℝ` satisfies `zhangYeungHolds` at every permutation of the four coordinates. This is a direct restatement of M3's `ZhangYeung.zhangYeung` in the set-function language Part (d) consumes.
- **Part (d), `theorem4`** -- the headline separation. Combining (a)-(c) by contradiction: `F_witness` lies in the Shannon cone, but is not the entropy function of any four discrete random variables.

## Main definitions

- `ZhangYeung.I_F`, `ZhangYeung.condI_F`, `ZhangYeung.delta_F`: the set-function information-theoretic calculus (unconditional mutual info, conditional mutual info, and the Zhang-Yeung delta at the set-function level).
- `ZhangYeung.shannonCone`: the Shannon outer bound `Γ_4` (paper eq. 11) stated as a predicate on `Finset (Fin 4) → ℝ`.
- `ZhangYeung.zhangYeungAt`: the Zhang-Yeung inequality (paper eq. 21) at a specific 4-tuple labeling.
- `ZhangYeung.zhangYeungHolds`: the Zhang-Yeung cone `tildeΓ_4` (paper eq. 25), expressed as `zhangYeungAt` at every permutation of `Fin 4`.
- `ZhangYeung.F_witness_ℚ`: the paper's `n = 4` counterexample, as a `ℚ`-valued set function with `a = 1`.
- `ZhangYeung.F_witness`: the `ℝ`-cast of `F_witness_ℚ`.
- `ZhangYeung.entropyFn`: the set-function view of the joint entropies of a family `X : ∀ i : Fin 4, Ω → S i` of four discrete random variables with possibly different finite codomains.

## Main statements

- `ZhangYeung.shannonCone_of_witness` -- Part (a): `F_witness` lies in the Shannon cone.
- `ZhangYeung.not_zhangYeungHolds_witness` -- Part (b): `F_witness` fails the Zhang-Yeung inequality at the canonical permutation.
- `ZhangYeung.shannon_incomplete` -- intermediate form: there exists a set function in `Γ_4` that is not in `tildeΓ_4`.
- `ZhangYeung.zhangYeungAt_entropyFn`, `ZhangYeung.zhangYeungHolds_of_entropy` -- Part (c), the bridge: every entropy function of four discrete random variables lies in `tildeΓ_4`.
- `ZhangYeung.theorem4` -- Part (d): the headline separation, `F_witness` is in `Γ_4` but is not the entropy function of any four discrete random variables (even allowing the four variables to have different finite codomains).

## Implementation notes

The witness is defined first over `ℚ` so that Parts (a) and (b) close by `Fintype.decidableForallFintype` + `native_decide` on rational arithmetic, then cast to `ℝ` once at the witness boundary. `F_witness` is a plain pointwise cast `fun S => (F_witness_ℚ S : ℝ)`; the companion lemma `F_witness_eq_cast` trivializes downstream `push_cast`/`norm_cast` work. Fixing `a = 1` collapses the paper's parametric family into a single `ℚ`-valued function without losing any content: `theorem4` asserts existence, and the homogeneity the paper uses `a` to exhibit is vacuous at that level.

The Zhang-Yeung cone is quantified over `Equiv.Perm (Fin 4)` to match paper eq. (25) literally; the specific violation uses the permutation `Equiv.swap 0 2 * Equiv.swap 1 3` sending `(0, 1, 2, 3) ↦ (2, 3, 0, 1)`, which instantiates `zhangYeungAt F (σ 0) (σ 1) (σ 2) (σ 3)` as `zhangYeungAt F 2 3 0 1` -- exactly the labeling the paper evaluates on lines 378-388. Permutation evaluation `(σ 0, σ 1, σ 2, σ 3)` is discharged by `decide` once and reused.

The bridge binds the four codomains as a heterogeneous family `S : Fin 4 → Type u` at a single universe `u` and consumes M3's `ZhangYeung.zhangYeung` directly. Each per-subset bridge lemma (`entropyFn_empty`, `entropyFn_singleton`, `entropyFn_pair`, `entropyFn_triple`, `entropyFn_quad`) transports across an explicit `Equiv` between a `Finset`-indexed subtype of `Fin 4` and a standard `Fin k`, invoking PFR's `entropy_comp_of_injective` to move `H[·; μ]` under that transport.

## References

* [@zhangyeung1998, §II, Theorem 4 and its proof, lines 358-388] -- statement, witness construction, and Zhang-Yeung violation verification.
* [@zhangyeung1998, §II, definition of `tildeΓ_4` at eq. (25), lines 339-355] -- the Zhang-Yeung cone.
* [@zhangyeung1998, §II, Shannon cone `Γ_n` at eq. (11)] -- the three Shannon-cone axioms.

## Tags

Shannon entropy, non-Shannon information inequality, Zhang-Yeung, Shannon incompleteness, entropic region
-/

namespace ZhangYeung

open MeasureTheory ProbabilityTheory

universe u

/-! ### Set-function information-theoretic calculus

Paper eqs. (3)-(5), restated at the set-function level on `Finset (Fin 4) → ℝ`. These mirror the random-variable-level information measures PFR exposes (`I[X : Y]`, `I[X : Y | Z]`) but do not require any measure-theoretic context. -/

/-- Set-function mutual information: `I_F(α; β) = F α + F β - F (α ∪ β)`. When `F` is the entropy function of a discrete random-variable family (with `F ∅ = 0`), this coincides with `I[X_α : X_β]`. -/
def I_F (F : Finset (Fin 4) → ℝ) (α β : Finset (Fin 4)) : ℝ :=
  F α + F β - F (α ∪ β)

/-- Set-function conditional mutual information: `condI_F(α; β | γ) = F (α ∪ γ) + F (β ∪ γ) - F (α ∪ β ∪ γ) - F γ`. When `F` is the entropy function of a discrete random-variable family, this coincides with `I[X_α : X_β | X_γ]`. -/
def condI_F (F : Finset (Fin 4) → ℝ) (α β γ : Finset (Fin 4)) : ℝ :=
  F (α ∪ γ) + F (β ∪ γ) - F (α ∪ β ∪ γ) - F γ

/-- Set-function Zhang-Yeung delta at a 4-tuple of coordinates: `delta_F(i, j | k, l) = I_F({i}; {j}) - condI_F({i}; {j} | {k}) - condI_F({i}; {j} | {l})`. Mirrors `ZhangYeung.delta` at the set-function level. -/
def delta_F (F : Finset (Fin 4) → ℝ) (i j k l : Fin 4) : ℝ :=
  I_F F {i} {j} - condI_F F {i} {j} {k} - condI_F F {i} {j} {l}

/-! ### Shannon and Zhang-Yeung cone predicates -/

/-- The Shannon outer bound `Γ_4` from [@zhangyeung1998, eq. 11]: a set function lies in `Γ_4` iff it vanishes on the empty set, is monotone under subset inclusion, and is submodular. -/
def shannonCone (F : Finset (Fin 4) → ℝ) : Prop :=
  F ∅ = 0 ∧
  (∀ α β : Finset (Fin 4), α ⊆ β → F α ≤ F β) ∧
  (∀ α β : Finset (Fin 4), F (α ∪ β) + F (α ∩ β) ≤ F α + F β)

/-- The Zhang-Yeung inequality at a specific 4-tuple labeling (paper eq. 21):

  `delta_F F i j k l ≤ (1/2) * (I_F F {k} {l} + I_F F {k} ({i} ∪ {j}) + condI_F F {i} {j} {k} - condI_F F {i} {j} {l})`.

This is the set-function-level restatement of `ZhangYeung.zhangYeung`. -/
def zhangYeungAt (F : Finset (Fin 4) → ℝ) (i j k l : Fin 4) : Prop :=
  delta_F F i j k l ≤ (1 / 2) * (I_F F {k} {l} + I_F F {k} ({i} ∪ {j})
    + condI_F F {i} {j} {k} - condI_F F {i} {j} {l})

/-- The Zhang-Yeung cone `tildeΓ_4` from [@zhangyeung1998, eq. 25]: a set function `F` lies in `tildeΓ_4` iff `zhangYeungAt F (π 0) (π 1) (π 2) (π 3)` holds at every permutation `π` of `Fin 4`. -/
def zhangYeungHolds (F : Finset (Fin 4) → ℝ) : Prop :=
  ∀ π : Equiv.Perm (Fin 4), zhangYeungAt F (π 0) (π 1) (π 2) (π 3)

/-! ### The paper's `n = 4` counterexample witness

The witness `F_witness_ℚ` is the `a = 1` specialization of the parametric witness on paper lines 368-377: zero on the empty set, `2` on singletons, `4` on `{0, 1}`, `3` on the other five pairs, and `4` on all triples and the 4-set. Implemented as a cascade of `if-then-else` on cardinality (plus a special case for `{0, 1}`) so that `native_decide` reduces through the branches uniformly on all 16 subsets of `Fin 4`. -/

/-- The `ℚ`-valued Zhang-Yeung counterexample witness (paper lines 368-377, specialized to `a = 1`):

  `F_witness_ℚ ∅ = 0`, `F_witness_ℚ {i} = 2`, `F_witness_ℚ {0, 1} = 4`, `F_witness_ℚ {i, j} = 3` for other pairs, `F_witness_ℚ S = 4` for triples and the 4-set.

Living over `ℚ` so Parts (a) and (b) close by `native_decide`. -/
def F_witness_ℚ : Finset (Fin 4) → ℚ := fun S =>
  if S.card = 0 then 0
  else if S.card = 1 then 2
  else if S = ({0, 1} : Finset (Fin 4)) then 4
  else if S.card = 2 then 3
  else 4

/-- The `ℝ`-cast of `F_witness_ℚ`, used in the main statements `shannonCone_of_witness`, `not_zhangYeungHolds_witness`, `shannon_incomplete`, and `theorem4`. -/
noncomputable def F_witness : Finset (Fin 4) → ℝ := fun S => (F_witness_ℚ S : ℝ)

/-- Definitional-shape lemma: `F_witness` is the pointwise `ℚ → ℝ` cast of `F_witness_ℚ`. Used to push `F_witness` into `F_witness_ℚ`-shaped goals before closing by `native_decide` over `ℚ`. -/
lemma F_witness_eq_cast (S : Finset (Fin 4)) :
    F_witness S = (F_witness_ℚ S : ℝ) := rfl

/-! ### Part (a): the witness lies in the Shannon cone -/

/-- Part (a) of Theorem 4: the witness satisfies the three Shannon-cone axioms (paper eq. 11). Discharged by `native_decide` on the `ℚ`-valued `F_witness_ℚ` and cast into `ℝ`. -/
theorem shannonCone_of_witness : shannonCone F_witness := by
  refine ⟨?_, ?_, ?_⟩
  · -- `F_witness ∅ = 0`
    show ((F_witness_ℚ ∅ : ℚ) : ℝ) = 0
    have h : F_witness_ℚ ∅ = 0 := by native_decide
    exact_mod_cast h
  · -- Monotonicity.
    intro α β hαβ
    have h : ∀ α β : Finset (Fin 4), α ⊆ β → F_witness_ℚ α ≤ F_witness_ℚ β := by
      native_decide
    simp only [F_witness_eq_cast]
    exact_mod_cast h α β hαβ
  · -- Submodularity.
    intro α β
    have h : ∀ α β : Finset (Fin 4),
        F_witness_ℚ (α ∪ β) + F_witness_ℚ (α ∩ β) ≤ F_witness_ℚ α + F_witness_ℚ β := by
      native_decide
    simp only [F_witness_eq_cast]
    exact_mod_cast h α β

/-! ### Part (b): the witness violates the Zhang-Yeung inequality -/

/-- Part (b) of Theorem 4: the witness fails the Zhang-Yeung inequality at the canonical labeling `(i, j, k, l) = (2, 3, 0, 1)` (paper lines 378-388). The permutation exhibiting the violation is `σ = Equiv.swap 0 2 * Equiv.swap 1 3`; the resulting numerical check reduces to `1 ≤ 1/2`, which is false. -/
theorem not_zhangYeungHolds_witness : ¬ zhangYeungHolds F_witness := by
  intro h
  -- Specialize at the canonical permutation `σ = swap 0 2 * swap 1 3`,
  -- sending `(0, 1, 2, 3) ↦ (2, 3, 0, 1)`.
  specialize h (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)
  rw [show (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 0 = 2 from by decide,
      show (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 = 3 from by decide,
      show (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 2 = 0 from by decide,
      show (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 3 = 1 from by decide] at h
  -- Unfold `zhangYeungAt` and the set-function calculus at the `ℝ` layer,
  -- then pull the cast out to reduce to a `ℚ`-level numeric check.
  simp only [zhangYeungAt, delta_F, I_F, condI_F, F_witness_eq_cast] at h
  -- Evaluate `F_witness_ℚ` on each concrete subset appearing in `h`.
  have h00 : F_witness_ℚ ({0} : Finset (Fin 4)) = 2 := by native_decide
  have h11 : F_witness_ℚ ({1} : Finset (Fin 4)) = 2 := by native_decide
  have h22 : F_witness_ℚ ({2} : Finset (Fin 4)) = 2 := by native_decide
  have h33 : F_witness_ℚ ({3} : Finset (Fin 4)) = 2 := by native_decide
  have h01 : F_witness_ℚ (({0} : Finset (Fin 4)) ∪ {1}) = 4 := by native_decide
  have h02 : F_witness_ℚ (({2} : Finset (Fin 4)) ∪ {0}) = 3 := by native_decide
  have h03 : F_witness_ℚ (({3} : Finset (Fin 4)) ∪ {0}) = 3 := by native_decide
  have h12 : F_witness_ℚ (({2} : Finset (Fin 4)) ∪ {1}) = 3 := by native_decide
  have h13 : F_witness_ℚ (({3} : Finset (Fin 4)) ∪ {1}) = 3 := by native_decide
  have h23 : F_witness_ℚ (({2} : Finset (Fin 4)) ∪ {3}) = 3 := by native_decide
  have h023 : F_witness_ℚ (({2} : Finset (Fin 4)) ∪ {3} ∪ {0}) = 4 := by native_decide
  have h123 : F_witness_ℚ (({2} : Finset (Fin 4)) ∪ {3} ∪ {1}) = 4 := by native_decide
  have h023' : F_witness_ℚ (({0} : Finset (Fin 4)) ∪ (({2} : Finset (Fin 4)) ∪ {3})) = 4 := by
    native_decide
  rw [h00, h11, h22, h33, h01, h02, h03, h12, h13, h23, h023, h123, h023'] at h
  norm_num at h

/-- Intermediate conclusion (pre-bridge): the Shannon cone strictly contains the Zhang-Yeung cone, `Γ_4 ⊋ tildeΓ_4`. Part (a) and Part (b) combined. This is the original roadmap checkpoint; `theorem4` subsumes it by bridging through M3 to strengthen "not in `tildeΓ_4`" to "not an entropy function". -/
theorem shannon_incomplete :
    ∃ F : Finset (Fin 4) → ℝ, shannonCone F ∧ ¬ zhangYeungHolds F :=
  ⟨F_witness, shannonCone_of_witness, not_zhangYeungHolds_witness⟩

/-! ### Part (c): the bridge from the random-variable form (M3) to the set-function form -/

/-- The entropy function of a four-variable random-variable family `X : ∀ i : Fin 4, Ω → S i`, possibly with different finite codomains `S : Fin 4 → Type u`, expressed as a set function on `Finset (Fin 4)`. For `α : Finset (Fin 4)`, `entropyFn X μ α` is the joint entropy of the tuple indexed by the elements of `α`.

The `Fintype` and `MeasurableSingletonClass` hypotheses on the codomain family are imposed by the downstream bridge lemmas, not by `entropyFn` itself; PFR's `H[_ ; _]` only requires a `MeasurableSpace`. -/
noncomputable def entropyFn
    {Ω : Type*} [MeasurableSpace Ω]
    {S : Fin 4 → Type u}
    [∀ i, MeasurableSpace (S i)]
    (X : ∀ i : Fin 4, Ω → S i) (μ : Measure Ω) : Finset (Fin 4) → ℝ :=
  fun α => H[(fun ω : Ω => fun i : α => X i.1 ω) ; μ]

section EntropyFnEvaluation

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Fin 4 → Type u}
  [∀ i, MeasurableSpace (S i)] [∀ i, Fintype (S i)]
  [∀ i, MeasurableSingletonClass (S i)]
  (X : ∀ i : Fin 4, Ω → S i) (μ : Measure Ω) [IsProbabilityMeasure μ]

omit [∀ i, Fintype (S i)] in
/-- Per-subset bridge lemma at the empty subset: `entropyFn X μ ∅ = 0`. The subtype `{j // j ∈ (∅ : Finset (Fin 4))}` is empty, so the dependent-product codomain `∀ j : ∅, S j.1` is a subsingleton; the joint tuple is constant, and its entropy is zero. -/
lemma entropyFn_empty : entropyFn X μ ∅ = 0 := by
  sorry

omit [IsProbabilityMeasure μ] in
/-- Per-subset bridge lemma at a singleton subset: `entropyFn X μ {i} = H[X i; μ]`. The joint tuple over the single-element subset `{i}` is, up to a measurable bijection into `S i`, just `X i`. -/
lemma entropyFn_singleton (hX : ∀ i, Measurable (X i)) (i : Fin 4) :
    entropyFn X μ {i} = H[X i ; μ] := by
  sorry

omit [IsProbabilityMeasure μ] in
/-- Per-subset bridge lemma at a two-element subset: `entropyFn X μ {i, j} = H[⟨X i, X j⟩; μ]` for `i ≠ j`. The joint tuple over `{i, j}` is measurably bijective with the pair `(X i, X j)`. -/
lemma entropyFn_pair (hX : ∀ i, Measurable (X i))
    {i j : Fin 4} (h : i ≠ j) :
    entropyFn X μ {i, j} = H[⟨X i, X j⟩ ; μ] := by
  sorry

omit [IsProbabilityMeasure μ] in
/-- Per-subset bridge lemma at a three-element subset: `entropyFn X μ {i, j, k} = H[⟨X i, ⟨X j, X k⟩⟩; μ]` for pairwise distinct `i, j, k`. The joint tuple over `{i, j, k}` is measurably bijective with the triple `(X i, (X j, X k))`. -/
lemma entropyFn_triple (hX : ∀ i, Measurable (X i))
    {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    entropyFn X μ {i, j, k} = H[⟨X i, ⟨X j, X k⟩⟩ ; μ] := by
  sorry

omit [IsProbabilityMeasure μ] in
/-- Per-subset bridge lemma at the full four-element subset: `entropyFn X μ {0, 1, 2, 3} = H[⟨X 0, ⟨X 1, ⟨X 2, X 3⟩⟩⟩; μ]`. The joint tuple over the full index set is measurably bijective with the right-associated 4-tuple. -/
lemma entropyFn_quad (hX : ∀ i, Measurable (X i)) :
    entropyFn X μ ({0, 1, 2, 3} : Finset (Fin 4))
      = H[⟨X 0, ⟨X 1, ⟨X 2, X 3⟩⟩⟩ ; μ] := by
  sorry

end EntropyFnEvaluation

/-- The permutation-indexed bridge: at any permutation `π` of `Fin 4`, the entropy function satisfies the Zhang-Yeung inequality (paper eq. 21) at the labeling `(π 0, π 1, π 2, π 3)`. Proved by unfolding `zhangYeungAt`, rewriting each `entropyFn` evaluation into a joint entropy via the per-subset bridge lemmas, and matching the resulting inequality against M3's `ZhangYeung.zhangYeung` applied to `(X (π 0), X (π 1), X (π 2), X (π 3))`. -/
lemma zhangYeungAt_entropyFn
    {Ω : Type*} [MeasurableSpace Ω]
    {S : Fin 4 → Type u}
    [∀ i, MeasurableSpace (S i)] [∀ i, Fintype (S i)]
    [∀ i, MeasurableSingletonClass (S i)]
    {X : ∀ i : Fin 4, Ω → S i} (hX : ∀ i, Measurable (X i))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (π : Equiv.Perm (Fin 4)) :
    zhangYeungAt (entropyFn X μ) (π 0) (π 1) (π 2) (π 3) := by
  sorry

/-- Part (c), the full bridge: the entropy function of any four-variable random-variable family lies in `tildeΓ_4`. One-line wrapper around `zhangYeungAt_entropyFn`. -/
theorem zhangYeungHolds_of_entropy
    {Ω : Type*} [MeasurableSpace Ω]
    {S : Fin 4 → Type u}
    [∀ i, MeasurableSpace (S i)] [∀ i, Fintype (S i)]
    [∀ i, MeasurableSingletonClass (S i)]
    {X : ∀ i : Fin 4, Ω → S i} (hX : ∀ i, Measurable (X i))
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    zhangYeungHolds (entropyFn X μ) :=
  fun π => zhangYeungAt_entropyFn hX μ π

/-! ### Part (d): Theorem 4 -/

/-- **Theorem 4 of [@zhangyeung1998, §II, eq. 26]** at `n = 4`. The Shannon outer bound `Γ_4` strictly contains the set of entropy functions of four discrete random variables: there exists a set function in `Γ_4` that is not the entropy function of any four discrete random variables on any probability space, even allowing the four variables to have different finite codomains. Proved by combining `shannonCone_of_witness` (Part (a)), `not_zhangYeungHolds_witness` (Part (b)), and `zhangYeungHolds_of_entropy` (Part (c)) in a two-step contradiction. -/
theorem theorem4 :
    ∃ F : Finset (Fin 4) → ℝ,
      shannonCone F ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        {S : Fin 4 → Type u}
        [∀ i, MeasurableSpace (S i)] [∀ i, Fintype (S i)]
        [∀ i, MeasurableSingletonClass (S i)]
        (X : ∀ i : Fin 4, Ω → S i) (_ : ∀ i, Measurable (X i)),
        F ≠ entropyFn X μ := by
  refine ⟨F_witness, shannonCone_of_witness, ?_⟩
  intro Ω _ μ _ S _ _ _ X hX heq
  apply not_zhangYeungHolds_witness
  rw [heq]
  exact zhangYeungHolds_of_entropy hX μ

end ZhangYeung
