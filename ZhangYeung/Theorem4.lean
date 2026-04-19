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
open scoped Topology

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
  simp only [entropyFn]
  haveI : IsEmpty {j : Fin 4 // j ∈ (∅ : Finset (Fin 4))} :=
    ⟨fun ⟨j, hj⟩ => Finset.notMem_empty j hj⟩
  haveI : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  have h_eq : (fun ω : Ω => fun j : (∅ : Finset (Fin 4)) => X j.1 ω)
      = fun _ =>
        (fun j : (∅ : Finset (Fin 4)) => X j.1 (Classical.arbitrary Ω)) := by
    funext ω
    exact Subsingleton.elim _ _
  rw [h_eq]
  exact entropy_const _

omit [IsProbabilityMeasure μ] in
/-- Per-subset bridge lemma at a singleton subset: `entropyFn X μ {i} = H[X i; μ]`. The joint tuple over the single-element subset `{i}` is, up to a measurable bijection into `S i`, just `X i`. -/
lemma entropyFn_singleton (hX : ∀ i, Measurable (X i)) (i : Fin 4) :
    entropyFn X μ {i} = H[X i ; μ] := by
  simp only [entropyFn]
  -- Projection π : (∀ j : {i}, S j.1) → S i sending g to its value at ⟨i, mem⟩.
  let π : (∀ j : ({i} : Finset (Fin 4)), S j.1) → S i :=
    fun g => g ⟨i, Finset.mem_singleton.mpr rfl⟩
  -- Injectivity: every j : {i} satisfies j.1 = i, so g is determined by its
  -- value at ⟨i, _⟩.
  have hπ : Function.Injective π := by
    intro g₁ g₂ heq
    funext j
    obtain ⟨j, hj⟩ := j
    have hji : j = i := Finset.mem_singleton.mp hj
    subst hji
    exact heq
  -- The joint RV is measurable: each coordinate `X j.1` is measurable.
  have h_meas : Measurable
      (fun ω : Ω => fun j : ({i} : Finset (Fin 4)) => X j.1 ω) :=
    measurable_pi_lambda _ (fun j => hX j.1)
  -- π ∘ joint = X i definitionally, so the composed entropy collapses.
  have h_ent := entropy_comp_of_injective μ h_meas π hπ
  exact h_ent.symm

omit [IsProbabilityMeasure μ] in
/-- Per-subset bridge lemma at a two-element subset: `entropyFn X μ {i, j} = H[⟨X i, X j⟩; μ]` for `i ≠ j`. The joint tuple over `{i, j}` is measurably bijective with the pair `(X i, X j)`. -/
lemma entropyFn_pair (hX : ∀ i, Measurable (X i))
    {i j : Fin 4} (h : i ≠ j) :
    entropyFn X μ {i, j} = H[⟨X i, X j⟩ ; μ] := by
  simp only [entropyFn]
  -- Projection π : (∀ k : {i, j}, S k.1) → S i × S j evaluating at both indices.
  have hi : i ∈ ({i, j} : Finset (Fin 4)) := by simp
  have hj : j ∈ ({i, j} : Finset (Fin 4)) := by simp
  let π : (∀ k : ({i, j} : Finset (Fin 4)), S k.1) → S i × S j :=
    fun g => (g ⟨i, hi⟩, g ⟨j, hj⟩)
  -- Injectivity: every k : {i, j} satisfies k.1 = i ∨ k.1 = j.
  have hπ : Function.Injective π := by
    intro g₁ g₂ heq
    have h₁ : g₁ ⟨i, hi⟩ = g₂ ⟨i, hi⟩ := (Prod.mk.inj heq).1
    have h₂ : g₁ ⟨j, hj⟩ = g₂ ⟨j, hj⟩ := (Prod.mk.inj heq).2
    funext k
    obtain ⟨k, hk⟩ := k
    rcases Finset.mem_insert.mp hk with hki | hk'
    · subst hki; exact h₁
    · have : k = j := Finset.mem_singleton.mp hk'
      subst this; exact h₂
  have h_meas : Measurable
      (fun ω : Ω => fun k : ({i, j} : Finset (Fin 4)) => X k.1 ω) :=
    measurable_pi_lambda _ (fun k => hX k.1)
  -- π ∘ joint = ⟨X i, X j⟩ definitionally.
  have h_ent := entropy_comp_of_injective μ h_meas π hπ
  exact h_ent.symm

omit [IsProbabilityMeasure μ] in
/-- Per-subset bridge lemma at a three-element subset: `entropyFn X μ {i, j, k} = H[⟨X i, ⟨X j, X k⟩⟩; μ]` for pairwise distinct `i, j, k`. The joint tuple over `{i, j, k}` is measurably bijective with the triple `(X i, (X j, X k))`. -/
lemma entropyFn_triple (hX : ∀ i, Measurable (X i))
    {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    entropyFn X μ {i, j, k} = H[⟨X i, ⟨X j, X k⟩⟩ ; μ] := by
  simp only [entropyFn]
  have hi : i ∈ ({i, j, k} : Finset (Fin 4)) := by simp
  have hj : j ∈ ({i, j, k} : Finset (Fin 4)) := by simp
  have hk : k ∈ ({i, j, k} : Finset (Fin 4)) := by simp
  let π : (∀ m : ({i, j, k} : Finset (Fin 4)), S m.1) → S i × (S j × S k) :=
    fun g => (g ⟨i, hi⟩, (g ⟨j, hj⟩, g ⟨k, hk⟩))
  have hπ : Function.Injective π := by
    intro g₁ g₂ heq
    have h₁ : g₁ ⟨i, hi⟩ = g₂ ⟨i, hi⟩ := (Prod.mk.inj heq).1
    have h₂ : g₁ ⟨j, hj⟩ = g₂ ⟨j, hj⟩ := (Prod.mk.inj (Prod.mk.inj heq).2).1
    have h₃ : g₁ ⟨k, hk⟩ = g₂ ⟨k, hk⟩ := (Prod.mk.inj (Prod.mk.inj heq).2).2
    funext m
    obtain ⟨m, hm⟩ := m
    rcases Finset.mem_insert.mp hm with hmi | hm'
    · subst hmi; exact h₁
    · rcases Finset.mem_insert.mp hm' with hmj | hmk
      · subst hmj; exact h₂
      · have : m = k := Finset.mem_singleton.mp hmk
        subst this; exact h₃
  have h_meas : Measurable
      (fun ω : Ω => fun m : ({i, j, k} : Finset (Fin 4)) => X m.1 ω) :=
    measurable_pi_lambda _ (fun m => hX m.1)
  have h_ent := entropy_comp_of_injective μ h_meas π hπ
  exact h_ent.symm

omit [IsProbabilityMeasure μ] in
/-- Per-subset bridge lemma at the full four-element subset: `entropyFn X μ {0, 1, 2, 3} = H[⟨X 0, ⟨X 1, ⟨X 2, X 3⟩⟩⟩; μ]`. The joint tuple over the full index set is measurably bijective with the right-associated 4-tuple. -/
lemma entropyFn_quad (hX : ∀ i, Measurable (X i)) :
    entropyFn X μ ({0, 1, 2, 3} : Finset (Fin 4))
      = H[⟨X 0, ⟨X 1, ⟨X 2, X 3⟩⟩⟩ ; μ] := by
  simp only [entropyFn]
  have h0 : (0 : Fin 4) ∈ ({0, 1, 2, 3} : Finset (Fin 4)) := by decide
  have h1 : (1 : Fin 4) ∈ ({0, 1, 2, 3} : Finset (Fin 4)) := by decide
  have h2 : (2 : Fin 4) ∈ ({0, 1, 2, 3} : Finset (Fin 4)) := by decide
  have h3 : (3 : Fin 4) ∈ ({0, 1, 2, 3} : Finset (Fin 4)) := by decide
  let π : (∀ m : ({0, 1, 2, 3} : Finset (Fin 4)), S m.1)
      → S 0 × (S 1 × (S 2 × S 3)) :=
    fun g => (g ⟨0, h0⟩, (g ⟨1, h1⟩, (g ⟨2, h2⟩, g ⟨3, h3⟩)))
  have hπ : Function.Injective π := by
    intro g₁ g₂ heq
    have e1 : g₁ ⟨0, h0⟩ = g₂ ⟨0, h0⟩ := (Prod.mk.inj heq).1
    have e2 : g₁ ⟨1, h1⟩ = g₂ ⟨1, h1⟩ := (Prod.mk.inj (Prod.mk.inj heq).2).1
    have e3 : g₁ ⟨2, h2⟩ = g₂ ⟨2, h2⟩ :=
      (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj heq).2).2).1
    have e4 : g₁ ⟨3, h3⟩ = g₂ ⟨3, h3⟩ :=
      (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj heq).2).2).2
    funext m
    obtain ⟨m, hm⟩ := m
    fin_cases m
    · exact e1
    · exact e2
    · exact e3
    · exact e4
  have h_meas : Measurable
      (fun ω : Ω => fun m : ({0, 1, 2, 3} : Finset (Fin 4)) => X m.1 ω) :=
    measurable_pi_lambda _ (fun m => hX m.1)
  have h_ent := entropy_comp_of_injective μ h_meas π hπ
  exact h_ent.symm

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
  -- Distinctness of the four permuted indices from injectivity of `π`.
  have h01 : π 0 ≠ π 1 := fun h => absurd (π.injective h) (by decide)
  have h02 : π 0 ≠ π 2 := fun h => absurd (π.injective h) (by decide)
  have h03 : π 0 ≠ π 3 := fun h => absurd (π.injective h) (by decide)
  have h12 : π 1 ≠ π 2 := fun h => absurd (π.injective h) (by decide)
  have h13 : π 1 ≠ π 3 := fun h => absurd (π.injective h) (by decide)
  have h23 : π 2 ≠ π 3 := fun h => absurd (π.injective h) (by decide)
  -- Apply M3 at the labeling `(X_M3, Y_M3, Z_M3, U_M3) = (X (π 2), X (π 3), X (π 0), X (π 1))`.
  have hM3 := ZhangYeung.zhangYeung (hX (π 2)) (hX (π 3)) (hX (π 0)) (hX (π 1)) μ
  -- Fully unfold `hM3` into unconditional `H[_ ; μ]` arithmetic, matching the
  -- shape the set-function bridge produces.
  rw [delta_def, mutualInfo_def, mutualInfo_def, mutualInfo_def,
      condMutualInfo_eq (hX (π 0)) (hX (π 1)) (hX (π 2)) μ,
      condMutualInfo_eq (hX (π 0)) (hX (π 1)) (hX (π 3)) μ,
      chain_rule'' μ (hX (π 0)) (hX (π 2)),
      chain_rule'' μ (hX (π 1)) (hX (π 2)),
      chain_rule'' μ ((hX (π 0)).prodMk (hX (π 1))) (hX (π 2)),
      chain_rule'' μ (hX (π 0)) (hX (π 3)),
      chain_rule'' μ (hX (π 1)) (hX (π 3)),
      chain_rule'' μ ((hX (π 0)).prodMk (hX (π 1))) (hX (π 3)),
      ← entropy_assoc (hX (π 0)) (hX (π 1)) (hX (π 2)) μ,
      ← entropy_assoc (hX (π 0)) (hX (π 1)) (hX (π 3)) μ] at hM3
  -- Unfold the set-function calculus on the goal.
  unfold zhangYeungAt delta_F I_F condI_F
  -- Collapse `{x} ∪ s` and `insert a s ∪ t` to canonical `insert`-form so the
  -- `entropyFn_pair`/`entropyFn_triple` bridges fire without further massage.
  simp only [Finset.singleton_union, Finset.insert_union]
  -- Apply the per-subset bridge lemmas.
  rw [entropyFn_singleton X μ hX (π 0), entropyFn_singleton X μ hX (π 1),
      entropyFn_singleton X μ hX (π 2), entropyFn_singleton X μ hX (π 3),
      entropyFn_pair X μ hX h01, entropyFn_pair X μ hX h02,
      entropyFn_pair X μ hX h03, entropyFn_pair X μ hX h12,
      entropyFn_pair X μ hX h13, entropyFn_pair X μ hX h23,
      entropyFn_triple X μ hX h01 h02 h12,
      entropyFn_triple X μ hX h01 h03 h13,
      entropyFn_triple X μ hX h02.symm h12.symm h01]
  linarith

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

/-! ### Optional stretch: closure form

Each of the inequalities `zhangYeungAt F (π 0) (π 1) (π 2) (π 3)` is a finite linear inequality among the `F α` values: both sides are linear combinations of the coordinate evaluations `F α`, hence continuous in the pointwise topology on `Finset (Fin 4) → ℝ`. The Zhang-Yeung cone `tildeΓ_4` is therefore pointwise closed, and `F_witness` is not even the pointwise limit of a sequence of set functions that all lie in `tildeΓ_4`. This strengthens `theorem4` past "F_witness is not any entropy function" to "F_witness is not a pointwise limit of `tildeΓ_4` members"; since every entropy function lies in `tildeΓ_4` by `zhangYeungHolds_of_entropy`, the closure form implies the closure-version separation the paper states ($\bar{\Gamma}^*_4 \ne \Gamma_4$) at $n = 4$ without unwinding $\Gamma^*_4$. -/

/-- `I_F` is jointly continuous in the set-function argument under pointwise convergence. -/
private lemma I_F_tendsto
    {F_seq : ℕ → Finset (Fin 4) → ℝ} {F : Finset (Fin 4) → ℝ}
    (h : ∀ α, Filter.Tendsto (fun k => F_seq k α) Filter.atTop (𝓝 (F α)))
    (α β : Finset (Fin 4)) :
    Filter.Tendsto (fun k => I_F (F_seq k) α β) Filter.atTop (𝓝 (I_F F α β)) := by
  simp only [I_F]
  exact ((h α).add (h β)).sub (h _)

/-- `condI_F` is jointly continuous in the set-function argument under pointwise convergence. -/
private lemma condI_F_tendsto
    {F_seq : ℕ → Finset (Fin 4) → ℝ} {F : Finset (Fin 4) → ℝ}
    (h : ∀ α, Filter.Tendsto (fun k => F_seq k α) Filter.atTop (𝓝 (F α)))
    (α β γ : Finset (Fin 4)) :
    Filter.Tendsto (fun k => condI_F (F_seq k) α β γ) Filter.atTop (𝓝 (condI_F F α β γ)) := by
  simp only [condI_F]
  exact (((h _).add (h _)).sub (h _)).sub (h _)

/-- `delta_F` is jointly continuous in the set-function argument under pointwise convergence. -/
private lemma delta_F_tendsto
    {F_seq : ℕ → Finset (Fin 4) → ℝ} {F : Finset (Fin 4) → ℝ}
    (h : ∀ α, Filter.Tendsto (fun k => F_seq k α) Filter.atTop (𝓝 (F α)))
    (i j k l : Fin 4) :
    Filter.Tendsto (fun n => delta_F (F_seq n) i j k l) Filter.atTop
      (𝓝 (delta_F F i j k l)) := by
  simp only [delta_F]
  exact ((I_F_tendsto h _ _).sub (condI_F_tendsto h _ _ _)).sub (condI_F_tendsto h _ _ _)

/-- `zhangYeungHolds` is closed under pointwise convergence: if each `F_seq k` lies in `tildeΓ_4` and `F_seq k α → F α` pointwise, then `F` lies in `tildeΓ_4` too. The inequality `zhangYeungAt F` is a finite `≤` between continuous linear combinations of coordinate evaluations, hence preserved under pointwise limits. -/
lemma zhangYeungHolds_of_tendsto
    {F_seq : ℕ → Finset (Fin 4) → ℝ} {F : Finset (Fin 4) → ℝ}
    (h_seq : ∀ k, zhangYeungHolds (F_seq k))
    (h_lim : ∀ α, Filter.Tendsto (fun k => F_seq k α) Filter.atTop (𝓝 (F α))) :
    zhangYeungHolds F := by
  intro π
  have h_LHS := delta_F_tendsto h_lim (π 0) (π 1) (π 2) (π 3)
  have h_RHS :
      Filter.Tendsto
        (fun k => (1 / 2 : ℝ) * (I_F (F_seq k) {π 2} {π 3}
              + I_F (F_seq k) {π 2} ({π 0} ∪ {π 1})
              + condI_F (F_seq k) {π 0} {π 1} {π 2}
              - condI_F (F_seq k) {π 0} {π 1} {π 3}))
        Filter.atTop
        (𝓝 ((1 / 2 : ℝ) * (I_F F {π 2} {π 3}
            + I_F F {π 2} ({π 0} ∪ {π 1})
            + condI_F F {π 0} {π 1} {π 2}
            - condI_F F {π 0} {π 1} {π 3}))) := by
    refine Filter.Tendsto.const_mul _ ?_
    exact (((I_F_tendsto h_lim _ _).add (I_F_tendsto h_lim _ _)).add
      (condI_F_tendsto h_lim _ _ _)).sub (condI_F_tendsto h_lim _ _ _)
  exact le_of_tendsto_of_tendsto' h_LHS h_RHS (fun k => h_seq k π)

/-- **Theorem 4 (closure form)** at `n = 4`. `F_witness` is not the pointwise limit of any sequence of set functions in `tildeΓ_4` -- a strictly stronger statement than `theorem4`, since every four-variable entropy function lies in `tildeΓ_4` by `zhangYeungHolds_of_entropy`. Combined with the latter, this implies the paper's closure-version separation $\bar{\Gamma}^*_4 \ne \Gamma_4$ at $n = 4$ (modulo the formalization of $\Gamma^*_4$, which is out of scope for M4). Proved by closing `zhangYeungHolds` under pointwise limits via `zhangYeungHolds_of_tendsto`, then contradicting `not_zhangYeungHolds_witness`. -/
theorem theorem4_closure :
    ∃ F : Finset (Fin 4) → ℝ, shannonCone F ∧
      ∀ (F_seq : ℕ → Finset (Fin 4) → ℝ),
        (∀ k, zhangYeungHolds (F_seq k)) →
        (∀ α, Filter.Tendsto (fun k => F_seq k α) Filter.atTop (𝓝 (F α))) →
        False := by
  refine ⟨F_witness, shannonCone_of_witness, ?_⟩
  intro F_seq h_seq h_lim
  exact not_zhangYeungHolds_witness (zhangYeungHolds_of_tendsto h_seq h_lim)

/-! ### Optional stretch: `n ≥ 4` extension

`Fin 4`-generic analogues of the set-function calculus and cone predicates, plus the lift of `F_witness` along the canonical embedding `Fin 4 ↪ Fin n` via `Finset.preimage`. The `n ≥ 4` witness `F_witness_n` satisfies the Shannon cone (each cone axiom transports across `Finset.preimage`) but fails the Zhang-Yeung inequality at the lifted canonical labeling `(Fin.castLE hn 2, Fin.castLE hn 3, Fin.castLE hn 0, Fin.castLE hn 1)`, which after preimage-reduction collapses to the base `n = 4` violation. Together these give the paper's `n ≥ 4` separation `shannon_incomplete_ge_four`. -/

/-- `I_F` generalized to `Finset (Fin n)`. The `n = 4` specialization coincides with `I_F` by definitional unfolding. -/
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

/-- The Zhang-Yeung inequality at a 4-tuple labeling over `Fin n`. -/
def zhangYeungAt_n {n : ℕ} (F : Finset (Fin n) → ℝ) (i j k l : Fin n) : Prop :=
  delta_F_n F i j k l ≤ (1 / 2) * (I_F_n F {k} {l} + I_F_n F {k} ({i} ∪ {j})
    + condI_F_n F {i} {j} {k} - condI_F_n F {i} {j} {l})

/-- The `Fin n`-indexed Zhang-Yeung cone `tildeΓ_n`: the Zhang-Yeung inequality holds at every ordered 4-tuple of pairwise distinct indices. Equivalent to the card-4 form used in the paper's eq. (25); the pairwise-distinctness presentation is easier to manipulate in proofs. -/
def zhangYeungHolds_n {n : ℕ} (F : Finset (Fin n) → ℝ) : Prop :=
  ∀ i j k l : Fin n, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
    zhangYeungAt_n F i j k l

/-- The `n = 4` witness lifted to `Fin n` for `n ≥ 4`: `F_witness_n hn α` evaluates `F_witness` on the preimage of `α` under the canonical embedding `Fin 4 ↪ Fin n`. Equivalent to `F_witness` applied to the intersection of `α` with the initial segment `{0, 1, 2, 3 : Fin n}`. -/
noncomputable def F_witness_n {n : ℕ} (hn : 4 ≤ n) (α : Finset (Fin n)) : ℝ :=
  F_witness (α.preimage (Fin.castLE hn) (Fin.castLE_injective hn).injOn)

/-- The lifted witness lies in `Γ_n`: each Shannon-cone axiom transports across `Finset.preimage` via `preimage_empty`, `monotone_preimage`, `preimage_union`, and `preimage_inter`, and then reduces to the base `shannonCone_of_witness`. -/
theorem shannonCone_of_witness_n {n : ℕ} (hn : 4 ≤ n) :
    shannonCone_n (F_witness_n hn) := by
  refine ⟨?_, ?_, ?_⟩
  · show F_witness _ = 0
    rw [Finset.preimage_empty]
    exact shannonCone_of_witness.1
  · intro α β hαβ
    exact shannonCone_of_witness.2.1 _ _
      (Finset.monotone_preimage (Fin.castLE_injective hn) hαβ)
  · intro α β
    show F_witness _ + F_witness _ ≤ F_witness _ + F_witness _
    rw [Finset.preimage_union, Finset.preimage_inter]
    exact shannonCone_of_witness.2.2 _ _

/-- The preimage of a singleton `{Fin.castLE hn i}` under `Fin.castLE hn` is `{i}`. -/
private lemma preimage_singleton_castLE {n : ℕ} (hn : 4 ≤ n) (i : Fin 4) :
    ({Fin.castLE hn i} : Finset (Fin n)).preimage (Fin.castLE hn)
        (Fin.castLE_injective hn).injOn = ({i} : Finset (Fin 4)) := by
  ext j
  simp [Finset.mem_preimage, Finset.mem_singleton,
    (Fin.castLE_injective hn).eq_iff]

/-- The specific `n = 4` failure from which the lift reads off. Factored out of `not_zhangYeungHolds_witness` so the `Fin n` violation can consume it without re-running the permutation specialization. -/
private lemma not_zhangYeungAt_witness_canonical :
    ¬ zhangYeungAt F_witness 2 3 0 1 := by
  intro h
  simp only [zhangYeungAt, delta_F, I_F, condI_F, F_witness_eq_cast] at h
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

/-- The Zhang-Yeung inequality at the lifted canonical labeling pulls back to the base labeling: every set-function operation in `zhangYeungAt_n F_witness_n` reduces through `Finset.preimage` to the corresponding `zhangYeungAt F_witness` operation on `Fin 4`. -/
private lemma zhangYeungAt_n_witness_castLE {n : ℕ} (hn : 4 ≤ n) (i j k l : Fin 4) :
    zhangYeungAt_n (F_witness_n hn) (Fin.castLE hn i) (Fin.castLE hn j)
        (Fin.castLE hn k) (Fin.castLE hn l)
      ↔ zhangYeungAt F_witness i j k l := by
  unfold zhangYeungAt_n zhangYeungAt delta_F_n delta_F I_F_n I_F condI_F_n condI_F F_witness_n
  simp only [Finset.preimage_union, preimage_singleton_castLE]

/-- Part (b) lifted to `Fin n`: the lifted witness fails `zhangYeungHolds_n` at the lifted canonical labeling. -/
theorem not_zhangYeungHolds_witness_n {n : ℕ} (hn : 4 ≤ n) :
    ¬ zhangYeungHolds_n (F_witness_n hn) := by
  intro h
  have inj := Fin.castLE_injective hn
  have d23 : (Fin.castLE hn 2 : Fin n) ≠ Fin.castLE hn 3 :=
    fun e => absurd (inj e) (by decide)
  have d20 : (Fin.castLE hn 2 : Fin n) ≠ Fin.castLE hn 0 :=
    fun e => absurd (inj e) (by decide)
  have d21 : (Fin.castLE hn 2 : Fin n) ≠ Fin.castLE hn 1 :=
    fun e => absurd (inj e) (by decide)
  have d30 : (Fin.castLE hn 3 : Fin n) ≠ Fin.castLE hn 0 :=
    fun e => absurd (inj e) (by decide)
  have d31 : (Fin.castLE hn 3 : Fin n) ≠ Fin.castLE hn 1 :=
    fun e => absurd (inj e) (by decide)
  have d01 : (Fin.castLE hn 0 : Fin n) ≠ Fin.castLE hn 1 :=
    fun e => absurd (inj e) (by decide)
  have hat := h (Fin.castLE hn 2) (Fin.castLE hn 3) (Fin.castLE hn 0) (Fin.castLE hn 1)
    d23 d20 d21 d30 d31 d01
  exact not_zhangYeungAt_witness_canonical ((zhangYeungAt_n_witness_castLE hn 2 3 0 1).mp hat)

/-- **Theorem 4 for `n ≥ 4`** [@zhangyeung1998, §II, eq. 26]. The lifted witness separates `Γ_n` from the `Fin n`-indexed Zhang-Yeung cone: there exists a set function on `Finset (Fin n)` satisfying the three Shannon-cone axioms but violating the Zhang-Yeung inequality at the lifted canonical labeling. -/
theorem shannon_incomplete_ge_four (n : ℕ) (hn : 4 ≤ n) :
    ∃ F : Finset (Fin n) → ℝ, shannonCone_n F ∧ ¬ zhangYeungHolds_n F :=
  ⟨F_witness_n hn, shannonCone_of_witness_n hn, not_zhangYeungHolds_witness_n hn⟩

end ZhangYeung
