---
title: "M4: Theorem 4, Shannon incompleteness (Zhang-Yeung 1998, §II, Theorem 4 / eq. 26)"
created: 2026-04-18
branch: formalize/m4-theorem-4
roadmap: docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md
milestone: M4
depends_on: M3 (`ZhangYeung/Theorem3.lean`, merged into `main` via PR #9). M2 (`ZhangYeung/CopyLemma.lean`), M1.5 (`ZhangYeung/Theorem2.lean`), and M1 (`ZhangYeung/Delta.lean`) are also all on `main`. The worktree `m4-theorem-4` is branched from the tip of `main`; the branch has a clean `make check` as the starting state.
---

## Context

Milestone M4 of the Zhang-Yeung roadmap (§6) formalizes **Theorem 4** of the 1998 paper: the Shannon outer bound $\Gamma_n$ strictly contains the set of entropic functions for $n \ge 4$. This is the "Shannon is incomplete" corollary of the Zhang-Yeung inequality — the scientific payoff of the Zhang-Yeung inequality itself, and the first known proof that Shannon's basic information inequalities do not fully characterize the entropy function.

M4's full content is four parts:

- **Part (a):** Construct an explicit set function $F \in \Gamma_4$ (the witness from paper lines 368-377).
- **Part (b):** Show $F$ violates the Zhang-Yeung inequality at the canonical labeling $(Z, U \mid X, Y) = (2, 3 \mid 0, 1)$, hence $F \notin \tilde{\Gamma}_4$.
- **Part (c) (uses M3):** Bridge the M3 `zhangYeung` theorem to the set-function level, proving that the entropy function of any four discrete random variables lies in $\tilde{\Gamma}_4$.
- **Part (d):** Close the proof of Theorem 4 by combining (a) + (b) + (c): $F$ lies in $\Gamma_4$ but is not the entropy function of any four discrete random variables. This is the headline `theorem4`.

Parts (a) and (b) are pure set-function arithmetic over `Finset (Fin 4)`; no measure theory needed. Parts (c) and (d) close over M3 at the measure-theoretic level; (c) is the new measure-theoretic content of M4 and (d) is a contradiction argument.

**Primary reference:** `references/transcriptions/zhangyeung1998.md` (verified 2026-04-16). The Theorem 4 statement and proof are on lines 358-388; the witness definition is on lines 368-377; $\tilde{\Gamma}_4$ is defined via paper eq. (25) on lines 339-355.

The paper's Theorem 4 statement (line 358):

> For $n \ge 4$,
> $$
> \bar{\Gamma}^*_n \neq \Gamma_n. \tag{26}
> $$

The paper's proof in prose (paraphrased from lines 366-388): it suffices to handle $n = 4$, because any separation witness for $n = 4$ lifts to any $n \ge 4$ by an embedding argument. For $n = 4$, define the set function $F: 2^{\{X, Y, Z, U\}} \to \mathbb{R}$ by

$$
\begin{aligned}
F(\phi) &= 0, \\
F(X) &= F(Y) = F(Z) = F(U) = 2a, \\
F(X, Y) &= 4a, \\
F(X, Z) = F(X, U) = F(Y, Z) &= F(Y, U) = F(Z, U) = 3a, \\
F(X, Y, Z) = F(X, Y, U) = F(X, Z, U) &= F(Y, Z, U) = F(X, Y, Z, U) = 4a,
\end{aligned}
$$

for any fixed $a > 0$. Then $F \in \Gamma_4$ (Shannon basic inequalities hold) and $F \notin \tilde{\Gamma}_4$ (Zhang-Yeung inequality fails for some permutation of the four variables). Since M3's Theorem 3 establishes $\bar{\Gamma}^*_4 \subseteq \tilde{\Gamma}_4$, this witness lies in $\Gamma_4 \setminus \bar{\Gamma}^*_4$, proving (26) for $n = 4$.

### Why M4 lands now

1. **M3 is on `main`.** The `zhangYeung` theorem (paper eq. 21) and its two partners (`zhangYeung_dual` eq. 22, `zhangYeung_averaged` eq. 23) landed in PR #9. M3 is the measure-theoretic black box Part (c) closes over.
1. **Parts (a) and (b) are fully independent of M3.** M4's combinatorial core (the witness, the Shannon cone check, the Zhang-Yeung violation) runs through set-function arithmetic on the 16 subsets of `Fin 4`. This is the cleanest "pure Lean" work in the project so far; it is `decide`-closable over `ℚ` with no measure theory surface.
1. **Part (c) (the bridge) is mechanical but not trivial.** The bridge formalizes the *set-function form* of M3's conclusion. It does not strengthen or weaken M3; it only restates M3's inequality in the `entropyFn`-flavored language that Part (d) consumes. The technical cost is a per-subset identity `entropyFn X μ α = H[<joint RV>; μ]`, multiplied across the ~12 subsets that appear inside a single `zhangYeungAt` invocation. We budget ~80-150 lines for the bridge.
1. **Part (d) is a two-line contradiction once (a)-(c) are in place.** `theorem4` follows from `not_zhangYeungHolds_witness` + `zhangYeungHolds_of_entropy` by `intro` + `exact`.

### What M4 does not do

- **Theorem 5 (n+2-variable generalization).** Roadmap §M5. Picks up after M4 lands.
- **Theorem 6 (inner bound on $\bar{\Gamma}^*_4$).** Deliberately excluded from S2 per roadmap §4. Revisit post-release.
- **Exact identity form with explicit slack $R$** (paper p. 1446, post-release extension #2). Out of scope.
- **Copy-lemma upstreaming to Mathlib** (post-release extension #1). Out of scope.
- **Closure version of Theorem 4** ($\bar{\Gamma}^*_4 \neq \Gamma_4$ via sequential closure of $\Gamma^*_4$). M4's *required* conclusion is the finite version: $F$ is not the entropy function of *any* four discrete random variables. The closure version upgrades "not an entropy function" to "not a pointwise limit of entropy functions"; this requires a single additional lemma ("`zhangYeungHolds` is closed under pointwise limits") and a topological setup that is trivially met by the finite product topology on `Finset (Fin 4) → ℝ`. M4 lands the closure version as an **optional stretch theorem** `theorem4_closure`; if it slips, it becomes a post-M4 follow-up. Neither the required `theorem4` nor the stretch `theorem4_closure` requires formalizing $\Gamma^*_4$ or $\bar{\Gamma}^*_4$ as named subsets of `Finset (Fin 4) → ℝ`; both state the separation directly.
- **n ≥ 4 extension.** The paper's Theorem 4 is for $n \ge 4$. M4's core delivers the $n = 4$ case; the $n \ge 4$ extension via the embedding `Fin 4 ↪ Fin n` is optional stretch. If it slips, it becomes a one-commit follow-up.

## Paper proof (transcription, lines 358-388)

Define $F: 2^{\{X, Y, Z, U\}} \to \mathbb{R}$ by the value table above (any $a > 0$). Theorem 4 is proved by two claims:

**Claim 1: $F \in \Gamma_4$.** The paper asserts this without proof; it is a direct check of the three Shannon-cone axioms (paper eq. 11): $F(\emptyset) = 0$, monotonicity, and submodularity. Each reduces to explicit `2a`, `3a`, `4a` arithmetic comparisons on the 16 subsets of `Fin 4`. In our Lean setup we discharge the three conditions directly by `decide` over a `ℚ`-valued witness.

**Claim 2: $F \notin \tilde{\Gamma}_4$.** Check the Zhang-Yeung inequality (eq. 21) at the canonical labeling $(Z, U, X, Y) = (2, 3, 0, 1)$ (the paper's X, Y, Z, U in Lean's `Fin 4`: X=0, Y=1, Z=2, U=3). All inputs are finite:

$$
\begin{aligned}
\Delta_F(2, 3 \mid 0, 1) &= I_F(2; 3) - I_F(2; 3 \mid 0) - I_F(2; 3 \mid 1) \\
&= (F(2) + F(3) - F(\{2, 3\})) - (F(\{0, 2\}) + F(\{0, 3\}) - F(\{0, 2, 3\}) - F(0)) \\
&\quad - (F(\{1, 2\}) + F(\{1, 3\}) - F(\{1, 2, 3\}) - F(1)) \\
&= (2a + 2a - 3a) - (3a + 3a - 4a - 2a) - (3a + 3a - 4a - 2a) \\
&= a - 0 - 0 = a.
\end{aligned}
$$

$$
\begin{aligned}
\tfrac{1}{2} \bigl[ I_F(0; 1) + I_F(0; \{2, 3\}) + I_F(2; 3 \mid 0) - I_F(2; 3 \mid 1) \bigr]
&= \tfrac{1}{2} (0 + a + 0 - 0) = \tfrac{a}{2}.
\end{aligned}
$$

For $a > 0$, $a \le a/2$ is false, so $F$ violates the Zhang-Yeung inequality at this specific labeling.

**The remaining link is the bridge.** Claims 1 and 2 establish $F \in \Gamma_4 \setminus \tilde{\Gamma}_4$. To upgrade this to $F \in \Gamma_4 \setminus (\text{entropy functions})$ -- the actual content of Theorem 4 -- we need:

**Bridge claim (paper's application of Theorem 3):** for any four discrete random variables $X_0, X_1, X_2, X_3$, their entropy function $F_{\Omega} : \alpha \mapsto H[X_\alpha]$ lies in $\tilde{\Gamma}_4$.

The paper treats this as a direct restatement of Theorem 3 (the Zhang-Yeung inequality). In Lean this is a per-permutation application of M3's `zhangYeung`, wrapped into the set-function `zhangYeungAt` predicate by unfolding the latter into joint-entropy terms. This is the measure-theoretic content of M4.

**Theorem 4 finite form (required):** combining Claims 1-2 with the bridge, $F_{\text{witness}} \in \Gamma_4$ but $F_{\text{witness}} \notin \{F_\Omega : \Omega \text{ is a set of four discrete RVs}\}$.

**Theorem 4 closure form (optional stretch):** $F_{\text{witness}}$ is not a pointwise limit of entropy functions either, because $\tilde{\Gamma}_4$ is closed under pointwise limits (a finite conjunction of $\le$-inequalities on continuous coordinate functionals). Hence $F_{\text{witness}} \notin \bar{\Gamma}^*_4$, which is exactly Theorem 4 for $n = 4$. For $n > 4$, extend $F_{\text{witness}}$ to $F_n(\alpha) := F_{\text{witness}}(\alpha \cap \{0, 1, 2, 3\})$.

## Prerequisites

M1 delivered (merged into `main` via PR #4):

- `ZhangYeung/Delta.lean` with `ZhangYeung.delta : (Ω → S₁) → (Ω → S₂) → (Ω → S₃) → (Ω → S₄) → Measure Ω → ℝ` and form-conversion lemmas.

M2 delivered (merged into `main` via PR #8):

- `ZhangYeung/CopyLemma.lean` with the copy construction and the two `copyLemma_delta_le_mutualInfo_*` inequalities.

M3 delivered (merged into `main` via PR #9):

- `ZhangYeung/Theorem3.lean` with three public theorems:
  - `zhangYeung : delta Z U X Y μ ≤ (1/2) * (I[X:Y; μ] + I[X:⟨Z,U⟩; μ] + I[Z:U|X; μ] - I[Z:U|Y; μ])` (eq. 21).
  - `zhangYeung_dual` (eq. 22).
  - `zhangYeung_averaged` (eq. 23).

M4 consumes `zhangYeung` as a black-box theorem applied at each of the 24 permutations of `Fin 4`. `zhangYeung_dual` and `zhangYeung_averaged` are not needed: every permutation-labeled instance of `zhangYeungAt` is the eq. (21) shape after matching indices, so a single `zhangYeung` application per permutation suffices.

Before starting M4, in the `m4-theorem-4` worktree: `bin/bootstrap-worktree`, then `make check`. Confirm the tip is green with M1 + M1.5 + M2 + M3 in place and `lake env lean --version` reports the pinned Lean toolchain.

## Design: set-function coordinates and the entropy-function bridge

M4 introduces two new kinds of object relative to M1-M3:

1. **Set functions** $F : 2^{\mathcal{N}_4} \to \mathbb{R}$. Lean encoding: `Finset (Fin 4) → ℝ` (or `Finset (Fin 4) → ℚ` for the witness). Used by Parts (a) + (b).
1. **Set-function view of an entropy function.** Given RVs $X_0, X_1, X_2, X_3$, the entropy function $\alpha \mapsto H[X_\alpha]$ packaged as a `Finset (Fin 4) → ℝ`. This is the object the bridge (Part (c)) rewrites against M3's conclusion.

### Why `Finset (Fin 4)` and not `Set (Fin 4)` or `ℕ`-bitmasks?

- `Finset (Fin 4)` is a `Fintype`; `Fintype.decidableForallFintype` closes Parts (a) + (b)'s `decide` calls for free.
- `Finset.decidableEq`, `Finset.decidableSubset`, `Finset.decidableMem` are all automatic.
- The literal syntax `{0, 1, 2} : Finset (Fin 4)` elaborates to `insert 0 (insert 1 (insert 2 ∅))` and reduces by `decide` on concrete literals.
- `Set (Fin 4)` would lose the `Fintype` and decidability story; bitmasks would hide the mathematical structure. `Finset` is the right fit.

### Working over `ℚ` vs `ℝ`

The witness values are integer-valued (at $a = 1$: $\{0, 2, 3, 4\}$); the Shannon cone and Zhang-Yeung inequalities both mention only rationals on the right-hand side. We will:

1. Define the witness $F_{\text{witness}_\mathbb{Q}} : \text{Finset (Fin 4)} \to \mathbb{Q}$ so that `decide` closes Parts (a) + (b) via `Fintype.decidableForallFintype` + `DecidableEq (Finset (Fin 4))` + `Decidable ((a : ℚ) ≤ b)`.
1. Cast to $\mathbb{R}$ at the statement level of `shannon_incomplete` and `theorem4`: each theorem supplies `(↑) ∘ F_{\text{witness}_\mathbb{Q}}` (i.e. the `ℚ`-valued witness cast pointwise into `ℝ`).
1. Parts (c) + (d) live in `ℝ` (to match PFR's entropy return type); the cast is inserted once at the witness boundary.

### Why `a = 1` (not parametrized)?

The paper phrases the witness parametrically in $a > 0$ for two reasons: (1) to make the homogeneity of the Shannon cone manifest (every conclusion scales linearly in $a$), (2) to make the witness unambiguous about signs. Neither reason applies in Lean: (1) is vacuous since `shannon_incomplete` and `theorem4` only assert *existence*, and (2) is discharged by the type `ℚ` (no sign ambiguity). Fixing $a = 1$ shrinks the proof and avoids threading `(ha : 0 < a)` through every lemma.

### Set-function calculus

M4 needs a small set-function calculus mirroring the random-variable-level entropy calculus of M1-M3. The minimum API:

```lean
/-- `I_F(α; β) := F(α) + F(β) - F(α ∪ β)`. When `F` is the entropy function of a
set of random variables, `I_F(α; β) = I(X_α; X_β)` (assuming `F(∅) = 0`). -/
def I_F (F : Finset (Fin 4) → ℝ) (α β : Finset (Fin 4)) : ℝ :=
  F α + F β - F (α ∪ β)

/-- `I_F(α; β | γ) := F(α ∪ γ) + F(β ∪ γ) - F(α ∪ β ∪ γ) - F(γ)`. -/
def condI_F (F : Finset (Fin 4) → ℝ) (α β γ : Finset (Fin 4)) : ℝ :=
  F (α ∪ γ) + F (β ∪ γ) - F (α ∪ β ∪ γ) - F γ

/-- `Δ_F(i, j | k, l) := I_F({i}; {j}) - I_F({i}; {j} | {k}) - I_F({i}; {j} | {l})`. -/
def delta_F (F : Finset (Fin 4) → ℝ) (i j k l : Fin 4) : ℝ :=
  I_F F {i} {j} - condI_F F {i} {j} {k} - condI_F F {i} {j} {l}
```

`I_F` above is the *unconditional* mutual information. It coincides with Shannon's $I(\alpha; \beta) = F(\alpha) + F(\beta) - F(\alpha \cup \beta) - F(\emptyset)$ whenever $F(\emptyset) = 0$, the first Shannon-cone axiom, so the distinction is vacuous inside $\Gamma_4$. We do not include the `γ` argument with a default of `∅` in `I_F`; callers choose between `I_F` and `condI_F`.

The Shannon cone and Zhang-Yeung predicates:

```lean
/-- `Γ_4` from Zhang-Yeung 1998 eq. (11): F is in the Shannon cone iff it is
zero on the empty set, monotone under subset inclusion, and submodular. -/
def shannonCone (F : Finset (Fin 4) → ℝ) : Prop :=
  F ∅ = 0 ∧
  (∀ α β : Finset (Fin 4), α ⊆ β → F α ≤ F β) ∧
  (∀ α β : Finset (Fin 4), F (α ∪ β) + F (α ∩ β) ≤ F α + F β)

/-- Zhang-Yeung inequality at a specific 4-tuple labeling, paper eq. (21):
`Δ_F(i, j | k, l) ≤ (1/2)(I_F(k; l) + I_F(k; {i, j}) + I_F(i; j | k) - I_F(i; j | l))`. -/
def zhangYeungAt (F : Finset (Fin 4) → ℝ) (i j k l : Fin 4) : Prop :=
  delta_F F i j k l ≤ (1/2) * (I_F F {k} {l} + I_F F {k} ({i} ∪ {j})
    + condI_F F {i} {j} {k} - condI_F F {i} {j} {l})

/-- `F` is in `tildeΓ_4`: the Zhang-Yeung inequality holds at every labeling
by a permutation of `{0, 1, 2, 3}`. (Paper eq. 25.) -/
def zhangYeungHolds (F : Finset (Fin 4) → ℝ) : Prop :=
  ∀ π : Equiv.Perm (Fin 4), zhangYeungAt F (π 0) (π 1) (π 2) (π 3)
```

Quantifying over `Equiv.Perm (Fin 4)` matches paper eq. (25) literally: the permutation variable `π` in the paper is exactly `Equiv.Perm`. For the violation proof we supply the specific permutation `σ = Equiv.swap 0 2 * Equiv.swap 1 3` (sending `0 ↦ 2, 1 ↦ 3, 2 ↦ 0, 3 ↦ 1`), which instantiates `zhangYeungAt F (σ 0) (σ 1) (σ 2) (σ 3)` as `zhangYeungAt F 2 3 0 1`.

### Entropy function as a set function

Given a family of random variables `X : Fin 4 → Ω → S` (a common codomain `S` for all four, discrete and finite-alphabet per M3's signature), define their entropy function on `Finset (Fin 4)`:

```lean
/-- The entropy function of a four-variable family: for `α : Finset (Fin 4)`,
`entropyFn X μ α` is the joint entropy `H[X_α ; μ]` where `X_α` is the tuple
indexed by the elements of `α`. -/
noncomputable def entropyFn
    {Ω : Type u} [MeasurableSpace Ω]
    {S : Type u} [MeasurableSpace S] [Fintype S] [MeasurableSingletonClass S]
    (X : Fin 4 → Ω → S) (μ : Measure Ω) : Finset (Fin 4) → ℝ :=
  fun α => H[(fun ω : Ω => fun i : α => X i.val ω) ; μ]
```

The type `{i : Fin 4 // i ∈ α}` is finite (a subtype of the finite `Fin 4`), so the joint `α → S` is a finite product, and PFR's `H[·; μ]` applies.

For the bridge (Part (c)) we need a collection of evaluation lemmas matching `entropyFn X μ α` to named joint entropies in PFR's pair/triple/tuple notation:

```lean
lemma entropyFn_empty : entropyFn X μ ∅ = 0
lemma entropyFn_singleton (i : Fin 4) : entropyFn X μ {i} = H[X i ; μ]
lemma entropyFn_pair {i j : Fin 4} (h : i ≠ j) :
    entropyFn X μ {i, j} = H[⟨X i, X j⟩ ; μ]
lemma entropyFn_triple {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    entropyFn X μ {i, j, k} = H[⟨X i, ⟨X j, X k⟩⟩ ; μ]
lemma entropyFn_quad :
    entropyFn X μ ({0, 1, 2, 3} : Finset (Fin 4))
      = H[⟨X 0, ⟨X 1, ⟨X 2, X 3⟩⟩⟩ ; μ]
```

Each of these is an entropy-of-tuple identity obtained by transporting across an `Equiv` between the subtype `{i // i ∈ α}` and the standard `Fin α.card`. PFR exposes `IdentDistrib.entropy_eq` and Mathlib's `entropy_comp_of_injective` for this transport. The pair version also uses `entropy_comm` to absorb the two possible orderings of `{i, j}`.

For the bridge (Part (c)), the per-subset lemmas feed into a single permutation-indexed identity:

```lean
lemma zhangYeungAt_entropyFn (π : Equiv.Perm (Fin 4)) :
    zhangYeungAt (entropyFn X μ) (π 0) (π 1) (π 2) (π 3)
```

proved by:

1. Unfold `zhangYeungAt` into `delta_F` and the RHS.
1. Unfold `delta_F`, `I_F`, `condI_F` into `entropyFn` evaluations.
1. Apply the per-subset bridge lemmas to rewrite each `entropyFn` evaluation as a joint entropy in PFR's pair/triple notation.
1. Recognize the LHS as `delta (X (π 0)) (X (π 1)) (X (π 2)) (X (π 3)) μ` and the RHS as M3's RHS with the same labeling.
1. Close by `zhangYeung` applied at that labeling (M3's headline theorem).

Budget ~30-60 tactic lines for the permutation-indexed bridge after the per-subset lemmas land. The per-subset lemmas are each ~5-10 tactic lines; there are 5-10 such lemmas depending on how aggressively we collapse across `Finset.insert` ordering permutations.

## PFR and Mathlib API surface used

All declarations live under `namespace ProbabilityTheory` unless noted.

**From the current project (consumed by the bridge):**

- `ZhangYeung.zhangYeung` (M3) -- applied 24 times (once per `Equiv.Perm (Fin 4)`). Every permutation yields a paper eq. (21) shape; after unfolding the set-function calculus, the RHS matches exactly.
- `ZhangYeung.delta`, `ZhangYeung.delta_def` (M1) -- used by the bridge to equate `delta_F (entropyFn X μ) (π 0) (π 1) (π 2) (π 3)` with `delta (X (π 0)) (X (π 1)) (X (π 2)) (X (π 3)) μ` (after subsets unfold into joint entropies).

**From PFR (for the bridge's per-subset lemmas):**

- `ProbabilityTheory.entropy`, `mutualInfo`, `condMutualInfo` -- already in the M1-M3 import surface via `ZhangYeung.Prelude`. Wrapped by the `H[_; _]`, `I[_:_; _]`, `I[_:_|_; _]` notation.
- `mutualInfo_def`, `condMutualInfo_eq` -- to translate `I_F` and `condI_F` into entropy sums.
- `entropy_comm : H[⟨X, Y⟩; μ] = H[⟨Y, X⟩; μ]` -- for the pair ordering in `entropyFn_pair`.
- `entropy_comp_of_injective : Function.Injective f → H[f ∘ X; μ] = H[X; μ]` -- the transport tool for the per-subset lemmas. Given an equivalence `({i, j} : Finset (Fin 4)) ≃ Fin 2` (say), we compose with the underlying function and invoke this lemma.
- `IdentDistrib.entropy_eq` -- an alternative transport, if `entropy_comp_of_injective` is awkward. Used in M3's proof of `mutualInfo_le_of_condIndepFun`; same pattern applies here.

**From Mathlib (set-function calculus and decidability):**

- `Finset.decidableEq`, `Finset.decidableMem`, `Finset.decidableBEx`, `Finset.decidableBAll` -- decidability of set predicates on concrete `Finset`s; drive `decide` closure for Parts (a) + (b).
- `Fintype.decidableForallFintype` -- closes `∀ α : Finset (Fin 4), ...` for decidable `P α`.
- `Finset.union`, `Finset.inter`, `Finset.subset_iff`, `Finset.Singleton` (literal `{x}`), `Finset.insert` -- the primitive set operations consumed by `I_F`, `condI_F`, `delta_F`.
- `Finset.card_empty`, `Finset.card_singleton`, `Finset.card_insert_of_not_mem` -- unfold cardinality on concrete literals.
- `Rat.cast_le`, `Rat.cast_lt`, `Rat.cast_add`, `Rat.cast_mul` -- push the `ℚ`-valued witness through to `ℝ`.
- `Equiv.Perm (Fin 4)`, `Equiv.swap`, `Equiv.Perm.mul_apply` -- permutation handling in `zhangYeungHolds` and the violation proof.
- `Fintype (α → S)` for `α : Finset (Fin 4)` (via `Finset.Fintype.coeSort` + `Pi.fintype`) -- required for `entropyFn` to elaborate.
- `MeasurableSpace.pi`, measurability of coordinate projections -- required for `Measurable (fun ω => fun i : α => X i.val ω)`.

**For the optional `theorem4_closure` (stretch):**

- `Filter.Tendsto`, `Filter.atTop` on `ℕ` -- pointwise convergence of sequences of set functions.
- `Filter.Tendsto.le_of_le`, `Filter.Tendsto.add`, `Filter.Tendsto.mul` -- preservation of $\le$ under pointwise limits.

**For the optional `n ≥ 4` extension:**

- `Fin.castLEEmb : n ≤ m → Fin n ↪ Fin m` -- canonical order-preserving embedding.
- `Finset.preimage`, `Finset.image` -- lift the witness along the embedding.

Nothing in Mathlib currently packages $\Gamma_n$ or the submodular cone over `Finset (Fin n) → ℝ`. M4 introduces `shannonCone`, `zhangYeungAt`, `zhangYeungHolds`, `entropyFn` locally under `namespace ZhangYeung`; later projects may upstream.

## The M4 theorems

M4's public API consists of six definitions and five theorems, in dependency order:

### Predicates (definitions)

```lean
def I_F (F : Finset (Fin 4) → ℝ) (α β : Finset (Fin 4)) : ℝ := ...
def condI_F (F : Finset (Fin 4) → ℝ) (α β γ : Finset (Fin 4)) : ℝ := ...
def delta_F (F : Finset (Fin 4) → ℝ) (i j k l : Fin 4) : ℝ := ...
def shannonCone (F : Finset (Fin 4) → ℝ) : Prop := ...
def zhangYeungAt (F : Finset (Fin 4) → ℝ) (i j k l : Fin 4) : Prop := ...
def zhangYeungHolds (F : Finset (Fin 4) → ℝ) : Prop := ...
```

### Witness (definitions)

```lean
def F_witness_ℚ : Finset (Fin 4) → ℚ := fun S =>
  if S.card = 0 then 0
  else if S.card = 1 then 2
  else if S = {0, 1} then 4
  else if S.card = 2 then 3
  else 4

noncomputable def F_witness : Finset (Fin 4) → ℝ := fun S => (F_witness_ℚ S : ℝ)
```

### Part (a): Shannon cone membership

```lean
theorem shannonCone_of_witness : shannonCone F_witness
```

Proof: three clauses (`F_witness ∅ = 0`, monotone, submodular), each closed by `decide` at the `ℚ` layer + `exact_mod_cast`. Budget ~10-15 tactic lines.

### Part (b): Zhang-Yeung violation

```lean
theorem not_zhangYeungHolds_witness : ¬ zhangYeungHolds F_witness
```

Proof: specialize `zhangYeungHolds` at the permutation `σ = Equiv.swap 0 2 * Equiv.swap 1 3`, which yields `zhangYeungAt F_witness 2 3 0 1`. Unfold and evaluate to `1 ≤ 1/2`, which is false. Budget ~15-20 tactic lines.

### Intermediate: Shannon cone ⊋ Zhang-Yeung cone

```lean
theorem shannon_incomplete :
    ∃ F : Finset (Fin 4) → ℝ, shannonCone F ∧ ¬ zhangYeungHolds F := by
  exact ⟨F_witness, shannonCone_of_witness, not_zhangYeungHolds_witness⟩
```

Three-line proof combining Parts (a) and (b). This was the original roadmap checkpoint; M4 retains it as an intermediate theorem, but the *headline* is `theorem4` below.

### Part (c): bridge from M3 to the set-function level

**Per-subset bridge lemmas:**

```lean
section EntropyFnEvaluation
variable {Ω : Type u} [MeasurableSpace Ω] {S : Type u}
  [MeasurableSpace S] [Fintype S] [MeasurableSingletonClass S]
  (X : Fin 4 → Ω → S) (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma entropyFn_empty : entropyFn X μ ∅ = 0
lemma entropyFn_singleton (i : Fin 4) : entropyFn X μ {i} = H[X i ; μ]
lemma entropyFn_pair {i j : Fin 4} (h : i ≠ j) :
    entropyFn X μ {i, j} = H[⟨X i, X j⟩ ; μ]
lemma entropyFn_triple {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    entropyFn X μ {i, j, k} = H[⟨X i, ⟨X j, X k⟩⟩ ; μ]
lemma entropyFn_quad :
    entropyFn X μ ({0, 1, 2, 3} : Finset (Fin 4))
      = H[⟨X 0, ⟨X 1, ⟨X 2, X 3⟩⟩⟩ ; μ]

end EntropyFnEvaluation
```

Each `entropyFn_*` lemma is proved by transporting `H` across an `Equiv`:

- For `entropyFn_singleton`: the subtype `{i // i ∈ ({i} : Finset (Fin 4))}` is equivalent to `Unit`, and the joint `Unit → S` is `S` (up to an `Equiv`).
- For `entropyFn_pair`: `{j // j ∈ ({i, k} : Finset (Fin 4))} ≃ Fin 2` for `i ≠ k`.
- Similarly for triples and the 4-set.

The transport invokes `entropy_comp_of_injective` with an explicit `Equiv`. Budget ~5-10 tactic lines per lemma.

**Permutation-indexed bridge:**

```lean
lemma zhangYeungAt_entropyFn (π : Equiv.Perm (Fin 4)) :
    zhangYeungAt (entropyFn X μ) (π 0) (π 1) (π 2) (π 3) := by
  -- Denote Z := X (π 0), U := X (π 1), X_mid := X (π 2), Y := X (π 3).
  -- Unfold zhangYeungAt into F-evaluations.
  -- Rewrite each F-evaluation using entropyFn_* (accounting for permutation
  -- distinctness, which follows from `π.injective`).
  -- Recognize the LHS as `delta Z U X_mid Y μ` and the RHS as M3's RHS.
  -- Close by `ZhangYeung.zhangYeung hZ hU hX_mid hY μ`.
  sorry
```

Proof route: unfold, rewrite with the per-subset lemmas, pattern-match against M3. Budget ~30-50 tactic lines.

**Full bridge:**

```lean
theorem zhangYeungHolds_of_entropy :
    zhangYeungHolds (entropyFn X μ) := fun π => zhangYeungAt_entropyFn X μ π
```

One-line wrapper.

### Part (d): Theorem 4 (headline)

```lean
/-- **Theorem 4 of Zhang-Yeung 1998** [@zhangyeung1998, §II, eq. 26, at n = 4].
The Shannon outer bound Γ_4 strictly contains the set of entropy functions of
four discrete random variables: there exists a set function F in Γ_4 that is
not the entropy function of any four discrete random variables on any
probability space. -/
theorem theorem4 :
    ∃ F : Finset (Fin 4) → ℝ,
      shannonCone F ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        {S : Type u} [MeasurableSpace S] [Fintype S] [MeasurableSingletonClass S]
        (X : Fin 4 → Ω → S) (_ : ∀ i, Measurable (X i)),
        F ≠ entropyFn X μ := by
  refine ⟨F_witness, shannonCone_of_witness, ?_⟩
  intro Ω _ μ _ S _ _ _ X hX heq
  apply not_zhangYeungHolds_witness
  rw [heq]
  exact zhangYeungHolds_of_entropy X μ
```

Proof: combine `shannonCone_of_witness` + `not_zhangYeungHolds_witness` + `zhangYeungHolds_of_entropy` by contradiction. Five-line proof.

### Optional stretch: closure version

```lean
/-- **Theorem 4 (closure form)** [@zhangyeung1998, §II, eq. 26]. F_witness is not
even a pointwise limit of entropy functions. -/
theorem theorem4_closure :
    ∃ F : Finset (Fin 4) → ℝ,
      shannonCone F ∧
      ∀ (X_seq : ℕ → (Σ' (Ω : Type u) (_ : MeasurableSpace Ω) (_ : Measure Ω)
            (_ : IsProbabilityMeasure _) (S : Type u) (_ : MeasurableSpace S)
            (_ : Fintype S) (_ : MeasurableSingletonClass S),
            Fin 4 → Ω → S)),
        ¬ (∀ α : Finset (Fin 4),
             Filter.Tendsto (fun k => entropyFn (X_seq k).snd...snd α) ...)
```

The signature above is a sketch; the `Σ'`-heavy form pulls in too much existentiality. A cleaner form:

```lean
theorem theorem4_closure :
    ∃ F : Finset (Fin 4) → ℝ, shannonCone F ∧
      ∀ (F_seq : ℕ → Finset (Fin 4) → ℝ),
        (∀ k, zhangYeungHolds (F_seq k)) →
        (∀ α, Filter.Tendsto (fun k => F_seq k α) Filter.atTop (𝓝 (F α))) →
        False
```

This version states: F_witness is not the pointwise limit of any sequence of set functions in $\tilde{\Gamma}_4$ -- which, via `zhangYeungHolds_of_entropy`, implies it is not the pointwise limit of entropy functions. Proof: zhangYeungHolds is a finite conjunction of $\le$-inequalities, each preserved under pointwise limits; so the limit F satisfies zhangYeungHolds, contradicting `not_zhangYeungHolds_witness`. Budget ~15-30 tactic lines.

### Optional stretch: n ≥ 4 extension

```lean
theorem shannon_incomplete_ge_four (n : ℕ) (hn : 4 ≤ n) :
    ∃ F : Finset (Fin n) → ℝ, shannonCone_n n F ∧ ¬ zhangYeungHolds_n n F
```

where `shannonCone_n` and `zhangYeungHolds_n` are the `Fin n`-indexed analogues. Proof: lift F_witness along `Fin.castLEEmb hn`. Budget ~20-40 tactic lines (most of it is the `Fin 4 ↪ Fin n` bookkeeping).

## File layout

```text
ZhangYeung/
  Prelude.lean              # unchanged (M1-M3)
  Delta.lean                # unchanged (M1)
  Theorem2.lean             # unchanged (M1.5)
  CopyLemma.lean            # unchanged (M2)
  Theorem3.lean             # unchanged (M3)
  Theorem4.lean             # NEW: this milestone
ZhangYeung.lean             # add `import ZhangYeung.Theorem4`
ZhangYeungTest/
  Delta.lean                # unchanged (M1)
  Theorem2.lean             # unchanged (M1.5)
  CopyLemma.lean            # unchanged (M2)
  Theorem3.lean             # unchanged (M3)
  Theorem4.lean             # NEW: this milestone
ZhangYeungTest.lean         # add `import ZhangYeungTest.Theorem4`
AGENTS.md (aka CLAUDE.md)   # extend `## Module Layout` with two lines
```

**Contingency:** if Part (c)'s bridge work exceeds ~200 lines in `ZhangYeung/Theorem4.lean`, factor the `entropyFn` definition and the per-subset bridge lemmas into a new file `ZhangYeung/EntropyFunction.lean`, which is imported from `Theorem4.lean`. Leave the `zhangYeungAt_entropyFn` (permutation-indexed bridge) and `zhangYeungHolds_of_entropy` in `Theorem4.lean`. Decision gate: trigger the split only if the final `Theorem4.lean` would otherwise exceed ~400 lines. Do not pre-emptively split.

### Section structure inside `ZhangYeung/Theorem4.lean`

```text
├── Module docstring (## Main definitions, ## Main statements, ## Implementation notes, ## References, ## Tags)
├── Imports: ZhangYeung.Theorem3 (pulls in the entire M1-M3 stack)
├── namespace ZhangYeung
├── section SetFunctionCalculus
│     - def I_F, condI_F, delta_F
├── section ConePredicates
│     - def shannonCone
│     - def zhangYeungAt
│     - def zhangYeungHolds
├── section Witness
│     - def F_witness_ℚ
│     - noncomputable def F_witness
├── section PartA_ShannonCone
│     - theorem shannonCone_of_witness
├── section PartB_ZYViolation
│     - theorem not_zhangYeungHolds_witness
├── section Intermediate
│     - theorem shannon_incomplete
├── section EntropyFunction (Part (c), §§ per-subset lemmas and bridge)
│     - noncomputable def entropyFn
│     - lemma entropyFn_empty, entropyFn_singleton, entropyFn_pair,
│             entropyFn_triple, entropyFn_quad  (per-subset bridge lemmas)
│     - lemma zhangYeungAt_entropyFn  (permutation-indexed bridge)
│     - theorem zhangYeungHolds_of_entropy  (full bridge)
├── section PartD_Theorem4
│     - theorem theorem4
├── section OptionalStretches
│     - theorem theorem4_closure  (if time permits)
│     - theorem shannon_incomplete_ge_four  (if time permits)
└── end ZhangYeung
```

The module docstring follows the M3 template: opening paragraph stating role, `## Main definitions` listing the seven public defs, `## Main statements` listing `shannonCone_of_witness`, `not_zhangYeungHolds_witness`, `shannon_incomplete`, `zhangYeungHolds_of_entropy`, `theorem4` with one-sentence descriptions, `## Implementation notes` explaining the `ℚ → ℝ` cast, the `Equiv.Perm` choice, and the bridge-lemma approach, `## References` pointing at lines 358-388 of the transcription (Theorem 4 + witness) plus lines 339-355 ($\tilde{\Gamma}_4$ definition), and `## Tags`.

## Sequencing: commits

Each commit maintains a green build + lint + test. Each commit is a conventional-commit-styled small unit.

1. **Bootstrap + pre-flight checks.** In the `m4-theorem-4` worktree: `bin/bootstrap-worktree`; confirm `make check` is green with M1 + M1.5 + M2 + M3 on `main`. Run one pre-flight experiment in a scratch `.lean` file (delete after):

    - **`decide` performance rehearsal.** Instantiate a three-line toy `F : Finset (Fin 4) → ℚ` and run `example : ∀ α β : Finset (Fin 4), α ⊆ β → F α ≤ F β := by decide`. Confirm elaboration is under 3 seconds without a heartbeat bump. If it exceeds ~15 seconds, pivot the Shannon-cone proof to the fallback tactic pattern (cardinality case-split). Log the outcome in the step-2 commit message.

    Halt on failure; investigate before writing module code.

1. **Scaffold `ZhangYeung/Theorem4.lean` and `ZhangYeungTest/Theorem4.lean` in the same change.** Add the module docstring, imports (`ZhangYeung.Theorem3` only), the empty `namespace ZhangYeung`, and `sorry` stubs for the seven public definitions and five public theorems. Add signature-pinning `example`s in `ZhangYeungTest/Theorem4.lean` (one per public definition/theorem stub). Wire both top-level re-export files. Confirm `lake build ZhangYeung.Theorem4`, `lake build ZhangYeung`, `lake build ZhangYeungTest`, and `lake test` all pass. Commit as `feat: scaffold Theorem 4 module and API tests`.

1. **Land the set-function calculus: `I_F`, `condI_F`, `delta_F`.** Three one-line definitions. No lemmas (yet). Commit as `feat(theorem4): add set-function information-theoretic calculus`.

1. **Land `shannonCone`, `zhangYeungAt`, `zhangYeungHolds`.** Three definitions in sequence (paper eqs. 11, 21, 25). Commit as `feat(theorem4): add shannonCone and zhangYeungHolds predicates`.

1. **Land the witness `F_witness_ℚ` and `F_witness`.** The `ℚ`-valued five-case definition plus its `ℝ`-cast wrapper. Commit as `feat(theorem4): add Zhang-Yeung 1998 Theorem 4 counterexample witness`.

1. **Prove `shannonCone_of_witness` via `decide` + `exact_mod_cast`.** ~10-15 tactic lines, Part (a) complete. If the pre-flight rehearsal flagged performance issues, apply the case-enumeration fallback (Risk §11.1); budget ~60 lines in that case. Commit as `feat(theorem4): prove witness lies in the Shannon cone`.

1. **Prove `not_zhangYeungHolds_witness` via permutation specialization + `norm_num`.** ~15-20 tactic lines, Part (b) complete. Specialize at `σ = Equiv.swap 0 2 * Equiv.swap 1 3`; reduce to concrete `ℝ` arithmetic using the witness evaluation. Commit as `feat(theorem4): prove witness violates Zhang-Yeung at the canonical labelling`.

1. **Land `shannon_incomplete` (intermediate).** Three-line proof combining steps 6-7. Commit as `feat(theorem4): derive Γ_4 ⊋ tildeΓ_4 as shannon_incomplete`.

1. **Land `entropyFn` and the per-subset bridge lemmas.** Start with `entropyFn_empty` (easy), then `entropyFn_singleton`, `entropyFn_pair`, `entropyFn_triple`, `entropyFn_quad`. Budget ~5-10 tactic lines each via `entropy_comp_of_injective` with explicit `Equiv`s. If any lemma elaborates awkwardly through the `Subtype` coercion, extract the `Equiv` as a named `private` definition and keep the bridge lemma's proof short. Split into 3-5 commits at logical boundaries (e.g., `feat(theorem4): entropyFn definition and empty/singleton bridge`, `feat(theorem4): pair/triple/quad bridge lemmas`).

1. **Prove `zhangYeungAt_entropyFn` (permutation-indexed bridge).** Unfold + rewrite + close by M3's `zhangYeung`. Budget ~30-50 tactic lines. If the chase exceeds 75 lines, split the permutation-unfolding and the M3 closure into two sub-lemmas. Commit as `feat(theorem4): bridge set-function ZY from M3 at every permutation`.

1. **Land `zhangYeungHolds_of_entropy`.** One-line wrapper. Commit as `feat(theorem4): derive tildeΓ_4 membership for all four-variable entropy functions`.

1. **Prove `theorem4` (headline).** Five-line proof combining steps 6, 7, 11. Commit as `feat(theorem4): prove Theorem 4, Shannon incompleteness at n = 4`.

1. **(Optional stretch) Land `theorem4_closure`.** ~15-30 tactic lines. If budget tight, skip and file as follow-up.

1. **(Optional stretch) Land `shannon_incomplete_ge_four`.** ~20-40 tactic lines. If budget tight, skip.

1. **Expand `ZhangYeungTest/Theorem4.lean` to cover the full public API.** Signatures were pinned in step 2; expand with:
    - A signature-pinning `example` for each public theorem: `shannonCone_of_witness`, `not_zhangYeungHolds_witness`, `shannon_incomplete`, `zhangYeungHolds_of_entropy`, `theorem4`.
    - A concrete-arithmetic test: evaluate `F_witness_ℚ` on each of the 16 subsets.
    - A theorem-application test: reconstruct the Zhang-Yeung violation from scratch using the public API (compute `delta_F F_witness 2 3 0 1` and the RHS, `linarith` the contradiction).
    - A bridge-application test: starting from a concrete four-variable random variable family (e.g., `X : Fin 4 → Ω → Fin 2`), invoke `zhangYeungHolds_of_entropy` and consume one permutation's `zhangYeungAt`.
    - A theorem-application test for `theorem4`: pick a specific `X : Fin 4 → Ω → Fin 2`, derive `F_witness ≠ entropyFn X μ`.

    Commit as `test: cover Theorem 4 API surface`.

1. **Update `AGENTS.md` (aka `CLAUDE.md`) Module Layout.** Add one line pointing to `ZhangYeung/Theorem4.lean` and one line pointing to `ZhangYeungTest/Theorem4.lean`. Amend the `ZhangYeung.lean` entrypoint bullet to include the new re-export. Commit as `docs: document Theorem 4 module in CLAUDE.md`.

1. **Run `make check`.** Address any remaining lint or build issues; update `cspell-words.txt` with any new tokens ("counterexample", "tildeΓ", "submodular", "entropyFn"). Commit any cspell/lint adjustments as `chore: address lint feedback`.

1. **Move the plan from `todo/` to `done/`** in the final commit. Commit as `chore: move completed M4 plan from todo to done`.

1. **Update README** to mark M4 done and document the Theorem 4 module. Commit as `docs(readme): mark M4 done and document Theorem 4 module`.

1. **Open the PR.** Title: `feat: prove Theorem 4, Shannon incompleteness`. Body links this plan and the roadmap, summarizes the public surface and the four parts, calls out the set-function/random-variable bridge as M4's new measure-theoretic content, and notes whether the optional stretches (closure, n ≥ 4) landed.

**Abort/regroup gates.** If Part (c)'s bridge work (steps 9-11) sprawls past ~250 lines without closing cleanly, halt and reconsider: (i) promote the contingency of factoring `entropyFn` and per-subset lemmas into `ZhangYeung/EntropyFunction.lean`; or (ii) relax `zhangYeungHolds_of_entropy` to a single-labeling version (sufficient for `theorem4` at the canonical labeling) and file the all-permutations version as a follow-up.

## Open questions and known risks

### 11.1 `decide` performance on `Finset (Fin 4) × Finset (Fin 4) → Prop` (moderate)

Parts (a)'s Shannon-cone verification attempts `decide` on `∀ α β : Finset (Fin 4), ..., ... ≤ ...` with `F_witness_ℚ` as the witness. This is 16 × 16 = 256 cases, each of which elaborates through the `if ... else` branches of `F_witness_ℚ` five times per side. Most Lean 4 `decide` calls at this scale are under a second, but pathological cases have been observed (particularly when `Finset` decidability reduces through a chain of `Finset.insert` unfolds rather than a flat `Finset.decidableMem`).

**Mitigation (try in order):**

1. Run the pre-flight rehearsal (sequencing step 1). If under 3 seconds, proceed.
1. If in 3-30 seconds, split the three Shannon-cone clauses into three separate lemmas so each `decide` runs in its own heartbeat bucket. Per `feedback_lean_split_before_bump.md`, split before bumping; only bump if splitting alone does not help.
1. If >30 seconds or hitting the reducer's stack limit, pivot to cardinality case-enumeration: `match α.card, β.card with` on the five-valued cardinality, then within each case `match α, β with` on the literal value. Budget ~60-100 lines in that fallback.
1. Last resort: enumerate all 16 `Finset (Fin 4)` subsets as an explicit `List` and prove the cone conditions on the product of that list with itself. `List.forall₂_iff` + `decide` on a flat list of rational comparisons tends to be faster.

### 11.2 Per-subset bridge lemma boilerplate (moderate-high)

Part (c)'s per-subset lemmas (`entropyFn_empty` through `entropyFn_quad`) each require an explicit `Equiv` between a `Finset`-indexed subtype and `Fin k`, plus an invocation of `entropy_comp_of_injective` or `IdentDistrib.entropy_eq`. Depending on how cleanly Mathlib's `Equiv` API handles the subtype, this can be ~5 lines per lemma or ~20 lines per lemma. Five lemmas × 20 lines = 100 lines; five lemmas × 5 lines = 25 lines.

**Mitigation:**

1. Before writing the first lemma, grep Mathlib for existing `Equiv`s between `Subtype` and `Fin n` -- e.g. `Finset.equivFin`, `Fintype.equivFin`. These may collapse the equivalence construction to a one-liner.
1. Share the `Equiv` construction across lemmas: if the pattern `{i, j} ≃ Fin 2` generalizes cleanly to `{i, j, k} ≃ Fin 3` via `Finset.equivFin`, factor the shared `Equiv` into a `private` helper and call uniformly.
1. If `entropy_comp_of_injective` proves awkward (universe issues, implicit argument mess), fall back to `IdentDistrib.entropy_eq` via a manually constructed `IdentDistrib` between the two joint distributions.
1. If any single per-subset lemma resists both routes, state the lemma in terms of a named local joint RV (`Y := fun ω => ⟨X i ω, X j ω⟩`) instead of a `⟨X i, X j⟩` packed tuple; this side-steps the subtype coercion at the cost of an extra variable.

### 11.3 Permutation-indexed bridge proof bookkeeping (moderate)

`zhangYeungAt_entropyFn` unfolds into five `F`-evaluations and needs to rewrite each into a joint entropy. For a fixed permutation `π`, the five evaluations are at `{π 0}`, `{π 2, π 3}`, `{π 0, π 1}`, `{π 0, π 1, π 2}`, `{π 0, π 1, π 3}`, `{π 2}`, `{π 3}`, `{π 2, π 0, π 1}` — depending on which `zhangYeungAt` sub-expression we look at. The rewrite chain is long.

**Mitigation:**

1. Introduce local abbreviations `Z := X (π 0)`, `U := X (π 1)`, `Xm := X (π 2)`, `Y := X (π 3)` at the top of the proof. This avoids re-writing `X (π 0)` at every invocation.
1. Use `simp only [entropyFn_singleton, entropyFn_pair, ...]` to batch-apply the per-subset lemmas. The distinctness hypotheses propagate through `π.injective`.
1. Close by `exact ZhangYeung.zhangYeung hZ hU hXm hY μ`; the tactic-level rewrites should leave a goal matching M3's conclusion exactly.
1. If the bookkeeping still sprawls, narrow `zhangYeungAt_entropyFn` to a single canonical labeling (trivially `π = 1`), prove `theorem4` at that one labeling, and file the all-permutations version as a follow-up. `theorem4` only needs one labeling to fail for `F_witness`; the bridge only needs one labeling to hold for `entropyFn`. The all-permutations form is cleaner but not strictly necessary.

### 11.4 Universe alignment with M3 (low-moderate)

M3's `zhangYeung` binds codomains `S₁, S₂, S₃, S₄ : Type u` at a single universe. The bridge `entropyFn X μ` with `X : Fin 4 → Ω → S` and `S : Type u` inherits this universe constraint. `theorem4`'s signature must bind `S : Type u` and `X : Fin 4 → Ω → S` accordingly.

**Mitigation:** fix the universe at `Type u` (inherited from M3) throughout M4. If a concrete caller at `Type 0` finds the `u` binding awkward, add a `ULift` shim or a `Type 0`-specialized wrapper as a follow-up. Not a blocker for M4.

### 11.5 `zhangYeungHolds` over `Equiv.Perm (Fin 4)` (low)

Quantifying over `Equiv.Perm (Fin 4)` (size 24) matches paper eq. (25) but requires constructing specific permutations (e.g., `Equiv.swap 0 2 * Equiv.swap 1 3` for the violation). The `Equiv.Perm.mul_apply` + `Equiv.swap_apply_*` simp set handles the normalization, but it may need a `decide` or explicit per-coordinate check to finish `π 0 = 2` etc.

**Mitigation:** if the `Equiv` normalization is finicky, pivot `zhangYeungHolds` to the equivalent "distinct 4-tuples" form:

```lean
def zhangYeungHolds (F : Finset (Fin 4) → ℝ) : Prop :=
  ∀ i j k l : Fin 4, ({i, j, k, l} : Finset (Fin 4)).card = 4 → zhangYeungAt F i j k l
```

The `card = 4` hypothesis is `decide`-closable. This form makes the violation and the bridge both simpler at the cost of some paper-alignment. Make the choice once (at sequencing step 4) and stick with it; do not switch mid-milestone.

### 11.6 Bridge sprawl into a separate module (moderate)

As noted in §File layout, if Part (c) exceeds ~200 lines, factor `entropyFn` and per-subset bridge lemmas into `ZhangYeung/EntropyFunction.lean`. This is a non-breaking refactor: same public namespace, different file. The entropyFn API is natural to reuse in any future non-Shannon inequality formalization (Matus, DFZ, Kinser), so a separate file is upstream-friendly.

**Mitigation:** the contingency is documented; activate only at the decision gate. Do not pre-emptively split.

### 11.7 `ℚ → ℝ` cast friction (low)

The main theorems state over `ℝ`; the witness is over `ℚ`. Any `simp`-normal-form of `(F_witness_ℚ S : ℝ)` should reduce to the same numerical values as `F_witness_ℚ S`. Potential snags: `Rat.cast_ite` or the `if ... then ... else ...` under the cast may need manual `simp only [Rat.cast_ite, Rat.cast_ofNat, Rat.cast_zero]`.

**Mitigation:** define `F_witness : Finset (Fin 4) → ℝ := fun S => (F_witness_ℚ S : ℝ)` as its own named definition. Land a one-line lemma `F_witness_eq_cast : F_witness S = (F_witness_ℚ S : ℝ) := rfl` to make the cast bridgeable inside downstream tactic proofs.

### 11.8 PFR API churn (low, carried forward)

Same as M2-M3 risk. PFR is a permanent pinned dependency. M4 consumes M3's `zhangYeung` plus `entropy_comp_of_injective`, `entropy_comm`, and the `H[_; _]`/`I[_:_; _]` notation, all of which are stable in the current PFR pin.

## Verification

Per the revised roadmap M4 checkpoint (see roadmap §M4 edits in this same change): three theorems land, along with their supporting public surface.

- `theorem shannon_incomplete : ∃ F, shannonCone F ∧ ¬ zhangYeungHolds F` — Parts (a) + (b).
- `theorem zhangYeungHolds_of_entropy` — Part (c), routes through M3.
- `theorem theorem4` — Part (d), the headline.

Operationally:

- `lake build ZhangYeung.Theorem4` compiles with no warnings, no `sorry`, no `admit`.
- `lake build ZhangYeung` compiles with `ZhangYeung.lean` re-exporting `ZhangYeung.Theorem4` cleanly.
- `lake build ZhangYeungTest.Theorem4` compiles; the test module imports only `ZhangYeung` and not `ZhangYeung.Theorem4` directly, exercising the public API surface.
- `lake build` and `lake test` both succeed on the default targets; CI goes green.
- `lake lint` passes (batteries linter via the `lintDriver`).
- `make check` passes in full.

**Test module contents** (`ZhangYeungTest/Theorem4.lean`, established incrementally in sequencing steps 2 and 15):

1. Signature-pinning `example`s for each public definition (`I_F`, `condI_F`, `delta_F`, `shannonCone`, `zhangYeungAt`, `zhangYeungHolds`, `F_witness_ℚ`, `F_witness`, `entropyFn`) and each public theorem (`shannonCone_of_witness`, `not_zhangYeungHolds_witness`, `shannon_incomplete`, `zhangYeungAt_entropyFn`, `zhangYeungHolds_of_entropy`, `theorem4`). ~15 `example`s.
1. Concrete-arithmetic witness evaluation: for each of the 16 `Finset (Fin 4)` subsets, assert the expected `F_witness_ℚ` value. Closes by per-subset `rfl`/`decide` or one `decide` over `Finset.univ`.
1. Theorem-application test 1 (violation reconstruction): compute `delta_F F_witness 2 3 0 1` and the RHS of eq. (21) at the canonical labeling using only the public API, verify the contradiction.
1. Theorem-application test 2 (bridge consumption): starting from a concrete `X : Fin 4 → Ω → Fin 2` family, invoke `zhangYeungHolds_of_entropy` and consume one permutation's `zhangYeungAt`.
1. Theorem-application test 3 (theorem4 consumption): pick a specific `X : Fin 4 → Ω → Fin 2`, derive `F_witness ≠ entropyFn X μ` via `theorem4`.

Each `example` lives inside `namespace ZhangYeungTest` with `open ZhangYeung`, following the M1-M3 `ZhangYeungTest/` precedents.

Land these in the same commits as the corresponding public surface (signatures in step 2, per-subset and theorem-application tests in step 15), so `lake test` exercises the public API continuously through the milestone.

**Out-of-scope for M4** (documented here so M5 and beyond can pick them up):

- Closure version `theorem4_closure` (optional stretch; file as M4.5 follow-up if it does not land).
- `n ≥ 4` extension `shannon_incomplete_ge_four` (optional stretch).
- No `Γ^*_n` or $\bar{\Gamma}^*_n$ as named named subsets of `Finset (Fin n) → ℝ`; M4 states the separation directly.
- No $\hat{\Gamma}_4$ inner-bound material (paper Theorem 6, roadmap §4 excluded from S2).
- No upstreaming of `shannonCone`, `zhangYeungHolds`, `entropyFn` to Mathlib. All stay local to `ZhangYeung` unless later work demonstrates external demand.

## Critical files

**This milestone:**

- `ZhangYeung/Theorem4.lean` (new).
- `ZhangYeungTest/Theorem4.lean` (new).
- `ZhangYeung.lean` (modified, add one `import` line).
- `ZhangYeungTest.lean` (modified, add one `import` line).
- `AGENTS.md` / `CLAUDE.md` (modified, two-line Module Layout addition + entrypoint manifest update).
- `docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md` (modified, M4 section revised to reflect the full Theorem 4 scope; §6 parallelism analysis revised to note M3 has landed).

**Potential new file (contingency per §File layout):**

- `ZhangYeung/EntropyFunction.lean` — only if Part (c)'s bridge work forces a split.

**Read-only references:**

- `ZhangYeung/Theorem3.lean` (M3 output; `zhangYeung`, `zhangYeung_dual`, `zhangYeung_averaged`, three public theorems).
- `ZhangYeung/Delta.lean` (M1 output; `ZhangYeung.delta` and form-conversion lemmas, consumed by the bridge).
- `ZhangYeung/CopyLemma.lean`, `ZhangYeung/Theorem2.lean`, `ZhangYeung/Prelude.lean` (M1-M2 outputs; style precedent).
- `references/transcriptions/zhangyeung1998.md` (paper transcription; Theorem 4 on lines 358-388, basic inequalities on lines 466-480, $\tilde{\Gamma}_4$ on lines 339-355).
- `.lake/packages/pfr/PFR/ForMathlib/Entropy/Basic.lean` (entropy + MI primitives used by the bridge).
- `.lake/packages/mathlib/Mathlib/Data/Finset/Basic.lean`, `Powerset.lean` (`Finset` operations, decidability instances).
- `.lake/packages/mathlib/Mathlib/Logic/Equiv/Perm.lean` (permutations, `Equiv.swap`).
- `.lake/packages/mathlib/Mathlib/Logic/Equiv/Fin.lean` (bijections between subtypes and `Fin n`).
- `docs/plans/done/2026-04-18-theorem-3-zhang-yeung-inequality.md` (M3 plan; style precedent).
- `docs/plans/done/2026-04-17-copy-lemma.md` (M2 plan; additional style precedent).

Reference: the `write-lean-code` skill is authoritative for Lean naming and proof style; the `write-math` skill governs the module docstring and any mathematical prose inside comments; the `write-pandoc-markdown` skill governs this plan document; the `write-formalization-roadmap` skill and the existing M2/M3 plan documents are the authoritative templates for this plan's structure.
