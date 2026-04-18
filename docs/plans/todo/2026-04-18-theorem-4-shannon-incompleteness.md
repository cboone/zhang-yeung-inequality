---
title: "M4: Theorem 4, Shannon incompleteness (Zhang-Yeung 1998, §II, Theorem 4 / eq. 26)"
created: 2026-04-18
branch: formalize/m4-theorem-4
roadmap: docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md
milestone: M4
depends_on: M3 (`ZhangYeung/Theorem3.lean`, merged into `main` via PR #9). M2 (`ZhangYeung/CopyLemma.lean`), M1.5 (`ZhangYeung/Theorem2.lean`), and M1 (`ZhangYeung/Delta.lean`) are also all on `main`. The worktree `m4-theorem-4` is branched from the tip of `main`; the branch has a clean `make check` as the starting state.
---

## Context

Milestone M4 of the Zhang-Yeung roadmap (§6) formalizes the **incompleteness corollary** of the 1998 paper: the fact that Shannon's basic information inequalities do not fully characterize the set of entropic functions for four or more random variables. Equivalently, the cone $\bar{\Gamma}^*_n$ of asymptotically constructible entropy functions is strictly smaller than the Shannon outer bound $\Gamma_n$ for $n \ge 4$. The argument is an immediate corollary of M3 (Theorem 3): exhibit a single set function $F \in \Gamma_4$ that violates the Zhang-Yeung inequality. Since entropy functions satisfy Zhang-Yeung (this is exactly M3's headline theorem at the set-function level), $F$ is not an entropy function, hence $\Gamma_4$ properly contains the entropy region.

**Primary reference:** `references/transcriptions/zhangyeung1998.md` (verified 2026-04-16). Equation and line numbers below reference that transcription. The Theorem 4 statement is on lines 358-388; the counterexample witness is defined on lines 368-377.

The paper's Theorem 4 statement (line 358):

> For $n \ge 4$,
> $$
> \bar{\Gamma}^*_n \neq \Gamma_n. \tag{26}
> $$

The paper's proof in prose (paraphrased from lines 366-379): it suffices to handle $n = 4$, because any separation witness for $n = 4$ lifts to any $n \ge 4$ by an embedding argument. For $n = 4$, define the set function $F: 2^{\{X, Y, Z, U\}} \to \mathbb{R}$ by

$$
\begin{aligned}
F(\phi) &= 0, \\
F(X) &= F(Y) = F(Z) = F(U) = 2a, \\
F(X, Y) &= 4a, \\
F(X, Z) = F(X, U) = F(Y, Z) &= F(Y, U) = F(Z, U) = 3a, \\
F(X, Y, Z) = F(X, Y, U) = F(X, Z, U) &= F(Y, Z, U) = F(X, Y, Z, U) = 4a,
\end{aligned}
$$

for any fixed $a > 0$. Then $F \in \Gamma_4$ (Shannon basic inequalities hold) and $F \notin \tilde{\Gamma}_4$ (Zhang-Yeung inequality fails for some permutation of the four variables). Since M3's Theorem 3 establishes $\bar{\Gamma}^*_4 \subseteq \tilde{\Gamma}_4$, this witness lies in $\Gamma_4 \setminus \bar{\Gamma}^*_4$, proving (26) for $n = 4$. The lift to $n \ge 4$ uses $F_n(\alpha) := F(\alpha \cap \{X, Y, Z, U\})$ (the extended function agrees with $F$ on the distinguished four coordinates and behaves polymatroidally on the remaining $n - 4$ "dummy" coordinates).

### Why M4 lands now

1. **M3 is on `main`.** The `zhangYeung` theorem (paper eq. 21) and its two partners (`zhangYeung_dual` eq. 22, `zhangYeung_averaged` eq. 23) landed in PR #9. The entire Shannon chase is available as a black-box theorem to plug into M4's bridge lemma. M1 (`delta`, form-conversion lemmas) and M2 (copy lemma, Lemma 2 Form B, the two inequality corollaries) are the dependencies M3 itself used and are all still on `main`.
1. **M4 is predominantly combinatorial, not analytic.** Unlike M1.5/M2/M3, M4's proofs are *direct computations on a concrete set function over $2^{\{0, 1, 2, 3\}}$* (16 subsets, fully enumerable). No new entropy-theoretic infrastructure is required; the milestone consumes M3 as a one-line bridge and otherwise builds its own small set-function calculus (the `Finset`-valued analogues of $H$, $I$, $I(\cdot;\cdot|\cdot)$, and $\Delta$).
1. **Parallelism with M3 was mooted; M4 can now run as a clean follow-on.** Roadmap §6 originally allowed M4 part (a) (Shannon cone definition + witness verification) to run before M3 merged. Since M3 is now on `main`, that parallelism is no longer needed: M4 can land as a single milestone against the M3-ready main branch.

### What M4 does not do

- **Theorem 5 (n+2-variable generalization).** Stretch goal, roadmap §M5; picks up after M4 lands.
- **Theorem 6 (inner bound on $\bar{\Gamma}^*_4$).** Deliberately excluded from S2 scope per roadmap §4. Revisit post-release.
- **Exact identity form with explicit slack $R$** (paper p. 1446, post-release extension #2). Out of scope.
- **Copy lemma upstreaming to Mathlib** (post-release extension #1). Out of scope.
- **Rigorous closure statement $\bar{\Gamma}^*_4 \neq \Gamma_4$ via sequential limits.** The paper's Theorem 4 is about the *closure* of $\Gamma^*_4$. For M4 we focus on the weaker-but-equivalent statement that $F \in \Gamma_4 \setminus \tilde{\Gamma}_4$ and its immediate consequence that $F$ is not the entropy function of any finitely-many discrete random variables. Extending this to "$F$ is not the limit of entropy functions" (the full closure claim) requires a short topological argument (the Zhang-Yeung inequality is $\le$ on a continuous functional of $F$, so the set of $F$ satisfying it is closed); that argument is not the scientific content of M4 and is tracked as a documentation-only remark in the final module docstring rather than as a Lean lemma. The hook is to revisit if a later milestone needs it.
- **n+2-variable extension beyond `n = 4`.** The roadmap's M4 bullet mentions "extend to $n \ge 4$ via embedding". That extension is a mechanical padding exercise on `Finset (Fin n)` and adds no new scientific content over `n = 4`. M4 lands the core `n = 4` witness and the mechanical extension as a single-paragraph remark; the explicit `∃ F : Finset (Fin n) → ℝ, ...` theorem for arbitrary `n ≥ 4` is optional stretch (see §11 "Optional extension" below). If M4 sprawls, drop the extension to a follow-up.

## Paper proof (transcription, lines 358-388)

Define $F: 2^{\{X, Y, Z, U\}} \to \mathbb{R}$ by the value table above (any $a > 0$). Theorem 4 is proved by two claims:

**Claim 1: $F \in \Gamma_4$.** The paper asserts this without proof; it is a direct check of 16 monotonicity constraints and a fully enumerable collection of submodularity constraints. The elemental-form restatement (paper eqs. 32, 33, listed on lines 466-480) reduces this to checking:

- $F[i] \ge 0$ for each $i$ (4 inequalities).
- $F[i, j] \ge 0$ for each ordered pair (6 inequalities).
- $F[i, j] + F[i, j, k] \ge 0$ for each $(i, j, k)$ (12 inequalities).
- $F[i, j] + F[i, j, k] + F[i, j, l] + F[i, j, k, l] \ge 0$ for each pair partition $(i, j) \ni (k, l)$ (6 inequalities).

28 elemental inequalities in total (the paper's informal "15 basic inequality constraints" in roadmap §M4 counts the generating *submodular* inequalities, not the per-permutation elementals; either counting discharges the Shannon cone). Every elemental inequality reduces to an explicit `2a`, `3a`, `4a` arithmetic comparison that `norm_num` / `linarith` closes at `a = 1`. In our Lean setup, we discharge the three native Shannon-cone conditions (`F ∅ = 0`, monotone, submodular) directly by `decide` over `ℚ`; the elemental decomposition is not needed as intermediate scaffolding.

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

For $a > 0$, $a \le a/2$ is false, so $F$ violates the Zhang-Yeung inequality (eq. 21) at this specific labeling. The set-function version of M3 says that every entropy function satisfies eq. 21 at *every* labeling; one failing labeling suffices to exhibit the separation.

**Conclusion.** $F \in \Gamma_4 \setminus \tilde{\Gamma}_4$. Since $\bar{\Gamma}^*_4 \subseteq \tilde{\Gamma}_4$ (Theorem 3), $F \in \Gamma_4 \setminus \bar{\Gamma}^*_4$, establishing eq. (26) for $n = 4$. For $n > 4$, extend $F$ to $F_n : 2^{\mathcal{N}_n} \to \mathbb{R}$ by $F_n(\alpha) := F(\alpha \cap \{0, 1, 2, 3\})$.

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

M4 consumes `zhangYeung` as a black-box theorem. The other two (dual, averaged) are not needed for the `n = 4` counterexample: a single labeling of the inequality suffices to witness the violation. If we include a bridge lemma that says "the entropy function of any four RVs lies in $\tilde{\Gamma}_4$" (all 24 permutations), the `zhangYeung_dual` theorem is the natural companion in that argument (combined with index-permutation, 6 to 12 applications depending on how one handles the $X \leftrightarrow Y$, $Z \leftrightarrow U$ symmetries of $\Delta_F$). The bridge lemma is planned as part of M4 but is scoped narrower than the full $\tilde{\Gamma}_4$-membership — see §8 "Bridge lemma" below.

Before starting M4, in the `m4-theorem-4` worktree: `bin/bootstrap-worktree`, then `make check`. Confirm the tip is green with M1 + M1.5 + M2 + M3 in place and `lake env lean --version` reports the pinned Lean toolchain.

## Design: set-function coordinates

M4 leaves PFR's random-variable entropy world and moves to the *set-function* world of $\mathcal{F}_n = \{F : 2^{\mathcal{N}_n} \to \mathbb{R}\}$. The Lean encoding uses `Finset (Fin n) → ℝ` for $F$ with $\mathcal{N}_n \equiv \{0, 1, \ldots, n-1\}$. For M4 the primary case is $n = 4$.

### Why `Finset (Fin 4)` and not `Set (Fin 4)` or `ℕ`-bitmasks?

- `Finset (Fin 4)` is a `Fintype`; `Fintype.decidableForallFintype` kicks in for free.
- `Finset.decidableEq`, `Finset.decidableSubset`, `Finset.decidableMem` are all automatic.
- The `Finset` literal syntax `{0, 1, 2}` elaborates to `insert 0 (insert 1 (insert 2 ∅)) : Finset (Fin 4)` and the card / subset / union / intersection operations all reduce by `decide` on concrete literals.
- `Set (Fin 4)` would lose the `Fintype` and decidability story; bitmasks would hide the mathematical structure behind bit-manipulation lemmas. `Finset` is the right fit.

### Working over `ℚ` vs `ℝ`

The witness values are integer-valued (at $a = 1$: $\{0, 2, 3, 4\}$), and the Shannon cone / Zhang-Yeung inequality both mention only rationals on the right-hand side. We will:

1. Define the witness $F_{\text{witness}} : \text{Finset (Fin 4)} \to \mathbb{Q}$ so that `decide` closes the Shannon cone membership via `Fintype.decidableForallFintype` + `DecidableEq (Finset (Fin 4))` + `Decidable ((a : ℚ) ≤ b)`.
1. Cast to $\mathbb{R}$ at the statement level of `shannon_incomplete`: the theorem signature reads `∃ F : Finset (Fin 4) → ℝ, shannonCone F ∧ ¬ zhangYeungHolds F`, and the proof supplies `(↑) ∘ F_witness` (i.e. the `ℚ`-valued witness cast pointwise into `ℝ`).
1. The ZY violation is proved over `ℝ` directly (or over `ℚ` then cast via `Rat.cast_lt`/`Rat.cast_le`). A single numerical instance suffices; `norm_num` closes the arithmetic.

This `ℚ`-then-cast strategy keeps the Shannon cone verification fully automatic while still presenting the main theorem over `ℝ` (the convention used throughout M1-M3).

### Why `a = 1` (not parametrized)?

The paper phrases the witness parametrically in $a > 0$ for two reasons: (1) to make the homogeneity of the Shannon cone manifest (every conclusion scales linearly in $a$), (2) to make the witness unambiguous about signs. Neither reason applies in Lean: (1) is vacuous since the `shannon_incomplete` statement only asserts *existence*, and (2) is discharged by the type `ℚ` (no sign ambiguity). Fixing $a = 1$ shrinks the proof and avoids threading an `a : ℝ` hypothesis with `(ha : 0 < a)` through every lemma.

### Set-function calculus

M4 needs a small set-function calculus mirroring the random-variable-level entropy calculus of M1-M3. The minimum API:

```lean
/-- `I_F(α; β) := F(α) + F(β) - F(α ∪ β)`. When `F` is the entropy function of a
set of random variables, `I_F(α; β) = I(X_α; X_β)`. -/
def I_F (F : Finset (Fin 4) → ℝ) (α β : Finset (Fin 4)) : ℝ :=
  F α + F β - F (α ∪ β)

/-- `I_F(α; β | γ) := F(α ∪ γ) + F(β ∪ γ) - F(α ∪ β ∪ γ) - F(γ)`. -/
def condI_F (F : Finset (Fin 4) → ℝ) (α β γ : Finset (Fin 4)) : ℝ :=
  F (α ∪ γ) + F (β ∪ γ) - F (α ∪ β ∪ γ) - F γ

/-- `Δ_F(i, j | k, l) := I_F({i}; {j}) - I_F({i}; {j} | {k}) - I_F({i}; {j} | {l})`. -/
def delta_F (F : Finset (Fin 4) → ℝ) (i j k l : Fin 4) : ℝ :=
  I_F F {i} {j} - condI_F F {i} {j} {k} - condI_F F {i} {j} {l}
```

Note that `I_F` above is the *unconditional* mutual information, not Shannon's definition (which uses $F(\gamma)$ at `γ = ∅`). The two coincide when $F(\emptyset) = 0$, which is the first Shannon-cone axiom, so this is a non-issue inside $\Gamma_4$. We include the `γ` argument explicitly in `condI_F` rather than defaulting; callers always use one or both of `I_F _ α β` and `condI_F _ α β γ`.

The Shannon cone predicate:

```lean
/-- `Γ_n` from Zhang-Yeung 1998 eq. (11): F is in the Shannon cone iff it is
zero on the empty set, monotone under subset inclusion, and submodular. -/
def shannonCone (F : Finset (Fin 4) → ℝ) : Prop :=
  F ∅ = 0 ∧
  (∀ α β : Finset (Fin 4), α ⊆ β → F α ≤ F β) ∧
  (∀ α β : Finset (Fin 4), F (α ∪ β) + F (α ∩ β) ≤ F α + F β)
```

The Zhang-Yeung predicate:

```lean
/-- Zhang-Yeung inequality at a specific 4-tuple labeling, paper eq. (21):
`Δ_F(i, j | k, l) ≤ (1/2)(I_F(k; l) + I_F(k; {i, j}) + I_F(i; j | k) - I_F(i; j | l))`. -/
def zhangYeungAt (F : Finset (Fin 4) → ℝ) (i j k l : Fin 4) : Prop :=
  delta_F F i j k l ≤ (1/2) * (I_F F {k} {l} + I_F F {k} ({i} ∪ {j})
    + condI_F F {i} {j} {k} - condI_F F {i} {j} {l})

/-- `F` is in the Zhang-Yeung cone `tildeΓ_4`: the Zhang-Yeung inequality holds at
every labeling by a permutation of `{0, 1, 2, 3}`. (Paper eq. 25.) -/
def zhangYeungHolds (F : Finset (Fin 4) → ℝ) : Prop :=
  ∀ π : Equiv.Perm (Fin 4), zhangYeungAt F (π 0) (π 1) (π 2) (π 3)
```

The choice to quantify over `Equiv.Perm (Fin 4)` (rather than over all distinct 4-tuples with an explicit distinctness hypothesis) matches the paper's $\tilde{\Gamma}_4$ definition (eq. 25) literally and avoids a 4-fold distinctness hypothesis at every call site. For the violation proof we supply a specific permutation (cycle `(0 2) (1 3)`), so the `Equiv.Perm` layer costs almost nothing.

## PFR and Mathlib API surface used

All declarations live under `namespace ProbabilityTheory` unless noted.

**From the current project (used in the bridge lemma only; §8):**

- `ZhangYeung.zhangYeung` (M3) -- the headline theorem. Applied once at the canonical labeling to discharge the bridge for a single entropy function.
- `ZhangYeung.delta` and `ZhangYeung.delta_def` (M1) -- used by the bridge to equate the set-function $\Delta_F$ with the random-variable $\Delta$ when $F$ is an entropy function.

**From Mathlib (set-function calculus):**

- `Finset.decidableEq`, `Finset.decidableMem`, `Finset.decidableBEx`, `Finset.decidableBAll` -- decidability of set predicates on concrete `Finset`s; drive `decide` closure for the Shannon cone verification.
- `Fintype.decidableForallFintype` -- closes `∀ α : Finset (Fin 4), ...` for decidable `P α`.
- `Finset.union`, `Finset.inter`, `Finset.subset_iff`, `Finset.Singleton` (literal `{x}`), `Finset.insert` -- the primitive set operations consumed by `I_F`, `condI_F`, `delta_F`.
- `Finset.card_empty`, `Finset.card_singleton`, `Finset.card_insert_of_not_mem` -- unfold cardinality on concrete literals (needed if we branch the witness on `Finset.card`).
- `Rat.cast_le`, `Rat.cast_lt`, `Rat.cast_add`, `Rat.cast_mul` -- to push a `ℚ`-valued witness through to `ℝ` at the statement boundary.

**For the bridge lemma (uses M3):**

- `ProbabilityTheory.entropy`, `mutualInfo`, `condMutualInfo` (PFR) -- already in M1-M3's import surface; wrapped by `H[_ ; _]`, `I[_ : _ ; _]`, `I[_ : _ | _ ; _]` notation.
- `IdentDistrib.entropy_eq`, `IdentDistrib.mutualInfo_eq`, `IdentDistrib.condMutualInfo_eq` -- not strictly needed for the single-labeling bridge, but useful if the bridge grows to cover all permutations (see §8).
- `mutualInfo_def`, `condMutualInfo_eq`, `mutualInfo_comm`, `entropy_comm` -- all used by M1-M3; any bridge from entropy functions to set functions re-enters the entropy calculus through the same door M3 did.

**For the optional `n ≥ 4` extension (§11):**

- `Fin.castLEEmb : n ≤ m → Fin n ↪ Fin m` -- canonical order-preserving embedding; used to lift the `n = 4` witness to any larger `n`.
- `Finset.preimage` -- restrict a `Finset (Fin n)` back to a `Finset (Fin 4)` through a function `Fin 4 → Fin n`.

Nothing in Mathlib currently packages $\Gamma_n$ or the submodular cone over `Finset (Fin n) → ℝ`. M4 introduces the predicate under `namespace ZhangYeung` locally; if a later project finds the definition useful, it is a candidate for upstream.

## The M4 theorems

### Headline: `shannon_incomplete`

```lean
theorem shannon_incomplete :
    ∃ F : Finset (Fin 4) → ℝ, shannonCone F ∧ ¬ zhangYeungHolds F := by
  refine ⟨fun S => (F_witness_ℚ S : ℝ), ?_, ?_⟩
  · exact shannonCone_of_witness
  · exact not_zhangYeungHolds_witness
```

where `F_witness_ℚ : Finset (Fin 4) → ℚ` is the concrete witness, and the two components are separate named lemmas. This is the roadmap §6 M4 checkpoint, stated at `ℝ`.

### Witness: `F_witness_ℚ` and evaluation lemmas

```lean
/-- The Zhang-Yeung 1998 counterexample witness (paper lines 368-377) at `a = 1`:
the unique set function with `F(∅) = 0`; `F = 2` on singletons; `F = 4` on the
special pair `{0, 1}`; `F = 3` on the other five pairs; `F = 4` on all triples
and on the full set. The function is symmetric in the five "non-special" pairs
and asymmetric only at `{0, 1}`. -/
def F_witness_ℚ : Finset (Fin 4) → ℚ := fun S =>
  if S.card = 0 then 0
  else if S.card = 1 then 2
  else if S = {0, 1} then 4
  else if S.card = 2 then 3
  else 4
```

Each of the 16 subsets evaluates to a concrete rational by `decide` (or by a one-line `simp` using the `Finset.card_insert_of_not_mem` family). No explicit evaluation lemma is required at each of the 16 points, because the Shannon-cone verification uses `decide` holistically; but the ZY-violation proof inlines the five distinct values via `show` and closes by `norm_num`.

### Shannon cone membership: `shannonCone_of_witness`

```lean
theorem shannonCone_of_witness :
    shannonCone (fun S => (F_witness_ℚ S : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- F_witness_ℚ ∅ = 0
    decide
  · -- monotonicity
    intro α β hαβ
    exact_mod_cast (show ∀ α β : Finset (Fin 4), α ⊆ β → F_witness_ℚ α ≤ F_witness_ℚ β
      from by decide) α β hαβ
  · -- submodularity
    intro α β
    exact_mod_cast (show ∀ α β : Finset (Fin 4),
        F_witness_ℚ (α ∪ β) + F_witness_ℚ (α ∩ β) ≤ F_witness_ℚ α + F_witness_ℚ β
      from by decide) α β
```

The three clauses are discharged by `decide` over the `ℚ`-valued witness, then lifted to `ℝ` via `exact_mod_cast`. Budget ~10 tactic lines. If `decide` is too slow (see Risk §11.1), the fallback is case enumeration over `Finset.card α, Finset.card β ∈ {0, 1, 2, 3, 4}` (25 × 2 = 50 cases, each closed by `simp [F_witness_ℚ] + norm_num`).

### ZY violation: `not_zhangYeungHolds_witness`

```lean
theorem not_zhangYeungHolds_witness :
    ¬ zhangYeungHolds (fun S => (F_witness_ℚ S : ℝ)) := by
  intro h
  -- Specialise `h` at the permutation σ = (0 2)(1 3), which sends 0↦2, 1↦3,
  -- 2↦0, 3↦1. Then `zhangYeungAt F (σ 0) (σ 1) (σ 2) (σ 3) = zhangYeungAt F 2 3 0 1`,
  -- the canonical (Z, U, X, Y) labelling of paper eq. (21).
  have h' : zhangYeungAt (fun S => (F_witness_ℚ S : ℝ)) 2 3 0 1 := by
    have := h (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)
    simpa [Equiv.swap_apply_left, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne,
           Equiv.Perm.mul_apply] using this
  -- h' : Δ_F(2, 3 | 0, 1) ≤ (1/2)(I_F(0; 1) + I_F(0; {2, 3})
  --                              + I_F(2; 3 | 0) - I_F(2; 3 | 1))
  -- Compute both sides numerically:
  --   LHS = 1,  RHS = 1/2  →  contradicts h'.
  simp only [zhangYeungAt, delta_F, I_F, condI_F] at h'
  norm_num [F_witness_ℚ] at h'
```

Budget ~15 tactic lines. The arithmetic reduces to seven `F_witness_ℚ` evaluations (at `∅`, `{0}`, `{1}`, `{2}`, `{3}`, `{0, 1}`, `{0, 2}`, `{0, 3}`, `{1, 2}`, `{1, 3}`, `{2, 3}`, `{0, 2, 3}`, `{1, 2, 3}`) and one final `linarith`/`norm_num` closure. If `norm_num` cannot peel the `F_witness_ℚ` definition cleanly, substitute `decide` or an explicit `show ... = ...; rfl` for each subset evaluation.

### Bridge lemma: entropy functions lie in the Zhang-Yeung cone

The M4 proof of `shannon_incomplete` does not use M3 directly — the witness is a set function, not an entropy function, and the arithmetic needs no probability-theoretic input. M3 is consumed only in the *interpretation* of the result: the witness is not an entropy function, because M3 says entropy functions lie in $\tilde{\Gamma}_4$. M4 makes this interpretation formal with a bridge lemma:

```lean
/-- The set-function analogue of M3's `zhangYeung`: the entropy function of any
four discrete random variables lies in `tildeΓ_4`. Proof: apply `zhangYeung` at
each of the six distinct labelings and close by rewriting entropies as
`Finset`-valued `F` evaluations. -/
theorem zhangYeungHolds_of_entropy
    {Ω : Type*} [MeasurableSpace Ω] {S : Type u} [MeasurableSpace S]
    [Fintype S] [MeasurableSingletonClass S]
    (X : Fin 4 → Ω → S) (hX : ∀ i, Measurable (X i))
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    zhangYeungHolds (fun α => H[fun ω => (fun i : α => X i ω) ; μ]) := by
  sorry -- see proof sketch below
```

The bridge is tight: its conclusion consumes M3 at every permutation of the four-element ground set, and the proof is a single application of `zhangYeung` per distinct labeling of (Z, U, X, Y), plus a rewrite of the M1 `delta` in terms of set-function `Finset`-valued entropies. The set-function entropies produce `H[joint RV ; μ]` terms which we then match to M3's unconditional $H$, $I$, $I(\cdot|\cdot)$ notation via a short calculation.

**Scope note:** the bridge lemma is nontrivial (~30-50 tactic lines including the "joint over `α : Finset (Fin 4)`" rewrite). If it threatens to dominate M4's scope, factor into two pieces:

1. A *local* bridge that states the single-labeling version: `zhangYeungAt (F := entropy_fn) 2 3 0 1 = zhangYeung (X 0) (X 1) (X 2) (X 3) μ` (one direction), proved by direct entropy arithmetic.
1. A *full* bridge that quantifies over `Equiv.Perm (Fin 4)` (for all 24 labelings).

Land the local single-labeling bridge in M4; defer the full `zhangYeungHolds_of_entropy` to a follow-up if the local bridge lands cleanly and there is spare budget. If even the local bridge threatens to sprawl, park it entirely and note in the module docstring that the interpretation "F is not an entropy function" follows informally from M3; upstream the bridge in a later milestone. The checkpoint theorem `shannon_incomplete` does not depend on the bridge.

### Optional extension: `n ≥ 4`

Roadmap §M4 mentions extending the counterexample to $n \ge 4$ via embedding. The statement is:

```lean
theorem shannon_incomplete_ge_four (n : ℕ) (hn : 4 ≤ n) :
    ∃ F : Finset (Fin n) → ℝ, shannonCone_n F ∧ ¬ zhangYeungHolds_n F
```

where `shannonCone_n` and `zhangYeungHolds_n` are the `Fin n`-indexed analogues of `shannonCone` and `zhangYeungHolds`. The proof: lift $F_{\text{witness}}$ along the canonical embedding `Fin 4 ↪ Fin n` by $F_n(\alpha) := F_{\text{witness}}(\alpha \cap \text{image}(\text{Fin 4} \hookrightarrow \text{Fin n}))$. The Shannon cone check reduces to the $n = 4$ case plus monotonicity of `Finset.filter`. The Zhang-Yeung violation lifts by choosing the permutation that places (Z, U, X, Y) at the four embedded coordinates.

**Scope note:** this is a mechanical but nontrivial exercise (the `Fin 4 ↪ Fin n` bookkeeping is the main fiddly bit). M4 does *not* include this as a core deliverable; if the core lands with headroom, attempt the extension, otherwise file a follow-up plan. The roadmap checkpoint is only the $n = 4$ `shannon_incomplete`, not the general-$n$ version.

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

### Section structure inside `ZhangYeung/Theorem4.lean`

```text
├── Module docstring (## Main definitions, ## Main statements, ## Implementation notes, ## References, ## Tags)
├── Imports: ZhangYeung.Theorem3 (pulls in the entire M1-M3 stack via its own imports)
├── namespace ZhangYeung
├── section SetFunctionCalculus
│     - `def I_F` (unconditional set-function MI)
│     - `def condI_F` (conditional set-function MI)
│     - `def delta_F` (set-function ZY delta)
│     - 3-5 simp lemmas collapsing `I_F`, `condI_F`, `delta_F` on Finset literals
│         when the arguments are concrete; kept private
├── section ShannonCone
│     - `def shannonCone`
│     - (no lemmas beyond the definition; consumers destructure directly)
├── section ZhangYeungPredicate
│     - `def zhangYeungAt`
│     - `def zhangYeungHolds`
├── section Witness
│     - `def F_witness_ℚ : Finset (Fin 4) → ℚ`
│     - `def F_witness : Finset (Fin 4) → ℝ := fun S => F_witness_ℚ S`
│     - `lemma shannonCone_of_witness`
│     - `lemma not_zhangYeungHolds_witness`
├── section Main
│     - `theorem shannon_incomplete : ∃ F, shannonCone F ∧ ¬ zhangYeungHolds F`
├── section Bridge (optional per §8; scope gate documented below)
│     - `theorem zhangYeungAt_of_entropy` (single-labeling bridge)
│     - `theorem zhangYeungHolds_of_entropy` (full bridge)
└── end ZhangYeung
```

The module docstring follows the M3 template: opening paragraph stating role, `## Main definitions` listing `F_witness_ℚ`, `shannonCone`, `zhangYeungHolds`; `## Main statements` listing `shannon_incomplete`, `shannonCone_of_witness`, `not_zhangYeungHolds_witness`; `## Implementation notes` explaining the `ℚ → ℝ` cast strategy, the `Equiv.Perm (Fin 4)` choice in `zhangYeungHolds`, and the bridge-lemma scope decision; `## References` pointing at lines 358-388 of the transcription (Theorem 4 + witness); and `## Tags`.

## Sequencing: commits

Each commit maintains a green build + lint + test. Each commit is a conventional-commit-styled small unit.

1. **Bootstrap + pre-flight checks.** In the `m4-theorem-4` worktree: `bin/bootstrap-worktree`; confirm `make check` is green with M1 + M1.5 + M2 + M3 on `main`. Run one pre-flight experiment in a scratch `.lean` file (delete after):

    - **`decide` performance rehearsal.** Instantiate a three-line toy `F : Finset (Fin 4) → ℚ` and run `example : ∀ α β : Finset (Fin 4), α ⊆ β → F α ≤ F β := by decide`. Confirm elaboration is under 3 seconds without a heartbeat bump. If it exceeds ~15 seconds, pivot the Shannon-cone proof to the fallback tactic pattern described in §6 (case-split on `Finset.card α, Finset.card β`). Log the rehearsal outcome in the first commit message of step 3.

    Halt on failure; investigate before writing module code.

1. **Scaffold `ZhangYeung/Theorem4.lean` and `ZhangYeungTest/Theorem4.lean` in the same change.** Add the module docstring, imports (`ZhangYeung.Theorem3` only), the empty `namespace ZhangYeung`, and `sorry` stubs for `F_witness_ℚ`, `shannonCone`, `zhangYeungHolds`, `shannon_incomplete`. Add the matching signature-pinning `example`s in `ZhangYeungTest/Theorem4.lean` (one per public definition/theorem stub). Wire both top-level re-export files (`ZhangYeung.lean`, `ZhangYeungTest.lean`). Confirm `lake build ZhangYeung.Theorem4`, `lake build ZhangYeung`, `lake build ZhangYeungTest`, and `lake test` all pass. Commit as `feat: scaffold Theorem 4 module and API tests`.

1. **Land the set-function calculus: `I_F`, `condI_F`, `delta_F`.** Three one-line definitions. No lemmas (yet). Commit as `feat(theorem4): add set-function information-theoretic calculus`.

1. **Land `shannonCone` and `zhangYeungAt`, `zhangYeungHolds`.** Three definitions in sequence. `shannonCone`: the three conditions of paper eq. (11). `zhangYeungAt`: the single-labeling inequality (paper eq. 21). `zhangYeungHolds`: the `Equiv.Perm` quantification (paper eq. 25). Commit as `feat(theorem4): add shannonCone and zhangYeungHolds predicates`.

1. **Land the witness `F_witness_ℚ`.** Single definition, five cases as in §8 above. Commit as `feat(theorem4): add Zhang-Yeung 1998 Theorem 4 counterexample witness`.

1. **Prove `shannonCone_of_witness` via `decide` + `exact_mod_cast`.** ~10 tactic lines. If the pre-flight rehearsal (step 1) flagged performance issues, apply the case-enumeration fallback here instead; budget ~60 lines in that case. Commit as `feat(theorem4): prove witness lies in the Shannon cone`.

1. **Prove `not_zhangYeungHolds_witness` via permutation specialization + `norm_num`.** ~15 tactic lines. Specialize at `σ = (0 2)(1 3)`, then reduce to concrete `ℝ` arithmetic using the witness evaluation + `norm_num`. Commit as `feat(theorem4): prove witness violates Zhang-Yeung at the canonical labelling`.

1. **Land the headline theorem `shannon_incomplete`.** Three-line proof consuming the two lemmas from steps 6-7. Commit as `feat(theorem4): derive Shannon incompleteness corollary (Theorem 4)`.

1. **Expand `ZhangYeungTest/Theorem4.lean` to cover the full public API.** Signatures were pinned in step 2; expand with:
    - A signature-pinning `example` for `shannon_incomplete` with the exact roadmap-stated signature.
    - A signature-pinning `example` for `shannonCone_of_witness` and `not_zhangYeungHolds_witness`.
    - A concrete-arithmetic test: state that `F_witness_ℚ` evaluates to the expected integers on each of the 16 concrete subsets. Closes by 16 `rfl`/`decide` per-subset evaluations or one `decide` over `Finset.univ`.
    - A theorem-application test: reconstruct the violation from scratch using the public API (compute `delta_F F_witness 2 3 0 1`, compute the RHS, and `linarith` the contradiction). Cross-checks that a downstream consumer can reconstruct the violation without peeking into the witness proof.

    Commit as `test: cover Theorem 4 API surface`.

1. **(Optional) Land the bridge lemma `zhangYeungAt_of_entropy` (single-labeling).** ~30-50 tactic lines. If this exceeds budget, drop to step 11 without the bridge. Commit as `feat(theorem4): bridge single-labeling ZY from entropy via M3`.

1. **Update `AGENTS.md` (aka `CLAUDE.md`) Module Layout.** Add one line pointing to `ZhangYeung/Theorem4.lean` and one line pointing to `ZhangYeungTest/Theorem4.lean`. Amend the `ZhangYeung.lean` entrypoint bullet to include the new re-export. Commit as `docs: document Theorem 4 module in CLAUDE.md`.

1. **Run `make check`.** Address any remaining lint or build issues, and update `cspell-words.txt` with any new tokens introduced in docstrings (likely a few: "counterexample", "tildeΓ", "elemental"). Commit any cspell/lint adjustments as `chore: address lint feedback`.

1. **Move the plan from `todo/` to `done/`** in the same commit that lands the milestone's final polish. Commit as `chore: move completed M4 plan from todo to done`.

1. **Open the PR.** Title: `feat: prove Theorem 4, Shannon incompleteness`. Body links this plan and the roadmap, summarizes the public surface (`shannonCone`, `zhangYeungHolds`, `F_witness_ℚ`, `shannon_incomplete`), calls out the connection to M3 via the bridge lemma (if landed) or notes it as a future extension (if not), and summarizes the `ℚ`-cast-to-`ℝ` design choice.

If the `shannonCone_of_witness` proof in step 6 sprawls past 60 lines without closing, halt and reconsider: either pivot to an explicit case enumeration by cardinality, or pre-compute the 16 `F_witness_ℚ` values as separate `@[simp]` lemmas and reduce the Shannon-cone check to an arithmetic simp. If the ZY-violation proof in step 7 sprawls past 25 lines, halt and reconsider: the subset `{0, 1, 2, 3}` is concrete; `norm_num` should handle the arithmetic after unfolding one layer of `F_witness_ℚ`. If `decide` is pathologically slow (>60s), apply the fallback documented in Risk §11.1.

## Open questions and known risks

### 11.1 `decide` performance on `Finset (Fin 4) × Finset (Fin 4) → Prop` (moderate)

The Shannon-cone verification attempts `decide` on `∀ α β : Finset (Fin 4), ..., ... ≤ ...` with `F_witness_ℚ` as the witness. This is 16 × 16 = 256 cases, each of which elaborates through the `if ... else` branches of `F_witness_ℚ` five times per side. Most Lean 4 `decide` calls at this scale are under a second, but pathological cases have been observed (particularly when `Finset` decidability reduces through a chain of `Finset.insert` unfolds rather than a flat `Finset.decidableMem`).

**Mitigation (try in order):**

1. Run the pre-flight rehearsal in sequencing step 1 before writing the real Shannon-cone proof. Log the outcome. If it is under 3 seconds, proceed with the `decide`-based proof as planned.
1. If `decide` is in the 3-30 second range, leave it as-is but wrap the three sub-goals in a `set_option maxHeartbeats` bump local to the lemma (not module-wide). Split the three clauses into three separate lemmas (`shannonCone_of_witness_empty`, `shannonCone_of_witness_monotone`, `shannonCone_of_witness_submodular`) so that each `decide` runs in its own heartbeat bucket. Per the user's `feedback_lean_split_before_bump.md`, split *before* bumping; only bump if splitting alone does not help.
1. If `decide` is >30 seconds or hits the kernel reducer's stack limit, pivot to the case-enumeration fallback: do `match α.card, β.card with` on the five-valued cardinality, then within each case `match α, β with` on the literal value (16 per cardinality level, or fewer by symmetry). Closes each case by `simp [F_witness_ℚ] + norm_num`. Budget ~60-100 lines in that fallback.
1. Last resort: define an explicit `List` of all 16 Finsets of `Fin 4` and verify the cone conditions on the product of that list with itself. `List.forall₂_iff` + `decide` on a flat list of rational comparisons tends to be faster than `decide` on the `Finset`-wrapped version.

### 11.2 `Finset` literal elaboration under `Fin 4` (low)

Writing `{0, 1, 2} : Finset (Fin 4)` requires Lean to (a) infer `Fin 4` for each literal, (b) find a `DecidableEq` for deduplication in the `insert` chain. Mathlib handles this uniformly, but the `OfNat` resolution may produce unnecessary `@[simp]` noise when we unfold `F_witness_ℚ` on these literals.

**Mitigation:** if `norm_num [F_witness_ℚ]` leaves stray `Nat` / `Fin` casts, prepend `push_cast` or `simp only [Fin.val_zero, Fin.val_one, ...]` to normalize. Prefer to introduce local `set`-statements (`set S := ({0, 1, 2} : Finset (Fin 4))`) only if elaboration is genuinely stuck; do not pre-emptively bind every literal.

### 11.3 `zhangYeungHolds` over `Equiv.Perm (Fin 4)` (low)

Quantifying over `Equiv.Perm (Fin 4)` (size 24) rather than over "all distinct 4-tuples" (size 4! = 24, same count) is slightly more ergonomic for the paper-alignment and slightly more awkward for the violation proof (we have to construct a specific permutation, rather than supply four distinct indices). The two formulations are equivalent and either works; the plan chooses `Equiv.Perm` to match paper eq. (25) literally.

**Mitigation:** if the `Equiv.swap 0 2 * Equiv.swap 1 3` normalization in `not_zhangYeungHolds_witness` is finicky, pivot to the "distinct 4-tuples" formulation. Keep the decision consistent with the `zhangYeungHolds_of_entropy` bridge (they must use the same predicate); if either side of the bridge is harder in one formulation, pick the other.

### 11.4 Bridge lemma scope sprawl (moderate)

The bridge `zhangYeungHolds_of_entropy` requires wrapping M3's `zhangYeung` in a setting where `X, Y, Z, U` come from a family `X : Fin 4 → Ω → S`. The M3 theorem takes four random variables at four *different* codomain types (`S₁, S₂, S₃, S₄`); the bridge needs them all at the same type `S`. For `zhangYeungHolds_of_entropy` over all permutations, we apply M3 at 24 labelings; each application needs a separate measurability proof for the tuple projection. The joint-entropy-over-a-`Finset` also requires one technical lemma linking `H[fun ω => (fun i : α => X i ω) ; μ]` to the standard `H[⟨X₁, X₂, ⟨X₃⟩⟩ ; μ]`-style joint, which is where the bookkeeping concentrates.

**Mitigation:**

1. Start with the *single-labeling* bridge (named `zhangYeungAt_of_entropy`) at the canonical `(Z, U, X, Y) = (2, 3, 0, 1)` labeling only. This is a single M3 application plus one rewrite from `delta` to `delta_F`. ~15-30 tactic lines. Ship this; defer the full permutation-quantified bridge to an optional step.
1. If even the single-labeling bridge requires a nontrivial joint-entropy-over-a-`Finset` lemma, note it in the docstring as "informal consequence of M3" and ship M4 without the Lean bridge. The `shannon_incomplete` theorem stands alone.
1. If the bridge becomes necessary but large, factor it into a new file `ZhangYeung/EntropyFunction.lean` containing the set-function-of-entropies construction; import from `Theorem4.lean`. This isolates the bookkeeping. Do not do this preemptively.

### 11.5 `ℚ → ℝ` cast friction at the statement boundary (low)

The main theorem is stated over `ℝ` (the convention of M1-M3) but the witness is over `ℚ` (for `decide`). The cast is uniform: `fun S => ((F_witness_ℚ S : ℚ) : ℝ)`. Any `simp`-normal-form of this should reduce to the same numerical values as `F_witness_ℚ`. Potential snags: `Rat.cast_ite` or the `if ... then ... else ...` under the cast may need a manual `simp only [Rat.cast_ite, Rat.cast_ofNat, Rat.cast_zero]`.

**Mitigation:**

1. Define `F_witness : Finset (Fin 4) → ℝ := fun S => (F_witness_ℚ S : ℝ)` as its own named definition with a docstring pointing at `F_witness_ℚ`. This makes `simp` work on either surface uniformly.
1. Land a one-line lemma `F_witness_eq_cast : F_witness S = (F_witness_ℚ S : ℝ) := rfl` to make the cast bridgeable inside downstream tactic proofs without peeling the definition.

### 11.6 `Finset.univ : Finset (Fin 4)` vs `{0, 1, 2, 3} : Finset (Fin 4)` (low)

When we need to talk about the full set `{0, 1, 2, 3}`, both `Finset.univ` and the literal `{0, 1, 2, 3}` elaborate to the same term up to `Finset`-structure but are *syntactically* different. `decide` and `simp` both handle the reconciliation via `Finset.ext_iff`, but `norm_num` may not; explicit `show` calls may be needed.

**Mitigation:** use `Finset.univ` consistently in the witness definition (`S = Finset.univ` rather than `S = {0, 1, 2, 3}`). At the ZY-violation arithmetic step, if `Finset.univ` appears where we want `{0, 1, 2, 3}`, close the gap with `show Finset.univ = ({0, 1, 2, 3} : Finset (Fin 4)) by decide`.

### 11.7 Entropy-function-of-`Finset` encoding (moderate; only relevant if bridge lands)

The bridge `zhangYeungHolds_of_entropy` needs a definition for "joint entropy of the random variables indexed by `α : Finset (Fin 4)`". The natural candidate is `H[fun ω => (fun i : α => X i ω) ; μ]` where `α : Finset (Fin 4)` is coerced to a type. This is what the planned bridge-lemma signature uses, but it elaborates through `Finset.coe_sort`, which is a `Finset`-to-`Subtype` conversion that PFR's entropy notation may not simplify through automatically.

**Mitigation:** state the bridge using `H[fun ω => α.val.map (fun i => X i ω) ; μ]` (using `α.val : Multiset (Fin 4)`) or manually enumerate the joint entropy as a nested pair via `Finset.rec`. The cleanest option may be to specialize the bridge to the single labeling that fires in the contradiction, avoiding the general joint-entropy-over-a-`Finset` machinery. This is the "local bridge first" mitigation from §11.4.

### 11.8 PFR API churn (low, carried forward)

Same as M2-M3 risk. This project treats PFR as a permanent pinned dependency (roadmap §3). M4 consumes only `zhangYeung` from M3 plus standard `Finset` and `Rat` Mathlib; PFR changes would not affect the core M4 theorems. The bridge lemma consumes PFR's entropy/mutualInfo/condMutualInfo API (inherited from M3); if PFR churns, the bridge follows the same update cadence as M3 did.

## Verification

Per the roadmap M4 checkpoint: `theorem shannon_incomplete : ∃ F, shannonCone F ∧ ¬ zhangYeungHolds F`, and the witness test module builds.

Operationally:

- `lake build ZhangYeung.Theorem4` compiles with no warnings, no `sorry`, no `admit`.
- `lake build ZhangYeung` compiles with `ZhangYeung.lean` re-exporting `ZhangYeung.Theorem4` cleanly.
- `lake build ZhangYeungTest.Theorem4` compiles; the test module imports only `ZhangYeung` and not `ZhangYeung.Theorem4` directly, exercising the public API surface.
- `lake build` and `lake test` both succeed on the default targets; CI goes green.
- `lake lint` passes (batteries linter via the `lintDriver`).
- `make check` passes in full.

**Test module contents** (`ZhangYeungTest/Theorem4.lean`, established incrementally in sequencing steps 2 and 9):

1. Signature-pinning `example`s for each of the public definitions and theorems: `F_witness_ℚ`, `shannonCone`, `zhangYeungHolds`, `shannonCone_of_witness`, `not_zhangYeungHolds_witness`, `shannon_incomplete`. Six `example`s.
1. Concrete-arithmetic witness evaluation: for each of the 16 `Finset (Fin 4)` subsets, assert the expected `F_witness_ℚ` value. Closes by per-subset `rfl`/`decide` or one holistic `decide` over `Finset.univ`.
1. Theorem-application test: reconstruct the Zhang-Yeung violation from scratch using the public API. Compute `delta_F F_witness 2 3 0 1` and the RHS of eq. (21) at the canonical labeling, use `norm_num` to collapse both sides to specific rationals, and close by `linarith` that `1 ≤ 1/2` is false. Cross-checks that a downstream consumer can reconstruct the violation without peeking into the witness proof.
1. (If the bridge lemma lands) Signature-pinning `example` for `zhangYeungAt_of_entropy` (single-labeling bridge). Confirms the expected hypothesis shape and conclusion type.

Each `example` lives inside `namespace ZhangYeungTest` with `open ZhangYeung`, following the `ZhangYeungTest/Delta.lean`, `ZhangYeungTest/Theorem2.lean`, `ZhangYeungTest/CopyLemma.lean`, and `ZhangYeungTest/Theorem3.lean` precedents.

Land these in the same commits as the corresponding public surface (signatures in step 2, per-subset and theorem-application tests in step 9), so `lake test` exercises the public API continuously through the milestone.

**Out-of-scope for M4** (documented here so M5 and beyond can pick them up):

- No $n \ge 4$ extension in the core milestone (see §8 "Optional extension" and §11 risk analysis). May land as an optional step if there is budget.
- No closure argument for $\bar{\Gamma}^*_4 \neq \Gamma_4$; M4 states the weaker $F \notin \text{(entropy function of any 4 RVs)}$ corollary via the bridge lemma (and informally notes the closure extension is routine).
- No $\hat{\Gamma}_4$ inner-bound material (paper Theorem 6). Roadmap §M4 excluded this from S2 scope.
- No upstreaming of `shannonCone` or `zhangYeungHolds` to Mathlib. Both stay local to `ZhangYeung` unless later work demonstrates external demand.

## Critical files

**This milestone:**

- `ZhangYeung/Theorem4.lean` (new).
- `ZhangYeungTest/Theorem4.lean` (new).
- `ZhangYeung.lean` (modified, add one `import` line).
- `ZhangYeungTest.lean` (modified, add one `import` line).
- `AGENTS.md` / `CLAUDE.md` (modified, two-line addition under "Module Layout", plus an entrypoint-manifest update).

**Read-only references:**

- `ZhangYeung/Theorem3.lean` (M3 output; `zhangYeung`, `zhangYeung_dual`, `zhangYeung_averaged`, the three public theorems).
- `ZhangYeung/Delta.lean` (M1 output; `ZhangYeung.delta` and form-conversion lemmas, consumed only by the bridge lemma).
- `ZhangYeung/CopyLemma.lean`, `ZhangYeung/Theorem2.lean`, `ZhangYeung/Prelude.lean` (M1-M2.5 outputs; style precedent, not consumed directly by M4 core).
- `references/transcriptions/zhangyeung1998.md` (paper transcription; Theorem 4 statement on lines 358-388, basic inequalities on lines 466-480, $\tilde{\Gamma}_4$ definition on lines 339-355).
- `.lake/packages/pfr/PFR/ForMathlib/Entropy/Basic.lean` (Shannon entropy primitives, consumed only by the bridge lemma).
- `.lake/packages/mathlib/Mathlib/Data/Finset/Basic.lean` and `.lake/packages/mathlib/Mathlib/Data/Finset/Powerset.lean` (`Finset` operations, decidability instances).
- `.lake/packages/mathlib/Mathlib/Logic/Equiv/Perm.lean` (permutations, `Equiv.swap`).
- `docs/plans/done/2026-04-18-theorem-3-zhang-yeung-inequality.md` (M3 plan; style precedent for this plan).
- `docs/plans/done/2026-04-17-copy-lemma.md` (M2 plan; additional style precedent and universe-bookkeeping note carried forward).

Reference: the `write-lean-code` skill is authoritative for Lean naming and proof style; the `write-math` skill governs the module docstring and any mathematical prose inside comments; the `write-pandoc-markdown` skill governs this plan document; the `write-formalization-roadmap` skill and the existing M2/M3 plan documents are the authoritative templates for this plan's structure.
