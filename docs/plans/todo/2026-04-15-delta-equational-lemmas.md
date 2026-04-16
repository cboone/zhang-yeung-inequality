---
title: "M1: Delta Equational Lemmas"
created: 2026-04-15
branch: formalize/delta-equational-lemmas
roadmap: docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md
milestone: M1
depends_on: M0 (branch `chore/scaffold-project`)
---

## Context

The Zhang-Yeung roadmap (§6) decomposes the formalization into milestones M0-M7. M0 scaffolds the Lake project and imports PFR's entropy API; M1 introduces the central quantity of the paper.

The **Zhang-Yeung delta** is

$$
\Delta(Z, U \mid X, Y) \;:=\; I(Z ; U) - I(Z ; U \mid X) - I(Z ; U \mid Y). \qquad (20)
$$

It measures how much the mutual information between $Z$ and $U$ exceeds the sum of the two conditional versions. The main theorem of the paper (eq. 23) is an upper bound on this quantity; its full proof rests on the copy lemma (M2) and is carried out in M3. **M1 only handles the purely equational content**: the definition and the algebraic identities that relate $\Delta$ to raw entropy terms and that express equivalences between the three inequality forms (21), (22), (23).

The value of landing these lemmas before M2 is twofold. First, `Delta.lean` gives M3 a ready-made vocabulary of rearrangements so the copy-lemma proof never has to re-derive linear identities; it just cites an equational lemma and closes the arithmetic with `linarith`. Second, many of these lemmas are pure algebra over entropy terms, so they compile and land without waiting for the heavier measure-theoretic work in M2.

## Paper equations this milestone formalizes

The paper presents Theorem 3 in three equivalent forms (pp. 1442-1443):

Equation (20), the definition:

$$
\Delta(Z, U \mid X, Y) \;=\; I(Z ; U) - I(Z ; U \mid X) - I(Z ; U \mid Y).
$$

Equation (21), the asymmetric form favoring $X$:

$$
\Delta(Z, U \mid X, Y) \;\le\; \tfrac{1}{2}\bigl[\, I(X ; Y) + I(X ; ZU) + I(Z ; U \mid X) - I(Z ; U \mid Y)\,\bigr].
$$

Equation (22), the asymmetric form favoring $Y$ (swap $X, Y$ in eq. 21):

$$
\Delta(Z, U \mid X, Y) \;\le\; \tfrac{1}{2}\bigl[\, I(X ; Y) + I(Y ; ZU) - I(Z ; U \mid X) + I(Z ; U \mid Y)\,\bigr].
$$

Equation (23), the symmetric form (average of (21) and (22)):

$$
\Delta(Z, U \mid X, Y) \;\le\; \tfrac{1}{2}\, I(X ; Y) + \tfrac{1}{4}\bigl[\, I(X ; ZU) + I(Y ; ZU)\,\bigr].
$$

Equations (21), (22), (23) are inequalities, not equalities. M1 does **not** prove the inequalities themselves; those follow from the copy lemma in M3. M1 proves the *equational* scaffolding: `delta` unfolds to eq. (20), the three RHS shapes are interderivable by arithmetic, and averaging (21) and (22) yields (23).

## Prerequisites

M0 delivers (verified in worktree `chore/scaffold-project`):

- `lakefile.toml` with `PFR` pinned at `80daaf1`; Lean toolchain `leanprover/lean4:v4.28.0-rc1`.
- `ZhangYeung/Prelude.lean`: `import PFR.ForMathlib.Entropy.Basic` and `open ProbabilityTheory`.
- `ZhangYeung.lean` re-exporting `ZhangYeung.Prelude`.
- `bin/bootstrap-worktree` (runs `lake update`, `lake exe cache get`, `lake build`).
- CI workflow at `.github/workflows/ci.yml` running `lake build` and `lake lint`.
- `CLAUDE.md` documenting the bootstrap script, namespace (`ZhangYeung`), style conventions, and vendored-package exclusions.

Before starting M1 in this worktree: fast-forward merge `chore/scaffold-project` into `formalize/delta-equational-lemmas`, run `bin/bootstrap-worktree`, and confirm `lake build ZhangYeung.Prelude` succeeds against the cached Mathlib/PFR artifacts. Do not attempt to land M1 before M0 merges to main; instead rebase this branch on the scaffold branch.

## PFR API surface used

All definitions live in `ProbabilityTheory` (file: `.lake/packages/PFR/PFR/ForMathlib/Entropy/Basic.lean`):

- `entropy`, notation `H[X ; μ]`.
- `condEntropy`, notation `H[X | Y ; μ]`.
- `mutualInfo`, notation `I[X : Y ; μ]`; definition `mutualInfo_def : I[X : Y ; μ] = H[X ; μ] + H[Y ; μ] - H[⟨X, Y⟩ ; μ]` (`rfl`).
- `condMutualInfo`, notation `I[X : Y | Z ; μ]` (no spaces around the bar).
- `mutualInfo_comm`: `I[X : Y ; μ] = I[Y : X ; μ]`.
- `condMutualInfo_comm`: `I[X : Y | Z ; μ] = I[Y : X | Z ; μ]`.
- `condMutualInfo_eq`: `I[X : Y | Z ; μ] = H[X | Z ; μ] + H[Y | Z ; μ] - H[⟨X, Y⟩ | Z ; μ]` (requires `[Countable U]`, measurability, `[IsZeroOrProbabilityMeasure μ]`, `[FiniteRange Z]`).
- `mutualInfo_nonneg`, `condMutualInfo_nonneg`.

All lemmas with a `FiniteRange` hypothesis apply to `Fintype`-valued random variables (either via a `Fintype -> FiniteRange` instance or by deriving `FiniteRange` directly). We specialize M1 to `Fintype` codomains to keep measurability/finite-range bookkeeping light; the roadmap's risk §7.2 explicitly sanctions this.

## Files

**Create** `ZhangYeung/Delta.lean` (the whole milestone is in this one file).

**Modify** `ZhangYeung.lean` to re-export the new module:

```lean
import ZhangYeung.Prelude
import ZhangYeung.Delta
```

No changes to `ZhangYeung/Prelude.lean` (the M0 version is already sufficient: it imports `PFR.ForMathlib.Entropy.Basic` and opens `ProbabilityTheory`).

No test suite exists in M0. The roadmap leaves test-suite creation for M7; we follow suit and rely on `lake build` for correctness in M1.

## Design: the `delta` definition

### Signature

```lean
variable {Ω : Type*} [MeasurableSpace Ω]
variable {S₁ S₂ S₃ S₄ : Type*}
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]

/-- The Zhang-Yeung delta quantity
`Δ(Z, U | X, Y) := I(Z; U) - I(Z; U | X) - I(Z; U | Y)`.
The main inequality of Zhang and Yeung (1998) bounds this quantity from above by a Shannon-type expression; the inequality is a non-Shannon information inequality. This definition only captures the quantity itself; bounds on it live in `ZhangYeung.Theorem3`. -/
noncomputable def delta
    (Z : Ω → S₁) (U : Ω → S₂) (X : Ω → S₃) (Y : Ω → S₄)
    (μ : Measure Ω := by volume_tac) : ℝ :=
  I[Z : U ; μ] - I[Z : U | X ; μ] - I[Z : U | Y ; μ]
```

Design notes:

- **Variable order** `(Z, U, X, Y)` matches the paper's notation $\Delta(Z, U \mid X, Y)$. The first two arguments are the "measured" pair and the last two are the "conditioning" pair. This is asymmetric to the paper's visual grouping but natural once you read the definition.
- **Four independent type variables** `S₁ S₂ S₃ S₄` rather than collapsing `U`'s codomain onto `X`'s: the paper treats the four RVs as potentially distinct, and forcing identification would complicate the M4 counterexample construction. PFR uses `S T U` for three types; we extend with subscripted `S₁..S₄` to avoid the name clash between `U` (RV) and `U` (its codomain).
- **`noncomputable def`** and **default measure** `(μ := by volume_tac)` mirror PFR's conventions for `mutualInfo` and `condMutualInfo`.
- **Namespace** `ZhangYeung`: avoids polluting `ProbabilityTheory` until the copy lemma (M2) is ready for an upstream attempt. Inside the namespace, lemma names use the unprefixed form `delta_def`, `delta_comm_cond`, etc.; outside the namespace they are `ZhangYeung.delta_def`.

### Notation

Defer a decision on notation `Δ[Z : U | X, Y ; μ]`. Reasons:

1. The unicode `Δ` parses fine as a notation head, but `notation3` priority and scoping interact with PFR's existing `I[...]` and `H[...]` macros. Getting this right risks an afternoon of fiddling for marginal readability gain in M1.
1. M3 will use `delta` in a handful of places; plain function application `delta Z U X Y μ` is fine.
1. If and when we upstream the copy lemma, the notation question becomes a Mathlib-stylebook question rather than a local choice.

Record a TODO in the module docstring: if M3 proofs become hard to read without notation, revisit.

## Design: the equational lemmas

All proofs are one-liners: `rfl`, `simp only [...]; ring`, or `linarith [delta_def ...]`. Each lemma below lists its role downstream (which M3 step or M4 sanity check it unblocks).

### Definitional unfolding

```lean
lemma delta_def (Z : Ω → S₁) (U : Ω → S₂) (X : Ω → S₃) (Y : Ω → S₄) (μ : Measure Ω) :
    delta Z U X Y μ
      = I[Z : U ; μ] - I[Z : U | X ; μ] - I[Z : U | Y ; μ] := rfl
```

The anchor lemma that every other proof cites. Role: lets downstream code unfold `delta` once without `unfold`.

### Symmetries

```lean
lemma delta_comm_cond (Z : Ω → S₁) (U : Ω → S₂) (X : Ω → S₃) (Y : Ω → S₄) (μ : Measure Ω) :
    delta Z U X Y μ = delta Z U Y X μ
```

The definition is symmetric under swapping the two conditioning arguments (addition is commutative). Proof: `simp [delta_def]; ring`. Role: M3 uses this to swap $X, Y$ when deriving eq. (22) from the copy lemma applied the other way around.

```lean
lemma delta_comm_main
    {Z : Ω → S₁} {U : Ω → S₂} (hZ : Measurable Z) (hU : Measurable U)
    (X : Ω → S₃) (Y : Ω → S₄) (μ : Measure Ω) :
    delta Z U X Y μ = delta U Z X Y μ
```

The definition is symmetric under swapping the two "measured" arguments (because mutual information is symmetric). Proof: `simp [delta_def, mutualInfo_comm hZ hU, condMutualInfo_comm hZ hU]`. Role: not strictly needed for M3 but cheap to prove and plausibly used in M5's induction argument.

### Trivial case

```lean
lemma delta_self (Z : Ω → S₁) (U : Ω → S₂) (X : Ω → S₃) (μ : Measure Ω) :
    delta Z U X X μ = I[Z : U ; μ] - 2 * I[Z : U | X ; μ]
```

The case `X = Y`. Proof: `simp [delta_def]; ring`. Role: M3's proof of Theorem 3 sums $\Delta(Z, U \mid X, Y)$ and $\Delta(Z, U \mid X, X_1)$, where $X_1$ is the copy of $X$; the second summand simplifies via this lemma in combination with the copy lemma's `IdentDistrib` facts.

### Expansion into entropy

```lean
lemma delta_eq_entropy
    {Z : Ω → S₁} {U : Ω → S₂} {X : Ω → S₃} {Y : Ω → S₄}
    (hZ : Measurable Z) (hU : Measurable U) (hX : Measurable X) (hY : Measurable Y)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [FiniteRange Z] [FiniteRange U] [FiniteRange X] [FiniteRange Y] :
    delta Z U X Y μ
      = (H[Z ; μ] + H[U ; μ] - H[⟨Z, U⟩ ; μ])
        - (H[Z | X ; μ] + H[U | X ; μ] - H[⟨Z, U⟩ | X ; μ])
        - (H[Z | Y ; μ] + H[U | Y ; μ] - H[⟨Z, U⟩ | Y ; μ])
```

Unfolds `delta` all the way down to raw entropy terms. Proof: `rw [delta_def, mutualInfo_def, condMutualInfo_eq ..., condMutualInfo_eq ...]`. Role: bridge to any future proof that needs to reason at the entropy layer directly (notably the M4 counterexample, where we evaluate all terms on a specific four-RV distribution; the counterexample works at the set-function level so this lemma is the glue).

### Form-(21) equivalence

```lean
/-- Eq. (21) of Zhang-Yeung (1998): the inequality
`Δ(Z, U | X, Y) ≤ (I(X;Y) + I(X;ZU) + I(Z;U|X) - I(Z;U|Y)) / 2`
is equivalent to the compact form `2·I(Z;U) - 3·I(Z;U|X) - I(Z;U|Y) ≤ I(X;Y) + I(X;ZU)`, which is the shape produced by the copy-lemma argument in M3. -/
lemma form21_iff
    (Z : Ω → S₁) (U : Ω → S₂) (X : Ω → S₃) (Y : Ω → S₄) (μ : Measure Ω) :
    2 * delta Z U X Y μ
        ≤ I[X : Y ; μ] + I[X : ⟨Z, U⟩ ; μ] + I[Z : U | X ; μ] - I[Z : U | Y ; μ]
    ↔ 2 * I[Z : U ; μ] - 3 * I[Z : U | X ; μ] - I[Z : U | Y ; μ]
        ≤ I[X : Y ; μ] + I[X : ⟨Z, U⟩ ; μ]
```

Proof: `constructor <;> intro h <;> linarith [delta_def Z U X Y μ]`. Role: in M3 we derive the compact RHS form from the copy lemma; `form21_iff` transports that to the paper's stated eq. (21).

### Form-(22) equivalence

```lean
lemma form22_iff
    (Z : Ω → S₁) (U : Ω → S₂) (X : Ω → S₃) (Y : Ω → S₄) (μ : Measure Ω) :
    2 * delta Z U X Y μ
        ≤ I[X : Y ; μ] + I[Y : ⟨Z, U⟩ ; μ] - I[Z : U | X ; μ] + I[Z : U | Y ; μ]
    ↔ 2 * I[Z : U ; μ] - I[Z : U | X ; μ] - 3 * I[Z : U | Y ; μ]
        ≤ I[X : Y ; μ] + I[Y : ⟨Z, U⟩ ; μ]
```

Analogous to `form21_iff`; obtained by swapping the roles of $X$ and $Y$. Proof: same shape.

### Form-(23) from (21) and (22)

```lean
/-- Eq. (23) of Zhang-Yeung (1998), the symmetric form of Theorem 3, follows from eqs. (21) and (22) by averaging. This lemma contains no measure-theoretic content; the inequalities (21) and (22) are the nontrivial inputs, proved in M3 via the copy lemma. -/
lemma form23_of_form21_form22
    {Z : Ω → S₁} {U : Ω → S₂} {X : Ω → S₃} {Y : Ω → S₄} {μ : Measure Ω}
    (h21 : 2 * delta Z U X Y μ
        ≤ I[X : Y ; μ] + I[X : ⟨Z, U⟩ ; μ] + I[Z : U | X ; μ] - I[Z : U | Y ; μ])
    (h22 : 2 * delta Z U X Y μ
        ≤ I[X : Y ; μ] + I[Y : ⟨Z, U⟩ ; μ] - I[Z : U | X ; μ] + I[Z : U | Y ; μ]) :
    4 * delta Z U X Y μ
      ≤ 2 * I[X : Y ; μ] + I[X : ⟨Z, U⟩ ; μ] + I[Y : ⟨Z, U⟩ ; μ]
```

Proof: `linarith`. Role: the bridge from M3's proof (which will likely produce eq. 21 and its $X \leftrightarrow Y$ swap) to the symmetric form the paper (and the roadmap's Theorem 3 signature) states.

We state the conclusion with a factor of $4$ rather than $1/2$ and $1/4$ to keep the Lean arithmetic integer-scaled. A companion `form23_iff` can wrap this in the scaled form if M3 prefers to match the paper verbatim:

```lean
lemma form23_iff
    (Z : Ω → S₁) (U : Ω → S₂) (X : Ω → S₃) (Y : Ω → S₄) (μ : Measure Ω) :
    4 * delta Z U X Y μ
        ≤ 2 * I[X : Y ; μ] + I[X : ⟨Z, U⟩ ; μ] + I[Y : ⟨Z, U⟩ ; μ]
    ↔ delta Z U X Y μ
        ≤ (1/2) * I[X : Y ; μ] + (1/4) * (I[X : ⟨Z, U⟩ ; μ] + I[Y : ⟨Z, U⟩ ; μ])
```

Proof: `constructor <;> intro h <;> linarith`.

### Upper bound from nonnegativity (optional)

```lean
lemma delta_le_mutualInfo
    {Z : Ω → S₁} {U : Ω → S₂} {X : Ω → S₃} {Y : Ω → S₄}
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω)
    [FiniteRange Z] [FiniteRange U] :
    delta Z U X Y μ ≤ I[Z : U ; μ]
```

From `condMutualInfo_nonneg` applied twice and the definition. Not strictly required for M3 but gives a sanity-check bound; if the proof needs more hypotheses than expected, skip.

## Sequencing inside M1

1. **Bootstrap verification.** Merge `chore/scaffold-project` into `formalize/delta-equational-lemmas`; run `bin/bootstrap-worktree` and `lake build ZhangYeung`. Halt if Mathlib or PFR fails to fetch from cache.
1. **Create `ZhangYeung/Delta.lean`** with module docstring, imports, `variable` block, and the `delta` definition. Build and confirm.
1. **Land the trivial lemmas**: `delta_def`, `delta_comm_cond`, `delta_self`. Each is `rfl` or one-line algebra; failure here signals a deeper setup problem.
1. **Land `delta_comm_main`.** First lemma that pulls in measurability and PFR's commutativity lemmas; resolves whether `Measurable` hypotheses need to be explicit or can be implicit via `variable`. The choice propagates to later lemmas.
1. **Land the entropy-expansion lemma `delta_eq_entropy`.** First use of `condMutualInfo_eq`, which wants `[IsProbabilityMeasure μ]`, `[FiniteRange ...]`. Confirm that a `Fintype` codomain yields `FiniteRange` by instance search, or add the assumption to the `variable` block explicitly.
1. **Land the form-equivalence lemmas `form21_iff`, `form22_iff`, `form23_iff`** and the bridging lemma `form23_of_form21_form22`. All are pure algebra via `linarith`; the only risk is that PFR's `⟨Z, U⟩` syntax for pair random variables requires a specific elaboration path (`Prod.mk ∘ (Z, U)` vs. `fun ω => (Z ω, U ω)`). Verify by successful compile.
1. **Consider `delta_le_mutualInfo`.** If it falls out cleanly, add it; otherwise drop it to keep the milestone crisp.
1. **Update `ZhangYeung.lean`** to `import ZhangYeung.Delta`.
1. **Run `lake build ZhangYeung && lake lint`** to close the milestone.

Commit at each numbered step. Keep commits small and conventional-commit-styled (`feat:`, `chore:`).

## Open questions and known risks

- **`FiniteRange` vs. `Fintype`.** PFR's lemmas require `[FiniteRange X]`. In practice, `X : Ω → S` with `[Fintype S]` should resolve via an existing instance, but if not, we add `[FiniteRange Z] [FiniteRange U] [FiniteRange X] [FiniteRange Y]` to the `variable` block and let the end-user supply them. Resolution: check `.lake/packages/PFR/PFR/ForMathlib/FiniteRange/Defs.lean` for an `instance : FiniteRange X` derived from `Fintype`; follow PFR's lead either way.
- **`⟨Z, U⟩` syntax for the paired random variable.** Lean's anonymous-constructor heuristic may or may not elaborate `⟨Z, U⟩` as `fun ω => (Z ω, U ω)` in the context of `I[X : ⟨Z, U⟩ ; μ]`. PFR uses this notation throughout `Basic.lean`, so it works there; we just mirror their usage and rely on the same elaboration path. If ambiguity arises, fall back to `(fun ω => (Z ω, U ω))`.
- **`Measurable` hypothesis hygiene.** PFR declares `Measurable` assumptions on random variables via explicit function arguments rather than through the `variable` block. Follow that style for consistency: pass measurability as a hypothesis on lemmas that need it (e.g. `delta_comm_main`, `delta_eq_entropy`), and omit it where `rfl` or `linarith` close the goal without it.
- **Notation `Δ[...]`** is deferred as above; revisit after M3 if proofs become hard to scan without it.

Reference: the `write-lean-code` skill is authoritative for naming and proof style; the `write-math` skill governs the module docstring and any prose inside comments; the `write-pandoc-markdown` skill governs this plan document.

## Verification

Per the roadmap checkpoint: "each equational form reduces to `ring_nf`/`linarith` over entropy terms." Operationally:

- `lake build ZhangYeung.Delta` compiles with no warnings or `sorry`.
- `lake build ZhangYeung` (full library) compiles, confirming `ZhangYeung.lean` re-exports cleanly.
- `lake lint` passes (batteries linter, called via `lake lint` target; see M0's `lakefile.toml`).
- Spot-check each lemma's proof script is one of: `rfl`, `simp only [...]; ring`, `constructor <;> intro h <;> linarith [...]`, or a linear combination thereof. Anything longer signals over-engineering.
- CI (`.github/workflows/ci.yml`) goes green on push.

Out-of-scope for M1 (documented here so the next milestone can pick them up):

- No test suite (deferred to M7, per roadmap).
- No notation macro for `delta` (deferred pending M3 readability assessment).
- No proof of any inequality form; all six `form*_iff` lemmas are `↔` between two forms of the same inequality, not a proof that either holds. The actual inequality is M3's responsibility.
- No bridge to `shannon-entropy`'s `entropyNat` (roadmap §9, item 8).

## Critical files

- `ZhangYeung/Delta.lean` (new, this milestone).
- `ZhangYeung.lean` (modified, add one import line).
- `ZhangYeung/Prelude.lean` (read-only; M0 has already set it up correctly).
- `.lake/packages/PFR/PFR/ForMathlib/Entropy/Basic.lean` (read-only; the PFR API surface).
