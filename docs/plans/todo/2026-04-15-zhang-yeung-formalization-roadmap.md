# Zhang-Yeung Inequality Formalization Roadmap

**Created:** 2026-04-15
**Target:** Lean 4 / Mathlib 4
**Paper:** Zhang & Yeung, "On Characterization of Entropy Function via Information Inequalities," *IEEE TIT* 44(4), July 1998, pp. 1440-1452.
**Source PDF:** `references/papers/zhangyeung1998.pdf`
**Source transcription:** `references/transcriptions/zhangyeung1998.md` (verified 2026-04-16)

**Resolved decisions:**

- **Scope:** S2 + Theorem 5 (stretch). Theorems 3, 4 as core; Theorem 5 (n+2-variable generalization) as stretch.
- **Dependency:** Permanent PFR dependency for Shannon entropy primitives. Pinned rev in `lakefile.toml`; upgrades are deliberate, not scheduled.
- **Blueprint:** No. Lean-only.
- **Mathlib intent:** Copy lemma yes (designed for upstream). Rest of proof stays local.

## 1. Context

The Zhang-Yeung inequality is the first known *non-Shannon-type* information inequality. Its discovery proved that the Shannon "basic" inequalities (nonnegativity of entropy, conditional entropy, and conditional mutual information) do not fully characterize the set of entropic functions for n >= 4 discrete random variables. The paper contains four main results:

- **Theorem 3** (the Zhang-Yeung inequality). For any four discrete random variables X, Y, Z, U, writing Delta(Z, U | X, Y) := I(Z; U) - I(Z; U | X) - I(Z; U | Y), the inequality (paper's eq. 21)
  Delta(Z, U | X, Y) <= (1/2) [I(X; Y) + I(X; Z, U) + I(Z; U | X) - I(Z; U | Y)]
  holds, and it does not follow from the basic Shannon inequalities. The left side is symmetric in X, Y, but the right side is not; swapping X <-> Y yields the dual form (22), and averaging (21) and (22) gives the symmetric corollary (23):
  Delta(Z, U | X, Y) <= (1/2) I(X; Y) + (1/4) [I(X; Z, U) + I(Y; Z, U)].
  The paper also restates Theorem 3 in atom coordinates (eq. 39) as S_F(1,2|3,4) + F[1,3|4] + F[1,4|3] + F[3,4|1] >= 0; the standard entropy-coordinate form is used throughout this roadmap.
- **Theorem 4.** The closure of the set of constructible entropy functions is strictly smaller than the Shannon outer bound: cl(Gamma*_n) != Gamma_n for n >= 4 (immediate corollary of Theorem 3).
- **Theorem 5.** Generalization of Theorem 3 to n + 2 random variables (same proof strategy; the paper omits the proof, noting it uses the Theorem 3 idea plus induction).
- **Theorem 6.** A nontrivial inner bound on cl(Gamma*_4), via seven explicit probabilistic constructions and a ~5-page case analysis.

The central proof technique is what modern information theory calls the **copy lemma**. The paper splits it into two pieces: equation (44) defines the auxiliary distribution q(x, y, z, u, x_1, y_1) := p(x, y, z, u) p(x_1, y_1, z, u) / p(z, u) by kernel composition, and Lemma 2 (eq. 45) is the resulting *identity* expressing Delta(Z, U | X, Y) in the six-variable joint. Together they give: (X, Y_1, Z, U) and (X_1, Y, Z, U) each have the original joint law, and I(X; Y_1 | Z, U) = 0 (conditional independence of the two copies given (Z, U)). Once this auxiliary distribution exists, Theorem 3 follows from a mechanical Shannon-inequality chase.

**Why formalize this?** No proof assistant (Lean, Coq/Rocq infotheo, Isabelle/HOL Hoelzl, HOL4, Mizar, HOL Light) has formalized any non-Shannon-type inequality. This would be a first. It is also the natural entry point to a family of follow-on results (Matus, Dougherty-Freiling-Zeger, Kinser, Chan-Yeung group-theoretic), all of which rest on the same copy-lemma infrastructure. Formalizing the copy lemma cleanly is therefore the highest-leverage artifact this project can produce.

## 2. State of the Art

### 2.1 Mathlib 4

Already upstream and directly usable (verified 2026-04-15):

- `Mathlib.MeasureTheory.Measure.ProbabilityMeasure`, `Mathlib.Probability.Distributions.Uniform` (finite-support RVs via `PMF`).
- `Mathlib.Probability.ConditionalProbability` (`ProbabilityTheory.cond`, Bayes, total probability).
- `Mathlib.Probability.Kernel.Basic`, `.Composition.MeasureCompProd` (joint `mu otimes_m kappa`), `.CondDistrib` (regular conditional distribution), `.Disintegration.Basic` (`condKernelCountable` for countable index).
- `Mathlib.Probability.Independence.Basic` (`IndepFun`, `iIndepFun`), `.Independence.Conditional` (`CondIndepFun`, `iCondIndepFun`).
- `Mathlib.Probability.IdentDistrib` (`IdentDistrib f g mu nu`, transports integrals).
- `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog` (`Real.negMulLog`, concavity). The analytic backbone of entropy.
- `Mathlib.Analysis.SpecialFunctions.BinaryEntropy`, `Mathlib.Analysis.Convex.Jensen`.
- `Mathlib.Analysis.Convex.Cone.Basic` (`ConvexCone`, `PointedCone`, `ProperCone`).

**Gap:** Mathlib has no Shannon entropy `H[X]`, `H[X|Y]`, `I[X:Y]`, `I[X:Y|Z]` operators.

### 2.2 `cboone/shannon-entropy` (user's own project)

A substantial Lean 4 formalization (~1,888 lines, 10 modules) of Shannon's 1948 finite-alphabet characterization theorem. **Lean 4.29.0 / Mathlib 4.29.0**, matching our target version.

**Provides:**

- `ProbDist alpha`: bundled type for probability distributions on `Fintype alpha`.
- `entropyNat` (`-Sum p log p`) and `entropyBase b p` (arbitrary base).
- `condEntropy`, `mutualInfo` (definitions; key lemmas for pairs).
- `marginalFst`, `marginalSnd`, `prodDist`, `IsIndependent` for `ProbDist (alpha x beta)`.
- Chain rule, subadditivity, Gibbs inequality, nonnegativity, conditioning-reduces-entropy.
- Bridge: `entropyNat_eq_sum_negMulLog` connects to Mathlib's `Real.negMulLog`.
- Shannon's uniqueness theorem: `entropyNat_unique`.

**Gaps relevant to Zhang-Yeung:**

- No conditional mutual information `I(X;Y|Z)`.
- No data processing inequality.
- No submodularity in the general 3+-variable form.
- `ProbDist`-on-product-types design does not scale cleanly to 4-6 variable joint constructions needed for the copy lemma.

### 2.3 PFR project (`teorth/pfr`)

The PFR project defines in `PFR/ForMathlib/Entropy/{Basic,MutualInfo,Kernel/*}.lean` (namespace `ProbabilityTheory`):

- `entropy` (`H[X; mu]`), `condEntropy` (`H[X | Y]`), `mutualInfo` (`I[X : Y]`), `condMutualInfo` (`I[X : Y | Z]`).
- All basic Shannon inequalities: nonnegativity, submodularity, chain rule, data processing, conditioning reduces entropy.
- KL divergence, Ruzsa distance (not needed here).
- Entropy operates on random variables as measurable functions on a probability space, scaling naturally to many variables.

PFR contains no non-Shannon inequalities and no copy lemma. It brings substantial unneeded machinery (Ruzsa distance, tau functional, group-theoretic entropy, fibring lemma). Only the `ForMathlib/Entropy/` subtree is imported; the remainder is carried by the dependency but unused.

### 2.4 Mathlib PR status

- **#34773** (`feat(InformationTheory): add Shannon entropy for PMFs`): **Open**, reviewed by sgouezel/dupuisf. Adds Shannon entropy for `PMF` with basic properties.
- **Merged:** Degenne's KL divergence chain (#21053, #21901, #34841, #35301). Binary entropy (#9734). Kraft-McMillan (#34108). PFR independence lemmas (#22516, #23418).
- **Open/WIP:** data processing for KL (#35349). Total variation (#37730).
- **Conclusion:** KL divergence is arriving; Shannon entropy on PMFs is in review; general measure-theoretic Shannon entropy (as in PFR) is not yet upstreamed.

### 2.5 Other proof assistants

- **Coq/Rocq `infotheo`** (Affeldt et al.): full Shannon apparatus, source/channel coding theorems, no non-Shannon.
- **Isabelle/HOL** (Hoelzl; AFP): measure-theoretic entropy, Shannon coding, no non-Shannon.
- **HOL4** (Hasan/Tahar): discrete entropy and relative entropy, no non-Shannon.
- **Mizar:** no relevant entries.

### 2.6 Non-formalized tooling

ITIP, Xitip, oXitip, minitip, PSITIP are LP-based Shannon-type provers. PSITIP uniquely supports the copy lemma + Fourier-Motzkin and can verify Zhang-Yeung, but emits no machine-checkable certificate.

## 3. Architecture: entropy dependency

### The representation tension

| Aspect | `shannon-entropy` (`ProbDist`) | PFR (measure-space RVs) |
|---|---|---|
| Core type | `ProbDist alpha` (bundled finite dist) | `X : Omega -> S` measurable function |
| Joint dists | `ProbDist (alpha x beta)` products | `(X, Y) : Omega -> S x T`, shared space |
| Conditional MI | Not defined | Defined and proven |
| Data processing | Not proven | Proven |
| Copy lemma suitability | Awkward (manual distribution construction) | Natural (kernel composition) |

The copy lemma needs to take a 4-variable joint, form a conditional distribution of (X, Y) given (Z, U), compose it to produce a 6-variable joint, and prove marginal/conditional-independence properties. This is most naturally done in a measure-space framework (PFR's approach, Mathlib's idiom).

### Resolved strategy: permanent PFR dependency

Depend on PFR via `lakefile.toml` at a pinned rev. Import only `PFR.ForMathlib.Entropy.{Basic,MutualInfo}` and kernel variants. Ignore Ruzsa distance, group theory, fibring lemma, etc. PFR stays as a permanent dependency; there is no plan to extract or replace it with a local entropy layer. Upgrades to the PFR pin are deliberate work scheduled alongside feature milestones.

## 4. Scope (resolved: S2 + Theorem 5 stretch)

### What we are building

**Core (S2):**

- **Theorem 2 (warm-up; Zhang-Yeung 1997 conditional inequality, restated from [39] as Theorem 2 of the paper):** Under I(X; Y) = I(X; Y | Z) = 0, I(X; Y | Z, U) <= I(Z; U | X, Y) + I(X; Y | U). Uses a single auxiliary copy (a degenerate form of the M2 construction); serves as a warm-up that exercises the construction machinery before the two-copy argument.
- **Lemma 2 / copy construction (copy lemma):** The highest-leverage artifact. Standalone, reusable, Mathlib-ready. Bundles the auxiliary distribution of eq. (44) and the Delta-identity of Lemma 2 (eq. 45).
- **Theorem 3 (Zhang-Yeung inequality):** For four discrete RVs X, Y, Z, U, paper's equation (21):
  Delta(Z, U | X, Y) <= (1/2) [I(X; Y) + I(X; Z, U) + I(Z; U | X) - I(Z; U | Y)],
  together with the dual (22) (via X <-> Y swap) and the averaged corollary (23).
- **Theorem 4 (Shannon is incomplete):** Explicit witness function F in Gamma_4 \ tilde{Gamma}_4, proving cl(Gamma*_n) != Gamma_n for n >= 4.

**Stretch (Theorem 5):**

- n+2-variable generalization. Same copy-lemma strategy with induction on n.

## 5. File Layout

```text
zhang-yeung-inequality/
  lakefile.toml               # Lake manifest; pins PFR and defers mathlib resolution transitively
  lean-toolchain              # matching Lean version
  ZhangYeung.lean             # top-level re-export
  ZhangYeungTest.lean         # top-level re-export for Lean API tests
  ZhangYeung/
    Prelude.lean              # notation, import surface, namespace setup
    Delta.lean                # Delta(Z,U|X,Y), equational lemmas
    Theorem2.lean             # conditional warm-up (single copy)
    CopyLemma.lean            # Lemma 2, generalized and standalone (Mathlib-ready)
    Theorem3.lean             # the main Zhang-Yeung inequality
    Theorem4.lean             # cl(Gamma*_n) != Gamma_n, explicit witness
    Theorem5.lean             # (stretch) n+2-variable generalization
  ZhangYeungTest/
    Delta.lean                # compile-time API regression tests for Delta
    Theorem2.lean             # Theorem 2 API and usage tests
    CopyLemma.lean            # copy-lemma API and usage tests
    Theorem3.lean             # theorem-level smoke tests
    Theorem4.lean             # witness arithmetic checks
    Theorem5.lean             # small-n specialization checks
  .github/workflows/ci.yml    # CI: lake build + lint
```

## 6. Milestone-by-Milestone Plan

### Dependency graph

```text
M0 (scaffolding)
 |
 v
M1 (Delta lemmas)
 |
 v
M1.5 (Thm 2, conditional warm-up)
 |
 v
M2 (copy lemma)
 |
 +------+------+
 |             |
 v             v
M3 (Thm 3)   M4 (Thm 4, partially parallel -- see note)
 |
 v
M5 (Thm 5, stretch)
 |
 v
M6 (polish)
```

### Parallelism analysis

**M4 is partially independent of M3, but substantively needs it.** Theorem 4's full proof has four parts: (a) prove the witness F satisfies the Shannon basic inequalities (independent of M2/M3, pure set-function arithmetic); (b) prove F violates the Zhang-Yeung inequality at a chosen labeling (pure set-function arithmetic); (c) bridge M3 to the set-function level so that every four-variable entropy function is shown to satisfy Zhang-Yeung (this *requires* M3 as more than a black box -- the bridge unwraps M3's conclusion into the set-function `zhangYeungAt` predicate via a family of joint-entropy identities); (d) assemble (a) + (b) + (c) into the headline `theorem4`. Parts (a) and (b) *could* be drafted before M3 lands, but Parts (c) and (d) close over M3 nontrivially. In retrospect the parallelism was marginal.

**M5 depends on M3** (uses the same proof structure plus induction), not on M4.

**Concurrent worktree strategy (historical):** The original plan envisioned Worktree A (M0 → M1 → M1.5 → M2 → M3 → M5) running alongside Worktree B (M4 Parts (a) + (b)) with B waiting for A to finish M3 before proceeding to Parts (c) + (d). In practice M3 has landed on `main` first; M4 now runs as a single follow-on from the M3-ready tip rather than as a parallel track.

### M0: Project scaffolding

- Initialize `lakefile.toml` with PFR as a direct dep (pin PFR at a specific rev and defer Mathlib resolution transitively).
- `lean-toolchain` set by the compatibility check in the root-package layout test.
- `.github/workflows/ci.yml` running `lake build` and `lake lint`.
- Ensure a sibling `ZhangYeungTest` library exists and is built by default. If the harness is still missing at M0 time, add it here before proceeding to proof milestones.
- Skeleton `ZhangYeung.lean` importing PFR entropy notation; verify it builds.
- Apply `write-lean-code` skill guidance from the first commit.
- **Testing:** `lake build` must build both the proof library and the test library, with at least one smoke-test module already wired into `ZhangYeungTest/`.
- **Deliverable:** green CI build importing PFR entropy notation and building the test harness.

### M1: Delta equational lemmas

- `ZhangYeung/Prelude.lean`: `open ProbabilityTheory`, import entropy notation.
- `ZhangYeung/Delta.lean`: define `delta` matching Delta(Z, U | X, Y) := I(Z; U) - I(Z; U | X) - I(Z; U | Y); prove equivalent reformulations (paper's equations 20-23).
- `ZhangYeungTest/Delta.lean`: add compile-time API tests covering the exported `delta` lemmas and one downstream composition from forms (21) and (22) to the paper's scaled form (23).
- **Checkpoint:** each equational form reduces to `ring_nf`/`linarith` over entropy terms, and the matching test module builds against the public API without opening the implementation file.

### M1.5: Theorem 2 (conditional warm-up)

- `ZhangYeung/Theorem2.lean`: the Zhang-Yeung 1997 conditional inequality, included in the 1998 paper as Theorem 2 (eq. 16-17).
- **Statement:** for four discrete RVs X, Y, Z, U, if I(X; Y) = 0 and I(X; Y | Z) = 0, then I(X; Y | Z, U) <= I(Z; U | X, Y) + I(X; Y | U).
- **Why now:** exercises the single-copy construction (a degenerate form of M2's two-copy construction) on a materially simpler statement. Validates the planned kernel-composition approach before M2's full bookkeeping load. Produces a reusable helper lemma for conditional inequalities.
- **Testing:** `ZhangYeungTest/Theorem2.lean` should restate the theorem in `example` form and cover at least one downstream use that plugs the conclusion into a simple Shannon-inequality chase, exercising the exported hypothesis shape without reaching into the single-copy construction.
- **Checkpoint:** theorem with all hypotheses explicit, discharged by the single-copy construction and Shannon basics, and the Theorem 2 test module builds.

### M2: The copy lemma

- `ZhangYeung/CopyLemma.lean`: state and prove the generalized copy lemma.
- **Statement:** given a probability measure mu on Omega with four RVs X, Y, Z, U (measurable functions to `Fintype` types), construct a probability measure nu on an extended space with six RVs (X, Y, Z, U, X_1, Y_1) such that:
  (i) the (X, Y, Z, U) marginal of nu equals the law under mu;
  (ii) the (X_1, Y_1, Z, U) marginal gives (X_1, Y_1) the same conditional distribution as (X, Y) given (Z, U);
  (iii) `CondIndepFun X Y_1 (Z, U) nu` (conditional independence).
- **Construction:** nu = mu otimes_m (condDistrib (X, Y) (Z, U) mu), a two-step kernel composition.
- **Supporting lemmas:** `IdentDistrib` for (X, Z, U) vs (X_1, Z, U) and symmetrically.
- **Key Mathlib deps:** `Kernel.compProd`, `condDistrib`, `condExpKernel`. Measurability bookkeeping concentrates here.
- **Design for Mathlib:** parametrize over any four RVs on Fintype (not specialized to the paper). Clean statement, no paper-specific notation.
- **Testing:** `ZhangYeungTest/CopyLemma.lean` should restate the public theorem in example form and exercise the intended downstream APIs (`IdentDistrib`, conditional independence, and the projection laws) without reaching into proof internals.
- **Checkpoint:** compiles with all measure-theoretic side conditions discharged, and the copy-lemma test module builds cleanly.

### M3: Theorem 3

- `ZhangYeung/Theorem3.lean`: derive the main inequality.
- Follow Section III. Two applications of Lemma 2 give `Delta(Z, U | X, Y) <= I(X; Y_1)` and `I(Z; U) - 2 I(Z; U | X) <= I(X; X_1)`. Combine: `2 I(Z; U) - 3 I(Z; U | X) - I(Z; U | Y) <= I(X; X_1, Y_1) + I(X_1; Y_1)`. Two distinct Shannon ingredients close the chase: (a) *marginal equality* `I(X_1; Y_1) = I(X; Y)` (the (X_1, Y_1, Z, U) marginal of q coincides with the (X, Y, Z, U) marginal of p, per eq. 44); (b) *data processing* `I(X; X_1, Y_1) <= I(X; Z, U)` via the Markov chain (X_1, Y_1) - (Z, U) - X under q.
- All steps are Shannon-type; the non-Shannon character enters only through the copy lemma.
- Prove (21) as the headline theorem, derive (22) by the X <-> Y swap, and (23) by averaging.
- **Testing:** `ZhangYeungTest/Theorem3.lean` should include an independent-variable smoke test and a theorem-application test that derives the averaged form (23) from the public theorem plus the M1 form-conversion lemmas.
- **Prelude promotion:** M2 left two private helpers in `ZhangYeung/CopyLemma.lean` (`condIndepFun_comp` and `IdentDistrib.condMutualInfo_eq`) under a "promote to `ZhangYeung/Prelude.lean` when a second module needs them" policy. M3 is the likely first consumer; if `Theorem3.lean` references either helper, promote it to the prelude in the same change rather than importing it across modules privately.
- **Checkpoint:** `theorem zhangYeung ... : delta Z U X Y mu <= (1/2) * (I[X : Y; mu] + I[X : (Z, U); mu] + I[Z : U | X; mu] - I[Z : U | Y; mu])` with all hypotheses explicit; averaged corollary `delta Z U X Y mu <= (1/2) * I[X : Y; mu] + (1/4) * (I[X : (Z, U); mu] + I[Y : (Z, U); mu])` follows mechanically, and the theorem test module builds.

### M4: Theorem 4

- `ZhangYeung/Theorem4.lean`: explicit counterexample plus the set-function/random-variable bridge that closes the full Theorem 4 statement.
- Encode the paper's function F (p. 1443: F(empty)=0, F(X)=F(Y)=F(Z)=F(U)=2a, F(XY)=4a, F(XU)=F(XZ)=F(YU)=F(YZ)=F(ZU)=3a, F(XYZ)=F(XYU)=F(XZU)=F(YZU)=4a, F(XYZU)=4a) as `Finset (Fin 4) -> Real` (at `a = 1` for the Lean encoding; the `a > 0` parametrization is vestigial for existence statements). F is symmetric on all pairs except (X, Y), which takes 4a rather than 3a.
- **Part (a):** Define the Shannon cone and prove F satisfies it (the three conditions of Γ_4 via eq. 11: `F(∅) = 0`, monotone, submodular). Discharged by `decide` over `Finset (Fin 4)` with `F` valued in `ℚ`; fallback to cardinality case-splits + `norm_num` if `decide` is pathologically slow.
- **Part (b):** Prove F violates the Zhang-Yeung inequality at the canonical (Z, U | X, Y) = (2, 3 | 0, 1) labeling (direct arithmetic; `norm_num` closes it after the six `F` evaluations the inequality mentions).
- **Part (c), requires M3:** Bridge M3 to the set-function level. Define the set-function entropy `entropyFn X μ : Finset (Fin 4) → ℝ` for a heterogeneous four-variable family `X : ∀ i : Fin 4, Ω → S i`, matching M3's existing theorem surface, then prove `zhangYeungHolds_of_entropy : zhangYeungHolds (entropyFn X μ)`: every four-variable entropy function lies in `tildeΓ_4`. Proof is a per-permutation application of M3's `zhangYeung` plus a single-labeling set-function-to-entropy bridge for each of the twelve `F`-evaluations that appear in `zhangYeungAt`, with the measurable hypotheses carried explicitly. This is M4's measure-theoretic content; Parts (a), (b) are pure set-function arithmetic.
- **Part (d):** State and prove the headline `theorem4 : ∃ F, shannonCone F ∧ F ≠ entropyFn X μ for any discrete RV family X, μ` -- the closure under M3 of the Parts (a) + (b) + (c) chain, still allowing the four codomains to differ. Optionally (stretch within this milestone, see plan): upgrade to the closure version via a short "zhangYeungHolds is closed under pointwise limits" lemma, and to the `n ≥ 4` version via the embedding `Fin 4 ↪ Fin n`.
- **Testing:** `ZhangYeungTest/Theorem4.lean` should replay the concrete witness arithmetic separately for Parts (a) and (b), pin the bridge signature from Part (c), and pin the headline `theorem4` statement from Part (d).
- **Checkpoint (required):**
  - `theorem shannon_incomplete : ∃ F, shannonCone F ∧ ¬ zhangYeungHolds F` (Parts (a) + (b), no M3 needed).
  - `theorem zhangYeungHolds_of_entropy` -- every four-variable entropy function lies in `tildeΓ_4` (Part (c), closes over M3).
  - `theorem theorem4 : ∃ F ∈ Γ_4, F is not the entropy function of any four discrete RVs` (Part (d), combines (a) + (b) + (c), still allowing the four codomains to differ).
- **Stretch within M4:** the closure version `theorem4_closure` (upgrading "not an entropy function" to "not a pointwise limit of entropy functions") and the `n ≥ 4` extension. Either may slip to a follow-up milestone if the core Parts (a)-(d) dominate budget.
- **Post-M4 exactness follow-up:** if M4 lands only the finite `n = 4` witness theorem, the sequence-level closure surrogate, and the cone-level `n ≥ 4` lift, but not the exact entropic-region closure statement `\bar{\Gamma}_n^* \neq \Gamma_n` as named sets, track the remaining work in `docs/plans/todo/2026-04-19-exact-theorem-4-entropic-region-closure.md` rather than silently treating the surrogate theorems as the final paper-level packaging.

### M5: Theorem 5 (stretch)

- `ZhangYeung/Theorem5.lean`: n+2-variable generalization.
- For n+2 RVs U, Z, X_1, ..., X_n and any i in {1,...,n}:
  nI(U; Z) - sum_j I(U; Z | X_j) - nI(U; Z | X_i) <= I(X_i; U, Z) + sum_j H(X_j) - H(X_1, ..., X_n)
- **Note:** the paper omits the proof ("it can be proved using exactly the same idea used in the proof of Theorem 3 and an inductive argument", p. 1443). M5 therefore requires reconstructing the argument via a single tuple-valued copy of `(X_1, ..., X_n)` over `(Z, U)`, pairwise projections feeding Lemma 2, and an internal induction proving the iterated conditional-subadditivity step. The outer theorem statement itself need not be proved by induction on `n`. Budget accordingly.
- **Testing:** `ZhangYeungTest/Theorem5.lean` should cover at least one small-`n` specialization and one API-level example showing the theorem rewrites to the expected bound in a concrete index regime.
- **Checkpoint:** statement over `Fin n -> Omega -> S` with the correct bound; averaged variant (eq. 28) as corollary, and the small-`n` theorem tests build.

### M6: Polish and release

- README with theorem statement, install instructions, citation.
- `write-math`/`write-lean-code`/`lint-and-fix` audit.
- Audit that every public module added in M1-M5 has a matching `ZhangYeungTest/` module, and make CI fail if `lake build` no longer includes the tests by default.
- Tag v0.1 once M0-M4 land; v0.2 once M5 lands.

## 7. Key Risks and Unknowns

### 7.1 PFR API churn (moderate)

PFR is under active upstreaming. Function names and namespaces may change. **Mitigation:** pin the rev; document the pin; treat upgrades as deliberate work scheduled alongside feature milestones.

### 7.2 Copy-lemma measurability bookkeeping (moderate-high)

The conceptual content of Lemma 2 is elementary, but the Lean proof needs to discharge measurability/standard-Borel/sigma-finite side conditions at each step. Finite RVs make standard Borel trivial but do not make `Kernel.compProd` go through without work. **Mitigation:** specialize to `Fintype` initially; generalize later.

### 7.3 PFR build weight (moderate)

PFR brings Ruzsa distance, tau functional, group-theoretic entropy, and more. Build times may be substantial. **Mitigation:** Mathlib cache from `lake exe cache get` and the CI elan/lake caches keep incremental builds fast; PFR itself compiles once per dependency-rev bump.

### 7.4 Log-base conventions (low)

The paper uses log base 2, base 3, and natural log interchangeably. Mathlib's `negMulLog` uses natural log. **Mitigation:** state all inequalities in log-base-agnostic form; base only matters in Theorem 4's explicit numerical check, where it cancels.

### 7.5 `IdentDistrib` vs joint-distribution equality (low-moderate)

The paper freely says "(X_1, Y_1) has the same distribution as (X, Y)." Lean's `IdentDistrib` is the right tool, but we need *joint* identity. **Mitigation:** work with tuples `(X, Z, U)` and `(X_1, Z, U)` as `IdentDistrib` pairs throughout.

### 7.6 Copy lemma Mathlib readiness (low-moderate)

Mathlib's canonical `mutualInfo` namespace is in flux. **Mitigation:** design the copy lemma for eventual upstream, but don't submit the PR until a stable target API exists.

### 7.7 Lean/PFR version alignment (low)

`shannon-entropy` uses Lean 4.29.0. PFR may use a different version. **Mitigation:** check PFR's `lean-toolchain` at M0; if mismatched, pin the closest compatible rev.

## 8. Verification Plan

- **Milestone rule:** every public module added or changed in M0-M5 must land with a matching `ZhangYeungTest/` module that imports only the public surface and proves API-level `example`s against it.
- **Build gate:** `lake build` must build both `ZhangYeung` and `ZhangYeungTest` by default, and `lake lint` must pass on both libraries.
- **API regression tests:** use `ZhangYeungTest/` to catch signature drift, missing re-exports, over-specialized hypotheses, and broken downstream proof scripts.
- **Small-model checks where practical:** when a milestone has a natural concrete witness or arithmetic sanity check, add it to the matching test module instead of leaving it as prose.
- **Paper cross-check:** confirm key intermediate identities (for example, the six-variable expansion on p. 1446) match the published derivation when the relevant milestone lands.
- **Concrete targets by milestone:**
  - M1: `ZhangYeungTest/Delta.lean` covering definition, symmetries, entropy expansion, form conversions, and `delta_le_mutualInfo`.
  - M1.5: `ZhangYeungTest/Theorem2.lean` covering the Theorem 2 statement and at least one downstream Shannon-inequality use.
  - M2: `ZhangYeungTest/CopyLemma.lean` covering theorem shape and intended downstream APIs.
  - M3: `ZhangYeungTest/Theorem3.lean` covering the independent-variable smoke test and the averaged-form (23) derivation.
  - M4: `ZhangYeungTest/Theorem4.lean` covering the witness arithmetic and strict violation.
  - M5: `ZhangYeungTest/Theorem5.lean` covering a small-`n` specialization.
- **CI:** GitHub Actions should keep using `lake build` and `lake lint`, with the confidence coming from the default targets including the tests.

## 9. Extensions (future work, post-release)

Ranked by leverage:

1. **Copy lemma upstream to Mathlib.** Single highest-impact follow-on; unlocks all non-Shannon formalization.
2. **Exact Theorem 3 with explicit slack (pp. 1445-1446).** The paper derives the exact remainder `R(X, Y, Z, U, X_1, Y_1) = (1/2) * [I(X; X_1 | U) + I(X; X_1 | Z) + I(Z; U | X X_1) + I(X_1; Y_1 | X) + I(X; Z U | X_1 Y_1) + I(X; Y_1 | U) + I(X; Y_1 | Z) + I(Z; U | X Y_1)]` that upgrades Theorem 3's `<=` to equality. A natural refinement once the copy lemma is in place; strengthens the formalization to an equality with a fully characterized remainder. Also yields the extremal F on p. 1446 that attains equality.
3. **Dougherty-Freiling-Zeger 2006/2011 six inequalities** (arXiv:1104.3602). Mechanical once copy lemma exists.
4. **ITIP certificate importer.** A Lean tactic consuming Farkas certificates to discharge Shannon-type subgoals.
5. **Matus 2007 infinite family** (IEEE TIT 53). Non-polyhedrality of cl(Gamma*_4). Closure/limit argument.
6. **Ingleton and Kinser inequalities, matroid connection.** Parallel stream.
7. **Chan-Yeung 2002 group-theoretic reformulation** (IEEE TIT 48(7)). Alternative proof via subgroup-index inequalities.
8. **Theorem 6 (inner bound on cl(Gamma*_4)).** The paper's ~5-page case analysis via seven constructions. Scope decision deliberately excluded this from S2; revisit once the outer-bound side is stable.
9. **Bridge to `shannon-entropy`.** Prove `entropyNat (toProbDist X mu) = H[X; mu]` connecting both projects.

## 10. Critical Files (implementation targets)

**New (this project):**

- `ZhangYeung/CopyLemma.lean` (highest-leverage, Mathlib-ready)
- `ZhangYeung/Delta.lean`
- `ZhangYeung/Theorem2.lean` (warm-up)
- `ZhangYeung/Theorem3.lean`
- `ZhangYeung/Theorem4.lean`
- `ZhangYeung/Theorem5.lean` (stretch)
- `ZhangYeungTest.lean`
- `ZhangYeungTest/{Delta,Theorem2,CopyLemma,Theorem3,Theorem4,Theorem5}.lean`

**External (depend on, do not modify):**

- `PFR/ForMathlib/Entropy/Basic.lean` (entropy, condEntropy, basic Shannon inequalities)
- `PFR/ForMathlib/Entropy/MutualInfo.lean` (mutualInfo, condMutualInfo)
- `Mathlib/Probability/Kernel/CondDistrib.lean` (condDistrib)
- `Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean` (mu otimes_m kappa)
- `Mathlib/Probability/Independence/Conditional.lean` (CondIndepFun)
- `Mathlib/Probability/IdentDistrib.lean` (IdentDistrib)
