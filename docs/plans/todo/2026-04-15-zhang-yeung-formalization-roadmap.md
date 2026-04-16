# Zhang-Yeung Inequality Formalization Roadmap

**Created:** 2026-04-15
**Target:** Lean 4 / Mathlib 4
**Paper:** Zhang & Yeung, "On Characterization of Entropy Function via Information Inequalities," *IEEE TIT* 44(4), July 1998, pp. 1440-1452.
**Source PDF:** `/Users/ctm/Downloads/zhenzhang1998.pdf`

**Resolved decisions:**
- **Scope:** S2 + Theorem 5 (stretch). Theorems 3, 4 as core; Theorem 5 (n+2-variable generalization) as stretch.
- **Dependency:** Start on PFR for entropy; progressively extract/reimplement just the needed subset into a local `ZhangYeung/Entropy/` module, then drop the PFR dep.
- **Blueprint:** No. Lean-only.
- **Mathlib intent:** Copy lemma yes (designed for upstream). Rest of proof stays local.

## 1. Context

The Zhang-Yeung inequality is the first known *non-Shannon-type* information inequality. Its discovery proved that the Shannon "basic" inequalities (nonnegativity of entropy, conditional entropy, and conditional mutual information) do not fully characterize the set of entropic functions for n >= 4 discrete random variables. The paper contains four main results:

- **Theorem 3** (the Zhang-Yeung inequality). For any four discrete random variables X, Y, Z, U, writing Delta(Z, U | X, Y) := I(Z; U) - I(Z; U | X) - I(Z; U | Y), the inequality
  Delta(Z, U | X, Y) <= (1/2) I(X; Y) + (1/4) [I(X; Z, U) + I(Y; Z, U)]
  holds, and it does not follow from the basic Shannon inequalities.
- **Theorem 4.** The closure of the set of constructible entropy functions is strictly smaller than the Shannon outer bound: cl(Gamma*_n) != Gamma_n for n >= 4 (immediate corollary of Theorem 3).
- **Theorem 5.** Generalization of Theorem 3 to n + 2 random variables (same proof strategy).
- **Theorem 6.** A nontrivial inner bound on cl(Gamma*_4), via seven explicit probabilistic constructions and a ~5-page case analysis.

The central proof technique is what modern information theory calls the **copy lemma** (Lemma 2 of the paper): given jointly distributed (X, Y, Z, U), construct X_1, Y_1 on a common extended space such that (X, Y_1, Z, U) and (X_1, Y, Z, U) each have the original joint distribution, and I(X; Y_1 | Z, U) = 0 (conditional independence of the two copies given (Z, U)). Once this auxiliary distribution exists, Theorem 3 follows from a mechanical Shannon-inequality chase.

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

PFR contains no non-Shannon inequalities and no copy lemma. It brings substantial unneeded machinery (Ruzsa distance, tau functional, group-theoretic entropy, fibring lemma). Only the `ForMathlib/Entropy/` subtree (~4-6 files) is relevant.

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

### Resolved strategy: bootstrap on PFR, extract progressively

**Phase 1 (bootstrap):** Depend on PFR via `lakefile.lean` (pinned rev). Import only `PFR.ForMathlib.Entropy.{Basic,MutualInfo}` and kernel variants. Ignore Ruzsa distance, group theory, fibring lemma, etc.

**Phase 2 (extraction):** As a parallel workstream, fork/copy with attribution (or reimplement from Mathlib primitives) just the definitions and lemmas actually used. Target: a local `ZhangYeung/Entropy/` module containing:
- `H[X; mu]`, `H[X | Y; mu]`, `I[X : Y; mu]`, `I[X : Y | Z; mu]` definitions and notation.
- Shannon inequalities: nonnegativity, chain rule, submodularity, data processing.
- ~4-6 files, ~1500-2000 lines, well-isolated from PFR's Freiman-Ruzsa machinery.

**Phase 3 (shed PFR):** Remove the PFR dep. Project depends only on Mathlib.

**Optional bridge:** A lemma `entropyNat (toProbDist X mu) = H[X; mu]` connecting to `shannon-entropy`'s definitions.

## 4. Scope (resolved: S2 + Theorem 5 stretch)

### What we are building

**Core (S2):**
- **Lemma 2 (copy lemma):** The highest-leverage artifact. Standalone, reusable, Mathlib-ready.
- **Theorem 3 (Zhang-Yeung inequality):** For four discrete RVs X, Y, Z, U:
  2I(Z;U) <= I(X;Y) + I(X;Z,U) + 3I(Z;U|X) + I(Z;U|Y).
- **Theorem 4 (Shannon is incomplete):** Explicit witness function F in Gamma_4 \ tilde{Gamma}_4, proving cl(Gamma*_n) != Gamma_n for n >= 4.

**Stretch (Theorem 5):**
- n+2-variable generalization. Same copy-lemma strategy with induction on n.

## 5. File Layout

```
zhang-yeung-inequality/
  lakefile.lean               # Lake manifest; pins mathlib + pfr (phase 1)
  lean-toolchain              # matching Lean version
  ZhangYeung.lean             # top-level re-export
  ZhangYeung/
    Prelude.lean              # notation, import surface, namespace setup
    CopyLemma.lean            # Lemma 2, generalized and standalone (Mathlib-ready)
    Delta.lean                # Delta(Z,U|X,Y), equational lemmas
    Theorem3.lean             # the main Zhang-Yeung inequality
    Theorem4.lean             # cl(Gamma*_n) != Gamma_n, explicit witness
    Theorem5.lean             # (stretch) n+2-variable generalization
    Entropy/                  # (phase 2) extracted/reimplemented Shannon layer
      Basic.lean              # H[X], H[X|Y]
      MutualInfo.lean         # I[X:Y], I[X:Y|Z]
      ShannonInequalities.lean  # nonnegativity, chain rule, submodularity, DPI
  test/                       # sanity tests
  .github/workflows/lean.yml  # CI: lake build
```

## 6. Milestone-by-Milestone Plan

### Dependency graph

```
M0 (scaffolding)
 |
 v
M1 (Delta lemmas) -----> M6 (entropy extraction, parallel)
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
M7 (polish)
```

### Parallelism analysis

**M4 is partially independent of M3.** Theorem 4's counterexample proof has two halves: (a) proving F satisfies all basic Shannon inequalities (entirely independent of M2/M3, can begin after M1), and (b) proving F violates the Zhang-Yeung inequality (requires M3's theorem statement, but only as a *black box*: the proof is a direct arithmetic check against the inequality). In practice: the `shannonCone` definition and the 15-constraint verification can be written before M3 lands; the final `not (zhangYeungHolds F)` step plugs in M3's result.

**M6 (entropy extraction) is fully independent** of the main proof chain M2-M5. It can begin as soon as M0 completes and run alongside everything else. The swap from PFR imports to local imports happens at the end; no milestone blocks on it.

**M5 depends on M3** (uses the same proof structure plus induction), not on M4.

**Concurrent worktree strategy:** Two worktrees can run productively:
- **Worktree A (main proof):** M0 -> M1 -> M2 -> M3 -> M5
- **Worktree B (infrastructure + counterexample):** M6 (entropy extraction) + M4 part (a) (Shannon cone definition and constraint verification), merging with Worktree A once M3 lands to close M4 part (b).

### M0: Project scaffolding

- Initialize `lakefile.lean` with Mathlib 4 and PFR as deps (pin PFR at a specific rev).
- `lean-toolchain` matched to PFR's pin.
- `.github/workflows/lean.yml` running `lake build`.
- Skeleton `ZhangYeung.lean` importing PFR entropy notation; verify it builds.
- Apply `write-lean-code` skill guidance from the first commit.
- **Deliverable:** green CI build importing PFR entropy notation.

### M1: Delta equational lemmas

- `ZhangYeung/Prelude.lean`: `open ProbabilityTheory`, import entropy notation.
- `ZhangYeung/Delta.lean`: define `delta` matching Delta(Z, U | X, Y) := I(Z; U) - I(Z; U | X) - I(Z; U | Y); prove equivalent reformulations (paper's equations 20-23).
- **Checkpoint:** each equational form reduces to `ring_nf`/`linarith` over entropy terms.

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
- **Checkpoint:** compiles with all measure-theoretic side conditions discharged.

### M3: Theorem 3

- `ZhangYeung/Theorem3.lean`: derive the main inequality.
- Follow Section III: expand Delta(Z, U | X, Y) using Lemma 2's six-variable joint; apply data-processing I(X; Y) = I(X; Y_1) and the entropy chain rule.
- All steps are Shannon-type; the non-Shannon character enters only through the copy lemma.
- **Checkpoint:** `theorem zhangYeung ... : delta Z U X Y mu <= (1/2) * I[X : Y; mu] + (1/4) * (I[X : (Z, U); mu] + I[Y : (Z, U); mu])` with all hypotheses explicit.

### M4: Theorem 4

- `ZhangYeung/Theorem4.lean`: explicit counterexample.
- Encode the paper's function F (p. 1443: F(empty)=0, F(X)=F(Y)=F(Z)=F(U)=2a, F(XY)=4a, F(XZ)=F(YZ)=F(ZU)=3a, F(XYZ)=F(XYU)=F(XZU)=F(YZU)=4a, F(XYZU)=4a) as `Finset (Fin 4) -> Real` parametrized by a > 0.
- **Part (a), parallelizable:** Define the Shannon cone and prove F satisfies all 15 basic inequality constraints (`norm_num`/`linarith`).
- **Part (b), requires M3:** Prove F violates the Zhang-Yeung inequality (direct arithmetic).
- Conclude cl(Gamma*_4) strictly contained in Gamma_4; extend to n >= 4 via embedding.
- **Checkpoint:** `theorem shannon_incomplete : exists F, shannonCone F /\ not (zhangYeungHolds F)`.

### M5: Theorem 5 (stretch)

- `ZhangYeung/Theorem5.lean`: n+2-variable generalization.
- For n+2 RVs U, Z, X_1, ..., X_n and any i in {1,...,n}:
  nI(U; Z) - sum_j I(U; Z | X_j) - nI(U; Z | X_i) <= I(X_i; U, Z) + sum_j H(X_j) - H(X_1, ..., X_n)
- Same proof: one copy per X_j, induction on n.
- **Checkpoint:** statement over `Fin n -> Omega -> S` with the correct bound.

### M6: Entropy extraction (parallel)

Fully independent of M2-M5. Begins after M0.

- Identify which PFR definitions and lemmas are actually imported by M1-M5.
- Fork/copy those files with attribution into `ZhangYeung/Entropy/`, or reimplement on Mathlib primitives.
- Target: `Basic.lean` (H, condEntropy), `MutualInfo.lean` (I, condMutualInfo), `ShannonInequalities.lean` (the ~20 key lemmas).
- Once this builds independently, remove PFR from `lakefile.lean`.
- Optionally, prove bridge lemma connecting to `shannon-entropy`'s `entropyNat`.

### M7: Polish and release

- README with theorem statement, install instructions, citation.
- `write-math`/`write-lean-code`/`lint-and-fix` audit.
- Tag v0.1 once M0-M4 land; v0.2 if M5+M6 complete.

## 7. Key Risks and Unknowns

### 7.1 PFR API churn (moderate)
PFR is under active upstreaming. Function names and namespaces may change. **Mitigation:** pin the rev; document the pin; treat upgrades as deliberate work. M6 (extraction) is the long-term fix.

### 7.2 Copy-lemma measurability bookkeeping (moderate-high)
The conceptual content of Lemma 2 is elementary, but the Lean proof needs to discharge measurability/standard-Borel/sigma-finite side conditions at each step. Finite RVs make standard Borel trivial but do not make `Kernel.compProd` go through without work. **Mitigation:** specialize to `Fintype` initially; generalize later.

### 7.3 PFR build weight (moderate)
PFR brings Ruzsa distance, tau functional, group-theoretic entropy, and more. Build times may be substantial. **Mitigation:** M6 (extraction) is the fix. Meanwhile, Mathlib cache from `lake exe cache get` should keep incremental builds fast.

### 7.4 Log-base conventions (low)
The paper uses log base 2, base 3, and natural log interchangeably. Mathlib's `negMulLog` uses natural log. **Mitigation:** state all inequalities in log-base-agnostic form; base only matters in Theorem 4's explicit numerical check, where it cancels.

### 7.5 `IdentDistrib` vs joint-distribution equality (low-moderate)
The paper freely says "(X_1, Y_1) has the same distribution as (X, Y)." Lean's `IdentDistrib` is the right tool, but we need *joint* identity. **Mitigation:** work with tuples `(X, Z, U)` and `(X_1, Z, U)` as `IdentDistrib` pairs throughout.

### 7.6 Copy lemma Mathlib readiness (low-moderate)
Mathlib's canonical `mutualInfo` namespace is in flux. **Mitigation:** design the copy lemma for eventual upstream, but don't submit the PR until a stable target API exists.

### 7.7 Lean/PFR version alignment (low)
`shannon-entropy` uses Lean 4.29.0. PFR may use a different version. **Mitigation:** check PFR's `lean-toolchain` at M0; if mismatched, pin the closest compatible rev.

## 8. Verification Plan

- **Sanity tests** (`test/`): instantiate on small examples with computable entropies.
  - Three independent fair coins: verify `I[X_1 : X_2] = 0`, `H[X_1,X_2,X_3] = 3 log 2`.
  - Zhang-Yeung applied to independent RVs: both sides = 0, giving 0 <= 0.
  - Theorem 4's counterexample: verify the numerical constraints hold and the violation is strict.
- **Paper cross-check**: confirm key intermediate identities (e.g., the six-variable expansion on p. 1446) match the published derivation.
- **CI**: `lake build` with warnings-as-errors on `main` via GitHub Actions.

## 9. Extensions (future work, post-release)

Ranked by leverage:

1. **Copy lemma upstream to Mathlib.** Single highest-impact follow-on; unlocks all non-Shannon formalization.
2. **Zhang-Yeung 1997 conditional inequality** (IEEE TIT 43(6)). Simpler than 1998; warm-up.
3. **Dougherty-Freiling-Zeger 2006/2011 six inequalities** (arXiv:1104.3602). Mechanical once copy lemma exists.
4. **ITIP certificate importer.** A Lean tactic consuming Farkas certificates to discharge Shannon-type subgoals.
5. **Matus 2007 infinite family** (IEEE TIT 53). Non-polyhedrality of cl(Gamma*_4). Closure/limit argument.
6. **Ingleton and Kinser inequalities, matroid connection.** Parallel stream.
7. **Chan-Yeung 2002 group-theoretic reformulation** (IEEE TIT 48(7)). Alternative proof via subgroup-index inequalities.
8. **Bridge to `shannon-entropy`.** Prove `entropyNat (toProbDist X mu) = H[X; mu]` connecting both projects.

## 10. Critical Files (implementation targets)

**New (this project):**
- `ZhangYeung/CopyLemma.lean` (highest-leverage, Mathlib-ready)
- `ZhangYeung/Delta.lean`
- `ZhangYeung/Theorem3.lean`
- `ZhangYeung/Theorem4.lean`
- `ZhangYeung/Theorem5.lean` (stretch)
- `ZhangYeung/Entropy/{Basic,MutualInfo,ShannonInequalities}.lean` (M6 extraction)

**External (depend on, do not modify):**
- `PFR/ForMathlib/Entropy/Basic.lean` (entropy, condEntropy, basic Shannon inequalities)
- `PFR/ForMathlib/Entropy/MutualInfo.lean` (mutualInfo, condMutualInfo)
- `Mathlib/Probability/Kernel/CondDistrib.lean` (condDistrib)
- `Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean` (mu otimes_m kappa)
- `Mathlib/Probability/Independence/Conditional.lean` (CondIndepFun)
- `Mathlib/Probability/IdentDistrib.lean` (IdentDistrib)

## 11. Note on Stray Artifact

During the research phase, a subagent created an extra file at `docs/plans/todo/2026-04-15-post-zhang-yeung-extension-survey.md`. Its content is summarized in section 9 above. Recommend deleting it (or moving to `docs/research/`) after plan approval.
