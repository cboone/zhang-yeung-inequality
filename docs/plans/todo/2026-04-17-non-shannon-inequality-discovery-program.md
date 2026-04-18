---
title: "Non-Shannon inequality discovery: a post-Zhang-Yeung research program"
created: 2026-04-17
status: exploratory
scope: research program spanning multiple Lean milestones, external tooling, and publishable mathematical results. Not a single implementation plan.
depends_on: M2 (copy lemma, `docs/plans/todo/2026-04-17-copy-lemma.md`); downstream, M3 (Zhang-Yeung 1998 full proof) and the DFZ/Matús formalizations catalogued in `docs/research/post-zhang-yeung-extension-survey.md`.
---

## Status

Exploratory. This document records a two-track research program that extends the project beyond formalization into open mathematics. No code exists for either track yet. The program is gated on M2 and M3 landing.

## Motivation

The post-Zhang-Yeung extension survey (`docs/research/post-zhang-yeung-extension-survey.md`) identifies eight directions downstream of the core formalization. Two of them go beyond "formalize one more known theorem" into open research territory:

- **Survey item 5: computer-aided discovery.** Existing LP-based tools (ITIP, Xitip, psitip, AITIP) detect candidate non-Shannon inequalities but cannot emit machine-checkable proof certificates for the non-Shannon portion. Lean-in-the-loop removes this bottleneck.
- **Survey item 8: the Chan-Yeung group-theoretic correspondence.** Chan-Yeung (2002) proved that every linear entropy inequality on quasi-uniform distributions is equivalent to a linear inequality on subgroup-index vectors of a finite group. The correspondence has not been systematically mined for new inequalities.

Both are open research programs, not formalization follow-ons. They are complementary: Track A produces candidate inequalities probabilistically and certifies them in Lean; Track B produces candidate inequalities combinatorially via finite-group lattices. Each track's outputs can validate the other's and seed the other's search space.

## Track A: copy-lemma-guided inequality discovery

### Goal

Discover new linear non-Shannon information inequalities by systematic enumeration over copy-lemma parameter space, with Lean certifying each candidate as (a) a valid new inequality, (b) valid but redundant (entailed by the known cone plus Shannon), or (c) not derivable by the method. Publishable output: each novel inequality with its Lean proof term.

### Why this is novel territory

1. Matús (2007) proved there are infinitely many independent non-Shannon inequalities at $n = 4$, but the structure of the tower is not mapped. Every new independent inequality at $n \in \{4, 5\}$ is a publishable result.
2. Existing automated tools (AITIP, psitip) emit numerical verdicts, not proof certificates. A Lean-certified pipeline closes the soundness gap and turns numerical conjectures into theorems.
3. The bottleneck on systematic search has historically been candidate *verification*, not generation. Hand-verifying a copy-lemma derivation is error-prone and slow. Lean-in-the-loop dissolves that bottleneck.

### Prerequisites

1. M2 complete: the 2-copy lemma formalized as a standalone Lean artifact.
2. M3 complete: a full proof of Zhang-Yeung 1998 exercising the M2 copy-lemma API end-to-end.
3. A parameterized N-copy lemma generalizing M2. Inputs: a partition of the base variable set into frozen and copied subsets; a conditional-independence pattern; a copy count $N$.
4. A canonical form for linear information inequalities (rational coefficient vectors over the $2^n - 1$ joint entropies, or equivalently over elementary entropies and mutual informations).
5. A redundancy LP: given a candidate inequality and the list of known valid inequalities, decide whether the candidate is a non-negative rational combination. Output a Farkas-style certificate on redundancy.

### Phases

1. **Parameterize the copy lemma.** Extend M2's concrete 2-copy construction to an $N$-copy lemma parameterized by the three inputs above. Output: one Lean theorem that, given a structured parameter, returns the auxiliary joint distribution together with its `IdentDistrib` and `CondIndepFun` facts. This is a substantial Lean deliverable on its own and stands independently as a Mathlib contribution.

2. **Build the in-Lean certification engine.** Given a candidate inequality (coefficient vector) and a copy-lemma parameterization, produce a Lean term that either closes the inequality via a Shannon chase over the copy's structural facts, or fails. Success yields a proof; failure is not evidence of invalidity, only of non-derivability by this method. This requires either custom tactics or a metaprogram that emits the Shannon-chase term.

3. **Build the external redundancy LP.** Outside Lean, in Python or SageMath. Given the Shannon cone and a list of known non-Shannon inequalities, check if a candidate is a non-negative rational combination. Can run in parallel with phases 1-2.

4. **Reproduce known results as validation.** Close Lean-certified proofs of the six DFZ inequalities (2006) and the first few Matús inequalities. Validates the pipeline and produces the first verified catalog.

5. **Search for new inequalities.** Enumerate copy-lemma parameterizations, filter with the redundancy LP, certify survivors in Lean. This is the core research phase; each survivor is a theorem.

6. **Publish.** Paper on the method and the catalog. Candidate venue: IEEE Trans. Inform. Theory or ISIT.

### Deliverables

- `ZhangYeung/CopyLemma/Parameterized.lean`: the N-copy lemma, Mathlib-ready.
- `ZhangYeung/NonShannon/Catalog.lean`: a verified library of discovered inequalities, each tagged with its parameter certificate.
- External tool `zhang-yeung-search`: enumeration + LP filter, emits Lean scripts for verified survivors.
- A paper reporting the new inequalities and structural patterns observed.

## Track B: finite-group correspondence

### Goal

Formalize the Chan-Yeung correspondence, use it to re-prove Zhang-Yeung combinatorially as validation, and mine finite-group families for new inequalities invisible on the probabilistic side.

### Why this is novel territory

1. Chan-Yeung (2002) proved the correspondence but never systematically mined it. The direction "given a finite group, extract its induced inequality" has been used case-by-case, never catalogued.
2. Specific group families (p-groups, nilpotent class 2, solvable, Frobenius) may impose structural constraints that produce characteristic non-Shannon inequalities not easily discovered probabilistically.
3. Finite-group search is especially Lean-friendly: decidable equality on finite groups, finite-verification for small group orders, natural interfaces with GAP's catalogue of small groups.

### Prerequisites

1. Mathlib's existing finite-group, subgroup-lattice, and coset API (sufficient for the forward direction).
2. Entropy theory from PFR (already used throughout this project).
3. A quasi-uniform approximation theorem: the closure of entropy vectors from quasi-uniform distributions equals the closure of the entropic region. This is the hard prerequisite; the Chan-Yeung paper proves it by a counting/limit argument.

### Phases

1. **Forward correspondence.** Formalize: for a finite group $G$ with subgroups $G_{1}, \dots, G_{n}$, the vector indexed by $S \subseteq [n]$ with component $\log \lvert G \rvert - \log \lvert \bigcap_{i \in S} G_{i} \rvert$ is an entropy vector, realized by uniform sampling of cosets. Mathlib's coset and index calculus plus PFR's entropy theory are sufficient.

2. **Reverse correspondence.** Formalize the density: quasi-uniform entropy vectors are dense in the closure of the entropic region. The Chan-Yeung proof uses a counting argument that lifts any quasi-uniform distribution to a group-induced one. This is the phase where formalization difficulty is genuinely open (see risks §1).

3. **Group-theoretic proof of Zhang-Yeung.** As validation, produce a Lean proof of Zhang-Yeung via the finite-group route, independent of the copy lemma. Matús showed on paper that this is possible; the Lean version is direct once phase 1 is complete. This gives a second certificate for the same inequality.

4. **Finite-group search infrastructure.** Integrate GAP (or an equivalent small-group enumerator) to iterate through groups of small order. For each candidate subgroup tuple, compute the rank vector and test against the Shannon cone via Track A's redundancy LP.

5. **Investigate structured group families.** Specific targets: p-groups of small order, nilpotent class 2 groups, solvable groups of bounded derived length, Frobenius groups. Mathematical question: do any of these families exhibit characteristic non-Shannon inequalities not directly visible probabilistically?

6. **Publish.** Paper reporting new inequalities discovered through the group-theoretic route plus any structural patterns (e.g., "every non-Shannon inequality realized by a p-group of class 2 has form $X$"). Candidate venue: J. Algebraic Combin. or IEEE Trans. Inform. Theory.

### Deliverables

- `ZhangYeung/GroupTheoretic/Correspondence.lean`: Chan-Yeung forward and reverse directions.
- `ZhangYeung/GroupTheoretic/ZhangYeung.lean`: group-theoretic proof of the Zhang-Yeung inequality, independent of the copy lemma.
- External tool `zhang-yeung-group-search`: GAP harness + Python wrapper emitting candidates to the redundancy LP.
- A paper reporting the group-theoretic findings.

## Integration between tracks

The two tracks share infrastructure and validate each other in four specific ways:

1. **Shared redundancy LP.** Both tracks need a "is this new?" oracle over the known cone. One LP implementation serves both.

2. **Dual certification.** An inequality discovered in Track A should, if valid, have a group-theoretic witness in Track B via quasi-uniform approximation. The converse is automatic (every group-induced inequality is entropic). Dual certificates strengthen published results.

3. **Search-space reduction.** Group-theoretic structural constraints (e.g., "every inequality from a p-group has coefficients of specific form") can prune Track A's copy-lemma enumeration. Conversely, Track A's probabilistic constructions can suggest group families worth examining.

4. **Shared catalog.** Both tracks feed into a single `ZhangYeung.NonShannon.Catalog` Lean module, where each inequality carries one or both certificates.

## Sequencing

Phase dependencies (without time estimates):

- Track A phases 1-2 depend on M2 and M3 landing.
- Track A phase 4 depends on phases 1-3.
- Track A phase 5 depends on phase 4 (validation) and the redundancy LP.
- Track B phase 1 depends only on Mathlib primitives. Can run in parallel with M2, M3, and Track A phase 1.
- Track B phase 2 depends on phase 1 and is the likely pacing bottleneck for Track B.
- Track B phase 3 depends on phase 1 and the completed M3 proof (for the equality being re-proven).
- Track B phases 4-5 depend on phase 3 (as validated launching point).

Critical path for the first publishable results:

$$
\text{M2} \to \text{M3} \to \text{A1 (parameterized copy lemma)} \to \text{A2, A3 (engine + LP)} \to \text{A4 (reproduce DFZ/Matús)} \to \text{A5 (new inequalities)}.
$$

Parallel track: Track B phases 1 and 3 can complete alongside Track A phases 1-4, giving an independent validation artifact without blocking Track A.

## Risks and open questions

1. **Reverse correspondence (Track B phase 2) may resist formalization.** Chan-Yeung's density argument is constructive in spirit but uses a counting argument that may demand substantial measure-theoretic machinery or non-standard analysis in Lean. If phase 2 stalls, Track B can still proceed with the forward direction alone, at the cost of not certifying "every entropy inequality comes from a group" in Lean.

2. **Redundancy LP scalability.** At $n = 5$, the elementary entropy space has dimension 31; the number of candidate inequalities and the number of combinations to check grows fast. Whether the redundancy LP scales to useful sizes is genuinely open. Sparse methods, symmetry reduction (via $\operatorname{Sym}(n)$ orbits), and incremental checking are the mitigations.

3. **Copy-lemma parameter-space redundancy.** Naive enumeration produces many parameterizations that yield equivalent inequalities under variable permutation or relabeling. A canonical form up to symmetry is itself a research problem; without it, Track A phase 5 wastes cycles.

4. **No guarantee of truly new inequalities.** Matús's infinite family is known. It is open whether known copy-lemma machinery exhausts the cone modulo limits. The search may rediscover the entire tower without finding genuinely new inequalities. Negative results remain publishable ("the $k$-copy machinery for $k \leq K$ exhausts the known cone up to symmetry"), but the framing shifts.

5. **External-tool trust boundary.** GAP output, LP solver output, and Python-side enumeration sit outside Lean's kernel guarantees. Each must either emit a Lean-checkable certificate (rational Farkas combinations, explicit group presentations) or be documented as a trusted oracle. Undocumented trust erodes the value of the Lean certification.

6. **PFR and Mathlib dependency churn.** Both are moving targets. Pinned revisions (this project's current discipline) trade stability against falling behind on upstream improvements. The program will need a maintenance budget.

7. **Publication venue fit.** Lean-certified non-Shannon inequalities are a new kind of artifact. Information-theory venues (IEEE Trans. Inform. Theory, ISIT) may not yet have reviewers comfortable with proof assistants; formal-methods venues (CPP, ITP, CAV) may not see the information-theoretic contribution as novel enough. Early outreach to program chairs or a joint CPP+ISIT submission is plausible.

## References

- Matús, F. *Infinitely many information inequalities*. ISIT 2007.
- Matús, F. *Two constructions on limits of entropy functions*. IEEE Trans. Inform. Theory 53 (2007).
- Dougherty, R., Freiling, C., Zeger, K. *Six new non-Shannon information inequalities*. ISIT 2006.
- Dougherty, R., Freiling, C., Zeger, K. *Non-Shannon information inequalities in four random variables*. arXiv:1104.3602 (2011).
- Chan, T. H., Yeung, R. W. *On a relation between information inequalities and group theory*. IEEE Trans. Inform. Theory 48 (7) (2002), 1992-1995.
- Kaced, T., Romashchenko, A. *Conditional information inequalities for entropic and almost entropic points*. arXiv:1207.5742.
- Matveev, R., Portegies, J. *Tropical probability theory and an application to the entropic cone*. Kybernetika 56 (2020), 1133.
- ITIP / Xitip / psitip / AITIP tool suite. See `docs/research/post-zhang-yeung-extension-survey.md` §5 for URLs.
- This project's extension survey: `docs/research/post-zhang-yeung-extension-survey.md`.
- This project's formalization roadmap: `docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md`.
- M2 plan: `docs/plans/todo/2026-04-17-copy-lemma.md`.
