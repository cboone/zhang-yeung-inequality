# Post-Zhang-Yeung Extension Survey (2026-04-15)

Survey of potential formalization extensions beyond the Zhang-Yeung (1998) unconditional non-Shannon inequality. Difficulty scale is relative to the core Zhang-Yeung formalization.

## 1. Matúš infinite family

- **Reference.** F. Matúš, *Infinitely many information inequalities*, Proc. 2007 IEEE Int. Symp. on Information Theory (ISIT), Nice, June 2007, pp. 41-44. Companion journal paper: F. Matúš, *Two constructions on limits of entropy functions*, IEEE Trans. Inform. Theory 53 (2007), 320-330.
- **Statement.** For every n >= 4 the closure `Gamma_bar*_n` of the entropic region is not polyhedral. Concretely, Matúš exhibits an explicit sequence of linear information inequalities (indexed by s >= 1) for 4 variables, together with a curve in the closure of the entropic region that witnesses mutual independence of the sequence. One presentation of the family is: for all s >= 1, s * I(A;B) <= ... (a convex combination of conditional-mutual-information terms) using s auxiliary copies. The `s -> infinity` limit squeezes the boundary into a non-polyhedral curve.
- **Technique.** Iterated "adhesive" pasting of polymatroid restrictions, i.e. the copy-lemma applied s times to materialize s independent copies of a random variable. So the machinery is the same copy-lemma plus Shannon facts, but applied combinatorially.
- **Difficulty.** Much harder than one Zhang-Yeung inequality: needs a clean parameterized copy construction plus a non-polyhedrality argument (showing no finite subfamily suffices). The individual inequalities are easy once the copy lemma is in place; the non-polyhedrality witness is the hard part.
- **New technique?** No fundamentally new probability tool, but a substantial piece of additional geometric/limit reasoning on `Gamma_bar*`.

## 2. Dougherty-Freiling-Zeger (DFZ)

- **Reference.** R. Dougherty, C. Freiling, K. Zeger, *Six new non-Shannon information inequalities*, Proc. 2006 IEEE ISIT, Seattle, pp. 233-236. Extended paper: *Non-Shannon information inequalities in four random variables*, arXiv:1104.3602 (2011), which produces a catalog of hundreds (214) of new inequalities.
- **Statement.** Six explicit linear inequalities in 4 variables, each provably independent of Zhang-Yeung and of each other.
- **Difficulty.** Easy follow-on once Zhang-Yeung and the copy lemma are formalized. Each DFZ inequality is derived by instantiating the copy lemma with a specific conditional-independence pattern and then doing Shannon-type linear-combination bookkeeping. Porting them is roughly "one lemma, copy-paste six times, adjust coefficients." Independence verification (showing a new inequality is not a positive combination of Shannon + earlier inequalities) is a separate LP obligation that is harder to close formally but not conceptually novel.
- **New technique?** No. Same copy lemma, different instantiations.

## 3. Zhang-Yeung 1997 conditional inequality

- **Reference.** Z. Zhang, R. W. Yeung, *A non-Shannon-type conditional inequality of information quantities*, IEEE Trans. Inform. Theory 43 (6) (1997), 1982-1986. (This is [39] in the 1998 paper.)
- **Statement.** A linear inequality in 4 variables that holds whenever certain linear entropy equalities (conditional-independence constraints) hold. Essentially conditional: Kaced-Romashchenko showed it does not extend to any unconditional inequality.
- **Relative difficulty.** The 1997 conditional result is *easier* as a standalone formal target: one fewer copy needed, and the proof is a shorter Shannon-inequality chase modulo an added conditional-independence hypothesis. It is also historically the natural warm-up. The 1998 unconditional inequality is the harder and higher-value target. If the core formalization is already Zhang-Yeung 1998, the 1997 result is a trivial corollary-style side theorem.
- **New technique?** No new technique vs. 1998; strictly simpler.

## 4. The Copy Lemma

- **Modern statement (Yeung, *Information Theory and Network Coding*, 2nd ed., Springer 2008, esp. Ch. 15; cf. Kaced-Romashchenko and Tang's 2020 REU notes).** Given random variables `(A, B, C, D)`, there exist random variables `(A, B', C, D)` on a common space such that:
  1. `(A, C, D)` has the same joint distribution as in the original tuple;
  2. `(B', C, D)` has the same joint distribution as `(B, C, D)` in the original tuple;
  3. `A` and `B'` are conditionally independent given `(C, D)`.
- **Proof.** Pure probability: take the conditional distribution of B given `(C, D)`, sample B' independently of A from it. No information-theoretic content; the argument is a Kolmogorov-style product-of-kernels construction. In Lean, this is the main missing piece of `Mathlib` infrastructure. `ProbabilityTheory.CondDistrib` / `Kernel.compProd` already give most of it.
- **Difficulty.** Moderate as probability infrastructure but orthogonal to Shannon theory. Once the copy lemma is stated and proven, Zhang-Yeung, DFZ six, and the Matúš family all reduce to Shannon-inequality bookkeeping.
- **New technique?** Yes: this is *the* probability-infrastructure bottleneck. Formalizing it is the single most leveraged piece of work; everything downstream becomes routine.

## 5. Computer-aided discovery

- **ITIP** (Yeung and Yan, 1996) and its descendants **Xitip** (Pulikkoonattu, Perron, Diggavi, EPFL), **oXitip**, **minitip** (Csirmaz), **Citip**, **psitip** (C. T. Li), and the cloud-based **AITIP** are all LP-based checkers for Shannon-type inequalities. They can *detect* non-Shannon-type by observing that LP returns infeasible over the Shannon cone yet a quasi-uniform counterexample is absent. They do not produce formalizable proofs in any proof-assistant sense; at best they emit a Farkas-style non-negative-combination certificate for Shannon-type inequalities.
- **Csirmaz and Matúš** (see Csirmaz's *minitip* and the Kybernetika volume 2020) produce explicit dualizations that yield machine-checkable certificates of Shannon-type derivations.
- **Apte-Massey-Lapidoth** (ITW) and subsequent symbolic/Groebner-style work (e.g. Gao et al., *Proving information inequalities and identities with symbolic computation*, arXiv:2202.02786, 2022; *Proving information inequalities by Gaussian elimination*, arXiv:2401.14916, 2024) push into algebraic-identity checking.
- **ML-aided discovery** (recent) is heuristic: it suggests candidate inequalities that then need a human or copy-lemma proof.
- **Difficulty / relevance.** Not a Lean extension in themselves, but they *generate the input problems* and *pre-certify Shannon portions* of larger proofs. A useful infrastructure goal is an interface in Lean that consumes an ITIP/AITIP Farkas certificate and closes a Shannon-type goal, reserving copy-lemma instantiations for the human.
- **New technique?** No mathematics, but a real proof-automation technique worth wiring in.

## 6. Ingleton, matroids, Kinser

- **References.** A. W. Ingleton, *Representation of matroids*, in Combinatorial Mathematics and its Applications (1971); R. Kinser, *New inequalities for subspace arrangements*, J. Combin. Theory Ser. A 118 (2011), 152-161; T. Boege, *No eleventh conditional Ingleton inequality*, Experimental Math. (2023).
- **Content.** Ingleton's inequality holds for rank functions of representable matroids but is *not* an entropy inequality, so "entropic Ingleton violation" quantifies the gap between the entropic region and the linear-representable region. Kinser gave an infinite family of inequalities on subspace-arrangement ranks that generalize Ingleton (n >= 4 new at each n). Boege settled the minimal-set question for conditional Ingleton at n=4.
- **Difficulty.** Unclear as Lean targets. Ingleton itself is trivially formalizable once Mathlib's matroid rank API is in place. Kinser is more significant but orthogonal to entropy: it's representable-matroid geometry. Entropy/Ingleton violation requires both Zhang-Yeung infrastructure and matroid theory.
- **New technique?** Yes, partially: it brings in the matroid-representability angle, which is a parallel universe to copy-lemma reasoning.

## 7. Connection to PFR

- **Reference.** Gowers, Green, Manners, Tao, *On a conjecture of Marton*, 2023; PFR Lean project `teorth/pfr` with blueprint at <https://teorth.github.io/pfr/>.
- **Content.** The PFR proof uses heavy Shannon-entropy machinery: entropic Ruzsa distance, submodularity, conditional entropy identities, data processing, fibrewise entropy. It was already formalized in Mathlib/PFR by late 2023.
- **Key fact.** The PFR proof uses *only Shannon-type inequalities* plus Ruzsa-distance manipulations (all of which derive from submodularity and chain rule). It does not invoke Zhang-Yeung or any other non-Shannon-type inequality. Tao's blueprint and blog explicitly say the only non-trivial theory needed was "the theory of Shannon entropy."
- **Implication for the Zhang-Yeung project.** Zhang-Yeung formalization does not directly feed PFR. However, it shares a probability-infrastructure boundary: the copy-lemma / conditional-independent-copy construction is also the pattern used in Ruzsa calculus. Formalizing the copy lemma benefits a prospective *extension* of PFR to regimes where non-Shannon inequalities would tighten the constant (currently open research; nothing concrete to formalize yet).
- **Difficulty.** N/A for PFR itself. The overlap is at the level of `Mathlib` probability lemmas about independent copies and kernels.
- **New technique?** Not for Zhang-Yeung; but aligning notation/lemma names with the PFR project is strategically useful.

## 8. Tropicalization / group-theoretic approach

- **Reference.** T. H. Chan, R. W. Yeung, *On a relation between information inequalities and group theory*, IEEE Trans. Inform. Theory 48 (7) (2002), 1992-1995. Follow-up: Chan, *A combinatorial approach to information inequalities*, 2001; and the tropical-probability framework of Matveev-Portegies, *Tropical probability theory and an application to the entropic cone*, Kybernetika 56 (2020), 1133.
- **Content.** Chan-Yeung prove a bijection between entropy inequalities (on quasi-uniform random variables) and inequalities on subgroup indices `[G : H_i ∩ H_j]`, i.e. every linear entropy inequality is equivalent to a linear inequality on subgroup-lattice cardinalities of finite groups. This gives an alternative proof route: to prove Zhang-Yeung, it suffices to prove the corresponding subgroup-index inequality, combinatorially. Matveev-Portegies develop a tropical / asymptotic semiring lifting the same picture.
- **Difficulty for Lean.** In principle a clean, discrete, finitary alternative route (no kernels, no copy construction, no joint distributions). In practice you would need (a) Mathlib's finite-group-index calculus, (b) a lemma that quasi-uniformity reaches the entropic region densely (this itself requires a limit / closure argument), (c) the combinatorial subgroup inequality. Steps (a) and (c) are easier than the probability side; (b) is the same closure difficulty as Matúš.
- **New technique?** Yes: a genuine alternative proof technique, Lean-friendly on the finite-combinatorics side. Worth a separate stream of work if the `Mathlib` group-theory surface is a better fit than its probability surface.

## Recommended extension order

1. Copy lemma as a standalone `Mathlib`-style probability lemma (item 4). Unlocks everything.
2. Zhang-Yeung 1997 conditional inequality as a warm-up / corollary (item 3).
3. DFZ six inequalities as mechanical exercises (item 2).
4. ITIP/Farkas-certificate importer for Shannon-type subgoals (item 5).
5. Matúš infinite family; non-polyhedrality of `Gamma_bar*_4` (item 1). This is the first theorem that goes beyond "one more inequality."
6. Optionally: Chan-Yeung group-theoretic equivalence as an alternative-proofs stream (item 8).
7. Ingleton / matroid angle (item 6) and PFR interop (item 7) are strategic rather than direct extensions.

## Sources

- Matús, *Infinitely many information inequalities*, ISIT 2007: <https://www.semanticscholar.org/paper/Infinitely-Many-Information-Inequalities-Mat%C3%BAs/f6c33bf427061e4c7aa5c7260721743c18798756>
- Matús, *Two constructions on limits of entropy functions*, IEEE Trans. Inform. Theory 53 (2007): <https://ieeexplore.ieee.org/document/4039669/>
- Dougherty-Freiling-Zeger, *Six new non-Shannon information inequalities*: <http://code.ucsd.edu/~zeger/publications/conferences/DoFrZe06-ISIT/DoFrZe06-ISIT.pdf>
- DFZ, *Non-Shannon information inequalities in four random variables*, arXiv:1104.3602: <https://arxiv.org/abs/1104.3602>
- Zhang-Yeung 1997 conditional inequality: <https://ieeexplore.ieee.org/document/641561/>
- Kaced-Romashchenko, *Conditional information inequalities for entropic and almost entropic points*, arXiv:1207.5742: <https://arxiv.org/pdf/1207.5742>
- Tang, *The copy lemma and non-Shannon information inequalities*, UMich REU 2020: <https://lsa.umich.edu/content/dam/math-assets/math-document/reu-documents/ugradreu/2020/Tang,%20Michael_2020%20REU%20Paper.pdf>
- Yeung, *Information Theory and Network Coding*: <http://iest2.ie.cuhk.edu.hk/~whyeung/tempo/main2.pdf>
- AITIP/Xitip/ITIP: <https://xitip.epfl.ch/>, <https://github.com/coldfix/Citip>, <https://github.com/lcsirmaz/minitip>, <https://github.com/cheuktingli/psitip>
- Gao et al., *Proving information inequalities by Gaussian elimination*, arXiv:2401.14916: <https://arxiv.org/pdf/2401.14916>
- Boege, *No eleventh conditional Ingleton inequality*: <https://arxiv.org/pdf/2204.03971>
- Kinser / Ingleton discussion: <https://scholar.lib.vt.edu/MTNS/Papers/164.pdf>
- PFR Lean project: <https://teorth.github.io/pfr/>, blueprint <https://teorth.github.io/pfr/blueprint.pdf>
- Tao blog on PFR blueprint: <https://terrytao.wordpress.com/2023/11/18/formalizing-the-proof-of-pfr-in-lean4-using-blueprint-a-short-tour/>
- Chan-Yeung, *On a relation between information inequalities and group theory*, IEEE TIT 2002: <http://www.mit.edu/~6.454/www_fall_2002/dslun/chan_yeung.pdf>
- Matveev-Portegies, *Tropical probability theory*: <https://www.kybernetika.cz/content/2020/6/1133>
