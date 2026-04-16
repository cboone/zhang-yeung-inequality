---
title: On Characterization of Entropy Function via Information Inequalities
authors: Zhen Zhang and Raymond W. Yeung
year: 1998
venue: IEEE Transactions on Information Theory, Vol. 44, No. 4, pp. 1440-1452
bibtex_key: zhangyeung1998
bibliography: ../papers.bib
doi: 10.1109/18.681320
pdf: zhenzhang1998.pdf
transcription_scope: full
---

## Notation

The paper uses lightweight subset-indexed notation throughout. For $n \geq 1$ let $\mathcal{N}_n := \{1, 2, \ldots, n\}$ and let $\mathcal{X} = \{X_1, \ldots, X_n\}$ be an $n$-tuple of jointly distributed discrete random variables. For $\alpha \subseteq \mathcal{N}_n$ write $X_\alpha := \{X_i : i \in \alpha\}$ and $H(\alpha) := H(X_\alpha)$ (with $H(\varnothing) := 0$ by convention, since $X_\varnothing$ is a constant random variable).

| Paper | Meaning | Modern equivalent |
| --- | --- | --- |
| $\mathcal{N}_n$ | Ground index set $\{1, 2, \ldots, n\}$ | -- |
| $X_\alpha$ | Joint RV indexed by $\alpha \subseteq \mathcal{N}_n$ | $(X_i)_{i \in \alpha}$ |
| $H(\alpha)$ | Joint entropy of $X_\alpha$ | $H(X_\alpha)$ |
| $I(X_\alpha; X_\beta \mid X_\gamma)$ | Conditional mutual information | $I(X_\alpha; X_\beta \mid X_\gamma)$ |
| $\mathcal{H}_n$ | All functions $2^{\mathcal{N}_n} \to [0, \infty)$ | -- |
| $\Gamma_n$ | Cone of functions satisfying the basic (Shannon) inequalities, viewed as a subset of $\mathbb{R}^{2^n - 1}$ | Shannon outer bound |
| $\Gamma^*_n$ | Set of entropy functions of $n$-tuples of discrete RVs (the **constructible** functions) | Entropic region |
| $\mathrm{cl}(\Gamma^*_n)$ | Closure of $\Gamma^*_n$ (the **asymptotically constructible** functions) | Almost-entropic region |
| $h$ (Section II, eq. 30-31) | Atom-valued reparametrization of a function $f : 2^{\mathcal{N}_n} \to \mathbb{R}$ | -- |
| $\mathcal{Z}(f)$ (Section II, eq. 42) | Paper-specific quantity controlling the inner bound of Theorem 6 | -- |

The paper freely switches logarithm base. Theorem 6's concrete construction uses base $3$ so that the three symmetric ternary RVs have entropy $1$. All inequalities in Theorems 3-5 are log-base-agnostic.

## Scope

The paper is the birthplace of the first non-Shannon-type information inequality. Its central contribution is Theorem 3, the **Zhang-Yeung inequality**, together with Theorem 4, which uses it to prove that the Shannon outer bound $\Gamma_n$ strictly contains the almost-entropic region $\mathrm{cl}(\Gamma^*_n)$ for every $n \geq 4$. This transcription covers every formal statement of the paper (propositions, theorems, and lemmas) together with the copy-lemma construction underlying the main proof. The seven explicit constructions driving Theorem 6's inner bound are recorded at a structural level; the 5-page case analysis that ties them together is summarized but not transcribed line by line.

## The Shannon outer bound and the entropic region

### Proposition 1 (basic information inequalities, eq. 4-5)

::: {.proposition}
**Proposition 1** ([@zhangyeung1998, Prop. 1]). For any three subsets $\alpha, \beta, \gamma$ of $\mathcal{N}_n$ and any set of $n$ jointly distributed discrete random variables,

$$I(X_\alpha; X_\beta \mid X_\gamma) \geq 0.$$

Equivalently, by the chain rule, every basic inequality is implied by the subset obtained when $|\alpha| = |\beta| = 1$ and $|\gamma|$ is arbitrary (the **elemental** inequalities; cf. [@yeung1997framework]):

$$I(X_i; X_j \mid X_\gamma) \geq 0, \qquad i \neq j, \quad \gamma \subseteq \mathcal{N}_n \setminus \{i, j\}.$$
:::

### Proposition 2 (basic inequalities lifted to the entropy function, eq. 8-10)

::: {.proposition}
**Proposition 2** ([@zhangyeung1998, Prop. 2]). Let $f = H$ be the entropy function of some jointly distributed discrete random variables. Then $f : 2^{\mathcal{N}_n} \to [0, \infty)$ satisfies:

1. **Submodularity.** For any two subsets $\alpha, \beta$ of $\mathcal{N}_n$,
$$f(\alpha) + f(\beta) \geq f(\alpha \cup \beta) + f(\alpha \cap \beta). \qquad (8)$$
2. **Monotonicity.** $\alpha \subseteq \beta$ implies $f(\alpha) \leq f(\beta) \qquad (9)$.
3. **Nonnegativity.** $f(\alpha) \geq 0 \qquad (10)$, with $f(\varnothing) = 0$.
:::

### Definitions (Section I)

::: {.definition}
**Definition 1** ([@zhangyeung1998, Def. 1]). A function $f : 2^{\mathcal{N}_n} \to [0, \infty)$ is **constructible** if there exists an $n$-tuple of jointly distributed discrete random variables $X_1, \ldots, X_n$ such that $f(\alpha) = H(X_\alpha)$ for every $\alpha \subseteq \mathcal{N}_n$. The set of constructible functions is denoted $\Gamma^*_n$ (eq. 12).
:::

::: {.definition}
**Definition 2** ([@zhangyeung1998, Def. 2]). A function $f : 2^{\mathcal{N}_n} \to [0, \infty)$ is **asymptotically constructible** if there exists a sequence of $n$-tuples of discrete random variables whose entropy functions converge to $f$. The set of asymptotically constructible functions is exactly $\mathrm{cl}(\Gamma^*_n)$.
:::

Let $\Gamma_n$ denote the cone of functions on $2^{\mathcal{N}_n}$ satisfying the three properties of Proposition 2. Then $\Gamma^*_n \subseteq \Gamma_n$, and $\Gamma_n$ is the **Shannon outer bound** of $\Gamma^*_n$.

### Prior results

::: {.theorem}
**Theorem 1** ([@zhangyeung1998, Thm. 1], originally [@zhangyeung1997]).

$$\mathrm{cl}(\Gamma^*_2) = \Gamma_2, \qquad \mathrm{cl}(\Gamma^*_3) = \Gamma_3. \qquad (13\text{-}14)$$
:::

::: {.theorem}
**Theorem 2** ([@zhangyeung1998, Thm. 2], originally [@zhangyeung1997]). For any four discrete random variables $X, Y, Z, U$, if $I(X; Y \mid Z) = 0$ and $I(X; Y \mid U) = 0$, then

$$I(X; Y) \leq I(X; Y \mid Z, U) + I(Z; U) + I(X; U \mid Z) + I(Y; Z \mid U). \qquad (16\text{-}17)$$

Consequently, the conditional independence structure of $(X, Y, Z, U)$ is not freely axiomatizable; in particular $\mathrm{cl}(\Gamma^*_4) \neq \Gamma_4$ under the corresponding conditional restriction (eq. 18).
:::

Theorem 2 is a *conditional* non-Shannon inequality: it only applies when two mutual informations vanish. The 1998 paper's central advance is removing this conditionality.

## Main results

### Theorem 3 (the Zhang-Yeung inequality)

::: {.theorem}
**Theorem 3** ([@zhangyeung1998, Thm. 3], eq. 20-23). For any four discrete random variables $X, Y, Z, U$,

$$2 \, I(Z; U) \leq I(X; Y) + I(X; Z, U) + 3 \, I(Z; U \mid X) + I(Z; U \mid Y). \qquad (21)$$

By swapping the roles of $X$ and $Y$, the symmetric inequality

$$2 \, I(Z; U) \leq I(X; Y) + I(Y; Z, U) + 3 \, I(Z; U \mid Y) + I(Z; U \mid X) \qquad (22)$$

also holds. Averaging (21) and (22) gives the symmetric form

$$2 \, I(Z; U) \leq I(X; Y) + \tfrac{1}{2}\bigl(I(X; Z, U) + I(Y; Z, U)\bigr) + 2\bigl(I(Z; U \mid X) + I(Z; U \mid Y)\bigr). \qquad (23)$$

Equivalently, defining

$$\Delta(Z, U \mid X, Y) := I(Z; U) - I(Z; U \mid X) - I(Z; U \mid Y), \qquad (20)$$

the inequality (23) becomes

$$\Delta(Z, U \mid X, Y) \leq \tfrac{1}{2} \, I(X; Y) + \tfrac{1}{4}\bigl(I(X; Z, U) + I(Y; Z, U)\bigr).$$

This inequality does **not** follow from the basic Shannon inequalities (Theorem 4).
:::

### Theorem 4 (Shannon incompleteness, eq. 26)

::: {.theorem}
**Theorem 4** ([@zhangyeung1998, Thm. 4]). For every $n \geq 4$,

$$\mathrm{cl}(\Gamma^*_n) \subsetneq \Gamma_n.$$
:::

The paper's proof sketch (p. 1442) observes that it suffices to prove the claim for $n = 4$: given a $4$-variable witness, embedding it on the first four coordinates of an $n$-tuple of random variables (with the remaining $n - 4$ set to a constant) produces an $n$-variable witness. The $n = 4$ witness is the explicit function $F : 2^{\mathcal{N}_4} \to [0, \infty)$ defined on p. 1443 (satisfying all 15 elemental Shannon inequalities but violating Theorem 3); concretely the roadmap's milestone M4 plans to reconstruct it as

$$F(\alpha) := \begin{cases} 0 & \alpha = \varnothing, \\ 2a & |\alpha| = 1, \\ 4a & \alpha \in \bigl\{\{X, Y\}\bigr\}, \\ 3a & \alpha \in \bigl\{\{X, Z\}, \{Y, Z\}, \{Z, U\}\bigr\}, \\ 4a & |\alpha| \geq 3, \end{cases}$$

for any $a > 0$, after identifying $\mathcal{N}_4$ with $\{X, Y, Z, U\}$.

### Theorem 5 (generalization to $n + 2$ variables, eq. 27-28)

::: {.theorem}
**Theorem 5** ([@zhangyeung1998, Thm. 5]). For any $n \geq 2$ and any $n + 2$ discrete random variables $U, Z, X_1, \ldots, X_n$, and for any $i \in \{1, \ldots, n\}$,

$$n \, I(U; Z) \leq \sum_{j = 1}^{n} I(U; Z \mid X_j) + n \, I(U; Z \mid X_i) + I(X_i; U, Z) + \sum_{j = 1}^{n} H(X_j) - H(X_1, \ldots, X_n). \qquad (27)$$

Averaging (27) over $i \in \{1, \ldots, n\}$ yields the symmetric form

$$n \, I(U; Z) \leq \sum_{j = 1}^{n} I(U; Z \mid X_j) + \sum_{j = 1}^{n} I(U; Z \mid X_j) + \tfrac{1}{n} \sum_{j = 1}^{n} I(X_j; U, Z) + \sum_{j = 1}^{n} H(X_j) - H(X_1, \ldots, X_n). \qquad (28)$$

The proof is the same as Theorem 3 combined with induction on $n$ (omitted in the paper).
:::

> **Transcription caveat.** The pdftotext extraction garbled the right-hand sides of (27) and (28). The form above is the statement referenced by the formalization roadmap (`docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md`, Section 4 and M5); verify against the source PDF before committing the Lean statement.

### Theorem 6 (inner bound of $\mathrm{cl}(\Gamma^*_4)$, Section II eq. 43)

The paper reparametrizes $f : 2^{\mathcal{N}_n} \to \mathbb{R}$ using the atom chart $h_f$ defined for pairs $(\alpha, \beta)$ with $\alpha \neq \varnothing$ by

$$h_f(\alpha, \beta) := \sum_{\sigma \subseteq \alpha^{\mathsf c}} (-1)^{|\sigma|} f(\alpha \cup \sigma \cup \beta) - (\text{terms not involving } \alpha), \qquad (30\text{-}31)$$

and then defines

$$\mathcal{Z}(f) := \min_\sigma \bigl[\text{expression in } h_f \text{ at atoms determined by the permutation } \sigma \text{ of } \{X, Y, Z, U\}\bigr], \qquad (42)$$

where the minimum is over all permutations of the four-element index set.

::: {.theorem}
**Theorem 6** ([@zhangyeung1998, Thm. 6], eq. 43). Every function $f \in \Gamma_4$ with $\mathcal{Z}(f) \geq 0$ lies in $\mathrm{cl}(\Gamma^*_4)$. Equivalently, the set $\{f \in \Gamma_4 : \mathcal{Z}(f) \geq 0\}$ is an inner bound of $\mathrm{cl}(\Gamma^*_4)$.
:::

The paper notes that $\mathcal{Z}(f)$ may be negative for some $f \in \Gamma_4$ (p. 1445, the projective-plane example), so the inner bound is strict; combined with Theorem 3's outer bound, this leaves the exact description of $\mathrm{cl}(\Gamma^*_4)$ open.

> **Transcription caveat.** The exact pair-of-subsets argument to $h_f$ and the minimum-over-permutations expression defining $\mathcal{Z}$ rely on equations whose bodies did not survive the pdftotext extraction. Verify against the source PDF (pp. 1443-1444) before formalizing Theorem 6.

## Lemmas

### Lemma 1 (atom-to-subset inversion, eq. 34)

::: {.lemma}
**Lemma 1** ([@zhangyeung1998, Lem. 1]). For the atom reparametrization $h$,

$$h(\alpha, \beta) = \sum_{\sigma \subseteq \alpha^{\mathsf c}} (-1)^{|\sigma|} \bigl[f(\alpha \cup \sigma \cup \beta) - f(\sigma \cup \beta)\bigr],$$

where $\alpha^{\mathsf c}$ denotes the complement of $\alpha$ in $\mathcal{N}_n$.
:::

> **Transcription caveat.** The right-hand side above is our best reconstruction of eq. (34) from the surrounding paper text; the two-column pdftotext output reduced it to the numeric label only. Verify against the source PDF.

### Lemma 2 (the copy lemma, eq. 44-45)

This is the central proof artifact of the paper. In the modern literature, this construction (together with its extension to any number of "copies" over a shared marginal) is called the **copy lemma**.

::: {.lemma}
**Lemma 2** ([@zhangyeung1998, Lem. 2]). Let $(X, Y, Z, U)$ be four jointly distributed discrete random variables on a probability space with joint distribution $\mu(x, y, z, u)$. Define the six-variable distribution

$$p(x, y, z, u, x', y') := \frac{\mu(x, y, z, u) \cdot \mu(x', y', z, u)}{\mu(z, u)} \qquad (44)$$

wherever $\mu(z, u) > 0$ (and $0$ otherwise). Equivalently, $p$ is the law of $(X, Y, Z, U)$ augmented with independent copies $(X', Y')$ of $(X, Y)$ drawn from the conditional distribution $\mu(\cdot, \cdot \mid Z, U)$. Then:

1. **Identical marginals.** The $(X, Y, Z, U)$-marginal and the $(X', Y', Z, U)$-marginal of $p$ both equal $\mu$.
2. **Conditional independence.** Under $p$, the pair $(X, Y)$ is conditionally independent of $(X', Y')$ given $(Z, U)$:
$$I_p\bigl((X, Y); (X', Y') \mid (Z, U)\bigr) = 0.$$
3. **Entropy identity** (eq. 45). The conditional joint entropy of all four named random variables under $p$ admits a decomposition in terms of mutual informations of the six random variables; this identity is what Section III uses to derive Theorem 3.
:::

The construction is the two-step kernel composition $p = \mu \otimes \kappa$ where $\kappa$ is the Markov kernel from $(Z, U)$ to $(X', Y')$ induced by $\mu(\cdot, \cdot \mid Z, U)$; equivalently, $(X', Y')$ is a conditionally independent "copy" of $(X, Y)$ over the common $(Z, U)$ coordinates.

> **Transcription caveat.** Eq. (45) is the single most important equation in the paper for the formalization project, and its right-hand side did not survive the pdftotext extraction. Verify it line by line against the source PDF before transcribing into Lean.

## Proof of Theorem 3 (Section III)

The proof uses Lemma 2 to construct the six-variable joint distribution $p$ and then proves the companion bound

$$I_p(X; Y') + I_p(X; Z, U) \geq I_p(X; Y) + \ldots$$

and its symmetric swap. The data-processing inequality together with the identity $I(X; Y) = I(X; Y')$ (which follows from Lemma 2's marginal identity and the conditional-independence structure) then yields (21) and (22) after straightforward Shannon algebra. The proof is mechanical once Lemma 2 is in place.

The paper remarks at the end of Section III (p. 1446) that all "missing terms" in the bound can be made explicit using the six-variable joint; these terms are listed as corollaries but not given independent theorem status.

## Proof of Theorem 6 (Section IV)

Section IV proves the inner bound via seven explicit probabilistic constructions, labeled $f_1, \ldots, f_7$. Each construction takes values on the atoms of $2^{\mathcal{N}_4}$; their chart is on p. 1447.

- **Construction 1** ($f_1$): indicator of a fixed atom. Used via Lemma 4 to show that nonnegative atom-valued functions are asymptotically constructible.
- **Constructions 2-7** ($f_2, \ldots, f_7$): seven more elaborate atom assignments. $f_2$ is symmetric over the four coordinates; $f_3^Z$ (and its permutations) places mass on atoms involving a distinguished single coordinate; $f_4$-$f_7$ are further symmetry-broken constructions.

Supporting lemmas:

- **Lemma 3** ([@zhangyeung1998, Lem. 3]). If $f, g \in \mathrm{cl}(\Gamma^*_n)$ and $\lambda \geq 0$, then $f + g \in \mathrm{cl}(\Gamma^*_n)$ and $\lambda f \in \mathrm{cl}(\Gamma^*_n)$. That is, $\mathrm{cl}(\Gamma^*_n)$ is a convex cone.
- **Lemma 4** ([@zhangyeung1998, Lem. 4]). Nonnegative atom-valued functions are asymptotically constructible. (Proved via Construction 1 and Lemma 3.)

The main argument is a case analysis (p. 1448-1451) showing that every function $f \in \Gamma_4$ with $\mathcal{Z}(f) \geq 0$ can be reduced via a sequence of **legal operations** (subtracting a nonnegative multiple of one of $f_2, \ldots, f_7$ while preserving seminonnegativity) to a nonnegative function, which is asymptotically constructible by Lemma 4. The case analysis splits on whether one of $f_2$ or $f_3^\bullet$ is forced to zero, then recursively refines.

> **Transcription caveat.** The seven constructions are defined in the paper using atom charts that did not render cleanly in the pdftotext extraction. If Theorem 6 becomes a formalization target (currently **out of scope** per the roadmap's S2 decision), the construction definitions must be verified against the source PDF pp. 1446-1447.

## Concluding remarks (Section V)

The authors remark that:

- Theorem 3 is the first unconditional non-Shannon inequality; its discovery originated from *failed* attempts to prove the opposite conjecture via the constructions of Theorem 6.
- The exact region $\mathrm{cl}(\Gamma^*_4)$ remains open; the gap between Theorems 3 and 6 is strict.
- "Missing terms" in (21)-(22) are determined explicitly by the six-variable joint of Lemma 2, in the hope that this may lead to further inequalities.
- Open applications: multiuser channel coding, multiuser source coding, probabilistic reasoning, relational databases.

## Formalization cross-references

The formalization targets in the roadmap (`docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md`, Sections 4-6) map to this transcription as follows.

| Paper statement | Formalization target | Scope decision |
| --- | --- | --- |
| Proposition 1 (basic inequalities) | PFR `ForMathlib/Entropy/{Basic,MutualInfo}`; available upstream | External |
| Proposition 2 (submodularity, monotonicity, nonnegativity) | `ZhangYeung/Theorem4.lean` (Shannon cone definition); PFR provides per-RV versions | Part of M4 |
| Theorem 1 (cl $\Gamma^*_n = \Gamma_n$ for $n \leq 3$) | Not formalized (cited as context only) | Out of scope |
| Theorem 2 (conditional non-Shannon inequality from 1997) | Not formalized (cited as historical precursor) | Out of scope |
| **Lemma 2 (copy lemma)** | `ZhangYeung/CopyLemma.lean` | **Core artifact, Mathlib-ready (M2)** |
| **Theorem 3 (Zhang-Yeung inequality)** | `ZhangYeung/Theorem3.lean` | **Core (M3)** |
| $\Delta(Z, U \mid X, Y)$ (eq. 20) | `ZhangYeung/Delta.lean` | Core (M1) |
| **Theorem 4 (cl $\Gamma^*_n \neq \Gamma_n$ for $n \geq 4$)** | `ZhangYeung/Theorem4.lean` (witness $F$) | **Core (M4)** |
| Theorem 5 ($(n + 2)$-variable generalization) | `ZhangYeung/Theorem5.lean` | Stretch (M5) |
| Theorem 6 (inner bound via atom charts) | Not formalized | Out of scope |
| Lemma 1 (atom-to-subset identity) | Only if Theorem 6 is formalized | Out of scope |
| Lemmas 3-4, Constructions 1-7 | Only if Theorem 6 is formalized | Out of scope |

The central formalization artifact is therefore **Lemma 2**, generalized away from paper-specific notation and proved on four arbitrary $\mathsf{Fintype}$-valued random variables. Theorem 3 is a short Shannon-algebra derivation from Lemma 2. Theorem 4's witness $F$ is a 15-constraint `norm_num`/`linarith` verification once the Shannon cone is defined.

## Open transcription items

Each caveat below marks a place where the pdftotext extraction was insufficient and the source PDF needs to be consulted before the statement can be considered paper-faithful. In priority order:

1. **Eq. (45) (Lemma 2's entropy identity).** Load-bearing for M2; verify before formalizing the copy lemma.
2. **Eq. (21), (22), (23), (27), (28).** The Zhang-Yeung inequality and its $(n + 2)$-variable generalization. The forms above match the roadmap but should be verified against the PDF to rule out sign errors or coefficient drift.
3. **Witness $F$ in Theorem 4.** The specific values of $F$ on $2^{\mathcal{N}_4}$ need verification; the paper's table on p. 1443 is the source.
4. **Lemma 1 (eq. 34).** Only if Theorem 6 becomes in scope.
5. **$\mathcal{Z}(f)$ definition and atom charts.** Only if Theorem 6 becomes in scope.

## References (from the paper)

Only the references actually used in the formalization roadmap are transcribed to BibTeX in `references/papers.bib`:

- **[39]** Zhang and Yeung, *A Non-Shannon Type Conditional Inequality of Information Quantities*, IEEE TIT 43(6), 1997 (= `zhangyeung1997`). Source of Theorems 1 and 2.
- **[35]** Yeung, *A Framework for Linear Information Inequalities*, IEEE TIT 43, 1997 (= `yeung1997framework`). Source of the regions $\Gamma_n$, $\Gamma^*_n$, and the elemental inequalities.

The remaining bibliography entries (Campbell, Hu, McGill, Watanabe, Csiszár-Körner, Han, Fujishige, Yeung [34], Kawabata-Yeung, Matús̆, Studený, Pearl, etc.) are context for the historical narrative in Section I and are not needed for the formalization targets.
