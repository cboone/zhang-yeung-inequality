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

## Abstract

Given $n$ discrete random variables $\Omega = \{X_1, \ldots, X_n\}$, associated with any subset $\alpha$ of $\{1, 2, \ldots, n\}$, there is a joint entropy $H(X_\alpha)$ where $X_\alpha = \{X_i : i \in \alpha\}$. This can be viewed as a function defined on $2^{\{1, 2, \ldots, n\}}$, taking values in $[0, +\infty)$. The nonnegativity of the joint entropies implies that this function is nonnegative; the nonnegativity of the conditional joint entropies implies that this function is nondecreasing; and the nonnegativity of the conditional mutual informations implies that this function has the property

$$H(\alpha) + H(\beta) \geq H(\alpha \cup \beta) + H(\alpha \cap \beta).$$

These properties are the so-called basic information inequalities of Shannon's information measures. The paper asks whether these properties fully characterize the entropy function. To make this question precise, the entropy function is viewed as a $(2^n - 1)$-dimensional vector whose coordinates are indexed by the nonempty subsets of the ground set. Let $\Gamma_n$ be the cone of all such vectors satisfying the three properties above, and let $\Gamma_n^*$ be the set of all $(2^n - 1)$-dimensional vectors corresponding to entropy functions of sets of $n$ discrete random variables. The question is whether $\mathrm{cl}(\Gamma_n^*) = \Gamma_n$ for every $n$. The answer is yes for $n = 2$ and $3$, as proved in earlier work. The main discovery of the paper is a new information-theoretic inequality involving four discrete random variables which gives a negative answer to this fundamental problem in information theory: $\mathrm{cl}(\Gamma_n^*)$ is strictly smaller than $\Gamma_n$ whenever $n > 3$. While this new inequality gives a nontrivial outer bound to the cone $\mathrm{cl}(\Gamma_4^*)$, an inner bound for $\mathrm{cl}(\Gamma_4^*)$ is also given. The inequality is also extended to any number of random variables.

Index terms: entropy, inequality, information measure, mutual information.

## Front Matter

Manuscript received December 12, 1996; revised November 15, 1997. The work of Z. Zhang was supported in part by the National Science Foundation under Grant NCR-9502828. The work of R. W. Yeung was supported in part by the Research Grant Council of Hong Kong under Earmarked Grant CUHK 332/96E.

Z. Zhang was with the Department of Electrical Engineering-Systems, Communication Sciences Institute, University of Southern California, Los Angeles, CA 90089-2565 USA (`zzhang@milly.usc.edu`).

R. W. Yeung was with the Department of Information Engineering, the Chinese University of Hong Kong, Shatin, N.T., Hong Kong, China (`whyeung@ie.cuhk.edu.hk`).

Publisher Item Identifier: `S 0018-9448(98)03630-X`.

## Notation

The paper uses lightweight subset-indexed notation throughout. For $n \geq 1$ let $\mathcal{N}_n := \{1, 2, \ldots, n\}$ and let $\mathcal{X} = \{X_1, \ldots, X_n\}$ be an $n$-tuple of jointly distributed discrete random variables. For $\alpha \subseteq \mathcal{N}_n$ write $X_\alpha := \{X_i : i \in \alpha\}$ and $H(\alpha) := H(X_\alpha)$ (with $H(\varnothing) := 0$ by convention, since $X_\varnothing$ is a constant random variable).

| Paper | Meaning | Modern equivalent |
| --- | --- | --- |
| $\mathcal{N}_n$ | Ground index set $\{1, 2, \ldots, n\}$ | -- |
| $X_\alpha$ | Joint RV indexed by $\alpha \subseteq \mathcal{N}_n$ | $(X_i)_{i \in \alpha}$ |
| $H(\alpha)$ | Joint entropy of $X_\alpha$ | $H(X_\alpha)$ |
| $I(X_\alpha; X_\beta \mid X_\gamma)$ | Conditional mutual information | $I(X_\alpha; X_\beta \mid X_\gamma)$ |
| $\mathcal{F}_n$ | All functions $2^{\mathcal{N}_n} \to [0, \infty)$ | -- |
| $\Gamma_n$ | Cone of functions satisfying the basic (Shannon) inequalities, viewed as a subset of $\mathbb{R}^{2^n - 1}$ | Shannon outer bound |
| $\Gamma^*_n$ | Set of entropy functions of $n$-tuples of discrete RVs (the **constructible** functions) | Entropic region |
| $\mathrm{cl}(\Gamma^*_n)$ | Closure of $\Gamma^*_n$ (the **asymptotically constructible** functions) | Almost-entropic region |
| $\tilde{\Gamma}_4$ (Section II, eq. 25) | Outer bound defined from Theorem 3's inequality in function coordinates | -- |
| $F[\alpha \mid \beta]$ (Section II, eq. 30) | Atom-valued reparametrization of a function $F : 2^{\mathcal{N}_n} \to \mathbb{R}$ | -- |
| $S_F$ (Section II, eq. 37) | Paper-specific quantity controlling the inner bound of Theorem 6 | -- |
| $\hat{\Gamma}_4$ (Section II, eq. 42) | Inner bound of $\mathrm{cl}(\Gamma^*_4)$ defined via $S_F$ | -- |

The paper freely switches logarithm base. Theorem 6's concrete construction uses base $3$ so that the three symmetric ternary RVs have entropy $1$. All inequalities in Theorems 3-5 are log-base-agnostic.

Section I begins by fixing the subset-indexed notation

$$X_\alpha := \{X_i : i \in \alpha\}. \qquad (1)$$

With $X_\varnothing$ taken to be a constant random variable, it writes

$$I_\Omega(\alpha; \beta \mid \gamma) := I(X_\alpha; X_\beta \mid X_\gamma), \qquad (2)$$

$$H_\Omega(\alpha) := H(X_\alpha). \qquad (3)$$

Sometimes the paper suppresses the subscript $\Omega$. It then views the entropy function of $\Omega$ as the map

$$H_\Omega : 2^{\mathcal{N}_n} \to [0, \infty), \qquad \alpha \mapsto H(X_\alpha), \qquad (6)$$

and recalls that every basic Shannon information measure is a linear function of the joint entropies; in particular,

$$I(\alpha; \beta \mid \gamma) = H(\alpha \cup \gamma) + H(\beta \cup \gamma) - H(\alpha \cup \beta \cup \gamma) - H(\gamma). \qquad (7)$$

The introduction begins by considering jointly distributed discrete random variables $\Omega_n = \{X_i : i = 1, \ldots, n\}$. The basic Shannon information measures associated with these variables include all joint entropies, conditional entropies, mutual informations, and conditional mutual informations involving some of these random variables. The associated entropy function $H_\Omega$ can be viewed as a function on $2^{\mathcal{N}_n}$, and the stated goal of the paper is to study this function for all possible sets of $n$ discrete random variables.

## Scope

The paper is the birthplace of the first non-Shannon-type information inequality. Its central contribution is Theorem 3, the **Zhang-Yeung inequality**, together with Theorem 4, which uses it to prove that the Shannon outer bound $\Gamma_n$ strictly contains the almost-entropic region $\mathrm{cl}(\Gamma^*_n)$ for every $n \geq 4$. This transcription now covers the paper's abstract, formal statements, main prose sections, constructions, atom charts, proof skeletons, acknowledgment, and full bibliography. The only remaining compression is that some repetitive inequality checks inside the deepest symmetric branches of the Theorem 6 proof are described structurally rather than reproduced symbol-for-symbol.

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
3. **Normalization.** $f(\varnothing) = 0 \qquad (10)$.
:::

In particular, (9) and (10) imply $f(\alpha) \geq 0$ for every $\alpha \subseteq \mathcal{N}_n$.

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
**Theorem 2** ([@zhangyeung1998, Thm. 2], originally [@zhangyeung1997]). For any four discrete random variables $X, Y, Z, U$, if

$$I(X; Y) = I(X; Y \mid Z) = 0, \qquad (16)$$

then

$$I(X; Y \mid Z, U) \leq I(Z; U \mid X, Y) + I(X; Y \mid U). \qquad (17)$$

The paper also recalls that [@zhangyeung1997] proves this implies

$$\mathrm{cl}(\Gamma^*_4) \neq \Gamma_4. \qquad (18)$$
:::

Theorem 2 is a *conditional* non-Shannon inequality: it only applies under the hypotheses $I(X; Y) = I(X; Y \mid Z) = 0$. The 1998 paper's central advance is removing this conditionality.

### Conjecture 1 (eq. 19)

::: {.conjecture}
**Conjecture 1** ([@zhangyeung1998, Conj. 1]). For every $n \geq 4$,

$$\mathrm{cl}(\Gamma_n^*) = \Gamma_n. \qquad (19)$$
:::

To give an affirmative answer to this problem is the stated goal of the paper. The paper is organized as follows: Section II states the main results and introduces the relevant definitions and notation; Sections III and IV prove the main theorems; Section V summarizes the findings and raises further problems.

### Literature Survey (Section I closing prose)

Before closing the introduction, the paper gives a brief account of earlier work relevant to the subject matter of the paper. Since Shannon's information measures are the most important measures in information theory, researchers in this area have been investigating their structural properties since the 1950s. The early work cited in the paper includes Campbell [2], Hu [10], McGill [21], and Watanabe [31], [32].

McGill [21] proposed a multiple mutual information for any number of random variables, generalizing Shannon's mutual information for two variables. Its properties were further studied by Kawabata and Yeung [6], Tsujishita [30], and Yeung [37].

Hu [10] was the first attempt to establish an analogy between information theory and set theory. Toward this end, he defined a formal substitution of symbols under a set-additive function $\mu$; for example,

$$H(X) + H(Y) = H(X, Y) + I(X; Y)$$

corresponds to

$$\mu(X) + \mu(Y) = \mu(X \cup Y) + \mu(X \cap Y).$$

Han [7], [9] pushed this further by emphasizing that every linear information expression can be rewritten as a linear combination of unconditional joint entropies, via repeated use of identities such as

$$I(X; Y \mid Z) = H(X, Z) + H(Y, Z) - H(X, Y, Z) - H(Z).$$

Han proved that a linear combination of unconditional joint entropies is always equal to zero if and only if all the coefficients are zero. He also established a necessary and sufficient condition for a symmetrical linear information expression to be always nonnegative, and a necessary and sufficient condition for a linear information expression involving three random variables to be always nonnegative. In [9], he raised the important question of what linear combinations of unconditional joint entropies are always nonnegative. In his work, Han viewed a linear combination of unconditional joint entropies as a vector space, and developed a lattice-theoretic description of Shannon's information measures with which some notations can be greatly simplified. During this time, Fujishige [5] found that the entropy function is a polymatroid [33].

In the 1990s, Yeung [34] further developed Hu's work into an explicit set-theoretic formulation of Shannon's information measures. Specifically, he showed that Shannon's information measures uniquely define a signed measure, called the $I$-measure, on a properly defined field. With this formulation, Shannon's information measures can formally be viewed as a signed measure, and McGill's multiple mutual information is naturally included. As a consequence, set-theoretic techniques can be used for the manipulation of information expressions, and the use of information diagrams becomes justified. Kawabata and Yeung [6] studied the structure of the $I$-measure when the random variables form a Markov chain, and Yeung, Lee, and Ye [36] extended this to Markov random fields.

Most directly relevant is Yeung [35], which defined the set of all constructible entropy functions and observed that whether an information inequality, linear or nonlinear, always holds is completely characterized by this region. This geometrical framework enables a unified description of all information inequalities, unconstrained or constrained, which are implied by the nonnegativity of Shannon's information measures, called the basic inequalities. This gives a partial answer to Han's question and directly leads to the question whether all information inequalities which always hold are implied by the basic inequalities for the same set of random variables, equivalently whether $\mathrm{cl}(\Gamma_n^*) = \Gamma_n$. With the result in [39] that $\mathrm{cl}(\Gamma_n^*)$ is a convex cone, answering Han's question becomes equivalent to determining $\Gamma_n^*$. In [37], the same region is used to study the distributed source-coding problem.

As a consequence of [35], the software ITIP (Information Theoretic Inequality Prover) [38] was developed, which can verify all linear information inequalities involving a definite number of random variables that are implied by the basic inequalities for the same set of random variables.

Along another line, motivated by the study of the logic of integrity constraints from databases, researchers in probabilistic reasoning spent much effort in characterizing the compatibility of conditional independence relations among random variables. This effort was launched by a seminal paper of Dawid [4], in which he proposed four axioms as heuristic properties of conditional independence. In information-theoretic terms, these four axioms can be summarized by the implication

$$I(X; Y, Z \mid U) = 0 \implies I(X; Y \mid U) = 0 \quad \text{and} \quad I(X; Z \mid Y, U) = 0.$$

Subsequent work on this subject was done by Pearl and his collaborators in the 1980s and summarized in Pearl's book [23]. Pearl conjectured that Dawid's four axioms completely characterize the conditional independence structure of any joint distribution. This conjecture, however, was refuted by the work of Studeny [25]. Since then, Matus and Studeny wrote a series of papers on this problem [13]-[29]. They solved the problem for up to four random variables. It has been shown in [35] that the problem of characterizing the compatibility of conditional independence relations among random variables is a subproblem of the determination of $\Gamma_n^*$.

## Main results

### Theorem 3 (the Zhang-Yeung inequality)

::: {.theorem}
**Theorem 3** ([@zhangyeung1998, Thm. 3], eq. 20-23). For any four discrete random variables $X, Y, Z, U$,

$$\Delta(Z, U \mid X, Y) \leq \tfrac{1}{2} \bigl[I(X; Y) + I(X; Z, U) + I(Z; U \mid X) - I(Z; U \mid Y)\bigr]. \qquad (21)$$

By swapping the roles of $X$ and $Y$, the symmetric inequality

$$\Delta(Z, U \mid X, Y) \leq \tfrac{1}{2} \bigl[I(X; Y) + I(Y; Z, U) - I(Z; U \mid X) + I(Z; U \mid Y)\bigr] \qquad (22)$$

also holds. Averaging (21) and (22) gives the symmetric form

$$\Delta(Z, U \mid X, Y) \leq \tfrac{1}{2} \, I(X; Y) + \tfrac{1}{4}\bigl[I(X; Z, U) + I(Y; Z, U)\bigr]. \qquad (23)$$

Where we define

$$\Delta(Z, U \mid X, Y) := I(Z; U) - I(Z; U \mid X) - I(Z; U \mid Y). \qquad (20)$$

This inequality does **not** follow from the basic Shannon inequalities (Theorem 4).
:::

### Auxiliary definitions for Theorem 4 (eq. 24-25)

For $F \in \mathcal{F}_n$ and subsets $\alpha, \beta, \gamma \subseteq \mathcal{N}_n$, the paper defines

$$I_F(\alpha; \beta \mid \gamma) := F(\alpha \cup \gamma) + F(\beta \cup \gamma) - F(\alpha \cup \beta \cup \gamma) - F(\gamma).$$

When $\gamma = \varnothing$, it writes $I_F(\alpha; \beta)$ in place of $I_F(\alpha; \beta \mid \varnothing)$. For distinct indices $i, j, k, l$,

$$\Delta_F(i, j \mid k, l) := I_F(\{i\}; \{j\}) - I_F(\{i\}; \{j\} \mid \{k\}) - I_F(\{i\}; \{j\} \mid \{l\}). \qquad (24)$$

It then defines

$$\tilde{\Gamma}_4 := \left\{F \in \Gamma_4 : \text{for any permutation } \pi \text{ of } \{1, 2, 3, 4\}, \Delta_F(\pi(1), \pi(2) \mid \pi(3), \pi(4)) \leq \tfrac{1}{2} \bigl[I_F(\{\pi(3)\}; \{\pi(4)\}) + I_F(\{\pi(3)\}; \{\pi(1), \pi(2)\}) + I_F(\{\pi(1)\}; \{\pi(2)\} \mid \{\pi(3)\}) - I_F(\{\pi(1)\}; \{\pi(2)\} \mid \{\pi(4)\})\bigr]\right\}. \qquad (25)$$

Theorem 3 says precisely that every four-variable entropy function lies in $\tilde{\Gamma}_4$.

### Theorem 4 (Shannon incompleteness, eq. 26)

::: {.theorem}
**Theorem 4** ([@zhangyeung1998, Thm. 4]). For every $n \geq 4$,

$$\mathrm{cl}(\Gamma^*_n) \neq \Gamma_n. \qquad (26)$$
:::

Since one always has $\mathrm{cl}(\Gamma^*_n) \subseteq \Gamma_n$, equation (26) is equivalent to strict inclusion. The paper's proof sketch (p. 1443) observes that it suffices to prove the claim for $n = 4$: given a $4$-variable witness, embedding it on the first four coordinates of an $n$-tuple of random variables (with the remaining $n - 4$ set to a constant) produces an $n$-variable witness. The $n = 4$ witness is the explicit function $F : 2^{\mathcal{N}_4} \to [0, \infty)$ defined on p. 1443 (satisfying all 15 elemental Shannon inequalities but violating Theorem 3):

$$F(\varnothing) = 0, \qquad F(X) = F(Y) = F(Z) = F(U) = 2a > 0,$$

$$F(X, Y) = 4a, \qquad F(X, U) = F(X, Z) = F(Y, U) = F(Y, Z) = F(Z, U) = 3a,$$

$$F(X, Y, Z) = F(X, Y, U) = F(X, Z, U) = F(Y, Z, U) = F(X, Y, Z, U) = 4a,$$

for any $a > 0$, after identifying $\mathcal{N}_4$ with $\{X, Y, Z, U\}$.

### Theorem 5 (generalization to $n + 2$ variables, eq. 27-28)

::: {.theorem}
**Theorem 5** ([@zhangyeung1998, Thm. 5]). For any $n \geq 2$ and any $n + 2$ discrete random variables $U, Z, X_1, \ldots, X_n$, and for any $i \in \{1, \ldots, n\}$,

$$n \, I(U; Z) - \sum_{j = 1}^{n} I(U; Z \mid X_j) - n \, I(U; Z \mid X_i) \leq I(X_i; U, Z) + \sum_{j = 1}^{n} H(X_j) - H(X_1 \cdots X_n). \qquad (27)$$

Averaging (27) over $i \in \{1, \ldots, n\}$ yields the symmetric form

$$n \, I(U; Z) - 2 \sum_{j = 1}^{n} I(U; Z \mid X_j) \leq \tfrac{1}{n} \sum_{i = 1}^{n} I(X_i; U, Z) + \sum_{j = 1}^{n} H(X_j) - H(X_1 \cdots X_n). \qquad (28)$$

The proof is the same as Theorem 3 combined with induction on $n$ (omitted in the paper).
:::

### Theorem 6 (inner bound of $\mathrm{cl}(\Gamma^*_4)$, Section II eq. 43)

The paper reparametrizes an arbitrary function $F \in \mathcal{F}_n$ using atom values $F[\alpha \mid \beta]$, defined for pairs $(\alpha, \beta)$ with $\alpha \neq \varnothing$ by

$$F[\alpha \mid \beta] := \sum_{\gamma \subseteq \alpha} (-1)^{1+|\gamma|} F(\gamma \cup \beta), \qquad (30)$$

and then defines $F[\alpha] := F[\alpha \mid \alpha^c]$ (31). For four variables, the paper next records the elemental inequalities in atom coordinates and rewrites Theorem 3 in those coordinates. It also defines the quantity

For an entropy function of four random variables, the elemental inequalities become, for every permutation $\{i, j, k, l\} = \{1, 2, 3, 4\}$,

$$F[i, j] \geq 0, \qquad F[i, j] + F[i, j, k] \geq 0, \qquad F[i, j] + F[i, j, k] + F[i, j, l] + F[i, j, k, l] \geq 0, \qquad F[i] \geq 0. \qquad (32\text{-}33)$$

Equation (20) becomes

$$\Delta(X_1, X_2 \mid X_3, X_4) = F[1, 2, 3, 4] - F[1, 2]. \qquad (35)$$

Accordingly, for an arbitrary function $F$ the paper extends this to

$$\Delta_F(i, j \mid k, l) := F[i, j, k, l] - F[i, j]. \qquad (36)$$

$$S_F(i, j \mid k, l) := F[i, j] + F[i, j, k] + F[i, j, l] + F[k, l] \qquad (37)$$

and observes that, with $\varnothing$ denoting the empty set,

$$S_F(i, j \mid k, l) = F[i, j \mid \varnothing] - \Delta_F(k, l \mid i, j) = F[i, j] + F[i, j, k] + F[i, j, l] + F[i, j, k, l] - \Delta_F(k, l \mid i, j). \qquad (38)$$

In this coordinate system, Theorem 3 becomes

$$S_F(1, 2 \mid 3, 4) + F[1, 3 \mid 4] + F[1, 4 \mid 3] + F[3, 4 \mid 1] \geq 0. \qquad (39)$$

The two companion inequalities are

$$S_F(1, 2 \mid 3, 4) + F[2, 3 \mid 4] + F[2, 4 \mid 3] + F[3, 4 \mid 2] \geq 0 \qquad (40)$$

and

$$2 S_F(1, 2 \mid 3, 4) + F[1, 3 \mid 4] + F[1, 4 \mid 3] + F[2, 3 \mid 4] + F[2, 4 \mid 3] + F[3, 4 \mid 1] + F[3, 4 \mid 2] \geq 0. \qquad (41)$$

Equivalently, $S_F(1, 2 \mid 3, 4)$ is bounded below by the maximum of

$$-\bigl(F[1, 3 \mid 4] + F[1, 4 \mid 3] + F[3, 4 \mid 1]\bigr), \qquad -\bigl(F[2, 3 \mid 4] + F[2, 4 \mid 3] + F[3, 4 \mid 2]\bigr).$$

It then defines the region

$$\hat{\Gamma}_4 := \{F \in \Gamma_4 : \text{for any permutation } \pi \text{ of } \{1, 2, 3, 4\}, S_F(\pi(1), \pi(2) \mid \pi(3), \pi(4)) \geq 0\}. \qquad (42)$$

::: {.theorem}
**Theorem 6** ([@zhangyeung1998, Thm. 6], eq. 43).

$$\hat{\Gamma}_4 \subset \mathrm{cl}(\Gamma^*_4) \qquad (43)$$

Equivalently, the set $\hat{\Gamma}_4$ is an inner bound of $\mathrm{cl}(\Gamma^*_4)$.
:::

The paper then gives a projective-plane construction (p. 1445) showing that $S_F$ may be negative even for an entropy function. For the resulting four random variables $X_1, X_2, X_3, X_4$, it computes

$$I(X_1; X_2) = \log_2(13/12), \qquad H(X_3) = H(X_4) = \log_2 13,$$

$$H(X_3, X_4) = \log_2 6 + \log_2 13,$$

$$H(X_3 \mid X_1) = H(X_3 \mid X_2) = H(X_4 \mid X_1) = H(X_4 \mid X_2) = \log_2 4,$$

$$H(X_3, X_4 \mid X_1) = H(X_3, X_4 \mid X_2) = \log_2 12.$$

Therefore

$$I(X_3; X_4) = \log_2 13 - \log_2 6, \qquad I(X_3; X_4 \mid X_1) = I(X_3; X_4 \mid X_2) = \log_2(4/3),$$

and hence

$$\begin{aligned}
S_F(1, 2 \mid 3, 4)
&= I(X_1; X_2) + I(X_3; X_4 \mid X_1) + I(X_3; X_4 \mid X_2) - I(X_3; X_4) \\
&= \log_2(13/12) + 2 \log_2(4/3) - \log_2(13/6) \\
&= -\log_2(9/8) < 0.
\end{aligned}$$

So the inner bound is strict; combined with the outer bound $\tilde{\Gamma}_4$ from Theorem 3, this leaves the exact description of $\mathrm{cl}(\Gamma^*_4)$ open.

## Lemmas

### Lemma 1 (atom-to-subset inversion, eq. 34)

::: {.lemma}
**Lemma 1** ([@zhangyeung1998, Lem. 1]). For the atom reparametrization $F[\alpha \mid \beta]$,

$$F[\alpha \mid \beta] = \sum_{\gamma \subseteq (\alpha \cup \beta)^c} F[\alpha \cup \gamma] \qquad (34)$$

where $A^c$ stands for the complement of the set $A$.
:::

### Lemma 2 (the copy lemma, eq. 44-45)

This is the central proof artifact of the paper. In the modern literature, this construction (together with its extension to any number of "copies" over a shared marginal) is called the **copy lemma**.

::: {.lemma}
**Lemma 2** ([@zhangyeung1998, Lem. 2]). Let $(X, Y, Z, U)$ be four jointly distributed discrete random variables on a probability space with joint distribution $p(x, y, z, u)$. Define the six-variable distribution

$$q(x, y, z, u, x_1, y_1) := \frac{p(x, y, z, u) \, p(x_1, y_1, z, u)}{p(z, u)} \qquad (44)$$

wherever $p(z, u) > 0$. Let $X_1, Y_1$ be two random variables jointly distributed with $X, Y, Z, U$ according to the joint distribution $q$. Equivalently, conditioned on $(Z, U)$, the pairs $(X, Y)$ and $(X_1, Y_1)$ are i.i.d. with common conditional law $p(\cdot, \cdot \mid Z, U)$. Then:

1. **Identical marginals.** The $(X, Y, Z, U)$-marginal and the $(X_1, Y_1, Z, U)$-marginal of $q$ both equal $p$.
2. **Conditional independence.** Under $q$, the pair $(X, Y)$ is conditionally independent of $(X_1, Y_1)$ given $(Z, U)$:
$$I_q\bigl((X, Y); (X_1, Y_1) \mid (Z, U)\bigr) = 0.$$
3. **Entropy identity** (eq. 45). The conditional mutual information of the original variables satisfies

$$\Delta(Z, U \mid X, Y) = I(X; Y_1) - I(X; Y_1 \mid U) - I(X; Y_1 \mid Z) - I(Z; U \mid X, Y_1) \qquad (45)$$
:::

The construction is the two-step kernel composition $q = p \otimes \kappa$ where $\kappa$ is the Markov kernel from $(Z, U)$ to $(X_1, Y_1)$ induced by $p(\cdot, \cdot \mid Z, U)$; equivalently, $(X_1, Y_1)$ is a conditionally independent "copy" of $(X, Y)$ over the common $(Z, U)$ coordinates.

## Proof of Theorem 3 (Section III)

With the six-variable joint distribution $q$ from Lemma 2, the paper first observes

$$I(Z; U) - I(Z; U \mid X) - I(Z; U \mid Y) \leq I(X; Y_1),$$

and similarly

$$I(Z; U) - 2 I(Z; U \mid X) \leq I(X; X_1).$$

It then combines these bounds as

$$\begin{aligned}
2 I(Z; U) - 3 I(Z; U \mid X) - I(Z; U \mid Y)
&\leq I(X; Y_1) + I(X; X_1) \\
&= I(X; X_1, Y_1) + I(X_1; Y_1) - I(X_1; Y_1 \mid X) \\
&\leq I(X; X_1, Y_1) + I(X_1; Y_1) \\
&\leq I(X; Z, U) + I(X_1; Y_1) \\
&= I(X; Z, U) + I(X; Y),
\end{aligned}$$

where the penultimate step is data processing and the last step uses the identical-marginal fact $I(X_1; Y_1) = I(X; Y)$. Rearranging gives (21); swapping $X$ and $Y$ gives (22), and averaging yields (23).

The paper also makes the deficit in (21) explicit. Writing

$$R_1 := I(X; Y_1 \mid U) + I(X; Y_1 \mid Z) + I(Z; U \mid X, Y_1),$$

$$R_2 := I(X; X_1 \mid U) + I(X; X_1 \mid Z) + I(Z; U \mid X, X_1),$$

Lemma 2 gives

$$\Delta(Z, U \mid X, Y) = I(X; Y_1) - R_1,$$

$$\Delta(Z, U \mid X, X_1) = I(X; X_1) - R_2,$$

so the missing term in (21) is

$$R(X, Y, Z, U, X_1, Y_1) = \tfrac{1}{2} \bigl[I(X; Z, U \mid X_1, Y_1) + I(X_1; Y_1 \mid X) + R_1 + R_2\bigr].$$

The paper then points out that the explicit function

$$F(\varnothing) = 0, \qquad F(X) = F(Y) = F(Z) = F(U) = 6a,$$

$$F(X, Y) = 12a, \qquad F(X, Z) = F(Y, Z) = F(Y, U) = F(X, U) = 9a, \qquad F(Z, U) = 10a,$$

$$F(X, Z, U) = F(Y, Z, U) = F(X, Y, Z) = F(X, Y, U) = F(X, Y, Z, U) = 12a.$$

This function lies in $\tilde{\Gamma}_4$ and satisfies one of the new inequalities with equality. The authors ask whether it is asymptotically constructible; if it were, one might expect the outer bound to be tight, i.e. $\mathrm{cl}(\Gamma^*_4) = \tilde{\Gamma}_4$. They report that they were unable to prove this and therefore doubt that conjecture.

## Proof of Theorem 6 (Section IV)

Section IV proves the inner bound via seven explicit probabilistic constructions. In the paper, these are defined from three independent ternary random variables $W_1, W_2, W_3$, each uniform on $\{0, 1, 2\}$, together with a constant random variable $W_0$; logarithms are taken in base $3$, so $H(W_i) = 1$ for $i = 1, 2, 3$.

- **Construction 1** ($F^1_\alpha$). For any nonempty subset $\alpha \subseteq \{1, 2, 3, 4\}$, set $X_i = W_1$ if $i \in \alpha$ and $X_i = W_0$ otherwise. Then $F^1_\alpha[\beta] = 0$ for every $\beta \neq \alpha$, while $F^1_\alpha[\alpha] = 1$. This is the single-atom indicator construction used in Lemma 4.
- **Construction 2** ($F^2$). Set $X_1 = W_1$, $X_2 = W_2$, $X_3 = W_3$, and $X_4 = W_1 + W_2 + W_3 \pmod 3$. Then the induced atom function is $0$ on all weight-one atoms, $1$ on all weight-two and weight-four atoms, and $-1$ on all weight-three atoms.
- **Construction 3** ($F^3_4$, and by permutation $F^3_i$). Set $X_1 = W_1$, $X_2 = W_2$, $X_3 = W_1 + W_2 \pmod 3$, and $X_4 = W_0$. Then $F^3_4[1, 2] = F^3_4[1, 3] = F^3_4[2, 3] = 1$, $F^3_4[1, 2, 3] = -1$, and all other atoms have value $0$. By symmetry, $F^3_i$ is obtained by making $X_i = W_0$.
- **Construction 4** ($F^4_{3,4}$, and by symmetry $F^4_{i,j}$). Set $X_1 = W_1$, $X_2 = W_2$, and $X_3 = X_4 = W_1 + W_2 \pmod 3$. Then $F^4_{3,4}[1, 2] = 1$, $F^4_{3,4}[2, 3, 4] = F^4_{3,4}[1, 3, 4] = 1$, $F^4_{3,4}[1, 2, 3, 4] = -1$, and all other atoms have value $0$.
- **Construction 5** ($F^5$). Set $X_1 = W_1$, $X_2 = W_2$, $X_3 = W_1 + W_2 \pmod 3$, and $X_4 = W_1 - W_2 \pmod 3$. Then all weight-one and weight-two atoms have value $0$, all weight-three atoms have value $1$, and $F^5[1, 2, 3, 4] = -2$.
- **Construction 6** ($F^6_4$, and by symmetry $F^6_i$). Set $X_1 = W_1$, $X_2 = W_2$, $X_3 = W_3$, and $X_4 = (W_1 + W_2 \pmod 3, W_1 + W_3 \pmod 3)$. Then $F^6_4[1, 2, 3] = 1$, every weight-two atom containing $4$ has value $1$, $F^6_4[1, 2, 3, 4] = -1$, and all other atoms have value $0$.
- **Construction 7** ($F^7_4$, and by symmetry $F^7_i$). Set $X_1 = W_1$, $X_2 = W_2$, $X_3 = W_1 + W_2 \pmod 3$, and $X_4 = (W_1, W_2)$. Then all atoms of weight at most $2$ have value $0$, every weight-three atom except $[1, 2, 3]$ has value $1$, $F^7_4[1, 2, 3] = 0$, and $F^7_4[1, 2, 3, 4] = -1$.

The paper's atom chart on p. 1447 orders the atoms of weight at least $2$ as

```text
23
12   123   13
124  1234  134  14
24   234   34
```

With that ordering, the chart values for Constructions 2-7 are:

| Function | 23 | 12 | 123 | 13 | 124 | 1234 | 134 | 14 | 24 | 234 | 34 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| $F^2$ | 1 | 1 | -1 | 1 | -1 | 1 | -1 | 1 | 1 | -1 | 1 |
| $F^3_4$ | 1 | 1 | -1 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| $F^4_{3,4}$ | 0 | 1 | 0 | 0 | 0 | -1 | 1 | 0 | 0 | 1 | 0 |
| $F^5$ | 0 | 0 | 1 | 0 | 1 | -2 | 1 | 0 | 0 | 1 | 0 |
| $F^6_4$ | 0 | 0 | 1 | 0 | 0 | -1 | 0 | 1 | 1 | 0 | 1 |
| $F^7_4$ | 0 | 0 | 0 | 0 | 1 | -1 | 1 | 0 | 0 | 1 | 0 |

Supporting lemmas:

- **Lemma 3** ([@zhangyeung1998, Lem. 3]). If $f, g \in \mathrm{cl}(\Gamma^*_n)$ and $\lambda \geq 0$, then $f + g \in \mathrm{cl}(\Gamma^*_n)$ and $\lambda f \in \mathrm{cl}(\Gamma^*_n)$. That is, $\mathrm{cl}(\Gamma^*_n)$ is a convex cone.
- **Lemma 4** ([@zhangyeung1998, Lem. 4]). Nonnegative atom-valued functions are asymptotically constructible. (Proved via Construction 1 and Lemma 3.)

Before the case split, the paper rewrites membership in $\hat{\Gamma}_4$ as five families of atom inequalities. For any permutation $\{i, j, k, l\} = \{1, 2, 3, 4\}$, a function $F \in \hat{\Gamma}_4$ satisfies:

1. $F[\alpha] \geq 0$ for every atom $\alpha$ of weight $1$.
2. $F[i, j \mid \varnothing] = F[i, j] + F[i, j, k] + F[i, j, l] + F[i, j, k, l] \geq 0$.
3. $F[i, j \mid k] = F[i, j] + F[i, j, l] \geq 0$.
4. $S_F(i, j \mid k, l) = F[i, j] + F[i, j, k] + F[i, j, l] + F[k, l] \geq 0$.
5. $F[i, j] \geq 0$.

The paper calls a function **nonnegative** if all of its atom values are nonnegative, and **seminonnegative** if all atom values of weight at most $3$ are nonnegative. Lemma 4 is proved by the explicit decomposition

$$J = \sum_{\alpha \neq \varnothing} J[\alpha] \, F^1_\alpha,$$

valid for every nonnegative atom function $J$.

The main argument is a case analysis (p. 1448-1451) showing that every function $F \in \hat{\Gamma}_4$ can be reduced via a sequence of **legal operations** (subtracting a nonnegative multiple of one of the basic functions from Constructions 2-7 while preserving the relevant inequalities) to a nonnegative function, which is asymptotically constructible by Lemma 4. The proof proceeds in three stages.

1. **Normalize a weight-two atom with $F^2$.** Since $F^2$ satisfies Conditions 2-4 with equality, the paper subtracts $a F^2$, where $a := \min_{\{i,j\} \subset \{1,2,3,4\}} F[i, j]$, and thereby reduces to a function $F'$ with $F'[1, 2] = 0$.
2. **Reach seminonnegativity with $F^3_i$.** If one of the relevant weight-three atoms is negative, for instance $F'[1, 3, 4] < 0$, the paper sets $a := -F'[1, 3, 4]$ and subtracts $a F^3_2$. Repeating symmetrically if needed yields a seminonnegative function $G$.
3. **Eliminate the weight-four atom by a structured branch analysis.** For seminonnegative $G$, the remaining constraints are the six inequalities in which the weight-four atom $[1, 2, 3, 4]$ appears. The paper first records two reusable observations:

   Observation 1: if $J$ is seminonnegative, $\{i, j, k, l\}$ is a permutation of $\{1, 2, 3, 4\}$, and $J[i, j, k] + J[1, 2, 3, 4] \geq 0$, then subtracting $a F^4_{i,j}$ is legal and keeps the function seminonnegative, where

$$a = \min\{J[k, l], J[i, k, l], J[j, k, l]\}.$$

   Observation 2: if, in addition,

$$J[i, j, k] + J[1, 2, 3, 4] \geq 0, \qquad J[i, j, l] + J[1, 2, 3, 4] \geq 0, \qquad J[i, k, l] + J[1, 2, 3, 4] \geq 0,$$

then subtracting $a F^7_i$ is legal and produces a nonnegative function, where

$$a = \min\{J[i, k, l], J[i, j, l], J[i, j, k]\}.$$

   Before invoking these observations, the paper repeatedly subtracts suitable multiples of $F^3_i$, $F^5$, and $F^6_i$ as long as seminonnegativity is preserved. When no such move remains, the proof splits into two master cases.

   Case 1: some $3$-subset, without loss of generality $\{1, 2, 3\}$, has all three associated weight-two atoms zero:

$$G'[1, 2] = G'[1, 3] = G'[2, 3] = 0.$$

   Since no $F^6_4$ move is available, one of $G'[1,4]$, $G'[2,4]$, $G'[3,4]$, or $G'[1,2,3]$ must also be zero.

   Case 1.1: one of the remaining weight-two atoms vanishes, say $G'[1,4] = 0$. Since no $F^5$ move is available, one of $G'[1,2,4]$, $G'[1,3,4]$, or $G'[2,3,4]$ is also zero. The paper then dispatches the branches as follows.

   If $G'[1,2,4] = 0$, then Condition 2 gives

$$G'[1,3,4] + G'[1,2,3,4] \geq 0,$$

   because both $G'[1,4]$ and $G'[1,2,4]$ are zero. Subtract $a F^4_{1,3}$ with

$$a = \min\{G'[2,4], G'[1,2,3], G'[1,3,4]\};$$

   this is legal and yields a seminonnegative function $G''$. If $G''[1,2,3] = 0$ or $G''[1,3,4] = 0$, then $G''[1,2,3,4] \geq 0$ and the function is already nonnegative. Otherwise $G''[2,4] = 0$, which implies

$$G''[2,3,4] + G''[1,2,3,4] \geq 0.$$

   Let $b := -G''[1,2,3,4]$. If $b > 0$, then subtracting $b F^7_1$ is legal and produces a function that is nonnegative at all atoms.

   If $G'[2,3,4] = 0$, then

$$G'[1,2,3] + G'[1,2,3,4] \geq 0,$$

   because both $G'[2,3]$ and $G'[2,3,4]$ are zero. Subtract $a F^4_{1,2}$ with

$$a = \min\{G'[3,4], G'[1,2,3], G'[1,2,4]\};$$

   This yields a seminonnegative function $G''$. If $G''[1,2,3] = 0$, then $G''[1,2,3,4] \geq 0$. If $G''[1,2,4] = 0$, this reduces to the previous subcase. Otherwise $G''[3,4] = 0$, and then

$$G''[1,2,3,4] + G''[1,3,4] \geq 0.$$

   Now subtract $a' F^4_{1,3}$ with

$$a' = \min\{G''[2,4], G''[1,2,3], G''[1,3,4]\}.$$

   This produces a seminonnegative function $G'''$. If $G'''[1,2,3] = 0$ or $G'''[1,3,4] = 0$, then $G'''[1,2,3,4] \geq 0$. Otherwise $G'''[2,4] = 0$, in which case

$$G'''[1,2,4] + G'''[1,2,3,4] \geq 0,$$

$$G'''[1,2,3] + G'''[1,2,3,4] \geq 0,$$

$$G'''[1,3,4] + G'''[1,2,3,4] \geq 0.$$

   Let $b := -G'''[1,2,3,4]$. If $b > 0$, then subtracting $b F^7_1$ is legal and yields a function nonnegative at all atoms.

   Case 1.2: the extra zero is the weight-three atom $G'[1,2,3] = 0$. Then

$$G'[1,3,4] + G'[1,2,3,4] \geq 0, \qquad G'[1,2,4] + G'[1,2,3,4] \geq 0, \qquad G'[2,3,4] + G'[1,2,3,4] \geq 0,$$

   and the paper draws the corresponding atom chart for this case. Let $a := -G'[1,2,3,4]$. If $a > 0$, then subtracting $a F^7_1$ is a legal operation and results in a nonnegative function. Otherwise the function is already nonnegative.

   Case 2: two disjoint weight-two atoms vanish, without loss of generality

$$G'[1,2] = G'[3,4] = 0.$$

   Since no $F^5$ move remains, one may further assume $G'[1,2,3] = 0$. The paper first subtracts $a F^4_{1,4}$ with

$$a = \min\{G'[2,3], G'[1,3,4], G'[1,2,4]\}.$$

   This is legal, and the resulting function $G''$ has one of $G''[1,3,4]$, $G''[1,2,4]$, or $G''[2,3]$ equal to zero.

   If $G''[1,3,4] = 0$, then

$$G''[1,3] + G''[1,2,3,4] \geq 0.$$

   Apparently, subtracting $b F^4_{2,4}$ is legal, where

$$b = \min\{G''[1,3], G''[1,2,4], G''[2,3,4]\},$$

   and this results in a nonnegative function.

   If $G''[2,3] = 0$, then

$$G''[2,3,4] + G''[1,2,3,4] \geq 0.$$

   Let

$$a' = \min\{G''[1,3], G''[1,2,4], G''[2,3,4]\}.$$

   Subtracting $a' F^4_{2,4}$ is legal. Let $G''' := G'' - a' F^4_{2,4}$. Then either $G'''[1,2,4] = 0$ or $G'''[1,3,4] = 0$. In both cases, the paper notes that one must have $G'''[1,2,3,4] \geq 0$, so the function is nonnegative. Otherwise $G'''[1,3] = 0$, which implies

$$G'''[1,3,4] + G'''[1,2,3,4] \geq 0,$$

$$G'''[1,2,4] + G'''[1,2,3,4] \geq 0,$$

$$G'''[2,3,4] + G'''[1,2,3,4] \geq 0.$$

   Then subtracting $F^7_4$ is legal and results in a nonnegative function.

   If $G''[1,2,4] = 0$, then the paper concludes that $G''[1,2,3,4]$ must already be nonnegative. Hence $G''$ is a nonnegative function.

In every branch, the process terminates at a nonnegative atom function, proving Theorem 6.

> **Transcription note.** The chart values and the branch structure of the Theorem 6 proof are now recorded from the source PDF. The only remaining compression is that repeated inequality verifications inside symmetric subcases are not all reproduced symbol-for-symbol.

## Concluding remarks (Section V)

The key result of the paper is Theorem 3. This discovery shows that the set of so-called basic information inequalities cannot fully characterize Shannon's entropy function in the sense of Theorem 4. That is, the region $\Gamma_n$ is strictly greater than the region $\mathrm{cl}(\Gamma_n^*)$. This is a surprising result because, based on intuition, one tends to believe that the opposite is true.

Actually, when the authors started to look into this problem, they first tried to prove

$$\mathrm{cl}(\Gamma_4^*) = \Gamma_4$$

by finding all kinds of constructions for four random variables as in the proof of Theorem 6. Only after they failed to find a construction in one of many cases did they start to doubt the correctness of the conjecture. This led to the discovery of the new information inequality.

The full characterization of the region $\mathrm{cl}(\Gamma_n^*)$ seems to be a highly nontrivial problem. Even in the case $n = 4$, the authors were unable to determine the region. They instead provided an inner bound, namely Theorem 6. The inner bound and the outer bound found in the paper differ. It has been shown by an example that the inner bound is not tight. Unfortunately, the construction method used in this example is not powerful enough to show that the outer bound is tight.

The simplest case of the problem is the case $n = 4$ because this number is the smallest integer for which $\mathrm{cl}(\Gamma_n^*)$ and $\Gamma_n$ differ. Although the paper concentrates on this simplest case, it also proves Theorem 5, which is a generalization of Theorem 3 to any number of random variables.

The paper also determines the missing terms in the inequalities in Theorem 3. They are expressed in terms of some auxiliary random variables. The authors do so in the hope that this may be helpful in further searching for new information inequalities, as well as in further searching for improved inner bounds.

To get a better understanding of the behavior of the entropy function, it is important to fully characterize the function at least in the simplest case $n = 4$. That is, the simplest task in this research direction is to determine the region $\mathrm{cl}(\Gamma_4^*)$. Based on their experience, the authors do not believe the outer bound to be tight. That is, they believe that there may exist more linear unconditional information inequalities involving four random variables.

The meaning of the new information inequalities provided by Theorems 3 and 5 is still not fully understood. Although the authors have used the region $\mathrm{cl}(\Gamma_n^*)$ to study the distributed source-coding problem, it is still of great interest to find more applications of the inequalities in other information-theoretical problems, especially in multiuser channel coding or source coding problems.

The problems studied in the paper have close connection to other areas such as probabilistic reasoning, relational databases, and so on. To study the implication of the results in those areas is also of interest.

## Acknowledgment

The authors thank the two referees, noting that their detailed comments and suggestions greatly improved the readability of the paper.

## Formalization cross-references

The formalization targets in the roadmap (`docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md`, Sections 4-6) map to this transcription as follows.

| Paper statement | Formalization target | Scope decision |
| --- | --- | --- |
| Proposition 1 (basic inequalities) | PFR `ForMathlib/Entropy/{Basic,MutualInfo}`; available upstream | External |
| Proposition 2 (submodularity, monotonicity, normalization) | `ZhangYeung/Theorem4.lean` (Shannon cone definition); PFR provides per-RV versions | Part of M4 |
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

No known substantive content gaps remain. The prose, constructions, charts, acknowledgment, and bibliography are now transcribed. Some repetitive inequality checks inside the deepest Theorem 6 subcases are normalized and condensed slightly, but the mathematical content is preserved.

## References (paper bibliography)

- **[1]** N. M. Abramson, *Information Theory and Coding*. New York: McGraw-Hill, 1963.
- **[2]** L. L. Campbell, "Entropy as a measure," *IEEE Trans. Inform. Theory*, vol. IT-11, pp. 112-114, Jan. 1965.
- **[3]** I. Csiszár and J. Körner, *Information Theory: Coding Theorem for Discrete Memoryless Systems*. New York: Academic, and Budapest, Hungary: Akademiai Kiado, 1981.
- **[4]** A. P. Dawid, "Conditional independence in statistical theory (with discussion)," *J. Roy. Statist. Soc., Ser. B*, vol. 41, pp. 1-31.
- **[5]** S. Fujishige, "Polymatroidal dependence structure of a set of random variables," *Inform. Contr.*, vol. 39, pp. 55-72, 1978.
- **[6]** T. Kawabata and R. W. Yeung, "The structure of the I-measure of a Markov chain," *IEEE Trans. Inform. Theory*, vol. 38, pp. 1146-1149, 1992.
- **[7]** T. S. Han, "Linear dependence structure of the entropy space," *Inform. Contr.*, vol. 29, pp. 337-368.
- **[8]** T. S. Han, "Nonnegative entropy measures of multivariate symmetric correlations," *Inform. Contr.*, vol. 36, pp. 133-156, 1978.
- **[9]** T. S. Han, "A uniqueness of Shannon's information distance and related nonnegativity problems," *J. Comb., Inform. Syst. Sci.*, vol. 6, pp. 320-321, 1981.
- **[10]** G.-d. Hu, "On the amount of information," *Teor. Veroyatnost. i Primenen.*, vol. 4, pp. 447-455, 1962, in Russian.
- **[11]** F. Matus̆, private communication.
- **[12]** F. J. MacWilliams and N. J. A. Sloane, *The Theory of Error Correcting Codes*. Amsterdam, The Netherlands: North-Holland, Elsevier Science B.V., 1977.
- **[13]** M. Matus̆, "Abstract functional dependency structures," *Theor. Comput. Sci.*, vol. 81, pp. 117-126, 1991.
- **[14]** M. Matus̆, "On equivalence of Markov properties over undirected graphs," *J. Appl. Probab.*, vol. 29, pp. 745-749, 1992.
- **[15]** M. Matus̆, "Ascending and descending conditional independence relations," in *Trans. 11th Prague Conf. Information Theory, Statistical Decision Functions and Random Processes*, vol. B. Prague, Czechoslovakia: Academia, pp. 181-200, 1992.
- **[16]** M. Matus̆, "Probabilistic conditional independence structures and matroid theory: Background," *Int. J. Gen. Syst.*, vol. 22, pp. 185-196.
- **[17]** M. Matus̆, "Extreme convex set functions with many nonnegative differences," *Discr. Math.*, vol. 135, pp. 177-191, 1994.
- **[18]** F. Matus̆, "Conditional independences among four random variables II," *Combin., Prob. Comput.*, vol. 4, pp. 407-417, 1995.
- **[19]** F. Matus̆, "Conditional independence structures examined via minors," *Ann. Math. Artificial Intell.*, vol. 21, pp. 99-128, 1997.
- **[20]** F. Matus̆ and M. Studený, "Conditional independences among four random variables I," *Combin., Prob. Comput.*, vol. 4, pp. 269-278, 1995.
- **[21]** W. J. McGill, "Multivariate information transmission," in *Trans. Prof. Group Inform. Theory, 1954 Symp. Information Theory*, vol. PGIT-4, 1955, pp. 93-111.
- **[22]** A. Papoulis, *Probability, Random Variables and Stochastic Processes*, 2nd ed. New York: McGraw-Hill, 1984.
- **[23]** J. Pearl, *Probabilistic Reasoning in Intelligent Systems*. San Mateo, CA: Morgan Kaufman, 1988.
- **[24]** *An Introduction to Information Theory*. New York: McGraw-Hill, 1961.
- **[25]** M. Studený, "Attempts at axiomatic description of conditional independence," in *Proc. Workshop on Uncertainty Processing in Expert Systems*, supplement to *Kybernetika*, vol. 25, nos. 1-3, pp. 65-72, 1989.
- **[26]** M. Studený, "Multiinformation and the problem of characterization of conditional independence relations," *Probl. Contr. Inform. Theory*, vol. 18, pp. 3-16, 1989.
- **[27]** M. Studený, "Conditional independence relations have no finite complete characterization," in *Trans. 11th Prague Conf. Information Theory, Statistical Decision Functions and Random Processes*, vol. B. Prague, Czechoslovaka: Academia, pp. 377-396, 1992.
- **[28]** M. Studený, "Structural semigraphoids," *Int. J. Gen. Syst.*, vol. 22, no. 2, pp. 207-217, 1994.
- **[29]** M. Studený, "Descriptions of structures of stochastic independence by means of faces and imsets (in three parts)," *Int. J. Gen. Syst.*, vol. 23, pp. 123-137, pp. 201-219, pp. 323-341, 1994/1995.
- **[30]** T. Tsujishita, "On triple mutual information," *Adv. Appl. Math.*, vol. 16, pp. 269-274, 1995.
- **[31]** S. Watanabe, "A study of ergodicity and redundancy on intersymbol correlation of finite range," in *Trans. 1954 Symp. Inform. Theory* (Cambridge, MA, Sept. 15-17, 1954), p. 85.
- **[32]** S. Watanabe, "Information theoretical analysis of multivariate correlation," *IBM J.*, pp. 66-81, 1960.
- **[33]** D. J. A. Welsh, *Matroid Theory*. New York: Academic, 1976.
- **[34]** R. W. Yeung, "A new outlook on Shannon's information measures," *IEEE Trans. Inform. Theory*, vol. 37, pp. 466-474, 1991.
- **[35]** R. W. Yeung, "A framework for linear information inequalities," *IEEE Trans. Inform. Theory*, vol. 43, pp. 1924-1934, Nov. 1997.
- **[36]** R. W. Yeung, T. T. Lee, and Z. Ye, "An information-theoretic characterization of Markov random fields and its applications," *IEEE Trans. Inform. Theory*, submitted for publication.
- **[37]** R. W. Yeung and Z. Zhang, "Distributed source coding for satellite communication," *IEEE Trans. Inform. Theory*, submitted for publication.
- **[38]** R. W. Yeung and Y.-O. Yan, "Information theoretic inequality prover." [Online] Available: `http://www.ie.cuhk.edu.hk/ITIP` or `http://it.ucsd.edu/~whyeung` (mirror site).
- **[39]** Z. Zhang and R. W. Yeung, "A non-Shannon type conditional inequality of information quantities," *IEEE Trans. Inform. Theory*, vol. 43, pp. 1982-1985, Nov. 1997.
