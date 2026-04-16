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
| $\mathcal{F}_n$ | All functions $2^{\mathcal{N}_n} \to [0, \infty)$ | -- |
| $\Gamma_n$ | Cone of functions satisfying the basic (Shannon) inequalities, viewed as a subset of $\mathbb{R}^{2^n - 1}$ | Shannon outer bound |
| $\Gamma^*_n$ | Set of entropy functions of $n$-tuples of discrete RVs (the **constructible** functions) | Entropic region |
| $\mathrm{cl}(\Gamma^*_n)$ | Closure of $\Gamma^*_n$ (the **asymptotically constructible** functions) | Almost-entropic region |
| $\tilde{\Gamma}_4$ (Section II, eq. 25) | Outer bound defined from Theorem 3's inequality in function coordinates | -- |
| $F[\alpha \mid \beta]$ (Section II, eq. 30) | Atom-valued reparametrization of a function $F : 2^{\mathcal{N}_n} \to \mathbb{R}$ | -- |
| $S_F$ (Section II, eq. 37) | Paper-specific quantity controlling the inner bound of Theorem 6 | -- |
| $\hat{\Gamma}_4$ (Section II, eq. 42) | Inner bound of $\mathrm{cl}(\Gamma^*_4)$ defined via $S_F$ | -- |

The paper freely switches logarithm base. Theorem 6's concrete construction uses base $3$ so that the three symmetric ternary RVs have entropy $1$. All inequalities in Theorems 3-5 are log-base-agnostic.

## Scope

The paper is the birthplace of the first non-Shannon-type information inequality. Its central contribution is Theorem 3, the **Zhang-Yeung inequality**, together with Theorem 4, which uses it to prove that the Shannon outer bound $\Gamma_n$ strictly contains the almost-entropic region $\mathrm{cl}(\Gamma^*_n)$ for every $n \geq 4$. This transcription covers every formal statement of the paper (propositions, theorems, and lemmas) together with the copy-lemma construction underlying the main proof. The seven explicit constructions driving Theorem 6's inner bound are now recorded explicitly from the source PDF; the 5-page case analysis that ties them together is still summarized rather than transcribed line by line.

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

   If $G'[1,2,4] = 0$, subtract $a F^4_{1,3}$ with

$$a = \min\{G'[2,4], G'[1,2,3], G'[1,3,4]\};$$

   if the resulting function still has negative weight-four atom, subtract $b F^7_1$ with $b = -G''[1,2,3,4]$.

   If $G'[2,3,4] = 0$, subtract $a F^4_{1,2}$ with

$$a = \min\{G'[3,4], G'[1,2,3], G'[1,2,4]\};$$

   if needed, follow by a second $F^4_{1,3}$ move and then a final $F^7_1$ move. In all subbranches the output is nonnegative.

   Case 1.2: the extra zero is the weight-three atom $G'[1,2,3] = 0$. Then

$$G'[1,3,4] + G'[1,2,3,4] \geq 0, \qquad G'[1,2,4] + G'[1,2,3,4] \geq 0, \qquad G'[2,3,4] + G'[1,2,3,4] \geq 0,$$

   so a single $F^7_1$ move of size $-G'[1,2,3,4]$ yields a nonnegative function.

   Case 2: two disjoint weight-two atoms vanish, without loss of generality

$$G'[1,2] = G'[3,4] = 0.$$

   Since no $F^5$ move remains, one may further assume $G'[1,2,3] = 0$. The paper first subtracts $a F^4_{1,4}$ with

$$a = \min\{G'[2,3], G'[1,3,4], G'[1,2,4]\}.$$

   The resulting function $G''$ has one of $G''[1,3,4]$, $G''[1,2,4]$, or $G''[2,3]$ equal to zero.

   If $G''[1,3,4] = 0$, a single $F^4_{2,4}$ move with parameter $\min\{G''[1,3], G''[1,2,4], G''[2,3,4]\}$ finishes.

   If $G''[2,3] = 0$, the paper subtracts an $F^4_{2,4}$ move; if that still leaves the weight-four atom negative, the remaining three inequalities needed for Observation 2 hold, and a final $F^7_4$ move completes the reduction.

   If $G''[1,2,4] = 0$, then the weight-four atom is already nonnegative, so the function is done.

In every branch, the process terminates at a nonnegative atom function, proving Theorem 6.

> **Transcription caveat.** The construction definitions on pp. 1446-1447 are now verified against the PDF. What remains summarized rather than transcribed line by line is the atom-chart bookkeeping and the full legal-operation case analysis on pp. 1447-1451.

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

Each caveat below marks a place where the pdftotext extraction was insufficient and the source PDF needs to be consulted before the statement can be considered paper-faithful. In priority order:

1. **Theorem 6 atom charts and case analysis.** The construction definitions on pp. 1446-1447 are now verified, but the atom charts and the detailed legal-operation case split on pp. 1447-1451 are still summarized rather than transcribed line by line.

## References (from the paper)

Only the references actually used in the formalization roadmap are transcribed to BibTeX in `references/papers.bib`:

- **[39]** Zhang and Yeung, *A Non-Shannon Type Conditional Inequality of Information Quantities*, IEEE TIT 43(6), 1997 (= `zhangyeung1997`). Source of Theorems 1 and 2.
- **[35]** Yeung, *A Framework for Linear Information Inequalities*, IEEE TIT 43, 1997 (= `yeung1997framework`). Source of the regions $\Gamma_n$, $\Gamma^*_n$, and the elemental inequalities.

The remaining bibliography entries (Campbell, Hu, McGill, Watanabe, Csiszár-Körner, Han, Fujishige, Yeung [34], Kawabata-Yeung, Matús̆, Studený, Pearl, etc.) are context for the historical narrative in Section I and are not needed for the formalization targets.
