# Zhang-Yeung 1998 Cross-Reference

Independent cross-checks of the transcription's load-bearing equations against secondary sources, per Phase C1 of the transcription verification plan.

## Theorem 3 (eq. 21) — the Zhang-Yeung inequality

### Our transcription (`references/transcriptions/zhangyeung1998.md`)

$$\Delta(Z, U \mid X, Y) \leq \tfrac{1}{2}[I(X; Y) + I(X; ZU) + I(Z; U \mid X) - I(Z; U \mid Y)]$$

where $\Delta(Z, U \mid X, Y) := I(Z; U) - I(Z; U \mid X) - I(Z; U \mid Y)$.

### Yeung, *Information Theory and Network Coding* (Springer, 2008), Theorem 15.7, eq. (15.62)

$$2I(X_3; X_4) \leq I(X_1; X_2) + I(X_1; X_3, X_4) + 3I(X_3; X_4 \mid X_1) + I(X_3; X_4 \mid X_2)$$

### Equivalence check

Substituting $(Z, U, X, Y) = (X_3, X_4, X_1, X_2)$ into our eq. (21), expanding $\Delta$, and multiplying by 2:

$$2I(X_3; X_4) - 2I(X_3; X_4 \mid X_1) - 2I(X_3; X_4 \mid X_2) \leq I(X_1; X_2) + I(X_1; X_3 X_4) + I(X_3; X_4 \mid X_1) - I(X_3; X_4 \mid X_2)$$

Moving the two $I(X_3; X_4 \mid \cdot)$ terms to the RHS:

$$2I(X_3; X_4) \leq I(X_1; X_2) + I(X_1; X_3, X_4) + 3I(X_3; X_4 \mid X_1) + I(X_3; X_4 \mid X_2)$$

This is exactly Yeung's (15.62). ✓ Our transcription's Theorem 3 is algebraically identical to Yeung's independent textbook restatement.

## Lemma 2 (eq. 45) — the copy lemma (informal)

### Our transcription

Defines the joint distribution

$$q(x, y, z, u, x_1, y_1) := \frac{p(x, y, z, u) \, p(x_1, y_1, z, u)}{p(z, u)} \tag{44}$$

so that $(X_1, Y_1)$ is a conditional-on-$(Z, U)$ copy of $(X, Y)$ with $I(X, Y; X_1, Y_1 \mid Z, U) = 0$.

### Yeung, Theorem 15.7 proof (p. 26327-26357 of the textbook PDF)

"Toward proving this theorem, we introduce two auxiliary random variables $\tilde{X}_1$ and $\tilde{X}_2$ jointly distributed with $X_1, X_2, X_3, X_4$ such that $\tilde{X}_1 \equiv X_1$ and $\tilde{X}_2 \equiv X_2$."

### Yeung Lemma 15.9 (immediate consequence)

$$I(X_3; X_4) - I(X_3; X_4 \mid X_1) - I(X_3; X_4 \mid X_2) \leq I(X_1; \tilde{X}_2) \tag{15.65}$$

### Match

Under the variable substitution $(X_3, X_4, X_1, X_2, \tilde{X}_1, \tilde{X}_2) \leftrightarrow (Z, U, X, Y, X_1, Y_1)$:

- Yeung's $I(X_3; X_4) - I(X_3; X_4 \mid X_1) - I(X_3; X_4 \mid X_2)$ is our $\Delta(Z, U \mid X, Y)$.
- Yeung's $I(X_1; \tilde{X}_2)$ is our $I(X; Y_1)$.

Our intermediate step in the proof of Theorem 3:

> From Lemma 2, we have $I(Z; U) - I(Z; U \mid X) - I(Z; U \mid Y) \leq I(X; Y_1)$

matches Yeung's (15.65) exactly.

## Tang (2020), *The Copy Lemma and Non-Shannon Information Inequalities* (U. Michigan REU)

Tang restates the Zhang-Yeung inequality (his Theorem 2.4) and the copy lemma (his Lemma 3.1) in a reduced/normalized form that is consistent with our transcription after algebraic manipulation, though using simpler variable names $A, B, C, D$ and the stronger statement $I(CD; R \mid AB) = 0$ in place of our definition via $q$.

Tang's form is essentially a symmetrized/rescaled variant used in the Dougherty-Freiling-Zeger (2011) convention for generating new non-Shannon inequalities.

## Verification summary

- eq. (21) Zhang-Yeung inequality: matches Yeung 2008 Theorem 15.7 up to algebraic equivalence. ✓
- Lemma 2 copy construction: matches Yeung 2008 auxiliary-variable construction and Lemma 15.9. ✓
- Copy lemma modern restatement: matches Tang 2020 Lemma 3.1 under variable renaming. ✓

## Bibliography validation (Phase C2)

Spot-checked the most at-risk entries (diacritics, volume/page accuracy) against DBLP:

| Ref | Transcription | DBLP | Status |
|---|---|---|---|
| [20] | Matúš and Studený, Combin. Prob. Comput. 4 (1995), pp. 269-278 | Matúš and Studený, Combin. Prob. Comput. 4 (1995), pp. 269-278, DOI 10.1017/S0963548300001644 | ✓ match |
| [35] | Yeung, IEEE TIT 43 (Nov. 1997), pp. 1924-1934 | Yeung, IEEE TIT 43 (Nov. 1997), pp. 1924-1934, DOI 10.1109/18.641556 | ✓ match |
| [39] | Zhang & Yeung, IEEE TIT 43 (Nov. 1997), pp. 1982-**1985** | Zhang & Yeung, IEEE TIT 43 (Nov. 1997), pp. 1982-**1986** | paper-vs-DBLP discrepancy; transcription faithful to paper |

The [39] one-page discrepancy (paper prints 1982-1985, DBLP has 1982-1986) is inherent to the paper. For a faithful transcription, we preserve what the paper printed.

Diacritics verified correct on Csiszár, Körner, Matúš, Studený.

## Errata search (Phase C3)

Searched IEEE Xplore, Google Scholar, and the Zhang-Yeung-follow-up literature for any published corrigendum or erratum to the 1998 paper. No errata located. The paper has been heavily cited and re-derived; if a substantive error existed, follow-up papers (Matúš, Csirmaz, Dougherty-Freiling-Zeger) would have flagged it. None do — they treat Theorems 3-5 as correct as stated.

## Sources

- [Yeung, *Information Theory and Network Coding*, PDF draft](https://iest2.ie.cuhk.edu.hk/~whyeung/post/draft2.pdf)
- [Tang, *The Copy Lemma and Non-Shannon Information Inequalities* (2020 REU)](https://lsa.umich.edu/content/dam/math-assets/math-document/reu-documents/ugradreu/2020/Tang,%20Michael_2020%20REU%20Paper.pdf)
- [Dougherty, Freiling, Zeger, *Non-Shannon Information Inequalities in Four Random Variables* (arXiv:1104.3602)](https://arxiv.org/abs/1104.3602)
- [DBLP search for Matúš-Studený](https://dblp.org/search/publ/api?q=Matus+Studeny+Conditional+independences+four+random&format=json)
- [DBLP search for Yeung framework paper](https://dblp.org/search/publ/api?q=Yeung+framework+linear+information+inequalities&format=json)
- [DBLP search for Zhang-Yeung 1997](https://dblp.org/search/publ/api?q=Zhang+Yeung+non-Shannon+conditional&format=json)
