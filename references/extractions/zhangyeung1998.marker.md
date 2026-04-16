# On Characterization of Entropy Function via Information Inequalities

Zhen Zhang, Senior Member, IEEE, and Raymond W. Yeung, Senior Member, IEEE

Abstract—Given n discrete random variables  $\Omega=\{X_1,\cdots,X_n\}$ , associated with any subset  $\alpha$  of  $\{1,2,\cdots,n\}$ , there is a joint entropy  $H(X_\alpha)$  where  $X_\alpha=\{X_i:i\in\alpha\}$ . This can be viewed as a function defined on  $2^{\{1,2,\cdots,n\}}$  taking values in  $[0,+\infty)$ . We call this function the entropy function of  $\Omega$ . The nonnegativity of the joint entropies implies that this function is nonnegative; the nonnegativity of the conditional joint entropies implies that this function is nondecreasing; and the nonnegativity of the conditional mutual informations implies that this function has the following property: for any two subsets  $\alpha$  and  $\beta$  of  $\{1,2,\cdots,n\}$ 

$$H_{\Omega}(\alpha) + H_{\Omega}(\beta) \ge H_{\Omega}(\alpha \cup \beta) + H_{\Omega}(\alpha \cap \beta).$$

These properties are the so-called basic information inequalities of Shannon's information measures. Do these properties fully characterize the entropy function? To make this question more precise, we view an entropy function as a  $2^n - 1$ -dimensional vector where the coordinates are indexed by the nonempty subsets of the ground set  $\{1, 2, \dots, n\}$ . Let  $\Gamma_n$  be the cone in  $R^{2^n-1}$ consisting of all vectors which have these three properties when they are viewed as functions defined on  $2^{\{1,2,\dots,n\}}$ . Let  $\Gamma_n^*$  be the set of all  $2^n - 1$ -dimensional vectors which correspond to the entropy functions of some sets of n discrete random variables. The question can be restated as: is it true that for any n,  $\overline{\Gamma}_n^* = \Gamma_n$ ? Here  $\overline{\Gamma}_n^*$  stands for the closure of the set  $\Gamma_n^*$ . The answer is "yes" when n = 2 and 3 as proved in our previous work. Based on intuition, one may tend to believe that the answer should be "yes" for any n. The main discovery of this paper is a new information-theoretic inequality involving four discrete random variables which gives a negative answer to this fundamental problem in information theory:  $\overline{\Gamma}_n^*$  is strictly smaller than  $\Gamma_n$ whenever n > 3. While this new inequality gives a nontrivial outer bound to the cone  $\overline{\Gamma}_4^*$ , an inner bound for  $\overline{\Gamma}_4^*$  is also given. The inequality is also extended to any number of random

Index Terms—Entropy, inequality, information measure, mutual information.

#### I. INTRODUCTION

ET  $\Omega_n = \{X_i: i = 1, \dots, n\}$  be n jointly distributed discrete random variables. The basic Shannon's information measures associated with these random variables include

Manuscript received December 12, 1996; revised November 15, 1997. The work of Z. Zhang was supported in part by the National Science Foundation under Grant NCR-9502828. The work of R. W. Yeung was supported in part by The Research Grant Council of Hong Kong under Earmarked Grant CUHK 332/96E.

- Z. Zhang is with the Department of Electrical Engineering-Systems, Communication Sciences Institute, University of Southern California, Los Angeles, CA 90089-2565 USA (e-mail: zzhang@milly.usc.edu).
- R. W. Yeung is with the Department of Information Engineering, the Chinese University of Hong Kong, Shatin, N.T., Hong Kong, China (e-mail: whyeung@ie.cuhk.edu.hk).

Publisher Item Identifier S 0018-9448(98)03630-X.

all joint entropies, conditional entropies, mutual informations, and conditional mutual informations involving some of these random variables. For any subset  $\alpha$  of  $\mathcal{N}_n = \{1, \dots, n\}$ , let

$$X_{\alpha} = \{X_i : i \in \alpha\}. \tag{1}$$

Let  $X_{\phi}$ , where  $\phi$  is the empty set, be a random variable taking a fixed value with probability 1. Let

$$I_{\Omega}(\alpha, \beta|\gamma) = I(X_{\alpha}; X_{\beta}|X_{\gamma}) \tag{2}$$

be the conditional mutual information and let

$$H_{\Omega}(\alpha) = H(X_{\alpha}) \tag{3}$$

be the joint entropy. Sometimes, we drop the subscript  $\Omega$  in these notations, when no confusion may occur. It is well known that Shannon's information measures satisfy the following inequalities.

Proposition 1: For any three subsets  $\alpha$ ,  $\beta$ , and  $\gamma$  of  $\mathcal{N}_n$ , any set of n jointly distributed discrete random variables  $\Omega = \{X_i, i = 1, \dots, n\}$ 

$$I(\alpha, \beta|\gamma) \ge 0. \tag{4}$$

We call these inequalities the basic inequalities of Shannon's information measures, or simply the basic inequalities. By means of the chain rule for conditional mutual informations, we can see that these inequalities are implied by a subset of these inequalities of the form

$$I(\{i\}, \{j\}|\gamma) \ge 0.$$
 (5)

That is, the subset of inequalities (4) in which the cardinalities of  $\alpha$  and  $\beta$  are both 1. This subset of basic information inequalities is referred to as elemental information inequalities [35].

For any set of n jointly distributed discrete random variables  $\Omega = \{X_i, i = 1, \cdots, n\}$ , the associated joint entropies  $H_{\Omega}(\alpha)$  can be viewed as a function defined on  $2^{\mathcal{N}_n}$ 

$$H_{\Omega}: 2^{\mathcal{N}_n} \to [0, \infty).$$
 (6)

The goal of this paper is to study this function for all possible sets  $\Omega$  of n discrete random variables.

All basic Shannon's information measures can be expressed as linear functions of the joint entropies. Actually, we have

$$I(\alpha, \beta | \gamma) = H(\alpha \cup \gamma) + H(\beta \cup \gamma) - H(\alpha \cup \beta \cup \gamma) - H(\gamma).$$
 (7)

The basic inequalities can be interpreted as a set of inequalities for the entropy function as follows:

*Proposition 2:* For any set of jointly distributed discrete random variables the entropy function associated with these random variables has the following properties.

• For any two subsets and of

$$H(\alpha \cup \beta) + H(\alpha \cap \beta) \le H(\alpha) + H(\beta).$$
 (8)

• implies

$$H(\alpha) \le H(\beta).$$
 (9)

and

•

$$H(\phi) = 0. (10)$$

Let be the set of all functions defined on taking values in . Define

$$\Gamma_n \stackrel{\text{def}}{=} \{ F \in \mathcal{F}_n : F(\phi) = 0; \ \alpha \subset \beta \Rightarrow F(\alpha) \le F(\beta);$$

$$\forall \alpha, \beta \in 2^{\mathcal{N}_n}, F(\alpha) + F(\beta) \ge F(\alpha + F(\alpha \cap \beta)) \}.$$
 (11)

Apparently, for any . This means that the set characterizes some of the properties of the entropy function. A natural question to ask is whether or not this set "fully" characterizes the entropy function. To make the question more precise, we have introduced in [39] the following definitions.

*Definition 1:* A function is called *constructible* if and only if there exists a set of jointly distributed discrete random variables such that the joint entropy function associated with these random variables satisfies . Define

$$\Gamma_n^* = \{ F \in \mathcal{F}_n : F \text{ is constructible} \}.$$
 (12)

In [39], we have seen that the structure of this set could be very complicated and we mentioned that the following concept is more manageable:

*Definition 2:* A function is called *asymptotically constructible* if and only if there exist a sequence of sets of discrete random variables for such that the joint entropy functions associated with satisfy .

Obviously, a function is asymptotically constructible if and only if , the closure of the set .

In [39], we proved the following results.

*Theorem 1:*

$$\Gamma_2^* = \Gamma_2 \tag{13}$$

and

$$\overline{\Gamma}_3^* = \Gamma_3. \tag{14}$$

Up to this work, it was not known whether or not this result can be generalized. That is, we did not know whether for

$$\overline{\Gamma}_n^* = \Gamma_n. \tag{15}$$

This is a fundamental problem in information theory. In [39], we proved a conditional inequality of Shannon's information measures.

*Theorem 2:* For any four discrete random variables

$$I(X; Y) = I(X; Y|Z) = 0$$
 (16)

implies

$$I(X; Y|Z, U) \le I(Z; U|X, Y) + I(X; Y|U).$$
 (17)

We also proved in [39] that this result implies

$$\Gamma_n^* \neq \Gamma_n. \tag{18}$$

Therefore, it lends some evidence for the following conjecture.

*Conjecture 1:* For

$$\overline{\Gamma}_n^* \neq \Gamma_n. \tag{19}$$

To give an affirmative answer to this problem is the goal of the current paper.

The paper is organized as follows: in the next section, we state the main results and introduce some definitions and notations; Sections III and IV are devoted to the proofs of the results; in Section V, we summarize the findings of the paper and raise some problems for future study.

Before closing this section, we would like to give a brief account of the works we found in the literature which are relevant to the subject matter of the current paper. As Shannon's information measures are the most important measures in information theory, researchers in this area have been investigating their structural properties since the 1950's. The early works on this subject have been done along various directions by Campbell [2], Hu [10], McGill [21], Watanabe [31], [32].

McGill [21] has proposed a multiple mutual information for any number of random variables, which is a generalization of Shannon's mutual information for two random variables. Properties of the multiple mutual information have been investigated in the subsequent works of Kawabata and Yeung [6], Tsujishita [30], and Yeung [37].

The work of Hu [10] was the first attempt to establish an analogy between information theory and set theory. Toward this end, he defined the following formal substitution of symbols:

$$\begin{array}{cccc} H/I & \leftrightarrow & \mu \\ , & \leftrightarrow & \cup \\ ; & \leftrightarrow & \cap \\ | & \leftrightarrow & - \end{array}$$

where is any set-additive function. In the above substitution, on the left are symbols in information theory, while on the right are symbols in set theory. He showed that a linear informationtheoretic identity holds for all distributions if and only if the corresponding set-theoretic identity obtained via the formal substitution of symbols holds for all additive function . For example, the information-theoretic identity

$$H(X) + H(Y) = H(X, Y) + I(X; Y)$$

corresponds to the set-theoretic identity

$$\mu(X) + \mu(Y) = \mu(X \, \cup \, Y) + \mu(X \, \cap \, Y)$$

Hu's work was originally published in Russian, and it was not widely known in the west until it was reported in Csiszar and ´ Korner [3]. ¨

Important progress has been made in the mid 1970's and the early 1980's, mainly by Han [7], [9]. Let us point out that any linear information expression can be expressed as a linear combination of unconditional joint entropies by repeated applications (if necessary) of the following identity:

$$I(X; Y|Z) = H(X, Z) + H(Y, Z) - H(X, Y, Z) - H(Z).$$

In [7], Han proved the fundamental result that a linear combination of unconditional joint entropies is always equal to zero if and only if all the coefficients are zero. This result was also obtained independently by Csiszar and K ´ orner [3]. ¨ Han further established a necessary and sufficient condition for a symmetrical linear information expression to be always nonnegative, and a necessary and sufficient condition for a linear information expression involving three random variables to be always nonnegative [9]. In [9], he raised the important question of what linear combinations of unconditional joint entropies are always nonnegative. In his work, Han viewed a linear combination of unconditional joint entropies as a vector space, and he developed a lattice-theoretic description of Shannon's information measures with which some notations can be greatly simplified. During this time, Fujishige [5] found that the entropy function is a polymatroid [33].

In the 1990's, Yeung [34] further developed Hu's work into an explicit set-theoretic formulation of Shannon's information measures. Specifically, he showed that Shannon's information measures uniquely define a signed measure , called the measure, on a properly defined field. With this formulation, Shannon's information measures can formally be viewed as a signed measure, and McGill's multiple mutual information is naturally included. As a consequence, all set-theoretic techniques can now be used for the manipulation of information expressions. Furthermore, the use of information diagrams to represent the structure of Shannon's information measures becomes justified. We note that information diagrams have previously been used informally to illustrate the structure of Shannon's information measures [1], [22], [24]. Subsequently, Kawabata and Yeung [6] studied the structure of when the random variables form a Markov chain. Recently, Yeung *et al.* [36] have extended the study in [6] to random variables forming a Markov random field.

Recently, Yeung [35] defined the set of all constructible entropy functions and observed that whether an information inequality (linear or nonlinear) always holds is completely characterized by . This geometrical framework enables him to develop a unified description of all information inequalities (unconstrained or constrained) which are implied by the nonnegativity of Shannon's information measures, called the basic inequalities. This gives a partial answer to the question raised by Han in [9], and it directly leads to the question of whether all information inequalities which always hold are implied by the basic inequalities for the same set of random variables, or equivalently, whether is true. In fact, the same question was raised in [26] and [34], although at that time had not been defined and the intimate relation between and information inequalities was not known. This question is the starting point of the work by the authors in [39] and in the current paper. With the result in [39] that is a convex cone, answering the question raised by Han in [9] is equivalent to determining . In a recent paper [37], we have used the region to study the so-called distributed source-coding problem.

As a consequence of the work in [35], a software called ITIP (Information Theoretic Inequality Prover) [38] has been developed which can verify all linear information inequalities involving a definite number of random variables that are implied by the basic inequalities for the same set of random variables.

Along another line, motivated by the study of the logic of integrity constraints from databases, researchers in the area of probabilistic reasoning have spent much effort in characterizing the compatibility of conditional independence relation among random variables. This effort was launched by a seminal paper by Dawid [4], in which he proposed four axioms as heuristical properties of conditional independence. In information-theoretic terms, these four axioms can be summarized by the following statement:

$$I(X; Y, Z|U) = 0 \Leftrightarrow I(X; Y|U) = 0$$

and

$$I(X; Z|Y, U) = 0$$

Subsequent work on this subject has been done by Pearl and his collaborators in the 1980's, and their work is summarized in the book by Pearl [23]. Pearl conjectured that Dawid's four axioms completely characterize the conditional independence structure of any joint distribution. This conjecture, however, was refuted by the work of Studen´y [25]. Since then, Mat´u˘s and Studeny have written a series of papers on this problem ´ [13]–[29]. They have solved the problem for up to four random variables. It has been shown in [35] that the problem of characterizing the compatibility of conditional independence relations among random variables is a subproblem of the determination of .

## II. STATEMENT OF MAIN RESULTS

The key result of this paper is the following theorem:

*Theorem 3:* For any four discrete random variables , let

$$\Delta(Z, U|X, Y) = I(Z; U) - I(Z; U|X) - I(Z; U|Y)$$
. (20)

Then the following inequality holds:

$$\Delta(Z, U|X, Y) \le \frac{1}{2} [I(X; Y) + I(X; ZU) + I(Z; U|X) - I(Z; U|Y)].$$
(21)

Note that the right-hand side of (21) is not symmetric in and , whereas the left-hand side is. Therefore, we also have the following inequality:

$$\begin{split} \Delta(Z,\,U|X,\,Y) &\leq \tfrac{1}{2} \left[ I(X;\,Y) + I(Y;\,ZU) \right. \\ &\left. - I(Z;\,U|X) + \,I(Z;\,U|Y) \right] . \end{split} \tag{22}$$

Averaging inequalities (21) and (22) gives

$$\Delta(Z, U|X, Y) \le \frac{1}{2} I(X; Y) + \frac{1}{4} [I(X; ZU) + I(Y; ZU)]. \tag{23}$$

This theorem will be proved in the next section.

Let . Define for three subsets and of

$$I_F(\alpha;\beta|\gamma) = F(\alpha \cup \gamma) + F(\beta \cup \gamma) - F(\alpha \cup \beta \cup \gamma) - F(\gamma).$$

When is the empty set, we simply write in place of . Let

$$\Delta_F(i, j|k, l) = I_F(\{i\}; \{j\}) - I_F(\{i\}; \{j\}|\{k\})$$

$$-I_F(\{i\}; \{j\}|\{l\}). \tag{24}$$

Define

$$\tilde{\Gamma}_{4} = \{ F \in \Gamma_{4}: \text{ for any permutation } \pi \text{ of } \{1, 2, 3, 4\} 
\Delta_{F}(\pi(1), \pi(2) | \pi(3), \pi(4)) 
\leq \frac{1}{2} [I_{F}(\pi(3); \pi(4)) + I_{F}(\pi(1); \pi(2) | \pi(3)) 
-I_{F}(\pi(1); \pi(2) | \pi(4)) 
+I_{F}(\pi(3); \pi(1)\pi(2)) ] \}.$$
(25)

(Notice that, if we replace for by , respectively, then the inequality in (25) is just (21).) Theorem 3 says that

$$\overline{\Gamma}_4^* \subset \widetilde{\Gamma}_4$$
.

Theorem 3 implies the following result.

*Theorem 4:* For

$$\overline{\Gamma}_n^* \neq \Gamma_n. \tag{26}$$

*Proof:* Apparently, we need to prove the theorem only for . This will imply the conclusion of the theorem for any . Define a function by letting

$$\begin{split} F(\phi) &= 0 \\ F(X) &= F(Y) = F(Z) = F(U) = 2a > 0 \\ F(X,Y) &= 4a, \ F(X,U) = F(X,Z) = F(Y,U) \\ &= F(Y,Z) = F(Z,U) = 3a \\ F(X,Y,Z) &= F(X,Y,U) = F(X,Z,U) \\ &= F(Y,Z,U) = F(X,Y,Z,U) = 4a. \end{split}$$

Then Theorem 4 is proved by checking that and .

From Theorem 4, we have

$$\tilde{\Gamma}_4 \neq \Gamma_4 \qquad \tilde{\Gamma}_4 \subset \Gamma_4$$

That is, the set is a nontrivial outer bound of the set . Theorem 3 can be generalized to the following information inequalities for random variables where .

*Theorem 5:* For any set of discrete random variables and any

$$nI(U; Z) - \sum_{j=1}^{n} I(U; Z|X_j) - nI(U; Z|X_i)$$

$$\leq I(X_i; UZ) + \sum_{j=1}^{n} H(X_j) - H(X_1X_2 \cdots X_n). \quad (27)$$

Furthermore, by averaging (27) over , we obtain

$$nI(U; Z) - 2\sum_{j=1}^{n} I(U; Z|X_{j})$$

$$\leq \frac{1}{n}\sum_{i=1}^{n} I(X_{i}; UZ) + \sum_{j=1}^{n} H(X_{j}) - H(X_{1}X_{2} \cdots X_{n}).$$
(28)

The proof of this theorem is omitted because it can be proved using exactly the same idea used in the proof of Theorem 3 and an inductive argument.

So far, when we study the entropy function, it is viewed as a function defined on . That is, we use the subsets of as coordinates. is simply the joint entropy . It is more convenient to use another coordinate system when we study the inner bound of the set . To introduce this new coordinate system, we employ the concept of atoms. The atoms are also indexed by the subsets of , or the elements of . To motivate the definitions we are going to introduce, we first check the definitions of the conditional mutual informations of more than two random variables. Let be discrete random variables, then the conditional mutual information of random variables given [37] is defined as

$$I(X_{i1}; \dots; X_{ik} | X_{\alpha}) = \sum_{\gamma \subset \{i_1, \dots, i_k\}} (-1)^{1+|\gamma|} H(X_{\gamma \cup \alpha}).$$
(29)

Consider an arbitrary function in . We define a function for any pair of subsets , of the ground set where is nonempty. The values of the original function are denoted by , while for the values of the function , we use to replace to indicate that these are different from the values of the original function.

$$F[\alpha|\beta] \stackrel{\text{def}}{=} \sum_{\gamma \subset \alpha} (-1)^{1+|\gamma|} F(\gamma \cup \beta). \tag{30}$$

$$F[\alpha] \stackrel{\text{def}}{=} F[\alpha | \alpha^c] \tag{31}$$

where stands for the complement of with respect to the ground set . As we said, this concept is parallel to the concept of conditional mutual informations of more than two random variables. We have, for instance, when , , is the entropy function of five random variables

$$F[\alpha] = I(X_1; X_2; X_3 | X_4 X_5)$$

We say is the value of the function at the atom . The atoms are also indexed by the subsets of . The weight of an atom is defined as the cardinality of its index set.

The basic information inequalities can be restated under this new coordinate system as follows: *If is the entropy function of a set of random variables* , *then for any subset of of cardinality of and any subset of*

$$F[\alpha|\beta] \ge 0 \tag{32}$$

and for any single element set

$$F[\alpha] \ge 0. \tag{33}$$

This includes only a subset of the basic inequalities (called the elemental inequalities in [35]). But as we mentioned before, this subset of basic inequalities implies all other basic inequalities.

We use some simplified notations: as an example, if , , we write in place of . A useful formula for the function is the following lemma.

*Lemma 1:*

$$F[\alpha|\beta] = \sum_{\gamma \subset (\alpha \cup \beta)^c} F[\alpha \cup \gamma] \tag{34}$$

where stands for the complement of the set .

For four random variables , if is the entropy function of the four random variables, the basic inequalities are as follows: let be a permutation of

$$F[i,\,j] \geq 0$$
 
$$F[i,\,j] + F[i,\,j,\,k] \geq 0$$
 
$$F[i,\,j] + F[i,\,j,\,k] + F[i,\,j,\,l] + F[i,\,j,\,k,\,l] \geq 0$$
 and

We have from (20)

$$\Delta(X_1, X_2|X_3, X_4) = F[1, 2, 3, 4] - F[1, 2].$$
 (35)

We use in place of when is the entropy function. By the same formula, can be extended to any function which may not be an entropy function, that is,

$$\Delta_F(i,j|k,l) \stackrel{\text{def}}{=} F[i,j,k,l] - F[i,j]. \tag{36}$$

The following is an interesting quantity useful in the study of :

$$S_F(i, j|k, l) \stackrel{\text{def}}{=} F[i, j] + F[i, j, k] + F[i, j, l] + F[k, l].$$
 (37)

Let be the empty set, we have

$$S_{F}(i, j|k, l) = F[i, j|\phi] - \Delta_{F}(k, l|i, j)$$

$$= F[i, j] + F[i, j, k] + F[i, j, l]$$

$$+ F[i, j, k, l] - \Delta_{F}(k, l|i, j). \quad (38)$$

When is the entropy function of four discrete random variables , and

$$S_F(1, 2|3, 4) = I(X_1; X_2) + I(X_3; X_4|X_1) + I(X_3; X_4|X_2) - I(X_3; X_4).$$

This quantity may be negative. This fact will be proved at the end of this section. The importance of this information quantity will be seen in Theorem 6 stated in this section. Theorem 3 can be restated as follows.

*Theorem 3:* For four random variables , if is the entropy function, then

$$S_F(1, 2|3, 4) + F[1, 3|4] + F[1, 4|3] + F[3, 4|1] \ge 0.$$
 (39)

Inequalities (22) and (23) are now

$$S_F(1, 2|3, 4) + F[2, 3|4] + F[2, 4|3] + F[3, 4|2] \ge 0 \quad (40)$$
 and

$$2S_{F}(1, 2|3, 4) + F[1, 3|4] + F[1, 4|3] + F[2, 3|4] + F[2, 4|3] + F[3, 4|1] + F[3, 4|2] \ge 0.$$
(41)

That is, although the quantity can be negative for some entropy functions , but it is bounded from below by the maximum of the following two quantities:

$$-(F[1, 3|4] + F[1, 4|3] + F[3, 4|1])$$
$$-(F[2, 3|4] + F[2, 4|3] + F[3, 4|2])$$

We notice that is the conditional mutual information of the two random variables and given which is always nonnegative.

Define

$$\hat{\Gamma}_4 = \{ F \in \Gamma_4 : \text{ for any permutation } \pi \text{ of } \{1, 2, 3, 4\}$$
  
 $S_F(\pi(1), \pi(2) | \pi(3), \pi(4)) \ge 0 \}.$  (42)

The last theorem of the paper is

*Theorem 6:*

$$\hat{\Gamma}_4 \subset \overline{\Gamma}_4^*$$
 (43)

Theorem 6 has been previously proven in [20]. The example in [22, Sec. V and Lemma 4.1] imply this result. But their proof is very abstract and [22, Lemma 4.1] is based on further references. To make this result more understandable, we give a direct proof of Theorem 6 in Section IV. This theorem provides an inner bound to the cone .

The following nontrivial example shows that this inner bound is not tight. In other words, this example shows that the information quantity can be negative for some entropy functions .

*A Counterexample for the Positivity of :* A projective plane (for ) is a collection of subsets of of cardinality such that the intersection of any pair of subsets from the collection has cardinality exactly (see, for instance, [14, Appendix B]). For instance, is a projective plane for on the ground set .

$$169c,\,248c,\,259a,\,267b,\,349b,\,357c,\,368a$$

is another example of a projective plane on the ground set for . We are going to construct four discrete random variables for which the function is negative. In our construction, we use a pair of projective planes of the same size satisfying an additional property that, if we take one subset from each projective plane, the intersection of the two subsets taken always has cardinality at most . An example for such a pair is the previous projective plane for and the following projective plane of the same cardinality and on the same ground set:

0148, 025
$$c$$
, 037 $a$ , 069 $b$ , 1279, 156 $a$ , 13 $bc$ , 2346, 457 $b$ , 49 $ac$ , 28 $ab$ , 3589, 678 $c$ .

Let the ground set of the projective plane be , let be the diagonal of . Any projective plane has the property that

$$\cup_{A \in \mathcal{A}} (A \times A - \mathcal{D}) = \mathcal{P} \times \mathcal{P} - \mathcal{D}$$

where the sets are disjoint. Let the two projective planes we constructed above be for . For and , if the intersection of the two sets has cardinality , then and intersect at a set of cardinality . Otherwise, they are disjoint.

We define the following random variables : let both and take values in and the pair has the uniform joint distribution over . Let the first projective plane be and the second projective plane be . Let take value on for . Let take value on for . We have .

$$H(X_3) = H(X_4) = \log_2 13$$

$$H(X_3X_4) = \log_2 6 + \log_2 13.$$

$$H(X_3|X_1) = H(X_3|X_2) = H(X_4|X_1)$$

$$= H(X_4|X_2) = \log_2 4$$

$$H(X_3X_4|X_1) = H(X_3X_4|X_2) = \log_2 12.$$

Therefore,

$$I(X_3; X_4) = \log_2 13 - \log_2 6$$

and

$$I(X_3; X_4|X_1) = I(X_3; X_4|X_2) = \log_2(4/3).$$

This gives that for these four random variables

$$\begin{split} S(1,\,2|3,\,4) = & I(X_1;\,X_2) + I(X_3;\,X_4|X_1) \\ & + I(X_3;\,X_4|X_2) - I(X_3;\,X_4) \\ & = \log(13/12) + 2 \times \log_2(4/3) - \log_2(13/6) \\ & = \log_2(52/27) - \log_2(13/6) = -\log_2(9/8) \\ & < 0. \end{split}$$

This example shows that the function may be negative for some entropy functions and that our inner bound is not tight.

#### III. PROOF OF THEOREMS 3 AND 5

Let be four jointly distributed discrete random variables with distribution . We denote all marginals of this distribution by the same letter . For instance, its marginal on is denoted by . Define

$$q(x, y, z, u, x_1, y_1) \stackrel{\text{def}}{=} \frac{p(x, y, z, u)p(x_1, y_1, z, u)}{p(z, u)}.$$
(44)

Since both and are absolutely continuous with respect to , we can see that is a distribution of six random variables. Let be two random variables jointly distributed with according to the joint distribution .

Actually, we can express in terms of the information quantities of the six random variables defined above.

*Lemma 2:*

$$\Delta(Z, U|X, Y) = I(X; Y_1) - I(X; Y_1|U) - I(X; Y_1|Z) - I(Z; U|X, Y_1). \tag{45}$$

*Proof:*

$$\begin{split} \Delta(Z,U|X,Y) &= I(Z;U) - I(Z;U|X) - I(Z;U|Y) \\ &= I(Z;U) - I(Z;U|X) - I(Z;U|Y_1) \\ &= I(Z;U;X;Y_1) - I(Z;U|XY_1) \\ &= I(X;Y_1) - I(X;Y_1|U) - I(X;Y_1|Z) \\ &+ I(X;Y_1|ZU) - I(Z;U|XY_1) \\ &= I(X;Y_1) - I(X;Y_1|U) - I(X;Y_1|Z) \\ &- I(Z;U|XY_1). \end{split}$$

The last step is due to the fact that . The lemma is proved.

*Proof of Theorem 3:* From Lemma 2, we have

$$I(Z; U) - I(Z; U|X) - I(Z; U|Y) \le I(X; Y_1).$$

Similarly, we can prove

$$I(Z; U) - 2I(Z; U|X) \le I(X; X_1)$$

By means of these two inequalities, Theorem 3 is proved in the following way:

$$2I(Z; U) - 3I(Z; U|X) - I(Z; U|Y)$$

$$\leq I(X; Y_1) + I(X; X_1)$$

$$= I(X; X_1Y_1) + I(X; X_1; Y_1)$$

$$= I(X; X_1Y_1) + I(X_1; Y_1) - I(X_1; Y_1|X)$$

$$\leq I(X; X_1Y_1) + I(X_1; Y_1)$$

$$\leq I(X; ZU) + I(X_1; Y_1)$$

$$= I(X; ZU) + I(X; Y).$$

In the penultimate step, we used the data processing inequality and the fact that . The theorem is proved.

Using the six random variables , we can actually determine all the missing terms of the inequality in Theorem 3. This is done as follows: from Lemma 2

$$\Delta(Z, U|X, Y) = I(Z; U) - I(Z; U|X) - I(Z; U|Y)$$

$$= I(X; Y_1) - I(X; Y_1|U) - I(X; Y_1|Z)$$

$$- I(Z; U|XY_1).$$

Let . This equality is restated as

$$\Delta(Z, U|X, Y) = I(X; Y_1) - R_1$$

Similarly, we have

$$\Delta(Z, U|X, X_1) = I(Z; U) - I(Z; U|X) - I(Z; U|X_1)$$

$$= I(Z; U) - 2I(Z; U|X)$$

$$= I(X; X_1) - I(X; X_1|U) - I(X; X_1|Z)$$

$$- I(Z; U|XX_1).$$

Let . This equality is restated as

$$\Delta(Z, U|X, X_1) = I(X; X_1) - R_2.$$

Therefore,

$$\begin{split} 2I(Z;\,U) - 3I(Z;\,U|X) - I(Z;\,U|Y) \\ &= I(X;\,Y_1) + I(X;\,X_1) - R_1 - R_2 \\ &= I(X;\,X_1Y_1) + I(X;\,X_1;\,Y_1) - R_1 - R_2 \\ &= I(X;\,ZU) - I(X;\,ZU|X_1Y_1) + I(X_1;\,Y_1) \\ &- I(X_1;\,Y_1|X) - R_1 - R_2 \\ &= I(X;\,ZU) + I(X;\,Y) - I(X;\,ZU|X_1Y_1) \\ &- I(X_1;\,Y_1|X) - R_1 - R_2. \end{split}$$

This implies that the missing terms of the first inequality in Theorem 3 are

$$\begin{split} R(X,Y,Z,U,X_1,Y_1) &= \frac{1}{2} \left[ I(X;ZU|X_1Y_1) + I(X_1;Y_1|X) + R_1 + R_2 \right] \\ &= \frac{1}{2} \left[ I(X;X_1|U) + I(X;X_1|Z) + I(Z;U|XX_1) \right. \\ &+ I(X_1;Y_1|X) + I(X;ZU|X_1Y_1) \\ &+ I(X;Y_1|U) + I(X;Y_1|Z) + I(Z;U|XY_1) \right]. \end{split}$$

Apparently, the following function is in :

$$\begin{split} F(\phi) = 0, & F(X) = F(Y) = F(Z) = F(U) = 6a, \\ F(XY) = 12a, & F(XZ) = F(YZ) = F(YU) = F(XU) = 9a, \\ F(ZU) = 10a, & F(XZU) = F(YZU) = F(XZY) \\ & = F(XYU) = F(XZYU) = 12a. \end{split}$$

For this function, one of our new inequalities is satisfied with equality. A natural question to ask is whether or not this function is asymptotically constructible. If this is true, then it is likely that

$$\overline{\Gamma}_{4}^{*} = \widetilde{\Gamma}_{4}$$

Unfortunately, we were unable to prove this. Therefore, we doubt the correctness of this plausible conjecture.

## IV. PROOF OF THEOREM 6

In this section, we prove Theorem 6, the inner bound of . The result is proven via a series of basic constructions. Before we start to work on the proof of the result, we present first the basic constructions. In all constructions that follow, we use three independent and identically distributed ternary random variables , , and taking values in the set . The common distribution of the random variables is the uniform distribution. Let represent a constant random variable taking a fixed value with probability . To make the notations simpler, in this section, we assume that the logarithmic function is based to . Therefore, the random variables has entropy for . The entropy of is zero. In this section, we are going to use the concept of atoms. There are 15 atoms in the case of four random variables. They are represented by the nonempty subsets of . For any function , we will use the values of the function at atoms. The values of at atoms are linear functions of the values of the function at subsets of . The values of the function at subsets will be denoted, for instance, for , by . When is an entropy function, this is the joint entropy. To distinguish from the values at subsets, the values of the function at atoms are represented, for instance, at atom , by . When is the entropy function of four discrete random variables , we have

$$F[1, 2, 3] = I(X_1; X_2; X_3 | X_4)$$

*Construction 1:* For any nonempty subset of let if and , otherwise. The function defined by this construction is denoted by . It is easy to check that, for this construction, for any , and .

*Construction 2:* . The function defined by this construction is denoted by . For this construction, the function has value zero at all weight-one atoms, has value at all weight-two and weight-four atoms, and has value at all weight-three atoms.

*Construction 3:* . The function defined by this construction is denoted by where indicates that random variable . The construction is actually symmetric for the other three random variables. We also have the other three similar constructions obtained by permuting the four random variables. The functions so constructed are denoted by where indicates that . For this construction

$$F_4^3[1, 2] = F_4^3[1, 3] = F_4^3[2, 3] = 1$$

and

$$F_4^3[1, 2, 3] = -1.$$

At all other atoms the values are zero.

*Construction 4:* . The function so constructed is denoted by . We can also construct a function and its meaning is self-explanatory. For this construction,

$$F_{3,4}^4[1, 2] = 1$$
  
$$F_{3,4}^4[2, 3, 4] = F_{3,4}^4[1, 3, 4] = 1$$

and

$$F_{3,4}^4[1, 2, 3, 4] = -1.$$

At all other atoms it has zero value.

*Construction 5:* . The function constructed by this method is denoted by . For this construction, at all weight-one and -two atoms the value is zero; at all weight–three atoms the value is ; and .

*Construction 6:* , . The function constructed by this method is denoted by . We can also construct functions for other values of by the same method. For this construction, ; at all weighttwo atoms containing , the values are ; and . At all other atoms the values are zero.

*Construction 7:* , . The function constructed by this method is denoted by . We can also construct for other values of by the same method. For this construction, at all atoms of weight at most two the value is zero; at all weight-three atoms except the atom the values are ; and .

To help the reader to understand the proof, we give charts for the values of the functions constructed in Constructions 2–7. Since these functions take zero values at all weight-one atoms, we give their values at atoms of weight at least two. The atoms of weight at least two are arranged as follows:

$$\begin{array}{c|ccccccccccccccccccccccccccccccccccc$$

The values of the functions 2–7 are given as follows using this chart.

$$\begin{array}{c|ccccccccccccccccccccccccccccccccccc$$

$$\begin{array}{cccccccccccccccccccccccccccccccccccc$$

Function

$$\begin{array}{c|ccccccccccccccccccccccccccccccccccc$$

$$\begin{array}{c|ccccccccccccccccccccccccccccccccccc$$

$$\begin{array}{cccccccccccccccccccccccccccccccccccc$$

$$\begin{array}{c|ccccccccccccccccccccccccccccccccccc$$

In [39], we proved the following result:

*Lemma 3:* If and , then . If , then .

That is, is a convex cone.

*Proof of Theorem 6:* A function in the region should satisfy the following conditions in terms of atoms: Let the four indices of the random variables be which is a permutation of the set . From the definition of the region , the inequalities the function should satisfy include:

- 1) is nonnegative at all atoms of weight one;
- 2) , where is the empty set;

$$\begin{array}{c|ccccccccccccccccccccccccccccccccccc$$

The atoms involved in inequality (2).

3) 
$$F[i, j|k] = F[i, j] + F[i, j, l] \ge 0;$$

$$23$$

$$| (12) - (123) - 13$$

$$| | | | |$$

$$124 - 1234 - 134 - 14$$

$$| | | |$$

$$24 - 234 - 34$$

The atoms involved in inequality (3).

4) 
$$F[i, j] + F[i, j, k] + F[i, j, l] + F[k, l] \ge 0;$$

$$23$$

$$| (12) - (123) - 13$$

$$| | | | | (124) - 1234 - 134 - 14$$

$$| | | | | | (24) - 234 - (34)$$

The atoms involved in inequality (4).

5) 
$$F[i, j] \ge 0$$
.

Notice that the fourth condition comes from the constraint

$$S_F(i, j, k, l) \ge 0.$$

Other inequalities come from the nonnegativity of conditional mutual informations of two random variables and the nonnegativity of the conditional entropies. Lemma 1 is useful in finding the atoms involved in these inequalities. These five conditions will be referred to as Conditions 1–5 in the proof. The readers can extremely reduce the difficulty in subsequent reading by familiarizing themselves with these five conditions in the atom chart for all permutations of and .

A function is called nonnegative if its values at all atoms are nonnegative.

*Lemma 4:* Nonnegative functions are asymptotically constructible.

*Proof:* If is a function that takes nonnegative values at all atoms, then

$$J = \sum_{\alpha} J[\alpha] F_{\alpha}^{1}$$

where is nonnegative for all . It is asymptotically constructible from Construction 1 and Lemma 4. The lemma is proved.

The basic idea for the proof is that for any function in , we can find a sequence of basic functions from Constructions 1–7 for some and a sequence of nonnegative reals such that

$$F = \sum_{j=1}^{m} a_j F_j.$$

Once we can prove this, then the theorem is proved by invoking Lemma 4. Suppose is in and is a basic function from Constructions 1–7 and . If , then we say that subtracting from is a legal operation. We prove the theorem by finding a sequence of legal operations to reduce to a nonnegative function, which is asymptotically constructible by Lemma 5. This implies by invoking Lemma 4 that the original function is asymptotically constructible.

Construction 1 is used only in Lemma 5. In the proof that follows, we use only the other six constructions. We notice that in Constructions 2–7, no atom of weight one is involved. As long as the values of the function at the weight-one atoms are nonnegative to start with, upon subtracting a nonnegative multiple of any of these constructions, Condition 1 remains satisfied. Therefore, we can always ignore the weight-one atoms when we consider subtracting a nonnegative multiple of any of these constructions.

We find these legal operations in the following steps.

*Step 1:* We notice that satisfies all inequalities in Conditions 2–4 with equalities. So subtracting from where

$$a = \min_{\{i, j\} \subset \{1, 2, 3, 4\}} F[i, j]$$

is a legal operation because 1) Conditions 2–4 will remain to be satisfied since subtracting zero does not change the direction of the inequalities and 2) since is defined as the minimum of the values of the function at all weight-two atoms, after subtracting the values of at these atoms are at least . Therefore, Condition 5 holds. Without loss of generality, we assume that

$$F[1, 2] = \min_{\{i, j\} \subset \{1, 2, 3, 4\}} F[i, j].$$

Let . We have

i) 
$$F' \in \hat{\Gamma}_4$$
;

ii) 
$$F'[1, 2] = 0$$
.

In the following chart, the atoms are marked either by a indicating that the value of the function at this atom is zero, or by a indicating that the value of the function at this atom is nonnegative, or by an indicating that the value of the function at this atom may be negative.

The Function

*Step 2:* A function is called seminonnegative if its values at all atoms of weight up to three are nonnegative. In this step, we prove that can be reduced to a seminonnegative function via a series of legal operations. From the chart for , we see is not seminonnegative if and only if at least one of two values of , and , is negative. Suppose

Let . We prove that subtracting from is legal. Let . We notice that

$$F_2^3[i, j|\phi] = 0$$
  
 $F_2^3[i, j|k] = 0$ 

for any . These observations and imply that

$$G[i, j|\phi] \ge 0$$
$$G[i, j|k] \ge 0$$

From , we see that

$$G[1, 3] = G[1, 3] + G[1, 3, 4] = F'[1, 3] + F'[1, 3, 4] > 0.$$

Similarly, we have

$$G[1, 4] \ge 0$$
  
 $G[3, 4] \ge 0$ .

For other pairs , since the values of are not affected by the operation, we still have

$$G[i, j] \ge 0$$

To show that , we need to check only Condition 4

$$G[i,\,j] + G[i,\,j,\,k] + G[i,\,j,\,l] + G[k,\,l] \geq 0.$$

There are six of them for

$$(i, j) = (3, 4), (1, 4), (1, 3), (1, 2), (2, 3), (2, 4).$$

The inequalities for are trivial because all entries are nonnegative. The proofs for are the same. We prove it only for

. We need also to prove it for . For

$$G[1, 3]+G[1, 2, 4]+G[2, 3, 4]+G[2, 4]$$

$$=F'[1, 3]+F'[1, 2, 4]+F'[2, 3, 4]+F'[2, 4]$$

$$-a(F_2^3[1, 3]+F_2^3[1, 2, 4]+F_2^3[2, 3, 4]+F_2^3[2, 4])$$

$$=F'[1, 3]+F'[1, 2, 4]+F'[2, 3, 4]+F'[2, 4]-aF_2^3[1, 3]$$

$$=F'[1, 3]+F'[1, 2, 4]+F'[2, 3, 4]+F'[2, 4]+F'[1, 3, 4]$$

$$\geq F'[1, 3]+F'[1, 3, 4]+F'[2, 3, 4]+F'[2, 4]$$

$$\geq 0.$$

In the next to the last step, we used the fact that and in the last step, we used the fact that . For

$$G[1, 2] + G[2, 3, 4] + G[1, 3, 4] + G[3, 4]$$

$$= F'[1, 2] + F'[1, 3, 4] + F'[2, 3, 4] + F'[3, 4]$$

$$- a(F_2^3[1, 2] + F_2^3[1, 3, 4] + F_2^3[2, 3, 4] + F_2^3[3, 4])$$

$$= F'[1, 2] + F'[1, 3, 4] + F'[2, 3, 4] + F'[3, 4]$$

$$- a(F_2^3[1, 3, 4] + F_2^3[3, 4])$$

$$= F'[1, 2] + F'[1, 3, 4] + F'[2, 3, 4] + F'[3, 4]$$

$$\geq 0.$$

In the next to the last step, we used the fact that and in the last step, we used the fact that . This proves that . If , then is already seminonnegative. Otherwise, repeating the same proof by replacing atom by , we can obtain a seminonnegative function. Therefore, without loss of generality, we assume that is already seminonnegative.

*Step 3:* Since is seminonnegative, if the value of at is nonnegative, then the function is already nonnegative and therefore asymptotically constructible from Lemma 5. Otherwise, we continue to find legal operations to convert the function to a nonnegative function. In doing so, the inequalities we need to consider are those in which the atom of weight four is involved. That is, the following six inequalities

$$\sum_{\{i,j\}\subset\alpha} G[\alpha] \ge 0$$

for all six pairs from . The following observations will be useful in the remaining part of the proof.

*Observation 1:* Let be a permutation of , and let be a seminonnegative function. Then

$$J[i, j, k] + J[1, 2, 3, 4] \ge 0$$

implies that subtracting from is legal and results in a seminonnegative function where

$$a = \min\{J[k, \, l], \, J[i, \, k, \, l], \, J[j, \, k, \, l]\}.$$

*Observation 2:* Let be a permutation of , and let be a seminonnegative function. Then

$$J[i, j, k] + J[1, 2, 3, 4] \ge 0$$
$$J[i, j, l] + J[1, 2, 3, 4] \ge 0$$
$$J[i, k, l] + J[1, 2, 3, 4] \ge 0$$

implies that subtracting from is legal and results in a nonnegative function where

$$a = \min\{J[i, k, l], J[i, j, l], J[i, j, k]\}.$$

The validity of these propositions is obvious.

Since functions , , and satisfy all these six inequalities with equalities, as long as at atoms of weight up to three the values of the function are not reduced below zero, subtracting a nonnegative multiple of one of these functions is always legal and results in a seminonnegative function. Suppose we keep performing these legal operations until no more legal operations resulting in a seminonnegative function using these three functions are possible. We distinguish the following cases according to the function that is resulted in.

Because no operation using function is legal, for any subset of , is zero at least one of the following atoms: , , (cf., the atom chart for ). There are only two possible cases:

*Case 1:* There exists a -subset, say , such that is zero at all three atoms: , , .

*Case 2:* There exist two disjoint weight-two atoms, say and , such that the values of the function at these two atoms are both zero.

In Case 1, without loss of generality, we assume that

$$G'[1,\,2]=G'[1,\,3]=G'[2,\,3]=0.$$

Since does not give a legal operation resulting in a seminonnegative function, the function takes value zero at one of the following four atoms: , , , . This gives two subcases,

*Case 1.1:* The function is zero at (or equivalently one of two other weight-two atoms listed above).

*Case 1.2:* The function is zero at .

In Case 1.1, since does not give a legal operation resulting in a seminonnegative function, at least one of the four weight-three atoms, the function takes zero value. We consider only the cases where at one of the three atoms , , and , the value of the function is zero. The case where the function is zero at the atom is equivalent to Case 1.2. Since the first two atoms are symmetric in this context, we consider only the case that the function is zero at . We can see that Condition 2 implies

$$G'[1, 3, 4] + G'[1, 2, 3, 4] \ge 0$$

because both and are zero

$$\begin{array}{c|ccccccccccccccccccccccccccccccccccc$$

The Function in Case 1.1 for

Let

$$a = \min\{G'[2, 4], G'[1, 2, 3], G'[1, 3, 4]\}.$$

The inequalities above imply that subtracting from is legal and results in a seminonnegative function . If is zero at either or , then . The function obtained is already nonnegative. Otherwise, . This implies

$$G''[2, 3, 4] + G''[1, 2, 3, 4] \ge 0.$$

Let , if then subtracting is a legal operation and this results in a function that is nonnegative at all atoms.

If , we have

$$G'[1, 2, 3] + G'[1, 2, 3, 4] \ge 0$$

because both and are zero.

$$\begin{array}{c|ccccccccccccccccccccccccccccccccccc$$

The Function in Case 1.1 for

Let

$$a = \min\{G'[3, 4], G'[1, 2, 3], G'[1, 2, 4]\}.$$

The inequalities above imply that subtracting from is legal and results in a seminonnegative function . If is zero at then . If is zero at then this goes back to the previous case. In both cases, either the function obtained is already nonnegative, or it can be reduced to a nonnegative function by legal operations. Otherwise, . For this function, we have

$$G''[1, 2, 3, 4] + G''[1, 3, 4] \ge 0.$$

Let

$$a=\min\{G''[2,\,4],\;G''[1,\,2,\,3],\;G''[1,\,3,\,4]\}.$$

The inequalities above imply that subtracting from is legal and results in a seminonnegative function . If is zero at either or , then . Otherwise, . For this function, we have

$$\begin{split} G'''[1,2,3,4] + G'''[1,2,4] \ge 0 \\ G'''[1,2,3,4] + G'''[1,2,3] \ge 0 \\ G'''[1,2,3,4] + G'''[1,3,4] \ge 0. \end{split}$$

Let , if then subtracting is a legal operation and this results in a function that is nonnegative at all atoms.

In Case 1.2, we have

$$G'[1, 3, 4] + G'[1, 2, 3, 4] \ge 0,$$
  

$$G'[1, 2, 4] + G'[1, 2, 3, 4] \ge 0,$$
  

$$G'[2, 3, 4] + G'[1, 2, 3, 4] \ge 0.$$

$$\begin{array}{c|ccccccccccccccccccccccccccccccccccc$$

The Function in Case 1.2.

Let . If , then subtracting is a legal operation. This results in a nonnegative function. Otherwise, the function is already nonnegative.

We now consider Case 2. Without loss of generality, we assume that . Since does not give a legal operation resulting in a seminonnegative function, the function has value zero at least one of the four weight-three atoms. Without loss of generality, we assume . Then we have

$$G'[1, 2, 4] + G'[1, 2, 3, 4] \ge 0.$$

$$\begin{array}{c|ccccccccccccccccccccccccccccccccccc$$

The Function in Case 2.

Let . Then subtracting is legal. The function resulting from this legal operation takes zero value at either , , or . In the first case, , we have

$$G''[1, 3] + G''[1, 2, 3, 4] \ge 0.$$

Apparently, subtracting is legal where

$$b = \min\{G''[1, 3], G''[1, 2, 4], G''[2, 3, 4]\}.$$

This results in a nonnegative function. In the second case, , we have

$$G'[2, 3, 4] + G'[1, 2, 3, 4] \ge 0$$

Let

$$a = \min\{G'[1, 3], G'[1, 2, 4], G'[2, 3, 4]\}$$

Subtracting is legal. Let be . Then either or . In both cases, we must have , that is, the function is nonnegative. Otherwise, . This implies

$$G''[1, 3, 4] + G''[1, 2, 3, 4] \ge 0$$
  
 $G''[1, 2, 4] + G''[1, 2, 3, 4] \ge 0$ 

and

$$G''[2, 3, 4] + G''[1, 2, 3, 4] \ge 0$$

Then, subtracting is legal and results in a nonnegative function. In the third case, , must be nonnegative. Hence, is a nonnegative function.

Thus we have proved that we can always reduce a function in by legal operations to a function that takes nonnegative values at all atoms. By Lemma 5, Theorem 6 follows.

# V. CONCLUDING REMARKS

The key result of this paper is Theorem 3. This discovery shows that the set of so-called basic information inequalities cannot fully characterize Shannon's entropy function in the sense of Theorem 4. That is, the region is strictly greater than the region . This is a surprising result because based on intuition, one tends to believe that the opposite is true. Actually, when we started to look into this problem, we tried first to prove that

$$\overline{\Gamma}_{4}^{*} = \Gamma_{4}$$

by finding all kinds of constructions for four random variables as in the proof of Theorem 6. Only after we failed to find a construction in one of many cases, we started to doubt the correctness of our conjecture. This led to the discovery of this new information inequality.

The full characterization of the region seems to be a highly nontrivial problem. Even in the case of , we were unable to determine the region. We, instead, provided an inner bound of the region. This is Theorem 6 of the paper. The inner bound and the outer bound we found in this paper differ. It has been shown by an example that the inner bound is not tight. Unfortunately, the construction method we used in this example is not powerful enough to show that our outer bound is tight.

The simplest case of the problem is the case of because this number is the smallest integer for which and differ. Although we mainly have concentrated on this simplest case, we have proved Theorem 5 which is a generalization of Theorem 3 to any number of random variables.

We also determined the missing terms in the inequalities in Theorem 3. They are expressed in terms of some auxiliary random variables. We did so in hope that this may be helpful in further searching for new information inequalities, as well as in further searching for improved inner bounds.

To get a better understanding of the behavior of the entropy function, it is important to fully characterize the function at least in the simplest case of . That is, the simplest task in this research direction is to determine the region . Based on our experience, we do not believe our outer bound to be tight. That is, we believe that there may exist more linear unconditional information inequalities involving four random variables.

The meaning of the new information inequalities provided by Theorems 3 and 5 are still not fully understood. Although we have used the region to study the so-called distributed source coding problem, it is still of great interest to find more applications of the inequalities in other information-theoretical problems, especially in multiuser channel coding or source coding problems.

The problems studied in this paper have close connection to some other areas such as probabilistic reasoning, relational database, and so on. To study the implication of our results in those areas is also of interest.

#### ACKNOWLEDGMENT

The authors are grateful to the two referees. Their detailed comments and suggestions have greatly improved the readability of the paper.

#### REFERENCES

- [1] N. M. Abramson, *Information Theory and Coding.* New York: McGraw-Hill, 1963.
- [2] L. L. Campbell, "Entropy as a measure," *IEEE Trans. Inform. Theory*, vol. IT-11, pp. 112–114, Jan. 1965.
- [3] I. Csiszar and J. K ´ orner, ¨ *Information Theory: Coding Theorem for Discrete Memoryless Systems.* New York: Academic, and Budapest, Hungary: Akademiai Kiado, 1981.
- [4] A. P. Dawid, "Conditional independence in statistical theory (with discussion)," *J. Roy. Statist. Soc., Ser. B*, vol. 41, pp. 1–31.
- [5] S. Fujishige, "Polymatroidal dependence structure of a set of random variables," *Inform. Contr.*. vol. 39, pp. 55–72, 1978.
- [6] T. Kawabata and R. W. Yeung, "The structure of the I-measure of a Markov chain," *IEEE Trans. Inform. Theory*, vol. 38, pp. 1146–1149, 1992.
- [7] T. S. Han, "Linear dependence structure of the entropy space," *Inform. Contr.*, vol. 29, pp. 337–368.
- [8] , "Nonnegative entropy measures of multivariate symmetric correlations," *Inform. Contr.*, vol. 36, pp. 133–156, 1978.
- [9] , "A uniqueness of Shannon's information distance and related nonnegativity problems," *J. Comb., Inform. Syst. Sci.*, vol. 6, pp. 320–321, 1981.
- [10] G.-d. Hu, "On the amount of information," *Teor. Veroyatnost. i Primenen.*, vol. 4, pp. 447–455, 1962, in Russian.
- [11] F. Matu´s, private communication. ˘
- [12] F. J. MacWilliams and N. J. A. Sloane, *The Theory of Error Correcting Codes.* Amsterdam, The Netherlands: North-Holland, Elsevier Science B.V., 1977.

- [13] M. Mat´u˘s, "Abstract functional dependency structures," *Theor. Comput. Sci.*, vol. 81, pp. 117–126, 1991.
- [14] , "On equivalence of Markov properties over undirected graphs," *J. Appl. Probab.*, vol. 29, pp. 745–749, 1992.
- [15] , "Ascending and descending conditional independence relations," in *Trans. 11th Prague Conf. Information Theory, Statistical Decision Functions and Random Processes*, vol. B. Prague, Czechoslovakia: Academia, pp. 181–200, 1992.
- [16] , "Probabilistic conditional independence structures and matroid theory: Background," *Int. J. Gen. Syst.*, vol. 22, pp. 185–196.
- [17] , "Extreme convex set functions with many nonnegative differences," *Discr. Math.*, vol. 135, pp. 177–191, 1994.
- [18] F. Matu´s, "Conditional independences among four random variables II," ˘ *Combin., Prob. Comput.*, vol. 4, pp. 407–417, 1995.
- [19] , "Conditional independence structures examined via minors," *Ann. Math., Artificial Intell.*, vol. 21, pp. 99–128, 1997.
- [20] F. Matu´s and M. Studen ˘ y, "Conditional independences among four ´ random variables I," *Combin., Prob. Comput.*, vol. 4, pp. 269–278, 1995.
- [21] W. J. McGill, "Multivariate information transmission," in *Trans. Prof. Group Inform. Theory, 1954 Symp. Information Theory*, vol. PGIT-4, 1955, pp. 93–111.
- [22] A. Papoulis, *Probability, Random Variables and Stochastic Processes*, 2nd ed. New York: McGraw-Hill, 1984.
- [23] J. Pearl, *Probabilistic Reasoning in Intelligent Systems.* San Mateo, CA: Morgan Kaufman, 1988.
- [24] *An Introduction to Information Theory.* New York: McGraw-Hill, 1961.
- [25] M. Studeny, "Attempts at axiomatic description of conditional indepen- ´ dence," in *Proc. Workshop on Uncertainty Processing in Expert Systems*, supplement to *Kybernetika*, vol. 25, nos. 1–3, pp. 65–72, 1989.
- [26] , "Multiinformation and the problem of characterization of conditional independence relations," *Probl. Contr. Inform. Theory*, vol. 18, pp. 3–16, 1989.
- [27] , "Conditional independence relations have no finite complete characterization," in *Trans. 11th Prague Conf. Information Theory, Statistical Decision Functions and Random Processes*, vol. B. Prague, Czechoslovaka: Academia, pp. 377–396, 1992.
- [28] , "Structural semigraphoids," *Int. J. Gen. Syst.*, vol. 22, no. 2, pp. 207–217, 1994.
- [29] , "Descriptions of structures of stochastic independence by means of faces and imsets (in three parts)," *Int. J. Gen. Syst.*, vol. 23, pp. 123–137, pp. 201–219, pp. 323–341, 1994/1995.
- [30] T. Tsujishita, "On triple mutual information," *Adv. Appl. Math.*, vol. 16, pp. 269–274, 1995.
- [31] S. Watanabe, "A study of ergodicity and redundancy on intersymbol correlation of finite range," in *Trans. 1954 Symp. Inform. Theory* (Cambridge, MA, Sept. 15–17, 1954), p. 85.
- [32] , "Information theoretical analysis of multivariate correlation," *IBM J.*, pp. 66–81, 1960.
- [33] D. J. A. Welsh, *Matroid Theory.* New York: Academic 1976.
- [34] R. W. Yeung, "A new outlook on Shannon's information measures," *IEEE Trans. Inform. Theory*, vol. 37, pp. 466–474, 1991.
- [35] , "A framework for linear information inequalities," *IEEE Trans. Inform. Theory*, vol. 43, pp. 1924–1934, Nov. 1997.
- [36] R. W. Yeung, T. T. Lee, and Z. Ye, "An information-theoretic characterization of Markov random fields and its applications," *IEEE Trans. Inform. Theory*, submitted for publication.
- [37] R. W. Yeung and Z. Zhang, "Distributed source coding for satellite communication," *IEEE Trans. Inform. Theory*, submitted for publication.
- [38] R. W. Yeung and Y.-O. Yan, "Information theoretic inequality prover." [Online] Available: http://www.ie.cuhk.edu.hk/ ITIP or http://it.ucsd. edu/\verb+˜+whyeung(mirrorsite)..
- [39] Z. Zhang and R. W. Yeung, "A non-Shannon type conditional inequality of information quantities," *IEEE Trans. Inform. Theory*, vol. 43, pp. 1982–1985, Nov. 1997.