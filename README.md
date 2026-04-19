# The Zhang-Yeung Inequality

A Lean 4 formalization of the Zhang-Yeung conditional information inequality, a non-Shannon-type bound on Shannon entropy that cannot be derived from the Shannon inequalities alone.

The central object is the Zhang-Yeung delta,

```text
Δ(Z, U | X, Y) := I(Z ; U) - I(Z ; U | X) - I(Z ; U | Y),
```

and the main theorem (Theorem 3 of [Zhang and Yeung 1998](https://doi.org/10.1109/18.705560)) is the upper bound

```text
Δ(Z, U | X, Y) ≤ (1/2) · I(X ; Y) + (1/4) · (I(X ; Z,U) + I(Y ; Z,U)).
```

The proof rests on the copy lemma, which identifies the inequality as genuinely non-Shannon: no amount of Shannon-type reasoning can replace the copy construction.

## Status

| Milestone | Title                                    | State       |
| --------- | ---------------------------------------- | ----------- |
| M0        | Project scaffolding                      | done        |
| M1        | Delta equational lemmas                  | done        |
| M1.5      | Theorem 2 (standalone conditional result)| done        |
| M2        | The copy lemma                           | done        |
| M3        | Theorem 3 (main inequality)              | done        |
| M4        | Theorem 4 (Shannon-cone separation)      | planned     |
| M5        | Theorem 5 (stretch goal)                 | planned     |
| M6        | Polish and release                       | planned     |

M1.5 is complete: the public `ZhangYeung.theorem2` is fully proved with no `sorry`. The proof factors into (a) a Shannon-algebra reduction of the target inequality to `Δ(Z, U | X, Y) ≤ 0` under the hypotheses `I[X:Y] = I[X:Y|Z] = 0`, and (b) a non-Shannon closing argument via the [@zhangyeung1997] auxiliary `p̃`/`p̂` PMF construction and `Real.sum_mul_log_div_leq`. Kaced and Romashchenko [@kaced2013] classify this inequality as essentially conditional -- it fails on the closure of the entropic region, so no Lagrange combination of Shannon-type inequalities and the premises suffices, and the KL route is effectively the only known proof. To our knowledge this is the first formalization of any non-Shannon-type information inequality in any proof assistant.

M2 is complete: the copy lemma of [@zhangyeung1998, §III eqs. 44-45] is formalized as the existential `copyLemma`, which wraps PFR's `ProbabilityTheory.condIndep_copies` on the pair `⟨X, Y⟩` conditioned on the shared variable `⟨Z, U⟩` and produces an extended law `ν` with a second conditionally-independent copy `(X₁, Y₁)` of `(X, Y)` over `(Z, U)`. Lemma 2 of the same paper (eq. 45) ships both as the abstract Shannon identity `delta_of_condMI_vanishes_eq`, which holds whenever a single conditional mutual information vanishes, and as six Zhang-Yeung-flavored corollaries specialized to the copy's projections: `copyLemma_delta_transport_Y_to_Y₁` and `copyLemma_delta_transport_X_to_X₁` transport `Δ` between `μ` and `ν`; `copyLemma_delta_identity_Y₁` and `copyLemma_delta_identity_X_X₁` instantiate Lemma 2 at the copy; and `copyLemma_delta_le_mutualInfo_Y₁` and `copyLemma_delta_le_mutualInfo_X_X₁` combine the identity with nonnegativity of the three conditional-mutual-information terms on its right-hand side to yield the two `Δ ≤ I(·;·)` inequalities that feed the Shannon chase for Theorem 3.

M3 is complete: Theorem 3 of [@zhangyeung1998, §III eqs. 21-23], the headline Zhang-Yeung inequality and the first known non-Shannon-type linear inequality on Shannon entropies of four random variables, is formalized in all three of the paper's equivalent forms. The public theorems `zhangYeung` (eq. 21, asymmetric), `zhangYeung_dual` (eq. 22, the `X ↔ Y` swap), and `zhangYeung_averaged` (eq. 23, the averaged symmetric form displayed in this README's header) sit on top of a single private `zhangYeung_integer` that closes the paper's Shannon chase at the integer-scaled shape `2·I[Z:U] - 3·I[Z:U|X] - I[Z:U|Y] ≤ I[X:Y] + I[X:⟨Z,U⟩]`; the three public wrappers route this through the M1 form-conversion lemmas `delta_form21_iff`, `delta_form22_iff`, `delta_form23_iff`, and `delta_form23_of_form21_form22`. The chase itself takes the two M2 copy-lemma inputs (`copyLemma_delta_le_mutualInfo_Y₁` and `copyLemma_delta_le_mutualInfo_X_X₁`), adds a generic three-way mutual-information identity, invokes data processing for PFR's `CondIndepFun` on the copy (via the `ZhangYeung.condIndepFun_comp` helper promoted to `ZhangYeung/Prelude.lean` as part of M3), and transports the result back to `μ` through `IdentDistrib.mutualInfo_eq`.

The full roadmap is in [`docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md`](docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md).

## Formalization Scope

- Finite-alphabet, real-valued probability distributions.
- Built on top of PFR's entropy API (`H[X]`, `I[X:Y]`, `I[X:Y|Z]`) from [teorth/pfr](https://github.com/teorth/pfr), pinned in `lakefile.toml`.
- Measurability and finite-range side conditions expressed via [Mathlib](https://github.com/leanprover-community/mathlib4)'s [`[MeasurableSpace]`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Defs.html#MeasurableSpace), [`[Fintype]`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Fintype/Defs.html#Fintype), and [`[MeasurableSingletonClass]`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Defs.html#MeasurableSingletonClass) typeclasses.
- Deferred: infinite alphabets, computable entropy, upstream push of the copy lemma into PFR or Mathlib.

## Module Layout

- [`ZhangYeung.lean`](ZhangYeung.lean) — project entrypoint; re-exports `ZhangYeung.CopyLemma`, `ZhangYeung.Delta`, `ZhangYeung.Prelude`, `ZhangYeung.Theorem2`, and `ZhangYeung.Theorem3`.
- [`ZhangYeung/Prelude.lean`](ZhangYeung/Prelude.lean) — import surface for PFR's entropy API, plus the generic `ZhangYeung.condIndepFun_comp` helper (post-composition of PFR's random-variable-form `CondIndepFun` by measurable codomain functions, promoted from `ZhangYeung/CopyLemma.lean` in M3).
- [`ZhangYeung/Delta.lean`](ZhangYeung/Delta.lean) — M1 delta quantity and equational lemmas (`delta_def`, `delta_comm_cond`, `delta_comm_main`, `delta_self`, `delta_eq_entropy`, `delta_form21_iff`, `delta_form22_iff`, `delta_form23_iff`, `delta_form23_of_form21_form22`, `delta_le_mutualInfo`).
- [`ZhangYeung/Theorem2.lean`](ZhangYeung/Theorem2.lean) — M1.5 Zhang-Yeung conditional information inequality (`theorem2`), a standalone formalization of the first known non-Shannon-type conditional information inequality; factored into a Shannon-algebra reduction (`theorem2_shannon_identity`) and the KL-divergence core (`theorem2_delta_le_zero`) with supporting lemmas `ptilde_sum_eq_one`, `phat_sum_eq_one`, `delta_eq_sum_log_ratio`, `sum_joint_eq_sum_ptilde`.
- [`ZhangYeung/CopyLemma.lean`](ZhangYeung/CopyLemma.lean) — M2 Zhang-Yeung copy lemma (§III eqs. 44-45 of the 1998 paper); ships the `copyLemma` existential (a thin wrapper over PFR's `ProbabilityTheory.condIndep_copies`), the abstract Lemma 2 `delta_of_condMI_vanishes_eq`, and six copy-projection corollaries (`copyLemma_delta_transport_Y_to_Y₁`, `copyLemma_delta_transport_X_to_X₁`, `copyLemma_delta_identity_Y₁`, `copyLemma_delta_identity_X_X₁`, `copyLemma_delta_le_mutualInfo_Y₁`, `copyLemma_delta_le_mutualInfo_X_X₁`) covering the two delta transports, two delta identities, and two `Δ ≤ I(·;·)` inequalities feeding the Shannon chase for Theorem 3.
- [`ZhangYeung/Theorem3.lean`](ZhangYeung/Theorem3.lean) — M3 Zhang-Yeung inequality (Theorem 3 of the 1998 paper, §III eqs. 21-23): `zhangYeung` (eq. 21), `zhangYeung_dual` (eq. 22), and `zhangYeung_averaged` (eq. 23), all derived from a private `zhangYeung_integer` that closes the paper's Shannon chase on the copy joint and routes through the M1 form-conversion lemmas.
- [`ZhangYeungTest.lean`](ZhangYeungTest.lean) + [`ZhangYeungTest/Delta.lean`](ZhangYeungTest/Delta.lean) + [`ZhangYeungTest/Theorem2.lean`](ZhangYeungTest/Theorem2.lean) + [`ZhangYeungTest/CopyLemma.lean`](ZhangYeungTest/CopyLemma.lean) + [`ZhangYeungTest/Theorem3.lean`](ZhangYeungTest/Theorem3.lean) — compile-time API regression tests for each module.

## Build and Verify

Fresh clone or worktree:

```bash
bin/bootstrap-worktree      # mandatory: downloads Mathlib + PFR prebuilt artifacts, then builds
```

Day-to-day commands:

```bash
make build                  # lake build ZhangYeung
make test                   # lake test (ZhangYeungTest example suite)
make lean-lint              # lake lint (batteries/runLinter)
make lint                   # markdownlint-cli2 + cspell
make check                  # lint + lean-lint + build + test
make help                   # show all targets
```

See [`AGENTS.md`](AGENTS.md) for the full command reference and [`CONTRIBUTING.md`](CONTRIBUTING.md) for the development workflow.

## Dependencies

- [Lean 4](https://lean-lang.org/) toolchain, pinned in [`lean-toolchain`](lean-toolchain).
- [Lake](https://github.com/leanprover/lean4/blob/master/src/lake/README.md) (bundled with Lean).
- [PFR](https://github.com/teorth/pfr), pinned by Git revision in [`lakefile.toml`](lakefile.toml). PFR supplies the entropy API used throughout.
- [Mathlib](https://github.com/leanprover-community/mathlib4) (via PFR), downloaded as prebuilt artifacts by the bootstrap script. Never built from source in CI or in a fresh worktree.

## References

Primary sources and transcriptions live in [`references/`](references/). The paper being formalized and the principal background text:

- Zhang and Yeung (1998). _On characterization of entropy function via information inequalities_. IEEE Transactions on Information Theory 44(4). [DOI: 10.1109/18.705560](https://doi.org/10.1109/18.705560). ([`references/papers/zhangyeung1998.pdf`](references/papers/zhangyeung1998.pdf); verified transcription at [`references/transcriptions/zhangyeung1998.md`](references/transcriptions/zhangyeung1998.md).)

Other closely related texts:

- Zhang and Yeung (1997). _A non-Shannon-type conditional inequality of information quantities_. IEEE Transactions on Information Theory 43(6). ([`references/papers/zhangyeung1997.pdf`](references/papers/zhangyeung1997.pdf).) This is the primary reference for the M1.5 Theorem 2 proof via Kullback-Leibler divergence.
- Yeung (2008). _Information Theory and Network Coding_. Springer. [DOI: 10.1007/978-0-387-79234-7](https://doi.org/10.1007/978-0-387-79234-7). (Cross-reference for Theorem 3 and the copy lemma.)

Additional entries are listed in [`references/README.md`](references/README.md).

## AI Statement

This formalization is being completed with substantial assistance from Opus 4.6 + 4.7 and GPT 5.4, through [`claude`](https://claude.com/claude-code) and [`opencode`](https://opencode.ai), and [GitHub Copilot](https://github.com/features/copilot).

## License

Reference materials in `references/papers/` and `references/transcriptions/` are bundled for study and verification context only. They are not covered by the repository's Apache 2.0 or CC BY 4.0 grants; copyright remains with the original authors and publishers. See the per-file SPDX metadata and [the reference-material notice](./LICENSES/LicenseRef-Reference-Material.txt).

Everything else is copyright 2026 Christopher Boone. Project-authored software and configuration files are licensed under [Apache 2.0](./LICENSES/Apache-2.0.txt). Project-authored prose and mathematical exposition are licensed under [CC BY 4.0](./LICENSES/CC-BY-4.0.txt). [`CODE_OF_CONDUCT.md`](./CODE_OF_CONDUCT.md) is adapted from Contributor Covenant and licensed under [CC BY-SA 4.0](./LICENSES/CC-BY-SA-4.0.txt).
