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
| M1.5      | Theorem 2 (conditional warm-up)          | in progress |
| M2        | The copy lemma                           | planned     |
| M3        | Theorem 3 (main inequality)              | planned     |
| M4        | Theorem 4 (Shannon-cone separation)      | planned     |
| M5        | Theorem 5 (stretch goal)                 | planned     |
| M6        | Polish and release                       | planned     |

M1.5 is in progress: the public `ZhangYeung.theorem2` statement is wired, the Shannon-algebra reduction to `Δ(Z, U | X, Y) ≤ 0` under the hypotheses `I[X:Y] = I[X:Y|Z] = 0` is proved without `sorry`, and the API regression tests for the theorem land. The one remaining obligation is the non-Shannon core `theorem2_delta_le_zero`, which by the [@zhangyeung1997] argument follows from `Real.sum_mul_log_div_leq` applied to the auxiliary `p̃` and `p̂` distributions described in that helper's docstring. Closing it requires formalizing the full 4-tuple joint-PMF algebra; downstream milestones may assume the public theorem holds.

The full roadmap is in [`docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md`](docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md).

## Formalization Scope

- Finite-alphabet, real-valued probability distributions.
- Built on top of PFR's entropy API (`H[X]`, `I[X:Y]`, `I[X:Y|Z]`) from [teorth/pfr](https://github.com/teorth/pfr), pinned in `lakefile.toml`.
- Measurability and finite-range side conditions expressed via [Mathlib](https://github.com/leanprover-community/mathlib4)'s [`[MeasurableSpace]`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Defs.html#MeasurableSpace), [`[Fintype]`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Fintype/Defs.html#Fintype), and [`[MeasurableSingletonClass]`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Defs.html#MeasurableSingletonClass) typeclasses.
- Deferred: infinite alphabets, computable entropy, upstream push of the copy lemma into PFR or Mathlib.

## Module Layout

- [`ZhangYeung.lean`](ZhangYeung.lean) — project entrypoint; re-exports `ZhangYeung.Prelude`, `ZhangYeung.Delta`, and `ZhangYeung.Theorem2`.
- [`ZhangYeung/Prelude.lean`](ZhangYeung/Prelude.lean) — import surface for PFR's entropy API.
- [`ZhangYeung/Delta.lean`](ZhangYeung/Delta.lean) — M1 delta quantity and equational lemmas (`delta_def`, `delta_comm_cond`, `delta_comm_main`, `delta_self`, `delta_eq_entropy`, `form21_iff`, `form22_iff`, `form23_iff`, `form23_of_form21_form22`, `delta_le_mutualInfo`).
- [`ZhangYeung/Theorem2.lean`](ZhangYeung/Theorem2.lean) — M1.5 Zhang-Yeung conditional information inequality (`theorem2`), factored into a Shannon-algebra reduction (complete) and a non-Shannon KL-divergence core (one localized `sorry`).
- [`ZhangYeungTest.lean`](ZhangYeungTest.lean) + [`ZhangYeungTest/Delta.lean`](ZhangYeungTest/Delta.lean) + [`ZhangYeungTest/Theorem2.lean`](ZhangYeungTest/Theorem2.lean) — compile-time API regression tests for each module.

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
- Zhang and Yeung (1997). _A non-Shannon-type conditional inequality of information quantities_. IEEE Transactions on Information Theory 43(6). ([`references/papers/zhangyeung1997.pdf`](references/papers/zhangyeung1997.pdf).) This is the primary reference for the M1.5 Theorem 2 proof via Kullback-Leibler divergence.
- Yeung (2008). _Information Theory and Network Coding_. Springer. [DOI: 10.1007/978-0-387-79234-7](https://doi.org/10.1007/978-0-387-79234-7). (Cross-reference for Theorem 3 and the copy lemma.)

Additional entries are listed in [`references/README.md`](references/README.md).

## AI Statement

This formalization is being completed with substantial assistance from Opus 4.6 + 4.7 and GPT 5.4, through [`claude`](https://claude.com/claude-code) and [`opencode`](https://opencode.ai), and [GitHub Copilot](https://github.com/features/copilot).

## License

MIT. See [`LICENSE`](LICENSE).
