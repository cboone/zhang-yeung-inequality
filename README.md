# zhang-yeung-inequality

A Lean 4 formalization of the Zhang-Yeung conditional information inequality, a non-Shannon-type bound on Shannon entropy that cannot be derived from the Shannon inequalities alone.

The central object is the Zhang-Yeung delta,

```text
Δ(Z, U | X, Y) := I(Z ; U) - I(Z ; U | X) - I(Z ; U | Y),
```

and the main theorem (Theorem 3 of Zhang and Yeung 1998) is the upper bound

```text
Δ(Z, U | X, Y) ≤ (1/2) · I(X ; Y) + (1/4) · (I(X ; Z,U) + I(Y ; Z,U)).
```

The proof rests on the copy lemma, which identifies the inequality as genuinely non-Shannon: no amount of Shannon-type reasoning can replace the copy construction.

## Status

| Milestone | Title                                    | State       |
| --------- | ---------------------------------------- | ----------- |
| M0        | Project scaffolding                      | done        |
| M1        | Delta equational lemmas                  | in progress |
| M1.5      | Theorem 2 (conditional warm-up)          | planned     |
| M2        | The copy lemma                           | planned     |
| M3        | Theorem 3 (main inequality)              | planned     |
| M4        | Theorem 4 (Shannon-cone separation)      | planned     |
| M5        | Theorem 5 (stretch goal)                 | planned     |
| M6        | Polish and release                       | planned     |

The full roadmap is in [`docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md`](docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md).

## Formalization Scope

- Finite-alphabet, real-valued probability distributions.
- Built on top of PFR's entropy API (`H[X]`, `I[X:Y]`, `I[X:Y|Z]`) from [teorth/pfr](https://github.com/teorth/pfr), pinned in `lakefile.toml`.
- Measurability and finite-range side conditions expressed via Mathlib's `[MeasurableSpace]`, `[Fintype]`, and `[MeasurableSingletonClass]` typeclasses.
- Deferred: infinite alphabets, computable entropy, upstream push of the copy lemma into PFR or Mathlib.

## Module Layout

- [`ZhangYeung.lean`](ZhangYeung.lean) — project entrypoint; re-exports `ZhangYeung.Prelude` and `ZhangYeung.Delta`.
- [`ZhangYeung/Prelude.lean`](ZhangYeung/Prelude.lean) — import surface for PFR's entropy API.
- [`ZhangYeung/Delta.lean`](ZhangYeung/Delta.lean) — M1 delta quantity and equational lemmas (`delta_def`, `delta_comm_cond`, `delta_comm_main`, `delta_self`, `delta_eq_entropy`, `form21_iff`, `form22_iff`, `form23_iff`, `form23_of_form21_form22`, `delta_le_mutualInfo`).
- [`ZhangYeungTest.lean`](ZhangYeungTest.lean) + [`ZhangYeungTest/Delta.lean`](ZhangYeungTest/Delta.lean) — compile-time API regression tests for the delta module.

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

- Lean 4 toolchain, pinned in [`lean-toolchain`](lean-toolchain).
- Lake (bundled with Lean).
- [PFR](https://github.com/teorth/pfr), pinned by Git revision in [`lakefile.toml`](lakefile.toml). PFR supplies the entropy API used throughout.
- Mathlib (via PFR), downloaded as prebuilt artifacts by the bootstrap script. Never built from source in CI or in a fresh worktree.

## References

Primary sources and transcriptions live in [`references/`](references/). The paper being formalized and the principal background text:

- Zhang and Yeung (1998). _On characterization of entropy function via information inequalities_. IEEE Transactions on Information Theory 44(4). ([`references/papers/zhangyeung1998.pdf`](references/papers/zhangyeung1998.pdf); verified transcription at [`references/transcriptions/zhangyeung1998.md`](references/transcriptions/zhangyeung1998.md).)
- Yeung (2008). _Information Theory and Network Coding_. Springer. (Cross-reference for Theorem 3 and the copy lemma.)

Additional entries are listed in [`references/README.md`](references/README.md).

## AI Assistance

This project was developed with substantial assistance from Claude (Anthropic). Claude contributed to proof development, code structure, and documentation throughout the formalization effort.

## License

MIT. See [`LICENSE`](LICENSE).
