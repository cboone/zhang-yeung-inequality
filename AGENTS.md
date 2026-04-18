# AGENTS.md

This file provides guidance to AI coding agents when working with code in this repository.

## Project Overview

A Lean 4 formalization of the Zhang-Yeung conditional information inequality for Shannon entropy. Depends on PFR (teorth/pfr) for Shannon entropy definitions (H[X], I[X:Y], I[X:Y|Z]).

## Build Commands

```bash
bin/bootstrap-worktree            # mandatory first-time setup (lake update + cache + build)
make bootstrap                    # same as bin/bootstrap-worktree
lake build ZhangYeung             # build the ZhangYeung library
lake build ZhangYeung.Prelude     # build a single module
lake test                         # run the ZhangYeungTest example suite
lake lint                         # run batteries/runLinter over the ZhangYeung library
make build                        # lake build ZhangYeung (guards against missing Mathlib cache)
make test                         # lake test
make lean-lint                    # lake lint
make lint                         # markdownlint-cli2 + cspell
make check                        # lint + lean-lint + build + test
```

Full local check: `make check` (or `lake build ZhangYeung && lake lint && lake test`).

## Fresh Clone / Worktree Bootstrap

In a fresh clone or worktree, run:

```bash
bin/bootstrap-worktree
```

This is mandatory in every fresh clone or worktree. The script runs `lake update`, `lake exe cache get`, verifies that Mathlib's prebuilt artifacts exist, and only then runs `lake build ZhangYeung`. Never bootstrap by running `lake build` directly in a clean worktree or clone. Mathlib must always come from downloaded prebuilt artifacts, not a local source compilation.

The `make build` target also guards against this: it checks for Mathlib artifacts and refuses to proceed if they are missing, directing you to run `make bootstrap` or `bin/bootstrap-worktree` first.

## Module Layout

- `ZhangYeung.lean`: project entrypoint (re-exports `ZhangYeung.CopyLemma`, `ZhangYeung.Delta`, `ZhangYeung.Prelude`, and `ZhangYeung.Theorem2`)
- `ZhangYeung/Prelude.lean`: import surface for PFR's entropy API
- `ZhangYeung/Delta.lean`: M1 delta quantity and equational lemmas
- `ZhangYeung/Theorem2.lean`: M1.5 Zhang-Yeung conditional information inequality (Theorem 2 of the 1998 paper, via a KL-divergence argument on auxiliary `p̃`/`p̂` PMFs)
- `ZhangYeung/CopyLemma.lean`: M2 Zhang-Yeung copy lemma (§III eqs. 44-45 of the 1998 paper) -- `copyLemma` existential, abstract Lemma 2 `delta_of_condMI_vanishes_eq`, and the six copy-projection corollaries (two transports, two identities, two inequalities)
- `ZhangYeungTest.lean`: top-level re-export for Lean API tests
- `ZhangYeungTest/Delta.lean`: compile-time API regression tests for the delta module
- `ZhangYeungTest/Theorem2.lean`: compile-time API regression tests for the Theorem 2 module
- `ZhangYeungTest/CopyLemma.lean`: compile-time API regression tests for the copy lemma module

## Namespace Convention

Flat under `ZhangYeung` for now. New files go under `ZhangYeung/` as the project grows.

## Top-Level Namespace

`ZhangYeung`

## Lean Conventions

- Tab size: 2 spaces (no hard tabs)
- Unicode: standard Lean 4 unicode symbols
- `autoImplicit = false`, `relaxedAutoImplicit = false` (matching PFR's strictness)
- Final newline in all files; trim trailing whitespace
- Follow existing proof style in this repo

### Skill and Workflow

Invoke the `write-lean-code` skill before any Lean edit, read-for-review, or planning discussion. The skill carries generic Lean/Mathlib guidance; user-level overrides (no line-length limit, no hardwrapping in comments or docstrings) are documented in `~/.claude/CLAUDE.md`. This file (`AGENTS.md`, symlinked as `CLAUDE.md`) is authoritative for zhang-yeung-inequality-specific facts: bootstrap script, build targets, module layout, namespace conventions.

### Testing Discipline

Every public module added in `ZhangYeung/` must land with a matching module under `ZhangYeungTest/` that imports only the public surface and proves API-level `example`s against it. `lake test` must continue to pass; the `testDriver` is `ZhangYeungTest`, and `defaultTargets = ["ZhangYeung"]` so `lake build` and `lake test` stay semantically distinct. When renaming or removing public definitions, update the corresponding test module in the same change.

## Vendored Lean Dependencies

Exclude from style searches: PFR, APAP, checkdecls, batteries (everything under `.lake/packages/`). Valid style references: (1) this project's own code under `ZhangYeung/`, (2) Mathlib under `.lake/packages/mathlib/`.

## Lean Toolchain

See `lean-toolchain` (currently v4.28.0-rc1, matching PFR's Mathlib dependency).

## CI

Two workflows under `.github/workflows/`:

- `ci.yml`: Lean job (build + lint + test via `leanprover/lean-action@v1` plus a dedicated `lake test` step). `paths-ignore` keeps it from running on docs-only changes.
- `text-lint.yml`: markdown + cspell via `cboone/gh-actions/.github/workflows/text-lint.yml`. Runs on every push/PR.

## Key Files

- `lakefile.toml` — Lake project config (library names, Mathlib/PFR dependency, `testDriver`).
- `lean-toolchain` — pinned Lean version.
- `Makefile` — build, lint, test, and check targets.
- `bin/bootstrap-worktree` — zsh bootstrap script.
- `.github/copilot-instructions.md` — general GitHub Copilot PR-review guidance.
- `.github/lean.instructions.md` — Copilot PR-review rules scoped to `**/*.lean` (entrypoint manifest pattern, no line-length limit, single-line comment paragraphs, vendored-deps exclusion).
- `references/papers/zhangyeung1998.pdf` and `references/transcriptions/zhangyeung1998.md` — primary source.
