# CLAUDE.md

This file provides guidance to AI coding agents when working with code in this repository.

## Project Overview

A Lean 4 formalization of the Zhang-Yeung conditional information inequality for Shannon entropy. Depends on PFR (teorth/pfr) for Shannon entropy definitions (H[X], I[X:Y], I[X:Y|Z]).

## Build Commands

```bash
bin/bootstrap-worktree            # mandatory first-time setup (lake update + cache + build)
lake build ZhangYeung             # build the ZhangYeung library
lake build ZhangYeung.Prelude     # build a single module
lake lint                         # run batteries/runLinter over the ZhangYeung library
```

Full local check: `lake build ZhangYeung && lake lint`

## Fresh Clone / Worktree Bootstrap

In a fresh clone or worktree, run:

```bash
bin/bootstrap-worktree
```

This is mandatory in every fresh clone or worktree. The script runs `lake update`, `lake exe cache get`, verifies that Mathlib's prebuilt artifacts exist, and only then runs `lake build ZhangYeung`. Never bootstrap by running `lake build` directly in a clean worktree or clone. Mathlib must always come from downloaded prebuilt artifacts, not a local source compilation.

## Module Layout

- `ZhangYeung.lean`: project entrypoint (re-exports `ZhangYeung.Prelude`)
- `ZhangYeung/Prelude.lean`: import surface for PFR's entropy API

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

Invoke the `write-lean-code` skill before any Lean edit, read-for-review, or planning discussion. The skill carries generic Lean/Mathlib guidance; user-level overrides (no line-length limit, no hardwrapping in comments or docstrings) are documented in `~/.claude/CLAUDE.md`. This file is authoritative for zhang-yeung-inequality-specific facts: bootstrap script, build targets, module layout, namespace conventions.

## Vendored Lean Dependencies

Exclude from style searches: PFR, APAP, checkdecls, batteries (everything under `.lake/packages/`). Valid style references: (1) this project's own code under `ZhangYeung/`, (2) Mathlib under `.lake/packages/mathlib/`.

## Lean Toolchain

See `lean-toolchain` (currently v4.28.0-rc1, matching PFR's Mathlib dependency).

## CI

`.github/workflows/ci.yml` runs a Lean job (build + lint via `leanprover/lean-action@v1`).
