# CI performance improvements

## Context

PR #1's first CI run took 5m31s; the second took ~3 min thanks to `lean-action@v1`'s built-in cache restore-key. The remaining wall-clock cost has identifiable layers we can shave, plus our workflow contains a duplicate lint step. This plan is a separate scope from any milestone in the formalization roadmap and only touches `.github/workflows/ci.yml` (and possibly an additional `actions/cache@v4` step).

## Investigation findings (already complete)

- `leanprover/lean-action@v1` already wraps `actions/cache/restore@v4` and `actions/cache/save@v4` around its build step; cache key includes `runner.os`, `runner.arch`, `hashFiles('lean-toolchain')`, `hashFiles('lake-manifest.json')`, and `github.sha`. Restore-keys fall back to the (`lean-toolchain` + `lake-manifest.json`) prefix so every commit on an unchanged manifest restores the previous build's `.lake/`.
- `lean-action`'s auto-config detects our `lintDriver = "batteries/runLinter"` setting and runs `lake lint` automatically. Our explicit `Lean lint` step in `ci.yml` is therefore redundant; cold-run logs show it ran and added a few seconds on top of the action's own `Lake Lint` step.
- elan is reinstalled from scratch on every run (no cache for `~/.elan`).
- `lake exe cache get` runs unconditionally inside `lean-action`, even when `.lake/packages/mathlib` was already restored from cache. With a warm cache it's a fast revalidation, not a full download.

## Steps

### 1. Drop the redundant `Lean lint` step

Remove the trailing `- name: Lean lint / run: lake lint` step in `ci.yml`. `lean-action@v1` already runs `lake lint` because our lakefile declares `lintDriver = "batteries/runLinter"`. Verify by reading `lean-action`'s `Lake Lint Output` group in the next CI run.

### 2. Cache `~/.elan` separately

Add an `actions/cache@v4` step before `leanprover/lean-action@v1` that caches `~/.elan` keyed on `hashFiles('lean-toolchain')`. This skips the elan toolchain download and install on warm runs, which is one of the largest fixed costs that `lean-action`'s built-in cache doesn't cover (the action only caches `.lake/`).

### 3. Skip CI on docs-only changes

Add `paths-ignore` to the workflow's `pull_request` and `push` triggers so PRs that touch only `docs/**`, `*.md`, `LICENSE`, or `.gitignore` don't run the full Lean build. PRs that mix doc and code changes still trigger CI. This addresses the case where roadmap or research notes get updated without affecting Lean code.

### 4. Pin `leanprover/lean-action@v1` to a commit SHA

Replace `uses: leanprover/lean-action@v1` with a SHA pin (currently `c544e89643240c6b398f14a431bcdc6309e36b3e`, observed from PR #1's logs) plus a `# v1` comment. This is supply-chain hardening rather than a performance change, but it fits naturally into a workflow edit and matches GitHub's recommended practice for third-party actions.

### 5. Measure before and after

Capture the `Run leanprover/lean-action@v1` step duration and total job duration from at least two runs after each change (one cold, one warm). For cold-run measurement, bump a dependency in `lake-manifest.json` (or a one-off whitespace bump on `lean-toolchain`) on a throwaway branch to force a cache miss. Record the numbers in this plan or in a follow-up note before moving the plan to `done/`.

## Explicitly out of scope

- **Splitting build and lint into parallel jobs.** Would improve wall-clock on multi-core runners but adds workflow complexity and a cache hand-off. Not worth it for a project of this size.
- **Replacing `lean-action` with hand-rolled Lake commands.** Would let us skip `lake exe cache get` on cache hits but loses the action's maintenance benefits and ergonomic auto-config.
- **Self-hosted runners.** Outside the scope of a free-tier project setup.
- **Pruning `runLinter`'s module set.** Possible to scope `lake lint` to a smaller module list, but reduces lint coverage and conflicts with the M0 promise of full-project linting.

## Deliverables

- Updated `.github/workflows/ci.yml` reflecting steps 1-4.
- Recorded before/after timings for cold and warm runs in this plan or PR description.
- Plan file moved to `docs/plans/done/` after the measurements land.
