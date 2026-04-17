# 2026-04-16 Bootstrap Repo

## Context

The repository is a Lean 4 formalization project (Zhang-Yeung inequality) built with Lake and depending on PFR. Core project scaffolding from prior work is already in place: `LICENSE`, `README.md` (stub), `CLAUDE.md`, `.gitignore`, Lean CI (`.github/workflows/ci.yml`), `.markdownlint-cli2.jsonc`, `cspell.jsonc`/`cspell-words.txt`, VS Code settings, `bin/bootstrap-worktree`, and `docs/plans/{todo,done}/`.

The sibling Lean project at `~/Development/shannon-entropy` is the template this bootstrap follows: same bootstrap script pattern, parallel CI (Lean + text-lint), `Makefile` with a `make check` pipeline, and `AGENTS.md` (symlinked as `CLAUDE.md`). Zhang-yeung already has the bootstrap script but lacks the other pieces.

**Test-harness readiness.** The `formalize/delta-equational-lemmas` branch has been rebased into this bootstrap branch, so `ZhangYeung/Delta.lean`, `ZhangYeungTest/Delta.lean`, and the test-library stanza in `lakefile.toml` are all present locally. Current `lakefile.toml` holds `defaultTargets = ["ZhangYeung", "ZhangYeungTest"]` with no `testDriver`. Per the decision below, this plan **flips that config** to `testDriver = "ZhangYeungTest"` + `defaultTargets = ["ZhangYeung"]` directly on this bootstrap branch (shannon-entropy's convention), so the Makefile, CI, and lakefile land together and `make check` passes on first try.

In-scope gaps:

- **Agent-config spokes:** `AGENTS.md` (from rename of current `CLAUDE.md`), `CLAUDE.md` symlink, `.github/copilot-instructions.md`.
- **Makefile:** local parity with shannon-entropy so `make lint`, `make lean-lint`, `make check` work.
- **CI markdown + cspell workflow:** shannon-entropy uses a parallel `markdown` job in the same `ci.yml` via `cboone/gh-actions/.github/workflows/text-lint.yml`; zhang-yeung currently skips cspell/markdownlint in CI entirely. Adding a new workflow file `.github/workflows/text-lint.yml` (no `paths-ignore`) keeps the existing `ci.yml` and its `paths-ignore` untouched while ensuring markdown/doc-only changes still get linted.
- **Cross-language editor config:** `.editorconfig`.
- **Community files:** `CONTRIBUTING.md`, `CODE_OF_CONDUCT.md`, `.github/SECURITY.md`, `.github/PULL_REQUEST_TEMPLATE.md`.
- **`README.md` expansion:** current file is a one-line stub; replace with a project-specific README modeled on shannon-entropy's, scaled to the project's current M0/M1 milestone state.

Explicitly deferred: `CHANGELOG.md`, `.claude/settings.json`, secret scanning, actionlint, yamllint, Prettier.

This plan runs the `bootstrap-project` workflow against that current state: skip what is done or deferred, run the chosen gaps, and leave Lean-specific build configuration untouched.

## Project Type

Lean 4 project (non-CLI, non-Go, non-Rust, non-JS, non-Python). The `bootstrap-project` overlap table does not include Lean directly; for execution we treat it as a "Generic / non-CLI" project: skip all Go/Rust CLI scaffolders, keep all universally-applicable pieces.

## Assessment Summary

| Tool | Status | What it does |
| --- | --- | --- |
| _New:_ Flip `lakefile.toml` | Will run | Change to `testDriver = "ZhangYeungTest"` + `defaultTargets = ["ZhangYeung"]` so `lake test` runs the test library |
| `scaffold-new-repo` | Scoped down | Only add `AGENTS.md` (from rename) + `.github/copilot-instructions.md`; skip `CHANGELOG.md` and `.claude/settings.json` |
| `scaffold-go-cli` / `scaffold-go-library` / `scaffold-rust-cli` | Not applicable | Lean project |
| `setup-ci` | Extended | Lean `ci.yml` unchanged; add new `text-lint.yml` workflow that calls `cboone/gh-actions/.github/workflows/text-lint.yml` (no paths-ignore) |
| `setup-linters` | Scoped down | Keep markdownlint-cli2 + cspell; add `.editorconfig` only |
| `setup-secret-scanning` | Skipped by user | Deferred to a later pass |
| `add-goreleaser-homebrew` | Not applicable | Not a Go CLI |
| `add-community-files` | Will run | `CONTRIBUTING.md`, `CODE_OF_CONDUCT.md`, `.github/SECURITY.md`, `.github/PULL_REQUEST_TEMPLATE.md` |
| `setup-installers` | Not applicable | No distributable binary |
| `add-scrut-cli-tests` | Not applicable | Not a CLI |
| _New:_ Add `Makefile` | Will run | Mirror shannon-entropy's Makefile (build, bootstrap, lint, lean-lint, test, check, clean, help) under the testDriver pattern. |
| _New:_ Expand `README.md` | Will run | Replace the one-line stub with a project-specific README modeled on shannon-entropy's, scaled to zhang-yeung's early-milestone state. |

## Confirmed Decisions

- **`CLAUDE.md` hub-and-spoke:** adopt hub-and-spoke. Rename existing `CLAUDE.md` to `AGENTS.md` preserving contents verbatim, then create a symlink `CLAUDE.md -> AGENTS.md` via `ln -sfn AGENTS.md CLAUDE.md`. Future edits land in one file consumed by both Claude Code and Codex.
- **Cross-language linters to add:** `.editorconfig` only. Defer `actionlint`, `yamllint`, and `Prettier`.
- **Skip `.claude/settings.json`.** Can be added later if team-shared Claude permissions become useful.
- **Skip `CHANGELOG.md`.** Add on first tagged release.
- **Skip `setup-secret-scanning` (gitleaks + TruffleHog).** Defer to a later pass.
- **Community contact addresses:**
  - `CODE_OF_CONDUCT.md` enforcement contact: `conduct@snappy.sh`
  - `.github/SECURITY.md` reporting: GitHub private vulnerability reporting only, no email fallback.
  - `CONTRIBUTING.md` general contact (if the template requires one): `contact@snappy.sh`
- **CI job name:** keep existing `Build and lint (Lean)`. Do not rename to `Lean` for parity with shannon-entropy.
- **Test wiring: adopt `testDriver` pattern** (shannon-entropy's convention), edit in this branch:
  - `lakefile.toml` changes to `testDriver = "ZhangYeungTest"` and `defaultTargets = ["ZhangYeung"]` (from `["ZhangYeung", "ZhangYeungTest"]`).
  - Makefile gets a `test` target wrapping `lake test`, and `check` includes it.
  - `.github/workflows/ci.yml` adds a `lake test` step after the `leanprover/lean-action` build step.
  - Lakefile flip lands as its own commit at the start of the sequence so later commits can rely on `lake test` already working.

## Execution Order and Scope

Run each step only for the gaps listed. Nothing else.

### 0. Flip `lakefile.toml` to the `testDriver` pattern

Edit `lakefile.toml` in place:

- Change `defaultTargets = ["ZhangYeung", "ZhangYeungTest"]` to `defaultTargets = ["ZhangYeung"]`.
- Add `testDriver = "ZhangYeungTest"` after `lintDriver`.

Result (illustrative):

```toml
name = "ZhangYeung"
version = "0.1.0"
defaultTargets = ["ZhangYeung"]
lintDriver = "batteries/runLinter"
testDriver = "ZhangYeungTest"

[leanOptions]
autoImplicit = false
relaxedAutoImplicit = false

[[require]]
name = "PFR"
git = "https://github.com/teorth/pfr"
rev = "80daaf1"

[[lean_lib]]
name = "ZhangYeung"

[[lean_lib]]
name = "ZhangYeungTest"
```

No Lean source changes: the `[[lean_lib]]` stanza for `ZhangYeungTest` already exists. Verify by running `lake test` after the edit; it should compile the `ZhangYeungTest` library and succeed.

This step lands first so every subsequent step (Makefile, CI) can assume `lake test` works.

### 1. `scaffold-new-repo` (scoped down to agent config)

- **File: `AGENTS.md`** — created by renaming existing `CLAUDE.md`. Preserve contents verbatim so project conventions and build commands survive.
- **File: `CLAUDE.md`** — replace with symlink to `AGENTS.md` via `ln -sfn AGENTS.md CLAUDE.md`.
- **File: `.github/copilot-instructions.md`** — template cross-referencing `AGENTS.md`; replace heading with `zhang-yeung-inequality`. Use shannon-entropy's version as the template (`~/Development/shannon-entropy/.github/copilot-instructions.md`): short, points to `AGENTS.md`, includes the "done plans are historical records" note to prevent drift-flagging.
- **Follow-up edit to `AGENTS.md`:** update the "Skill and Workflow" section wording to match shannon-entropy's pattern: "This file (`AGENTS.md`, symlinked as `CLAUDE.md`) is authoritative for zhang-yeung-inequality-specific facts..." — mirrors shannon-entropy's line at `AGENTS.md:81`. Also add a `Makefile` line to the Key Files list after step 3 lands.
- **Skipped:** `.claude/settings.json`, `CHANGELOG.md`, and the scaffolder's LICENSE / README / .gitignore / docs/plans bootstrap (already present).

Reference implementation: `/Users/ctm/.claude/plugins/cache/cboone-cc-plugins/scaffold-new-repo/1.7.0/commands/scaffold-new-repo.md` step 9 (sub-items for AGENTS.md, CLAUDE.md symlink, and copilot-instructions.md only).

### 2. `setup-linters` (cross-language only)

- **Skip:** markdownlint-cli2 (configured: `.markdownlint-cli2.jsonc`), cspell (configured: `cspell.jsonc`, `cspell-words.txt`), Lean tooling (handled by Lake / CI).
- **Add:**
  - `.editorconfig` — universal indent/newline rules aligned with repo style: `charset = utf-8`, `end_of_line = lf`, `insert_final_newline = true`, `trim_trailing_whitespace = true`, `indent_style = space`, `indent_size = 2` applied to Lean, YAML, Markdown, JSON(C), TOML. Makefile override: `indent_style = tab` (Make requires tabs).
- **Deferred:** `actionlint`, `yamllint`, `Prettier`, Taplo.

Reference: `/Users/ctm/.claude/plugins/cache/cboone-cc-plugins/setup-linters/1.9.0/skills/setup-linters/SKILL.md`.

### 3. Add `Makefile`

Model after `~/Development/shannon-entropy/Makefile`, adapted for zhang-yeung:

- **Targets:**
  - `build` — `lake build ZhangYeung`, guarded by `_check-mathlib-cache`. Scoped to the library, not defaults, matching shannon-entropy's semantic split between "build library" and "run tests".
  - `bootstrap` — `bin/bootstrap-worktree`.
  - `lean-lint` — `lake lint`, guarded by `_check-mathlib-cache`.
  - `test` — `lake test`, guarded by `_check-mathlib-cache`.
  - `lint-markdown` — `markdownlint-cli2 "**/*.md"`.
  - `lint-spelling` — `cspell --no-progress .`.
  - `lint` — depends on `lint-markdown` + `lint-spelling`.
  - `check` — depends on `lint` + `lean-lint` + `build` + `test`.
  - `clean` — `lake clean`.
  - `help` — auto-extract `##` docstrings, identical pattern to shannon-entropy.
- **Divergence from shannon-entropy's Makefile:**
  - Drop shannon-entropy's `build-all` target unless we identify a concrete reason to build beyond the library. shannon-entropy's `build-all` exists for that project's multi-component build; zhang-yeung doesn't currently need a variant.
- **Guard:** `_check-mathlib-cache` private target that verifies `.lake/packages/mathlib/.lake/build/lib/lean/Mathlib*.olean` exists and errors with a directive to run `make bootstrap` otherwise. Copy verbatim from shannon-entropy.
- **`.PHONY` list** covers all targets.
- **Reference to include in `AGENTS.md`:** after the Makefile lands, update the build-commands block in `AGENTS.md` to list the new `make` targets (mirroring shannon-entropy's block), and add `Makefile` under a Key Files section.

### 4. Add a markdown + cspell CI workflow (split from the Lean workflow)

Two workflow files under `.github/workflows/`:

- **`ci.yml` (existing): one step added.** Keep the current `paths-ignore` (`docs/**`, `**/*.md`, `LICENSE`, `.gitignore`), the elan cache step, the SHA-pinned `leanprover/lean-action`, and the job `name: Build and lint (Lean)`. Add a new step `- run: lake test` immediately after the `leanprover/lean-action` step. Rationale: under the `testDriver` pattern, `lake build` does not exercise the test library; `lake test` is required. The step is cheap (tests are compile-time `example`-based) and adds the independent signal the `testDriver` choice exists to provide.
- **`text-lint.yml` (new).** Triggers on all push/PR (no `paths-ignore`), invokes the same reusable workflow shannon-entropy uses. Template:

    ```yaml
    name: Text Lint

    on:
      push:
        branches: [main]
      pull_request:
      workflow_dispatch:

    jobs:
      markdown:
        name: Lint (Markdown and spelling)
        uses: cboone/gh-actions/.github/workflows/text-lint.yml@37896a7915c49270272a637ade714f2fea82655f  # v2.1.3
        with:
          run-cspell: true
          run-prettier: false
    ```

Naming rationale: keep `ci.yml` as-is to avoid disturbing any branch-protection required-check entries referencing `CI / Build and lint (Lean)`. The new workflow's identity is `Text Lint / Lint (Markdown and spelling)`.

Branch-protection note: after this lands, add `Text Lint / Lint (Markdown and spelling)` to the required-checks list for `main` (user action, not plan scope).

Reference: `~/Development/shannon-entropy/.github/workflows/ci.yml` (single-file version with both jobs).

### 5. `add-community-files`

- **File: `CONTRIBUTING.md`** — contribution guide modeled on `~/Development/shannon-entropy/CONTRIBUTING.md`. Lean-specific setup:
  - Requirements: Lean 4 toolchain, Lake, `markdownlint-cli2`, `cspell`.
  - Getting started: `bin/bootstrap-worktree`, `make lint`, `make check`.
  - Code Style: run `make lint` before committing; add domain-specific terms to `cspell-words.txt`.
  - Conventional Commits section (copied from shannon-entropy).
  - Pull request process with make-check gate.
  - General contact `contact@snappy.sh` if the template requires one.
- **File: `CODE_OF_CONDUCT.md`** — Contributor Covenant v3.0 verbatim from `~/Development/shannon-entropy/CODE_OF_CONDUCT.md` (which already uses `conduct@snappy.sh`). Confirm the reporting contact remains `conduct@snappy.sh`.
- **File: `.github/SECURITY.md`** — use `~/Development/shannon-entropy/.github/SECURITY.md` verbatim. Points to GitHub's private vulnerability reporting flow only; no email fallback, no `contact@snappy.sh` substitution.
- **File: `.github/PULL_REQUEST_TEMPLATE.md`** — use `~/Development/shannon-entropy/.github/PULL_REQUEST_TEMPLATE.md` verbatim but drop the `CHANGELOG` checklist item (we're skipping `CHANGELOG.md` until first release).

Reference: `/Users/ctm/.claude/plugins/cache/cboone-cc-plugins/add-community-files/1.0.0/skills/add-community-files/SKILL.md`.

### 6. Expand `README.md`

Current state: a one-line stub (`# zhang-yeung-inequality`). Replace with a project-specific README modeled on `~/Development/shannon-entropy/README.md`, scaled to zhang-yeung's current milestone state (M0 complete, M1 landing on the delta branch; M2-M6 still to come).

Sections, in order:

1. **Title (`# zhang-yeung-inequality`)** with a one-sentence subtitle pulled from `AGENTS.md` "Project Overview".
2. **Context note:** short paragraph explaining the paper being formalized (Zhang and Yeung, 1998) and the role of the non-Shannon conditional information inequality. Cite the paper and the Yeung 2008 textbook reference from `references/papers/`.
3. **Status.** Enumerate the milestones (M0-M6) from `docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md` with a state marker per row (`done` / `in progress` / `planned`). This section is intentionally short and will need updates as milestones land.
4. **Formalization Scope.** Brief bullets: finite-alphabet setting, reliance on PFR's entropy API (`H[·]`, `I[·:·]`, `I[·:·|·]`), deferred topics. Pulled from the roadmap.
5. **Module Layout.** Reflect the current state:
    - `ZhangYeung.lean` -- project entrypoint.
    - `ZhangYeung/Prelude.lean` -- import surface for PFR entropy API.
    - `ZhangYeung/Delta.lean` -- M1 delta quantity and equational lemmas.
    - `ZhangYeungTest/Delta.lean` -- M1 API regression tests (compile-time `example` checks).
6. **Build and Verify.** Concrete commands:
    - `bin/bootstrap-worktree` (mandatory first-time)
    - `make build` / `make lean-lint` / `make lint` / `make check`
    - Link to `AGENTS.md` / `CONTRIBUTING.md` for the full command reference.
7. **References.** Point to `references/` (README covering papers, transcriptions, textbook) and explicitly list:
    - Zhang and Yeung (1998), "On characterization of entropy function via information inequalities" — paper text in `references/papers/`.
    - Yeung (2008), _Information Theory and Network Coding_ — textbook reference for background.
8. **Dependencies.** Short list: Lean 4 toolchain (per `lean-toolchain`), Lake, PFR (`teorth/pfr`) pinned in `lakefile.toml`.
9. **AI Assistance.** Single paragraph matching shannon-entropy's wording: "This project was developed with substantial assistance from Claude (Anthropic). Claude contributed to proof development, code structure, and documentation throughout the formalization effort."
10. **License.** One sentence pointing to `LICENSE` with the MIT summary. No copyright duplication.

Sections deliberately omitted (compared to shannon-entropy):

- No "Main Theorems" section — no theorems landed yet. Add once M1-M3 stabilize.
- No "How To Read The Proof" section — reading order requires at least M1-M3 landed.
- No "Notes on Axioms" section — specific to shannon-entropy's axiomatization; zhang-yeung works inside PFR's entropy API and does not introduce axioms.

Reference material during write: `AGENTS.md` for project conventions; `docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md` for milestone phrasing; `references/README.md` for paper list; `~/Development/shannon-entropy/README.md` for structural template.

This step executes LAST in the plan because it depends on `AGENTS.md` being renamed (step 1) and the Makefile target list being finalized (step 3).

## Files To Be Created

```text
lakefile.toml                            (modified: testDriver pattern)
AGENTS.md                                (new, via rename of CLAUDE.md; then edited for Makefile refs)
CLAUDE.md                                (converted to symlink -> AGENTS.md)
.editorconfig                            (new)
.github/copilot-instructions.md          (new)
Makefile                                 (new)
.github/workflows/ci.yml                 (modified: add lake test step)
.github/workflows/text-lint.yml          (new)
CONTRIBUTING.md                          (new)
CODE_OF_CONDUCT.md                       (new)
.github/SECURITY.md                      (new)
.github/PULL_REQUEST_TEMPLATE.md         (new)
README.md                                (rewritten from stub to full project README)
```

Not touched: `LICENSE`, `.gitignore`, `.markdownlint-cli2.jsonc`, `cspell.jsonc`, `cspell-words.txt`, `.vscode/*`, `bin/bootstrap-worktree`, `lean-toolchain`, `lake-manifest.json`, `ZhangYeung*` (source), `ZhangYeungTest*` (source), `references/`, `docs/*`.

## Commit Strategy

Per repo convention (frequent small commits at each logical boundary, Conventional Commits, GPG-signed outside the sandbox). One commit per tool step:

1. `build: flip lakefile to testDriver pattern for ZhangYeungTest`
2. `chore: adopt AGENTS.md hub-and-spoke and add Copilot instructions`
3. `chore: add .editorconfig`
4. `build: add Makefile with build, lint, test, and check targets`
5. `ci: add text-lint workflow and lake test step`
6. `docs: add community files (contributing, code of conduct, security, PR template)`
7. `docs: expand README with project overview, status, and build instructions`

Commit 5 groups both CI edits (new `text-lint.yml` + `lake test` step in existing `ci.yml`) under one logical change since both touch CI.

All commits should be created outside the sandbox with `git commit -S` (or `gcsm`).

## Verification

After each step, and end-to-end at the close:

- After step 0: `lake test` — builds and passes (compile-time `example`-based ZhangYeungTest).
- After step 1: `ls AGENTS.md CLAUDE.md && readlink CLAUDE.md` prints `AGENTS.md`; `diff <(cat AGENTS.md) <(cat CLAUDE.md)` shows identical content.
- After step 4: `make help` lists every target with its docstring; `make lint` passes.
- End-to-end: `make check` — full pipeline (lint + lean-lint + build + test) passes.
- `git status` — working tree clean after each commit.
- Push branch and observe CI: `CI / Build and lint (Lean)` runs on code changes and now includes `lake test`; new `Text Lint / Lint (Markdown and spelling)` runs on every push/PR including docs-only ones. Confirm the Lean workflow is still skipped on docs-only changes per the retained `paths-ignore`.
- Open a test PR to verify `.github/PULL_REQUEST_TEMPLATE.md` renders.
- Render `README.md` in a browser (via `gh pr view --web` or GitHub's preview) and confirm all links resolve: `AGENTS.md`, `CONTRIBUTING.md`, `references/`, `docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md`.

## Post-Bootstrap Next Steps

- `/lint-and-fix` to sweep any initial lint issues surfaced by the new `.editorconfig`, Makefile-triggered lint, or CI markdown job.
- After M2+ milestones land, revisit `README.md` to add a "Main Theorems" section with file references, and update Module Layout as new modules arrive.
- When ready, run `/setup-secret-scanning` for gitleaks + TruffleHog workflows.
- When ready, add `actionlint` (and optionally `yamllint`) to validate `.github/workflows/`.
- When ready, add `.claude/settings.json` for team-shared Claude Code permissions.
- On first tagged release, generate `CHANGELOG.md`, re-add the `CHANGELOG` PR template checkbox, and consider a `release.yml` workflow.
