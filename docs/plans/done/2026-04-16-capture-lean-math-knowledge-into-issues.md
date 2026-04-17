# 2026-04-16 Capture Lean + math knowledge into issues

## Context

This session bootstrapped `zhang-yeung-inequality` to parity with the sibling Lean formalization project `shannon-entropy` and ~parity with the larger multi-component `strength-model` project. Along the way we surfaced a batch of Lean-specific and math-specific conventions that are currently duplicated across those three repos (or baked into shannon-entropy alone and copied by hand). This plan turns that knowledge into GitHub issues against `cboone/cboone-cc-plugins` (skills) and `cboone/gh-actions` (reusable workflows).

Goal: one issue per knowledge chunk, each targeted at an existing skill/workflow (extension) or a new one (creation), sized so a future session can address issues one at a time.

## Source review

- **zhang-yeung-inequality (this repo, post-bootstrap).** Lean 4 + PFR, uses `testDriver = "ZhangYeungTest"` + `defaultTargets = ["ZhangYeung"]`, Makefile with `_check-mathlib-cache` guard, two-workflow CI (`ci.yml` for Lean, `text-lint.yml` reusable for markdown + cspell), `.github/lean.instructions.md` for scoped Copilot PR review, AGENTS.md hub-and-spoke via symlink, paper-backed `.markdownlint-cli2.jsonc` + `cspell.jsonc` with LaTeX-math `ignoreRegExpList`, `docs/plans/{todo,done}/` + `docs/reviews/` + `docs/research/`, references/{papers,transcriptions}/ layout.
- **shannon-entropy (`~/Development/shannon-entropy`).** Same patterns except single-file `ci.yml` (both jobs in one workflow, no paths-ignore). Canonical `CONTRIBUTING.md`, `CODE_OF_CONDUCT.md`, `.github/SECURITY.md`, `.github/PULL_REQUEST_TEMPLATE.md`. Canonical `bin/bootstrap-worktree` zsh.
- **strength-model (`~/Development/strength-model`).** Superset: adds Python (`pyproject.toml`, `uv.lock`), per-paper Makefile targets (`$(PAPERS)`), Verso site build, zoo artifacts, `bin/audit-markdown-frontmatter.py` custom lint step, `check-proof-boundaries` exe, Pandoc-flavored LaTeX paper pipeline. Hosts the authoritative copies of `write-lean-code`, `write-math`, `write-latex`, `write-pandoc-markdown` skills under `skills/` (symlinked into `~/.claude/skills/`).

Common subset across all three: Lean + Mathlib + Lake + markdownlint-cli2 + cspell + paper-backed reference layout + milestone-based plan folders + AGENTS.md hub + copilot-instructions pair. This is the Lean formalization template that isn't captured anywhere executable.

## Skill inventory

### Currently in `cboone-cc-plugins/` (plugin distribution)

Scaffolders: `scaffold-new-repo`, `scaffold-go-cli`, `scaffold-go-library`, `scaffold-rust-cli`. Setup skills: `setup-ci`, `setup-linters`, `setup-secret-scanning`, `setup-installers`, `setup-gitleaks`. Write skills: `write-bash-scripts`, `write-go-code`, `write-markdown`, `write-scrut-tests`, `write-zsh-scripts`. Meta: `bootstrap-project`, `clean-up-agent-config`, `add-community-files`, `handle-secrets`.

No Lean scaffolder, no Lean write-skill, no math/LaTeX/Pandoc skill.

### Currently in `strength-model/skills/` (symlinked to user level)

`write-lean-code`, `write-math`, `write-latex`, `write-pandoc-markdown`. These apply across any Lean or paper-backed project the user works on but live in one specific project's repo, so they aren't distributable.

### Currently in `cboone/gh-actions`

Reusable workflows: `ci.yml`, `codeql.yml`, `create-release.yml`, `github-lint.yml`, `gitleaks.yml`, `go-ci.yml`, `go-release.yml`, `npm-publish.yml`, `pages-deploy.yml`, `release.yml`, `rust-ci.yml`, `rust-release.yml`, `scrut.yml`, `secret-scan.yml`, `shell-lint.yml`, `text-lint.yml`, `trufflehog.yml`, `zig-ci.yml`, `zig-release.yml`.

Pattern: one `{lang}-ci.yml` per language. **No `lean-ci.yml`.**

## Gap taxonomy

| Knowledge chunk | Owner today | Proposed home |
| --- | --- | --- |
| Lean Lake bootstrap script (zsh, Mathlib cache guard) | each repo ships its own copy | `write-lean-code` + (optionally) a Lean scaffolder |
| Lean Makefile standard targets | each repo ships its own copy | `write-lean-code` + Lean scaffolder |
| `testDriver` vs `defaultTargets` decision | nowhere (session-only) | `write-lean-code` |
| Test-library discipline (every public module mirrored in `*Test/`) | roadmap prose in each repo | `write-lean-code` + new `write-lean-tests` |
| Lean project-type detection | missing in `bootstrap-project` | extend `bootstrap-project` |
| Lean library scaffolder | missing | new `scaffold-lean-library` |
| Pandoc-academic markdownlint preset | `.markdownlint-cli2.jsonc` copy-pasted across repos | extend `setup-linters` + `write-pandoc-markdown` |
| cspell LaTeX-math `ignoreRegExpList` | `cspell.jsonc` copy-pasted across repos | `write-pandoc-markdown` + `setup-linters` |
| Copilot scoped instructions (`.github/*.instructions.md` with `applyTo`) | added ad hoc in shannon-entropy + zhang-yeung | extend `clean-up-agent-config` |
| Milestone-based formalization roadmap template | roadmap-by-imitation across repos | new `write-formalization-roadmap` or extension of `write-math` |
| Lean CI reusable workflow | duplicated `ci.yml` in each repo | new `lean-ci.yml` in `gh-actions` |
| Text-lint preset for Lean-math repos | overrides in each repo | extend `text-lint.yml` with `lean-math` preset |
| `write-lean-code` / `write-math` / etc. distribution | strength-model only | migrate to `cboone-cc-plugins` |

Prerequisite: the Lean/math write-skills live in `strength-model/skills/` today. Extending them via `cboone-cc-plugins` issues only makes sense if they also move there (otherwise extensions land in a single-project repo). One dedicated migration issue precedes the extension issues.

## Proposed issue roster

### cboone/cboone-cc-plugins (11 issues)

**#A. Migrate Lean + math write-skills from strength-model into cboone-cc-plugins**

- Title: `new plugin: migrate write-lean-code, write-math, write-latex, write-pandoc-markdown from strength-model`
- Labels: `new skill`
- Body: Context that the four skills currently live under `strength-model/skills/` and are symlinked into `~/.claude/skills/`, so they aren't distributable outside the user's laptop. Proposes importing them as-is into `cboone-cc-plugins/` (either as-four separate plugins or bundled), pinning the strength-model copies to redirects during transition, and updating the user-level symlinks. Enumerates downstream issues (#B, #C, #D, #G, #I, #J) that depend on this migration. Notes that the skills themselves are content-ready; this is a distribution/packaging change.

**#B. `write-lean-code`: capture Lake + Makefile + bootstrap patterns for Mathlib projects**

- Title: `write-lean-code: capture Lake + Makefile + bootstrap patterns for Mathlib projects`
- Labels: `enhancement`
- Body: Add sections for:
  - `bin/bootstrap-worktree` zsh template (lake update → cache get → Mathlib oleans check → `lake build <Lib>`). Include the `ensure_mathlib_cache_present` function pattern from shannon-entropy/zhang-yeung.
  - Makefile standard target set: `build`, `bootstrap`, `lean-lint`, `test`, `lint-markdown`, `lint-spelling`, `lint`, `check`, `clean`, `help`, plus the `_check-mathlib-cache` phony guard. Include the `help`-target auto-extraction snippet.
  - `lintDriver = "batteries/runLinter"` as the standard lint driver for Mathlib-downstream projects.
  - Entrypoint manifest pattern (`<Name>.lean` explicitly re-exports every submodule, mirroring `Mathlib.lean`).
- References shannon-entropy + zhang-yeung as canonical exemplars.
- Depends on #A.

**#C. `write-lean-code`: capture `testDriver` vs `defaultTargets` decision + test-library discipline**

- Title: `write-lean-code: document testDriver vs defaultTargets and test-library discipline`
- Labels: `enhancement`
- Body:
  - Decision criteria: `testDriver = "FooTest"` + `defaultTargets = ["Foo"]` is the Mathlib convention and keeps `lake test` as a distinct signal from `lake build`; `defaultTargets = ["Foo", "FooTest"]` is simpler but loses the distinction. For compile-time example-based tests either works, but the former is recommended.
  - `[[lean_lib]]` stanza for test library.
  - Naming: `FooTest/` mirrors `Foo/`, with `FooTest.lean` as a re-export surface.
  - Testing discipline rule (every public module has a matching test module that imports only the public surface).
  - zhang-yeung-inequality's M0/M1 roadmap `testDriver` discussion linked as rationale.
- Depends on #A.

**#D. `write-lean-code`: note `Fintype` + `MeasurableSingletonClass` specialization pattern from PFR**

- Title: `write-lean-code: document PFR finite-alphabet specialization pattern`
- Labels: `enhancement`
- Body: PFR's entropy API (`I[·:·]`, `I[·:·|·]`, `condMutualInfo_eq`) wants `FiniteRange` + singleton-measurable + countability instances; the common fix is to specialize codomains to `[Fintype Sᵢ] [MeasurableSpace Sᵢ] [MeasurableSingletonClass Sᵢ]` at module scope. Add a short subsection (or link to a reference file) capturing this pattern, `noncomputable def` + default measure `(μ := by volume_tac)`, and the recommendation to list `Measurable` as an explicit argument rather than in the `variable` block (matching PFR's hygiene).
- Depends on #A.

**#E. New skill: `scaffold-lean-library`**

- Title: `new skill: scaffold-lean-library`
- Labels: `new skill`
- Body: Scaffold a Mathlib-downstream Lean library project modeled on shannon-entropy + zhang-yeung-inequality:
  - Prompts for: project name, top-level namespace (default: kebab-to-PascalCase of name), Lean toolchain version, primary dependency (Mathlib vs PFR-downstream).
  - Generates: `lakefile.toml` (with lib + testDriver + lintDriver + PFR/Mathlib dep + leanOptions), `lean-toolchain`, `<Name>.lean` + `<Name>Test.lean` re-export surfaces, `<Name>/Prelude.lean` stub, `<Name>Test/Prelude.lean` stub, `bin/bootstrap-worktree`, `Makefile`, `.gitignore` (`/.lake`), `.vscode/settings.json` + `.vscode/extensions.json`, `.github/workflows/ci.yml` (Lean) and (optionally) `.github/workflows/text-lint.yml`, `.github/lean.instructions.md`, `AGENTS.md` stub with the Lean sections plus CLAUDE.md symlink, `.markdownlint-cli2.jsonc` + `cspell.jsonc` + `cspell-words.txt` (Pandoc-academic preset if paper-backed; generic otherwise), `docs/plans/{todo,done}/.gitkeep`, `references/README.md` if paper-backed.
  - Overlap rules: if it runs, `scaffold-new-repo` scopes down to agent-config-only; `setup-ci` is skipped; `setup-linters` scopes down to cross-language (Pandoc-markdown + cspell).
  - References shannon-entropy and zhang-yeung as exemplars.

**#F. `bootstrap-project`: add Lean project detection and overlap rules**

- Title: `bootstrap-project: add Lean project detection and overlap rules`
- Labels: `enhancement`
- Body:
  - Detection table entry: `lakefile.toml` + `.lean` source files → Lean library (or Lean CLI if `[[lean_exe]]` present).
  - Overlap rules: if `scaffold-lean-library` (from #E) will run, skip `setup-ci` (included), scope down `scaffold-new-repo` (agent config only), scope down `setup-linters` (cross-language only unless the project is paper-backed, in which case apply the Pandoc-academic preset).
  - Applicability table update: `scaffold-go-cli` / `scaffold-rust-cli` / CLI-only tools are Not Applicable for Lean libraries.
  - Depends on #E.

**#G. `setup-linters`: add Pandoc-academic markdownlint preset + LaTeX-math cspell preset**

- Title: `setup-linters: add Pandoc-academic Markdown preset for paper-backed Lean/math projects`
- Labels: `enhancement`
- Body:
  - Trigger: project contains `references/papers/` or `references/transcriptions/`, or user explicitly requests.
  - markdownlint preset: `MD013 false`, `MD033 false`, `MD041 false`, `MD040 false`, `MD024 { siblings_only: true }`, `MD025 false`, `MD026 { punctuation: ".,;!" }`, `MD010 { code_blocks: false }`, `MD060 false`. Ignores: `references/papers/**`, `references/papers.bib`, `references/transcriptions/**`, `docs/plans/done/**`.
  - cspell preset: `ignoreRegExpList` with the seven patterns for inline/display math, raw `{=latex}` blocks, Pandoc citations, bare citekeys, LaTeX commands. `project-words` dictionary at `cspell-words.txt`.
  - References shannon-entropy/zhang-yeung as canonical config pairs.

**#H. `setup-linters` (or new skill): Lean language detection**

- Title: `setup-linters: detect Lean projects and defer to lake lint`
- Labels: `enhancement`
- Body: When `.lean` files or `lakefile.toml` are present, treat Lean linting as project-local (handled by `lake lint` via `lintDriver = "batteries/runLinter"`). Do not attempt to install external Lean linters. Surface a recommendation to wire `make lean-lint` and the CI `lake lint` step via `leanprover/lean-action`. Keep cross-language linters (markdownlint, cspell, editorconfig) as usual.

**#I. New skill: `write-lean-tests`**

- Title: `new skill: write-lean-tests`
- Labels: `new skill`
- Body: Conventions for compile-time example-based API regression tests in `<Name>Test/`:
  - Import rule: test modules import only the public surface (`import <Name>`), never internals.
  - Test shape: `example` statements that restate each exported lemma/definition; at least one composed-downstream-use test per milestone.
  - Naming mirror: `<Name>/X/Y.lean` → `<Name>Test/X/Y.lean`.
  - Anti-patterns: reaching into proof internals, opening namespaces past the public surface, mocking.
  - Build-gate options: `testDriver` + `lake test` (preferred) or dual `defaultTargets` entries.
- References: zhang-yeung `ZhangYeungTest/Delta.lean` and shannon-entropy `ShannonTest/Entropy/*`.
- Depends on #C.

**#J. New skill: `write-formalization-roadmap`**

- Title: `new skill: write-formalization-roadmap`
- Labels: `new skill`
- Body: Conventions for the multi-milestone formalization roadmap document that zhang-yeung, shannon-entropy, and strength-model each ship:
  - Section order: Context, State of the Art, Architecture, Scope, File Layout, Milestone-by-Milestone Plan, Key Risks, Verification Plan, Extensions, Critical Files.
  - Milestone entry template: title, deliverables, testing checkpoint, risks, dependencies.
  - M0 = project scaffolding as a dedicated milestone.
  - Testing-parallel-with-proof rule (every milestone adds a matching test module).
  - Checkpoint gate structure (buildable + linted + testable).
- References: `docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md` in zhang-yeung as the current exemplar.
- Could be folded into `write-math` but standalone is cleaner since the skill governs plan-document structure, not mathematical prose.

**#K. `clean-up-agent-config`: capture `.github/*.instructions.md` scoped-Copilot pattern**

- Title: `clean-up-agent-config: handle .github/*.instructions.md scoped Copilot files`
- Labels: `enhancement`
- Body: GitHub Copilot supports scoped instruction files via `applyTo: "<glob>"` frontmatter. shannon-entropy and zhang-yeung both ship `.github/lean.instructions.md` alongside `.github/copilot-instructions.md`. Document the pattern, recommend cross-referencing between the general and scoped files, and add `.github/*.instructions.md` to the clean-up scan so stale or redundant scoped files are flagged.

### cboone/gh-actions (2 issues)

**#L. New workflow: `lean-ci.yml` (Lean build + lint + test reusable workflow)**

- Title: `new workflow: lean-ci.yml`
- Body: shannon-entropy and zhang-yeung-inequality ship nearly identical Lean CI (`checkout` → elan cache → `leanprover/lean-action` → `lake lint` → `lake test`). Propose a `lean-ci.yml` reusable workflow with inputs:
  - `lib-name` (informational, used in step names).
  - `lean-action-ref` (SHA-pinned ref; default to the current commonly-used pin).
  - `run-test` (boolean; default true).
  - `run-lint` (boolean; default true).
- Steps: `actions/checkout@v5`, `actions/cache@v4` for `~/.elan` keyed by `hashFiles('lean-toolchain')`, `leanprover/lean-action@<pin>`, conditional `lake lint`, conditional `lake test`.
- Downstream benefit: consumer repos shrink to a 5-line reusable-workflow call.

**#M. `text-lint.yml`: add `lean-math` preset for Pandoc-academic + LaTeX-math cspell**

- Title: `text-lint.yml: add lean-math preset for Pandoc-academic markdownlint and cspell`
- Body: Lean + paper-backed repos re-implement the same `.markdownlint-cli2.jsonc` and `cspell.jsonc`. Add an input `preset: "lean-math"` (or a new sibling workflow `text-lint-academic.yml`) that auto-applies the Pandoc-academic markdownlint config and the LaTeX-math cspell `ignoreRegExpList` when the consumer repo does not ship its own config. If consumer ships a config, the existing local-config behavior wins. Must interact cleanly with existing inputs (`run-cspell`, `run-prettier`).
- Reference: the preset content lives in the canonical shannon-entropy / zhang-yeung configs; cboone-cc-plugins issue #G captures the same preset on the skill side.

## Dependency graph and ordering

```text
#A (migrate skills)
├── #B (Lake + Makefile + bootstrap)
├── #C (testDriver + test discipline)
│   └── #I (write-lean-tests)
├── #D (PFR finite-alphabet pattern)
├── #G (markdownlint + cspell preset; pairs with #M on the workflow side)
└── #J (write-formalization-roadmap)

Independent:
#E (scaffold-lean-library)
  └── #F (bootstrap-project: add Lean)
#H (setup-linters: Lean detection)
#K (clean-up-agent-config: scoped Copilot files)

gh-actions:
#L (lean-ci.yml) — independent
#M (text-lint.yml preset) — pairs with #G
```

Address order (recommendation): #A first (unblocks skill extensions), then #E (unblocks #F), then the rest in parallel. Do not make issue dependencies hard blockers via `gh` metadata; keep them as body prose.

## Filing approach

Use `gh issue create --repo <repo> --title "<t>" --body-file <tmpfile> --label <label>` per issue (HEREDOC avoided — the plan's Git skill flags long multi-line `-b` args as permission-prompt risks). Draft each body in `/tmp/issue-<n>.md`, run `gh issue create`, capture the returned URL, append to a session summary.

Labels available in `cboone-cc-plugins`: `new skill`, `enhancement`, `bug`, `in progress`. Labels in `gh-actions`: none standardized yet — file without labels unless you confirm a set.

## Verification

After filing:

- `gh issue list --repo cboone/cboone-cc-plugins --search "lean OR math OR write-lean OR write-math"` returns the eleven new issues (or a subset if user deselected some).
- `gh issue list --repo cboone/gh-actions --search "lean"` returns the two gh-actions issues.
- Each issue body renders without broken markdown (via `gh issue view <n>`).
- No duplicate or near-duplicate of pre-existing open issues (verified during this plan's investigation pass: no existing Lean- or math-related issues in either repo).

## Open decisions for the user

1. **Migration vs re-import.** Issue #A proposes moving the four write-skills out of strength-model into cboone-cc-plugins. Alternatives: (a) copy them and let strength-model's copies become stale, (b) leave them in strength-model and file the extension issues there instead, (c) create a tiny new plugin repo `cboone/lean-cc-plugins` dedicated to the Lean/math stack. Default: migrate into `cboone-cc-plugins` as its owner currently hosts the non-Lean language skills.
2. **Issue granularity.** The plan is 11+2. If that's too many, natural bundles are: #B + #C + #D → single "write-lean-code: Mathlib-downstream patterns" issue; #E + #F → single "new scaffold-lean-library" issue with bootstrap-project integration included; #G + #M → single cross-repo preset issue. Default: stay at 13 issues for smaller review scope.
3. **`write-formalization-roadmap` standalone vs folded into `write-math`.** Either works. Default standalone, because plan-document structure is a different concern from mathematical prose.
4. **Labels on `gh-actions` issues.** That repo has no standardized label set. Either skip labels, or propose creating `new workflow` / `enhancement` labels as a preliminary chore.

## Post-bootstrap follow-ups (out of scope for this plan)

- Python + paper-pipeline knowledge from strength-model (uv-based Python, per-paper Makefile targets, Verso, bibliography auditing) — not addressed here, warrants a separate pass if/when a second paper-backed project starts.
- `.vscode/settings.json` standard Lean presets — small enough to live inside #E's scaffolder output rather than a dedicated issue.
- Cross-reference the filed issues from `write-lean-code`'s SKILL.md as "ongoing work" pointers so a future skill-reader finds them.
