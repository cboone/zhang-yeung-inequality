---
title: "M6: Polish and release for the full M0-M5 formalization"
created: 2026-04-22
status: in progress
branch: feature/implement-phase-m6
roadmap: docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md
milestone: M6
depends_on: M0-M5, all merged on `main` through commit `30d6c79` (docs sync after M5 landing). No further proof-level work is a prerequisite; the entire S2 scope (Theorems 2, 3, 4, 5, plus the copy lemma and the entropy-region layer) is live on `main` with `make check` green.
---

## Status

In progress. The `feature/implement-phase-m6` worktree starts from the tip of `main` after the M5 landing. `lake build ZhangYeung`, `lake lint`, and `lake test` are all green at baseline. No Lean code needs to change to close M6; the milestone is the documentation, polish, and release-packaging pass that sits on top of the landed formalization.

## Context

Milestone M6 of the Zhang-Yeung roadmap (§6) is the closing polish-and-release pass for the S2 scope the roadmap resolved on 2026-04-15. By the time M6 starts, everything the roadmap designates as **core** and **stretch** has landed:

- **M1 Delta equational lemmas** → `ZhangYeung/Delta.lean`.
- **M1.5 Theorem 2** → `ZhangYeung/Theorem2.lean`.
- **M2 Copy lemma** → `ZhangYeung/CopyLemma.lean`.
- **M3 Theorem 3** → `ZhangYeung/Theorem3.lean`.
- **M4 Theorem 4** → `ZhangYeung/{EntropyRegion,Theorem4}.lean`.
- **M5 Theorem 5** → `ZhangYeung/Theorem5.lean`.
- **Prelude helpers** → `ZhangYeung/Prelude.lean` (`condIndepFun_comp`, `IdentDistrib.condMutualInfo_eq`, `mutualInfo_add_three_way_identity`, `mutualInfo_le_of_condIndepFun`).

Every public module has a matching `ZhangYeungTest/` sibling, and the lakefile keeps `testDriver = "ZhangYeungTest"` paired with `defaultTargets = ["ZhangYeung"]`. Licensing, bibliography, `REUSE.toml`, `NOTICE`, community files (`CONTRIBUTING.md`, `CODE_OF_CONDUCT.md`, `.github/SECURITY.md`, PR template), and CI workflows are all already in place from prior milestones.

What is *not* yet in place:

1. A CITATION file that an external reader (or Zenodo, or the GitHub "Cite this repository" button) can consume to generate a canonical citation for the formalization itself.
1. A CHANGELOG summarizing the M0-M5 landings as release-worthy units.
1. An explicit version tag and a published GitHub release associated with it.
1. A `write-lean-code` / `write-math` / `lint-and-fix` sweep over the landed M0-M5 surface. Individual milestones landed with their own reviews, but a cross-cutting pass looking for drift (stale docstrings, convention breakage from later milestones, outdated cross-references) has not been done.
1. A test-module audit that formally confirms the "every public definition or theorem has a matching `example` in the sibling test module" invariant, rather than relying on the per-milestone testing discipline.
1. Documentation sync after the release lands: the roadmap's Status block, the README Status table's M6 row, and the roadmap's own filesystem location (`docs/plans/todo/` vs. staying in `todo/` as a living extensions document) all need a last pass once M6 itself is done.

M6 closes those gaps. It introduces no new Lean code and no new mathematical content.

## Paper / roadmap references

This milestone is purely administrative with respect to the paper. No new equations are formalized. The relevant roadmap anchors are:

- Roadmap §6 (Milestone-by-Milestone Plan), the **M6: Polish and release** subsection.
- Roadmap §8 (Verification Plan), which locks in the "every public module has a matching test module" invariant and the `make check` gate.
- Roadmap §9 (Extensions, future work, post-release), which scopes what is *not* in M6 and explicitly belongs to the post-release follow-up stream.

## Scope

### In scope

1. **Cross-cutting Lean-code audit.** Run `write-lean-code` over every file under `ZhangYeung/` and `ZhangYeungTest/`; run `write-math` over every public docstring and every Markdown document under `docs/`, `references/README.md`, `AGENTS.md`, `CONTRIBUTING.md`, and `README.md`; run `lint-and-fix` to close the pass. Address drift flagged by these skills; do not rewrite correct code.
1. **Test-module completeness audit.** For each public declaration in `ZhangYeung/*.lean`, verify that the matching `ZhangYeungTest/*.lean` module pins its signature and exercises at least one downstream use. File-by-file audit table produced as part of the plan's sign-off; any gaps are closed inside this milestone.
1. **CITATION file.** Add `CITATION.cff` in the Citation File Format v1.2.0 at the repository root so GitHub's "Cite this repository" widget picks it up and so Zenodo (if enabled later) can consume it unchanged.
1. **CHANGELOG.** Add `CHANGELOG.md` at the repository root, starting with `## [0.1.0] - YYYY-MM-DD` and summarizing M0-M5 as a single first release. Follow Keep-a-Changelog conventions.
1. **README polish.** Final pass: flip the M6 Status table row from "in progress" to "done" on landing; add a short "How to cite" section (or inline citation block) pointing at `CITATION.cff`; add an "Acknowledgments" section naming PFR, Mathlib, and any other dependencies; re-verify install instructions from a hypothetical fresh clone.
1. **Roadmap sync.** Update the roadmap's "Current status" paragraph, mark M6 complete in the roadmap's §6 block, and decide the roadmap file's final location (see §7.1 below).
1. **Release tagging and packaging.** Create a `v0.1.0` annotated tag on `main` once the polish PR merges, and publish a GitHub Release whose body is the CHANGELOG entry for `v0.1.0`. Do *not* push the tag or open the release before the polish PR merges.
1. **Plan housekeeping.** Move this plan from `docs/plans/todo/` to `docs/plans/done/` as the last step before (or immediately after) the PR merges.

### Out of scope

The following are roadmap §9 items and are explicitly deferred to follow-up work, not M6:

1. Copy-lemma upstream to Mathlib. Plan exists informally; drafting the Mathlib PR is a separate, multi-week undertaking.
1. Exact Theorem 3 with explicit slack (paper pp. 1445-1446 remainder `R`).
1. Dougherty-Freiling-Zeger 2006/2011 six inequalities.
1. ITIP certificate importer.
1. Matus 2007 infinite family.
1. Ingleton / Kinser / matroid connections.
1. Chan-Yeung 2002 group-theoretic reformulation.
1. Theorem 6 (inner bound on `cl(Gamma*_4)`).
1. Bridge to `cboone/shannon-entropy`.
1. The non-Shannon-inequality discovery program (`docs/plans/todo/2026-04-17-non-shannon-inequality-discovery-program.md`), which remains in `todo/` as an exploratory-status document and is *not* a prerequisite for closing M6.

## Baseline assessment

What the `feature/implement-phase-m6` worktree already satisfies, verified by inspection on 2026-04-22:

| Concern | Current state | M6 action |
|---|---|---|
| Lean proofs for M0-M5 | All landed, no `sorry` anywhere in `ZhangYeung/` or `ZhangYeungTest/`. `make check` green. | None required; protect via baseline check. |
| `lakefile.toml` invariants | `testDriver = "ZhangYeungTest"` and `defaultTargets = ["ZhangYeung"]` present. | Preserve verbatim. |
| SPDX / REUSE coverage | Every `*.lean` file has an inline header; `REUSE.toml` covers the rest. | Add headers to any M6-introduced files; confirm `reuse lint` stays clean. |
| README | Has project overview, averaged Zhang-Yeung statement, status table, formalization scope, module layout, build commands, dependencies, references, AI statement, and licensing. | Add "How to cite" and "Acknowledgments" sections; flip M6 row to done; sanity-check install block. |
| `AGENTS.md` / `CLAUDE.md` | Up to date as of M5 landing. | No changes expected unless the audit surfaces drift. |
| CI | Two workflows (`ci.yml` Lean, `text-lint.yml`) green on `main` at `30d6c79`. | Confirm green on the polish PR. |
| Community files | `CONTRIBUTING.md`, `CODE_OF_CONDUCT.md`, `.github/SECURITY.md`, `.github/PULL_REQUEST_TEMPLATE.md` all present. | No changes expected. |
| Test module coverage (qualitative) | Seven public `ZhangYeung/` modules; seven matching `ZhangYeungTest/` modules; 82 total `example` blocks across tests. | Produce the per-declaration audit table (§6.2). |
| CITATION file | Absent. | Add `CITATION.cff`. |
| CHANGELOG | Absent. | Add `CHANGELOG.md`. |
| Git tags | None. | Create `v0.1.0` after PR merges. |
| GitHub releases | None. | Publish `v0.1.0` release. |
| Roadmap status block | Lists M6 as "in progress"; Current Status paragraph already notes M0-M5 complete. | Flip to "done"; optionally reclassify post-release extensions into a separate extensions document. |

## Goals

1. Close out the Zhang-Yeung 1998 paper's Section II + Section III formalization as a citable artifact: named version, CHANGELOG entry, CITATION metadata, published GitHub release.
1. Audit the M0-M5 code surface for convention drift in a single cross-cutting pass, using the `write-lean-code` / `write-math` / `lint-and-fix` skills as the acceptance gate rather than another hand-written style review.
1. Record in this plan a file-by-file inventory of the public API and its test coverage, so any future milestone has a stable reference point for the invariant the roadmap §8 bullet locks in ("every public module added or changed in M0-M5 must land with a matching `ZhangYeungTest/` module").
1. Preserve all the invariants landed in prior milestones (`testDriver`/`defaultTargets` split, `autoImplicit = false`, no hard line-length cap, single-line comment paragraphs, SPDX-per-file for Lean, REUSE-glob for infrastructure) through the polish pass.

## Deliverables

### D1. Cross-cutting code audit artifact

- Output: one commit per skill pass (three commits max: `chore: lint-and-fix polish`, `refactor: apply write-lean-code audit`, `docs: apply write-math audit`). If a pass is a no-op, record it in the PR description instead of creating an empty commit.
- Audit scope: every file under `ZhangYeung/`, `ZhangYeungTest/`, plus the two top-level re-export files (`ZhangYeung.lean`, `ZhangYeungTest.lean`). Vendored deps under `.lake/packages/` are out of scope per `AGENTS.md`.
- Acceptance: `make check` green after each commit; no drift flagged by re-running the same skill a second time.

### D2. Test-module completeness audit table

- Output: a table inside this plan document's §6.2 block (below), file-by-file, mapping each public declaration in `ZhangYeung/*.lean` to the `example` in the sibling test module that pins its signature. Any gap is either closed by adding an `example` in the same commit as the audit, or justified in a short "intentionally deferred" note in this plan.
- Acceptance: the audit table is filled in with a ✅ or a commit hash for every public declaration.

### D3. CITATION.cff

- Output: `CITATION.cff` at the repository root, CFF v1.2.0, license Apache-2.0 or CC-BY-4.0 as appropriate (CFF metadata itself is prose-like; CC-BY-4.0 via the `REUSE.toml` prose-group glob is the cleanest fit, but confirm REUSE annotation coverage or add a per-file SPDX if the glob doesn't pick it up).
- Content: authors (Christopher Boone); title ("The Zhang-Yeung Inequality: a Lean 4 formalization"); year (2026); version (`0.1.0`); `date-released`; `repository-code`; `license: Apache-2.0` (the code license of the artifact); `type: software`; `keywords` (Lean, formalization, information theory, Shannon entropy, non-Shannon inequality, PFR, Mathlib); preferred-citation block pointing at the Zhang-Yeung 1998 paper (DOI 10.1109/18.681320) so tools can produce both a software citation and a scientific-source citation.
- Acceptance: GitHub's "Cite this repository" sidebar renders the CFF entry; `cffconvert --validate` (if installed) passes; `reuse lint` remains clean.

### D4. CHANGELOG.md

- Output: `CHANGELOG.md` at the repository root, Keep-a-Changelog format.
- First section: `## [0.1.0] - 2026-XX-XX`, followed by **Added** / **Build** / **Documentation** subsections that enumerate the M0-M5 landings at the resolution of the milestone, not the commit. Typical entries:
  - **Added**
    - M1: the Zhang-Yeung delta `ZhangYeung.delta` and its equational lemmas.
    - M1.5: `ZhangYeung.theorem2` for the 1997 conditional inequality.
    - M2: `ZhangYeung.copyLemma` and the six `copyLemma_*` corollaries.
    - M3: `ZhangYeung.zhangYeung`, `zhangYeung_dual`, `zhangYeung_averaged` (paper eqs. 21-23).
    - M4: `ZhangYeung.theorem4`, `theorem4_ge_four`, the `F_witness_ℚ` counterexample, the entropy-region layer.
    - M5: `ZhangYeung.theorem5`, `theorem5_averaged` (paper eqs. 27-28).
    - Generic helpers promoted to `ZhangYeung/Prelude.lean`.
  - **Build**
    - PFR dependency pinned to `80daaf1`.
    - `testDriver = "ZhangYeungTest"` / `defaultTargets = ["ZhangYeung"]` split.
    - CI workflows for Lean build + lint + test, and Markdown / spelling.
  - **Documentation**
    - Project README, AGENTS/CLAUDE, licensing (REUSE + NOTICE), bibliography, per-milestone plans and reviews.
- Top of file: an `## [Unreleased]` placeholder block empty except for the Keep-a-Changelog boilerplate, so follow-up work has a staging area.
- Acceptance: `make lint` (markdownlint + cspell) clean; `CHANGELOG.md` is picked up by the `REUSE.toml` prose-group glob.

### D5. README polish

- Output: one commit, `docs(readme): add citation and acknowledgments; flip M6 to done`.
- Changes:
  - Status table M6 row: `in progress` → `done`.
  - New `## How to cite` section after the status paragraphs, pointing at `CITATION.cff` and showing a short BibTeX-style snippet the reader can copy.
  - New `## Acknowledgments` section naming PFR (Terence Tao et al.), Mathlib, the Lean community, and any individual reviewers. Keep it short.
  - Verify the Build and Verify block still matches the actual Makefile targets (`make help` output).
- Acceptance: `make lint` clean; visual diff-review confirms no regressions in the Module Layout or License sections.

### D6. Roadmap sync

- Output: one commit, `docs(roadmap): mark M6 done and sync status block`.
- Changes:
  - Roadmap's `Current status` paragraph: "M0 through M5 are complete on `main`" → "M0 through M6 are complete on `main`; the S2 scope is closed and the repository carries a tagged `v0.1.0` release."
  - Roadmap §6 M6 subsection: inline status note that all three M6 bullets landed (README citation + audit sweep + release).
  - Do **not** delete or re-order §9 (Extensions, future work); that list remains the canonical post-release follow-up queue.
- Decision to take here: **does the roadmap stay in `todo/` as a living document, or move to `done/` because its S2 scope is closed?** Recommendation: it stays in `todo/` because its §9 extensions queue is the canonical index for post-release research work. Keeping it in `todo/` avoids forcing consumers to pivot to a second doc. Record the decision in the same commit.
- Acceptance: `make lint` clean; roadmap's §6 M6 entry reads as closed; the "Current status" paragraph is internally consistent with the status table and with `git tag -l`.

### D7. Release tagging and GitHub release

- Output: one annotated tag `v0.1.0` on `main`, and one GitHub Release whose body is the CHANGELOG's `## [0.1.0]` section.
- Preconditions for this deliverable (hard gates):
    1. The polish PR has merged to `main`.
    1. `make check` is green on the merge commit.
    1. `reuse lint` is green on the merge commit.
    1. The CHANGELOG entry's date has been back-filled to the actual merge date.
- Commands (run sequentially, post-merge, after user confirmation):

    ```bash
    git fetch origin main
    git checkout main
    git pull --ff-only origin main
    git tag -s -a v0.1.0 -m "v0.1.0 — Zhang-Yeung 1998 §II + §III formalization (M0-M5)"
    git push origin v0.1.0
    gh release create v0.1.0 \
        --title "v0.1.0: Zhang-Yeung 1998 Section II + III formalization" \
        --notes-file <(awk '/^## \[0\.1\.0\]/,/^## \[/{print}' CHANGELOG.md | sed '$d')
    ```

    The `awk | sed` pipeline extracts the `## [0.1.0]` section from the CHANGELOG while dropping the trailing header of the next section. If we end up with an `## [Unreleased]` block above the `0.1.0` section (likely), the extraction still works because the start pattern is anchored at `0.1.0`.
- Acceptance: `git tag -l` shows `v0.1.0`; `gh release view v0.1.0` shows the CHANGELOG body; the GitHub repository landing page displays the tag and release.
- The user prefers GPG-signed commits / tags (`gcsm` alias). The `-s` flag on `git tag -a` signs the tag.

### D8. Plan housekeeping

- Output: `git mv docs/plans/todo/2026-04-22-m6-polish-and-release.md docs/plans/done/2026-04-22-m6-polish-and-release.md` as part of the same polish PR (not a follow-up).
- Acceptance: the plan lives under `docs/plans/done/` at merge time; the roadmap sync (D6) mentions this plan's final location.

## Sequencing: commits

Each commit maintains a green `make check`. Each commit is a conventional-commit-styled unit. The audit commits (D1) come first so later commits aren't re-audited; the release-packaging commits (D3, D4, D5, D6) come next; the housekeeping commit (D8) is the last commit before the PR.

1. **Bootstrap + baseline check.** In the `implement-phase-m6` worktree: confirm `bin/bootstrap-worktree` is not required (this is a no-Lean-change milestone), but run `make check` once to confirm the baseline is green. No commit.

1. **Cross-cutting audit pass: `lint-and-fix`.** Invoke the `lint-and-fix` skill across the full repo. Address anything flagged that is safe auto-fix. Commit: `chore: apply lint-and-fix polish`. Skip the commit entirely if the skill is a no-op. `make check` green.

1. **Cross-cutting audit pass: `write-lean-code`.** Invoke the `write-lean-code` skill across every file under `ZhangYeung/` and `ZhangYeungTest/`. Focus on drift flagged by the skill rather than wholesale rewrites. Commit: `refactor: apply write-lean-code audit` (or skip). `make check` green.

1. **Cross-cutting audit pass: `write-math`.** Invoke the `write-math` skill across every public docstring in `ZhangYeung/`, plus `README.md`, `AGENTS.md`, and the plan documents under `docs/plans/done/` (if any prose drift has surfaced since those plans landed — by policy those done-plans are frozen, so this pass only touches them if the skill flags an outright factual error). Commit: `docs: apply write-math audit` (or skip). `make check` green.

1. **Test-module completeness audit.** Produce the audit table (§6.2 in this plan), filling in each row with ✅ or a commit hash. Any gap is closed in the same commit with an `example` added to the relevant `ZhangYeungTest/*.lean`. Commit: `test: audit public-API coverage for M0-M5` (body: narrative description plus a diff-friendly version of the table). `make check` green.

1. **CITATION.cff.** Add the root-level `CITATION.cff`. If `reuse lint` flags it, either add a per-file SPDX header comment or extend the `REUSE.toml` prose-group glob. Commit: `docs: add CITATION.cff`. `make check` green; `reuse lint` green.

1. **CHANGELOG.md.** Add the root-level `CHANGELOG.md` with the `## [Unreleased]` placeholder and the `## [0.1.0]` section. Date is a `YYYY-XX-XX` placeholder until the release commit; the polish PR can back-fill it on merge day. Commit: `docs: add CHANGELOG`. `make check` green; markdownlint + cspell green.

1. **README polish.** Flip the Status table M6 row, add "How to cite" and "Acknowledgments" sections, re-verify the Build and Verify block. Commit: `docs(readme): add citation and acknowledgments; flip M6 to done`. `make check` green.

1. **Roadmap sync.** Update the roadmap's Current Status paragraph and the §6 M6 entry. Commit: `docs(roadmap): mark M6 done and sync status block`. `make check` green.

1. **Plan housekeeping.** `git mv docs/plans/todo/2026-04-22-m6-polish-and-release.md docs/plans/done/`. Commit: `docs(plans): archive M6 plan`. `make check` green.

1. **Open the PR.** Using the `pr` skill (which wraps `gh pr create` with the repo's tmpfile convention from `use-git`). PR title: `M6: polish and release for the full M0-M5 formalization`. PR body: summary of deliverables, test-module audit table summary, note that the `v0.1.0` tag and GitHub release are a follow-up performed post-merge. Request user confirmation before pushing to remote.

**Post-merge sequence (D7, requires user confirmation at each step):**

1. Back-fill the CHANGELOG's `## [0.1.0]` date to the actual merge date with a `docs(changelog): backfill 0.1.0 release date` follow-up commit directly on `main` (no PR needed; the merge has already happened and this is a one-line date fix). Or include this in the polish PR if the merge date is known in advance.
1. Create the signed tag: `git tag -s -a v0.1.0 -m "v0.1.0 — Zhang-Yeung 1998 §II + §III formalization (M0-M5)"`.
1. Push the tag: `git push origin v0.1.0`.
1. Publish the release: `gh release create v0.1.0 --title "..." --notes-file <(...)` (see §D7 for the exact awk/sed pipeline).

## Verification and acceptance

`make check` must pass at every commit on the branch. Additional acceptance criteria, by deliverable:

- **D1 audit commits:** re-invoking each skill on the audited surface produces no additional changes. A second run of `lint-and-fix` is a no-op.
- **D2 test-module audit:** every public declaration from the §6.2 table has a ✅ or a commit hash in the "example in test module" column. Any intentionally deferred entry has a link to its follow-up issue.
- **D3 CITATION.cff:** GitHub's "Cite this repository" widget on the rendered repo page resolves the CFF correctly. `cffconvert --validate CITATION.cff` passes (install: `uv tool install cffconvert`).
- **D4 CHANGELOG.md:** markdownlint-cli2 clean; the `## [0.1.0]` section is a self-contained excerpt suitable as a GitHub Release body (awk/sed pipeline produces non-empty output).
- **D5 README:** the rendered README on GitHub shows the updated Status table, the "How to cite" section, and the "Acknowledgments" section; the Build and Verify block commands produce the expected `make help` output verbatim.
- **D6 Roadmap sync:** the roadmap's Current Status paragraph, the §6 M6 entry, the README Status table, and `git tag -l` are mutually consistent.
- **D7 Release:** `git tag -l v0.1.0`, `gh release view v0.1.0`, and the GitHub repo landing page all surface the release; the release body is the CHANGELOG's `## [0.1.0]` section; the tag is GPG-signed.
- **D8 Plan housekeeping:** `ls docs/plans/done/2026-04-22-m6-polish-and-release.md` succeeds after merge; `ls docs/plans/todo/2026-04-22-m6-polish-and-release.md` returns "No such file" after merge.

## Risks and unknowns

### R1. A skill pass produces a large mechanical diff (low)

Running `lint-and-fix`, `write-lean-code`, or `write-math` across the full M0-M5 surface for the first time as a sweep could surface a larger mechanical diff than individual milestones produced incrementally. **Mitigation:** commit the skill-flagged changes in a single per-skill commit with a narrative body describing what was flagged. If the diff touches more than ~500 lines across more than ~10 files, halt, split the commit by module, and surface the breakdown in the PR description. Do not bundle genuine code changes with skill-flagged polish.

### R2. CITATION.cff licensing interacts with REUSE (low)

The project's CFF file is prose-like metadata. If it's picked up by the `REUSE.toml` prose-group glob, it inherits CC-BY-4.0 automatically; if not, an inline SPDX comment at the top of the CFF (`# SPDX-FileCopyrightText: 2026 Christopher Boone` and `# SPDX-License-Identifier: CC-BY-4.0`) keeps `reuse lint` clean. **Mitigation:** run `reuse lint` before and after the CITATION commit and inspect the diff.

### R3. The CHANGELOG's `## [0.1.0]` section inflates (low)

Enumerating M0-M5 at milestone granularity is fine; enumerating at commit granularity would balloon the section beyond what a GitHub Release body should contain. **Mitigation:** hard rule: one bullet per public theorem or per infrastructure invariant. The full commit-level history is already in `git log` and does not belong in the CHANGELOG.

### R4. Plan moved before PR merges (low)

`git mv`-ing this plan from `todo/` to `done/` in the same PR that lands M6 creates a transient inconsistency between the plan's `status: in progress` frontmatter and its filesystem location. **Mitigation:** flip the frontmatter status to `done` in the same commit as the `git mv`. The plan is self-consistent at merge time and the transient inconsistency only exists on the open PR's HEAD, which is acceptable.

### R5. Release is published before CI has fully validated it (moderate)

Pushing a tag triggers no CI workflow by default (neither of this repo's two workflows has a `push.tags` trigger). The `gh release create` step publishes the release immediately and a downstream consumer who clones `v0.1.0` and runs `make check` must not hit a red build. **Mitigation:** the post-merge sequence in §6 runs `make check` on the merge commit *before* creating the tag. Do not tag until the gate is green locally. The user prefers GPG-signed tags; verify the tag is signed (`git tag -v v0.1.0`) before pushing.

### R6. Zenodo DOI minting is out of scope here (low)

A canonical academic archive (Zenodo) can be wired up to mint a DOI on each GitHub Release, but doing so requires enabling the Zenodo-GitHub integration in the user's GitHub account settings. **Mitigation:** this plan treats Zenodo as a post-M6 follow-up. The CITATION.cff is already Zenodo-compatible, so the bridge is cheap to add later. The M6 release body notes that a Zenodo DOI is available as a follow-up once the integration is enabled.

### R7. The roadmap's post-release follow-up queue inflates (low)

Once M6 lands and the S2 scope is closed, the roadmap's §9 Extensions list becomes the project's single remaining todo list. It may grow faster than it shrinks. **Mitigation:** this is a known feature of living roadmaps; the entry-level fix is to spin each §9 item into its own `docs/plans/todo/*.md` the moment it is actively picked up, rather than leaving large items implicit inside §9. Not an M6 action; a working-agreement reminder.

## 6. Audit tables

### 6.1. Public-API surface map

To be filled in during sequencing step 5. Template:

| Module | Public declaration | Kind | Sibling test file | `example` coverage | Notes |
|---|---|---|---|---|---|
| `ZhangYeung/Prelude.lean` | `IdentDistrib.condMutualInfo_eq` | lemma | `ZhangYeungTest/…` | TBD | |
| `ZhangYeung/Prelude.lean` | `mutualInfo_add_three_way_identity` | lemma | `ZhangYeungTest/…` | TBD | |
| `ZhangYeung/Prelude.lean` | `mutualInfo_le_of_condIndepFun` | lemma | `ZhangYeungTest/…` | TBD | |
| `ZhangYeung/Prelude.lean` | `condIndepFun_comp` | lemma | `ZhangYeungTest/…` | TBD | |
| `ZhangYeung/Delta.lean` | `delta`, `delta_def`, `delta_comm_cond`, `delta_comm_main`, `delta_self`, `delta_eq_entropy`, `delta_form21_iff`, `delta_form22_iff`, `delta_form23_iff`, `delta_form23_of_form21_form22`, `delta_le_mutualInfo` | def + lemma ×10 | `ZhangYeungTest/Delta.lean` | 9 `example`s; TBD whether signature coverage is exhaustive | |
| `ZhangYeung/EntropyRegion.lean` | `I_F_n`, `condI_F_n`, `delta_F_n`, `shannonCone_n`, `zhangYeungAt_n`, `zhangYeungHolds_n`, `entropyFn_n`, `entropyFn`, `shannonRegion_n`, `entropyRegion_n`, `almostEntropicRegion_n`, `restrictFirstFour`, `restrictFirstFour_continuous`, `entropyFn_n_restrictFirstFour`, `restrictFirstFour_mem_entropyRegion_n`, `restrictFirstFour_mem_almostEntropicRegion_n` | def ×12 + theorem ×4 | `ZhangYeungTest/EntropyRegion.lean` | 9 `example`s; TBD | |
| `ZhangYeung/Theorem2.lean` | `theorem2` + supporting public lemmas (`ptilde_sum_eq_one`, `phat_sum_eq_one`, `delta_eq_sum_log_ratio`, `sum_joint_eq_sum_ptilde`, `theorem2_delta_le_zero`, `theorem2_shannon_identity`) | theorem + lemma ×N | `ZhangYeungTest/Theorem2.lean` | 4 `example`s; audit whether the supporting lemmas are public or `private` | Supporting lemma visibility audit is an M6 action. |
| `ZhangYeung/CopyLemma.lean` | `copyLemma`, `delta_of_condMI_vanishes_eq`, `copyLemma_delta_identity_Y₁`, `copyLemma_delta_identity_X_X₁`, `copyLemma_delta_transport_Y_to_Y₁`, `copyLemma_delta_transport_X_to_X₁`, `copyLemma_delta_le_mutualInfo_Y₁`, `copyLemma_delta_le_mutualInfo_X_X₁` | theorem ×8 | `ZhangYeungTest/CopyLemma.lean` | 10 `example`s; TBD | |
| `ZhangYeung/Theorem3.lean` | `zhangYeung`, `zhangYeung_dual`, `zhangYeung_averaged` | theorem ×3 | `ZhangYeungTest/Theorem3.lean` | 6 `example`s; TBD | |
| `ZhangYeung/Theorem4.lean` | `I_F`, `condI_F`, `delta_F`, `shannonCone`, `zhangYeungAt`, `zhangYeungHolds`, `F_witness_ℚ`, `F_witness`, `F_witness_eq_cast`, `shannonCone_of_witness`, `not_zhangYeungHolds_witness`, `shannon_incomplete`, `entropyFn_empty`, `entropyFn_singleton`, `entropyFn_pair`, `entropyFn_triple`, `entropyFn_quad`, `zhangYeungHolds_of_entropy`, `theorem4_finite`, `theorem4`, `theorem4_ge_four`, `theorem4_seqClosure`, `shannon_incomplete_ge_four` | def ×8 + theorem ×N | `ZhangYeungTest/Theorem4.lean` | 39 `example`s; TBD | Largest test file; audit density suggests full coverage but confirm per-declaration. |
| `ZhangYeung/Theorem5.lean` | `theorem5`, `theorem5_averaged` | theorem ×2 | `ZhangYeungTest/Theorem5.lean` | 5 `example`s (including a base-case compatibility test against M3) | Per M5 review, coverage is complete. |

The actual audit fills each "TBD" with ✅ if every declaration in that module's public API has at least one `example` pinning its signature or instantiating it against a witness, or with a per-declaration breakdown if gaps exist.

### 6.2. Intentionally deferred items

List entries spun out to follow-up issues rather than closed inside M6. Candidates:

- Bridge to `cboone/shannon-entropy` (roadmap §9 item 9).
- Zenodo DOI minting (§R6).
- Zenodo-compatible metadata polish beyond CFF (ORCID IDs, affiliation, funding) if the user prefers to defer.

Empty at the start; populated only if the audit finds a gap the user prefers to punt.

## 7. Decisions and open questions

### 7.1. Final location of the roadmap document

**Decision:** keep `docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md` in `todo/` after M6 closes. The `write-formalization-roadmap` skill classifies roadmaps as long-lived documents with post-release extension queues; §9 is that queue and should remain discoverable at the same path. The "Current status" paragraph flips to reflect the closed S2 scope, but the filesystem location does not change.

If a future reader expects `todo/` to mean "work not yet done" rather than "living planning documents," the fix is to either introduce a `docs/plans/living/` directory for this kind of long-lived doc, or to add a note at the top of `todo/` itself describing the convention. Either change is out of scope for M6.

### 7.2. Should the polish PR bundle the post-merge release, or split?

**Decision:** split. The polish PR lands all seven polish/audit deliverables. The `v0.1.0` tag + GitHub Release happen after the PR merges, on `main`, as a separate user-confirmed step. Bundling is tempting but (a) makes the PR diff bigger than it needs to be, and (b) complicates the rollback story if a last-minute CI regression blocks the tag.

### 7.3. CITATION authorship

**Decision:** sole author is Christopher Boone. The README's AI Statement separately credits Opus, GPT, and Copilot as development tools; those are not CFF `authors`. CFF supports a `contact` block if a non-author maintainer contact is needed; use `cboone@sent.com` only with user consent (the email is in the user's global memory but may not be the preferred public contact). Use the GitHub profile URL as the fallback contact if the user does not want the email exposed.

### 7.4. Version-number convention for future releases

**Decision:** follow semver-ish but not strict semver. M6 lands `v0.1.0`. Future increments:

- New S-scope milestone (Theorem 6, DFZ inequalities, Matus family): minor bump (`v0.2.0`, etc.).
- Upstream-aligned breaking PFR-pin bumps or module renames: minor bump.
- Bug-fix-only releases: patch bump (`v0.1.1`).
- We do not claim semver 1.0 until the copy lemma upstreams to Mathlib and the project's API is declared stable.

This is a light convention suitable for an academic formalization; it can be tightened if downstream consumers materialize.

## 8. Critical files

**Modified (existing):**

- `README.md` — D5.
- `docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md` — D6.
- `docs/plans/todo/2026-04-22-m6-polish-and-release.md` → `docs/plans/done/…` — D8.
- Any `ZhangYeung/*.lean` or `ZhangYeungTest/*.lean` flagged by the audit passes (D1). Nothing specific anticipated.

**Added:**

- `CITATION.cff` — D3.
- `CHANGELOG.md` — D4.
- Possibly a thin `.github/ISSUE_TEMPLATE/` directory if the audit flags it as missing (out of scope unless `write-math` or community-files convention demands it; the repo already has `PULL_REQUEST_TEMPLATE.md` and `SECURITY.md`).

**External (depend on, do not modify):**

- The PFR pin at `80daaf1` in `lakefile.toml`. No pin bump in M6.
- Mathlib transitive dep via PFR. No pin bump in M6.
