# Roadmap update: permanent PFR dependency

## Context

The formalization roadmap at `docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md` originally specified a three-phase strategy: (1) bootstrap on PFR, (2) progressively extract the needed PFR entropy subset into a local `ZhangYeung/Entropy/` module, (3) drop the PFR dependency. The user has reversed that decision: the project will **permanently depend on and use teorth/pfr** for Shannon-entropy primitives. No extraction milestone, no local entropy layer.

M0 (project scaffolding, `docs/plans/done/2026-04-15-m0-project-scaffolding.md`) is complete and already aligns with a PFR-as-dependency design. The current `lakefile.toml` pins PFR at `80daaf1` and lets Lake resolve Mathlib transitively through PFR. `CLAUDE.md` already describes the project as "Depends on PFR (teorth/pfr) for Shannon entropy definitions." Neither file needs editing.

The remaining work is to rewrite the roadmap so it no longer plans for extraction or eventual PFR removal. The CI-performance-improvements plan is unaffected.

## Scope

Only `docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md` changes. No Lean code, no build config, no CI, no CLAUDE.md changes. No renaming of the roadmap file (its `2026-04-15` date still reflects its creation date; content updates are tracked in git history).

## Edits to the roadmap

### Section: Resolved decisions (line 10)

Replace the `Dependency:` bullet with a permanent-dependency phrasing:

- From: `Start on PFR for entropy; progressively extract/reimplement just the needed subset into a local ZhangYeung/Entropy/ module, then drop the PFR dep.`
- To: `Permanent PFR dependency for Shannon entropy primitives. Pinned-rev in lakefile.toml; upgrades are deliberate, not scheduled.`

### Section 2.3 (PFR project), ~line 74

Keep the factual description, but drop the implicit "only this subtree matters for extraction" framing. Rephrase the last sentence so "relevant" means "imported," not "candidate for local copy":

- From: `Only the ForMathlib/Entropy/ subtree (~4-6 files) is relevant.`
- To: `Only the ForMathlib/Entropy/ subtree is imported; the remainder is carried by the dependency but unused.`

### Section 3 (Architecture), lines 94-119

Retitle and collapse to a single strategy. Remove Phases 2 and 3 entirely.

- Replace heading `### Resolved strategy: bootstrap on PFR, extract progressively` with `### Resolved strategy: permanent PFR dependency`.
- Remove the Phase 1 / Phase 2 / Phase 3 structure; keep the single paragraph describing the pinned-rev PFR dep and the imported subset.
- Remove the `Optional bridge` paragraph (shannon-entropy ↔ PFR bridge). This stays on the extensions list in Section 9 item 8.

### Section 5 (File Layout), lines 136-154

Delete the `Entropy/` subtree block and its "(phase 2) extracted/reimplemented Shannon layer" comment. The layout ends after `Theorem5.lean` and `test/`.

### Section 6 (Milestone-by-Milestone Plan)

1. **Dependency graph** (lines 159-179): remove the `M6` node and the `M1 -----> M6` arrow. Graph ends at `M7 (polish)` flowing from `M5`.
2. **Parallelism analysis** (lines 181-191): strike the bullet "M6 (entropy extraction) is fully independent..." and its surrounding paragraph. Rewrite the Worktree B description to be just `M4 part (a) (Shannon cone definition and constraint verification), merging with Worktree A once M3 lands to close M4 part (b).`
3. **M6 section** (lines 245-253): delete the entire `### M6: Entropy extraction (parallel)` block.
4. **M7 section** (line 256): renumber to `M6`. Update the final release bullet from `Tag v0.1 once M0-M4 land; v0.2 if M5+M6 complete.` to `Tag v0.1 once M0-M4 land; v0.2 once M5 lands.`

### Section 7 (Risks)

1. **7.1 PFR API churn**: change mitigation from `... M6 (extraction) is the long-term fix.` to `... treat upgrades as deliberate work scheduled alongside feature milestones.`
2. **7.3 PFR build weight**: change mitigation from `M6 (extraction) is the fix. Meanwhile, Mathlib cache from lake exe cache get should keep incremental builds fast.` to `Mathlib cache from lake exe cache get and the CI elan/lake caches keep incremental builds fast; PFR itself compiles once per dependency-rev bump.`

### Section 10 (Critical Files)

Remove the line `ZhangYeung/Entropy/{Basic,MutualInfo,ShannonInequalities}.lean (M6 extraction)` from the "New" list. The "External" list already documents PFR imports correctly; no change there.

### Section 11 (Note on Stray Artifact)

Already resolved: the file was moved to `docs/research/post-zhang-yeung-extension-survey.md` (verified by `ls docs/research/`). Delete the entire Section 11.

## What is *not* changing

- **Scope** (Section 4): S2 + Theorem 5 stretch remains. M1-M5 and the copy-lemma focus are unchanged.
- **Copy-lemma Mathlib-readiness**: still designed for upstream per Section 2.1 / Section 9 item 1. Depending on PFR does not block that; the copy lemma builds on `Kernel.compProd`, `condDistrib`, `CondIndepFun`, `IdentDistrib`, all already in Mathlib.
- **Extensions list** (Section 9 item 8): the shannon-entropy bridge lemma remains listed as optional post-release work.
- **CI performance plan**: untouched.
- **M0 plan**: stays in `done/`, untouched.

## Critical files (read-only for context)

- `docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md` (target of all edits)
- `docs/plans/done/2026-04-15-m0-project-scaffolding.md` (confirms M0 is complete and already PFR-compatible)
- `docs/plans/todo/2026-04-15-ci-performance-improvements.md` (confirmed unaffected)
- `CLAUDE.md` (confirmed unaffected — already describes permanent PFR dependency)
- `lakefile.toml` (confirmed unaffected — PFR pinned at `80daaf1`)

## Verification

After edits:

1. `grep -nE 'M6|extract|extraction|Entropy/|shed PFR|Phase [23]' docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md` returns only legitimate hits (the `ForMathlib/Entropy/` PFR import path, "extensions" in Section 9, and nothing milestone-related).
2. `grep -n 'Stray Artifact' docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md` returns no matches.
3. Dependency graph in Section 6 ends at `M7 (polish)` (or `M6 (polish)` after renumbering), with no reference to entropy extraction.
4. Read the full file top-to-bottom once; confirm narrative consistency — no leftover sentences assuming a later PFR removal.
5. No build, lint, or CI changes are required; no Lean files are touched, so `bin/bootstrap-worktree` and `lake build ZhangYeung` do not need to be re-run for this plan.
