---
title: "Align Delta module citations with verified transcription"
created: 2026-04-16
branch: formalize/delta-equational-lemmas
supersedes_refs: docs/plans/done/2026-04-15-delta-equational-lemmas.md (M1 plan; still load-bearing, only citation wording changes)
---

## Context

Main recently completed a multi-phase verification pass over `references/transcriptions/zhangyeung1998.md` (frontmatter `verification.status: verified`, `last_audited: 2026-04-16`) and then pared the references tree down to just the source PDF, the verified transcription, and the BibTeX entries. As part of that cleanup (commit `a54d3d4`), the Phase C1 cross-reference document (`docs/references/zhangyeung1998-cross-reference.md`) was removed after its conclusions were folded into the transcription's verified status. The transcription is now the single authoritative mathematical reference for this project, and `references/README.md` sets a project convention for how Lean docstrings should cite it (`[@key]` Mathlib-style, keys lowercase).

The work on this branch (milestone M1: delta equational lemmas) predates that verification push. A line-by-line cross-check against the now-authoritative transcription confirms that every equation encoded in `ZhangYeung/Delta.lean` is mathematically correct:

- `delta_def` encodes transcription eq. (20) (line 294) verbatim.
- `form21_iff` (after multiplying the `Δ ≤ …` form by 2) encodes transcription eq. (21) (lines 302-303) verbatim.
- `form22_iff` encodes transcription eq. (22) (lines 311-312) verbatim.
- `form23_iff` encodes transcription eq. (23) (line 323) verbatim.
- `delta_eq_entropy`, `delta_comm_main`, `delta_comm_cond`, `delta_self`, `delta_le_mutualInfo` are all algebraic consequences with no counterpart to check against the paper's prose beyond the definition itself.

No mathematical content needs to change. What does need to change is a small amount of citation prose: the Delta module docstring predates the project's citation convention and does not point readers at the verified transcription, and the M1 plan and the overarching roadmap reference "the paper" as if the PDF were the only canonical artifact. This plan tightens those references.

## Scope: citation and pointer alignment only

Three small edits, no Lean API changes, no re-proofs:

### 1. `ZhangYeung/Delta.lean` module docstring

The current module docstring uses `[ZhangYeung1998]` (CamelCase) inline and then duplicates the bibliographic entry in a handwritten `## References` section. The project convention (per `references/README.md`) is `[@zhangyeung1998]` (lowercase, `@`-prefixed), matching Mathlib's documentation style and the BibTeX key in `references/papers.bib`.

Changes:

- Replace the inline `[ZhangYeung1998]` (around line 10 of `ZhangYeung/Delta.lean`) with `[@zhangyeung1998]`.
- Replace the handwritten bibliographic entry under `## References` (lines 33-35) with the Mathlib-style short form:
  ```
  ## References

  * [@zhangyeung1998] — see `references/transcriptions/zhangyeung1998.md` for a verbatim transcription of the paper's equations (20)-(23), verified 2026-04-16.
  ```

Rationale: one authoritative pointer at the verified transcription beats a handwritten duplicate of the bibliography. Future contributors checking whether `form2N_iff` matches the paper should land on the transcription directly.

### 2. `docs/plans/done/2026-04-15-delta-equational-lemmas.md` (M1 plan)

The M1 plan currently cites the paper's equation numbers without pointing readers at the verified transcription. Add a one-line "Primary reference" note near the top (after the `## Context` section), for example:

```
**Primary reference:** `references/transcriptions/zhangyeung1998.md` (verified 2026-04-16); citations below use equation numbers from that transcription.
```

No other changes. The rest of the plan's equation-number references remain correct.

### 3. `docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md`

The roadmap preamble (lines 1-7) records `**Source PDF:**` but not the transcription. Add a sibling entry:

```
**Source transcription:** `references/transcriptions/zhangyeung1998.md` (verified 2026-04-16)
```

on a new line immediately after the `**Source PDF:**` line. No other changes; the section on architecture, milestone plan, and verification rules remains intact.

## What explicitly stays the same

- Every `lemma` signature in `ZhangYeung/Delta.lean` and `ZhangYeungTest/Delta.lean`.
- All proof scripts.
- The `variable` block and the finite-alphabet specialization.
- Every per-lemma docstring in `Delta.lean` (the `eq. (21)` / `eq. (22)` / `eq. (23)` references already match the transcription).
- The M1 sequencing and test-coverage requirements.
- The roadmap's milestone structure and Milestone-level Testing Requirements.

## Critical files

- `ZhangYeung/Delta.lean` (module docstring only; see section 1 above).
- `docs/plans/done/2026-04-15-delta-equational-lemmas.md` (single `Primary reference` line near the top; see section 2).
- `docs/plans/todo/2026-04-15-zhang-yeung-formalization-roadmap.md` (single `Source transcription:` line in the preamble; see section 3).

## Verification

- `lake build ZhangYeung` still succeeds (docstring-only change cannot break the build, but run it anyway to catch any `[@zhangyeung1998]` parsing issue in Mathlib's docstring linter).
- `lake build ZhangYeungTest` still succeeds (no API surface change; tests are unaffected).
- `lake lint` passes; the `docBlame` / citation linters should be satisfied by the `[@zhangyeung1998]` form.
- Spot-check: open `ZhangYeung/Delta.lean` in the editor and confirm the `## References` section renders as a pointer to the transcription rather than a duplicated bibliographic entry.
- No `ZhangYeungTest` changes; the existing compile-time API tests already cover every lemma whose statement was reviewed.
