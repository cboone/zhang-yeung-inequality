---
title: "REUSE compliance, NOTICE, SPDX coverage, bibliography cleanup, and citation pass"
created: 2026-04-19
status: in_progress
scope: bounded repository-maintenance pass covering licensing metadata, bibliography normalization, and mathematical provenance citations.
depends_on: README.md and LICENSES/ license split updated on 2026-04-19 (`2569cb2 docs: update README and licenses`).
---

## Status

In progress. This plan drives a single implementation pass that (1) brings the repository into REUSE compliance, (2) adds a root `NOTICE` file matching the newly-updated license story, (3) normalizes `references/papers.bib` as the project's canonical bibliography, and (4) fills the remaining high-value mathematical citations in Lean docstrings.

## Goals

1. Add a root `NOTICE` file that explains the repository's license split and the main third-party / reference-material exceptions.
2. Add SPDX copyright and license identifiers to the files that need them under REUSE coverage rules, using inline headers where natural and sidecars only where required by file format.
3. Keep `references/papers.bib` as the canonical bibliography, clean up its metadata, and update all repo references that still point at the intended-but-nonexistent `docs/references.bib` path.
4. Add mathematical provenance citations where the public Lean docstrings describe externally sourced theorems, identities, or paper-numbered equation forms but currently omit an explicit citation.
5. End with a green `reuse lint`, `make lint`, `lake build ZhangYeung`, and `lake test`.

## Baseline Findings

From a baseline `reuse lint` run on 2026-04-19:

1. `LICENSES/APACHE-2.0.txt` is not recognized as a valid SPDX license file because the file basename does not match the SPDX identifier's case. Rename to `LICENSES/Apache-2.0.txt` and update links.
2. No project-authored source or documentation files currently carry SPDX tags.
3. The only files reported with missing license information rather than missing copyright-and-license blocks are:
   - `references/papers/zhangyeung1997.pdf`
   - `references/papers/zhangyeung1998.pdf`
   - `references/transcriptions/zhangyeung1998.md`
4. `references/README.md` already says the canonical bibliography file is `docs/references.bib`, but the actual repository uses `references/papers.bib`. This inconsistency must be removed in favor of the user's requested canonical path `references/papers.bib`.
5. `README.md` currently states only a Lean-code/prose split. It does not yet tell readers what license applies to the repository's non-Lean software/configuration files.
6. `CODE_OF_CONDUCT.md` is adapted from Contributor Covenant and cites CC BY-SA 4.0 in its own attribution section, so it must be treated as a third-party exception rather than folded into the repo's general CC BY 4.0 prose bucket.
7. `references/papers/.DS_Store` should be removed rather than annotated.

## Licensing Decisions To Encode

### Project-authored software / configuration

Use `Apache-2.0` for project-authored software and machine-consumed configuration, including:

- `ZhangYeung.lean`, `ZhangYeung/*.lean`
- `ZhangYeungTest.lean`, `ZhangYeungTest/*.lean`
- `bin/bootstrap-worktree`
- `Makefile`
- `lakefile.toml`
- `.github/workflows/*.yml`
- `.markdownlint-cli2.jsonc`
- `cspell.jsonc`
- `cspell-words.txt`
- `.vscode/*.json`
- `.editorconfig`
- `.gitignore`
- `lake-manifest.json`
- `lean-toolchain`

### Project-authored prose / mathematical exposition

Use `CC-BY-4.0` for project-authored prose and mathematical exposition, including:

- `README.md`
- `AGENTS.md`
- `CONTRIBUTING.md`
- `.github/SECURITY.md`
- `.github/PULL_REQUEST_TEMPLATE.md`
- `.github/copilot-instructions.md`
- `.github/lean.instructions.md`
- `references/README.md`
- `references/papers.bib`
- `docs/research/*.md`
- `docs/reviews/*.md`
- `docs/plans/todo/*.md`
- `docs/plans/done/*.md`
- `NOTICE`

### Third-party / special-case files

Handle explicitly and separately:

1. `CODE_OF_CONDUCT.md`: mark `CC-BY-SA-4.0` and add the matching license text under `LICENSES/CC-BY-SA-4.0.txt`.
2. `references/papers/*.pdf`: annotate with sidecar metadata reflecting that they are bundled reference papers under their own copyright, not relicensed project content.
3. `references/transcriptions/zhangyeung1998.md`: annotate explicitly after checking whether it should be treated as project-authored transcription prose under `CC-BY-4.0` or as a special reference artifact kept under a separate license expression.

## Coverage Strategy

### Inline SPDX headers

Use inline SPDX headers where the file syntax and repo conventions make them safe and readable:

- Lean files: file header comments before imports / module docstrings
- Shell / zsh scripts: after the shebang
- Markdown files without YAML frontmatter: HTML comment block at the top
- `Makefile`: `#` comments at top
- YAML / TOML / JSONC / `.editorconfig` / `.gitignore` / plain-text word lists: file-appropriate comment syntax at top
- BibTeX: `%` comments at top of `references/papers.bib`

### Sidecar `.license` files

Use sidecars where inline tags would be disruptive or unsupported:

- `docs/plans/**/*.md` if preserving YAML frontmatter as the first block is materially cleaner than inserting HTML comments above it
- `.github/lean.instructions.md` because it starts with YAML frontmatter consumed by tooling
- `lean-toolchain`
- `lake-manifest.json`
- `.vscode/*.json`
- reference PDFs
- any other file that `reuse lint` still reports after the inline pass

The bias is toward inline SPDX tags for ordinary source and prose files, and toward sidecars only for frontmatter-sensitive, commentless, or binary formats.

## Bibliography Cleanup Plan

Keep `references/papers.bib` as the canonical bibliography and normalize it in place.

### Immediate cleanup

1. Fix the `zhangyeung1998` metadata mismatch between `README.md` (currently linking DOI `10.1109/18.705560`) and `references/papers.bib` (currently `10.1109/18.681320`). Verify the correct DOI and make the bibliography and README agree.
2. Review capitalization protection, issue / page / DOI data, and note fields in the existing five entries:
   - `zhangyeung1998`
   - `zhangyeung1997`
   - `yeung1997framework`
   - `kaced2013`
   - `yeung2008`
3. Update all live references that still mention `docs/references.bib` so they instead point to `references/papers.bib`.
4. Update editor and lint tooling paths that currently assume `references/papers.bib` is just an auxiliary copy and not the canonical file.

### Scope expansion

Add BibTeX entries for papers already referenced in the repo's research and planning prose, prioritizing those in:

- `docs/research/post-zhang-yeung-extension-survey.md`
- `docs/plans/todo/2026-04-17-non-shannon-inequality-discovery-program.md`

This includes at least the Matús, DFZ, Chan-Yeung, Matveev-Portegies, Kinser, Boege, Tang, and PFR-adjacent references already named in those documents.

## Citation Pass Strategy

Add citations where public mathematical exposition benefits from provenance, but do not spray citations onto purely local helper statements.

### High-priority targets

1. Public theorem / definition docstrings in `ZhangYeung/Delta.lean` that refer to paper eqs. (21)-(23) without inline `[@zhangyeung1998]` citations.
2. Public copy-lemma theorem docstrings in `ZhangYeung/CopyLemma.lean` that describe eq. (44), Lemma 2, or paper-line identities without an explicit citation in the theorem docstring itself.
3. Remaining public theorem docstrings in `ZhangYeung/Theorem3.lean` whose statements are paper-numbered but only the surrounding module docstring carries the citation.
4. Any public-facing README / docs prose that references a paper by prose description alone but would be clearer and more maintainable with a bibliography key.

### Explicit non-goals

- No citations on local measurability helpers, transport lemmas, or test comments whose provenance is internal rather than bibliographic.
- No wholesale rewrite of already-good module docstrings purely for style.

## Commit Plan

The work should land as a sequence of small commits with verification between them:

1. `docs: add REUSE and citation implementation plan`
2. `docs(license): add NOTICE and fix license inventory`
3. `chore(reuse): add SPDX coverage for source and docs`
4. `docs(references): clean bibliography and update references`
5. `docs(citations): add provenance citations for public math content`
6. `chore: address verification fallout`

If the final shape suggests a cleaner split, preserve the same logical boundaries even if the exact commit subjects change.

## Verification

Run, in this order when the implementation is complete:

1. `reuse lint`
2. `make lint`
3. `lake build ZhangYeung`
4. `lake test`

If a smaller logical commit introduces a path change or SPDX syntax change likely to break tooling, run the relevant subset earlier as a guardrail.

## Exit Criteria

This task is complete when all of the following hold:

1. `reuse lint` reports a compliant repository.
2. `NOTICE` exists and matches the repository's actual license split.
3. `LICENSES/` contains every license text referenced by SPDX tags and no invalidly named SPDX license files.
4. `references/papers.bib` is the canonical bibliography, its metadata is cleaned up, and all live repo references point to it.
5. Public mathematical exposition has citations where provenance materially helps readers.
6. `make lint`, `lake build ZhangYeung`, and `lake test` all pass.
