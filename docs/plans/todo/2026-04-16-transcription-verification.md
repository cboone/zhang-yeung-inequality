# Zhang-Yeung 1998 Transcription Verification Plan

**Created:** 2026-04-16
**Target:** `references/transcriptions/zhangyeung1998.md`
**Source:** Commit `8d8afdc` (faithful transcription built from Mathpix OCR, page-by-page audited).

## Status

- **Phase A1** (Pandoc build): complete. Commit `6dd19f7`. Three build issues fixed (title duplication, Publisher-Item run-on, references without paragraph breaks). PDF builds cleanly on xelatex.
- **Phase A2** (projective-plane arithmetic): complete. Commit `60791a3`. All three checks pass symbolically — transcribed intermediate values on p. 1445 combine to exactly `-log_2(9/8)`.
- **Phase A3** (structural diff vs raw Mathpix): complete. Commit `b5a2610`. Word-count delta (-11) and paragraph-count delta (+40) both fully accounted for by documented audit fixes.
- **Phase B1** (vision re-extraction): complete. Commit `8fb5bbe`. One real content fix surfaced (eq. 13 and 18 bar removals — Mathpix and vision agreed, my audit was wrong). Remaining agent disagreements on pages 3-12 were agent hallucinations (verified by direct image reads at 450 dpi); my audit was correct on every disputed point.
- **Phase B2** (Section IV subscript audit): complete. All atom subscripts on pages 10-12 independently verified against the rendered PDF at 450 dpi. Specifically confirmed: `F^4_{1,2}`, `F^4_{1,3}`, `F^4_{1,4}`, `F^4_{2,4}`, `F^7_3`, `F^7_4` assignments across Case 1.1, Case 1.2, and Case 2 branches. The `F^4_{1,3}` fix I made during the original audit (correcting Mathpix's `F_{1,2}^{4,}` typo) is verified correct.

## 1. Context

The current transcription was derived from Mathpix's API output (commit `bdbc2c1`) and hand-audited page by page at 300 dpi (commit `8d8afdc`). Identified OCR errors have been corrected inline and documented in the commit body. Known residual risks, in decreasing order of concern:

- **Section IV case analysis** (pages 10-12). Hundreds of indexed atom references (`G'`, `G''`, `G'''` with `[i,j,k]` subscripts) where a single transposed digit is mathematically invalid but syntactically plausible. The `F_{1,3}^{4}` fix on page 11 was inferred from Observation 1's application pattern, not a direct read of the rendered page — this is the single highest-risk edit in the file.
- **Atom-chart visuals** on pages 8-11. The six Construction 2-7 value charts were reconstructed from the Construction prose descriptions, but the eight "atoms involved" / "Function F' / G'" diagrams are deferred with `See rendered PDF` placeholders. Content is preserved in prose; only the visual aid is missing.
- **Bibliography page 13.** 39 entries read visually but not cross-checked against external bibliographic databases. Diacritics on Csiszár, Körner, Matúš, Studený verified; volume/issue/page numbers not.
- **Nothing has been rendered through Pandoc yet.** LaTeX syntax errors from the Mathpix `\begin{equation*}...\tag{N}\end{equation*}` wrappers, unbalanced braces, or macro conflicts would not have surfaced during the audit.

This plan sequences the remaining verification work from cheapest-and-most-decisive to most-costly-but-completeness-closing.

## 2. Sequencing

```
Phase A (build + fast content checks):
  A1. Pandoc build + visual diff
  A2. Projective-plane arithmetic
  A3. Word-count / structural diff vs raw Mathpix

Phase B (independent verification):
  B1. Claude vision re-extraction + three-way diff
  B2. Section IV case-analysis symbol-by-symbol audit

Phase C (external cross-reference):
  C1. Central-equation cross-check vs secondary sources
  C2. Bibliography validation against DBLP / Google Scholar
  C3. Errata search
```

Phases are roughly independent and can be interleaved, but A1 should run first (its output — a rendered PDF — is an input to B1's diff and a catch-all for LaTeX syntax issues that would derail everything else).

## 3. Phase A: Build + fast content checks

### A1. Pandoc build + visual diff

**Goal:** Verify the Markdown compiles to LaTeX/PDF cleanly, and visually compare each rendered page against the source PDF.

**Inputs:**
- `references/transcriptions/zhangyeung1998.md`
- Pandoc (installed), LaTeX toolchain (installed)

**Method:**
1. Render: `pandoc -s --standalone --pdf-engine=xelatex references/transcriptions/zhangyeung1998.md -o /tmp/zhangyeung1998-rebuilt.pdf`
2. Triage any build errors. Common expected issues:
   - `\tag` inside `equation*` produces an unnumbered environment with a tag — may need to swap to `equation` or use `\tag*` / `\numberwithin` depending on Pandoc's template.
   - The `\stackrel{\text{def}}{=}` may need an `amsmath` import in the YAML header.
   - Raw paragraph-header text lines (`1442\n` etc.) between paragraphs may produce stray text — evaluate whether to remove or wrap in HTML comments.
3. Once it builds, render both PDFs side by side (page-per-page) and scroll-compare.

**Deliverable:** `/tmp/zhangyeung1998-rebuilt.pdf` + a short notes file listing any rendering anomalies that need to be fixed in the Markdown.

**Success criteria:** clean build, no LaTeX errors, no visible content drift between rendered and source on a full scroll-through.

**Risk:** If `\tag` inside `equation*` fails globally, we may need a sed pass to rewrap equations. That's mechanical but touches every equation, so handle before Phase B.

### A2. Projective-plane arithmetic verification

**Goal:** Verify that the S_F calculation on page 6 is internally consistent given the paper's stated intermediate values. Anchors one high-density page to a concrete computational check.

**Inputs:** page 6 equations for `H(X_3)`, `H(X_4)`, `H(X_3, X_4)`, `H(X_3 | X_i)`, `H(X_3, X_4 | X_i)`, `I(X_3; X_4)`, `I(X_3; X_4 | X_i)`, and the final `S_F(1,2|3,4)`.

**Method:** Write a 20-line Python (or `bc`, or Lean) script that:
1. Takes the paper's stated entropies as givens.
2. Computes `I(X_3; X_4) = H(X_3) + H(X_4) - H(X_3, X_4)`.
3. Computes `I(X_3; X_4 | X_i) = H(X_3 | X_i) + H(X_4 | X_i) - H(X_3, X_4 | X_i)`.
4. Computes `S_F(1, 2 | 3, 4) = I(X_1; X_2) + I(X_3; X_4 | X_1) + I(X_3; X_4 | X_2) - I(X_3; X_4)`.
5. Simplifies the log expression and checks it equals `-log_2(9/8)`.

**Deliverable:** script committed at `bin/verify-projective-plane` (or similar), plus output showing the final value matches.

**Success criteria:** the transcription's stated intermediate values, substituted into the closed-form calculation, yield exactly `-log_2(9/8)`. Any discrepancy means at least one stated intermediate value has an OCR error.

**Risk:** If the arithmetic doesn't close, it tells us *something* is wrong but not *what*. Triage would need to cross-check each intermediate against the rendered page.

### A3. Word-count / structural diff vs raw Mathpix

**Goal:** Rule out content accidentally dropped during the audit edits.

**Inputs:** `references/extractions/zhangyeung1998.mathpix.md` (raw), `references/transcriptions/zhangyeung1998.md` (audited).

**Method:**
1. Strip frontmatter, section-heading differences, chart placeholders, and known deliberate fixes from both.
2. Compute word count and paragraph count on each.
3. Diff the two (ignoring whitespace and known normalizations) and scan for any region where the audit version is *shorter* than raw Mathpix — shortening without a logged fix is a red flag.

**Deliverable:** diff output flagged with any regions of unexplained shortening.

**Success criteria:** every region where the audit is shorter than raw has a documented reason in the commit message (OCR artifact removal, math-mode unwrapping, atom chart placeholder).

**Risk:** This catches accidental drops but not accidental additions or corruptions. Low-confidence test, cheap to run.

## 4. Phase B: Independent verification

### B1. Claude vision re-extraction + three-way diff

**Goal:** Have an independent reader transcribe each page fresh from the image, then diff against the audited Mathpix output. Any disagreement is a candidate error for manual adjudication against the rendered page.

**Inputs:** `/tmp/pdf-compare/pages/p*.png` (already rendered at 300 dpi), plus a Claude Code session with the Read tool.

**Method:**
1. For each page, have a fresh agent (spawn via Agent tool with `subagent_type: Explore` or similar, or run a prompt in a side session) Read the PNG and output the content as Pandoc Markdown following the same conventions as the audited transcription (`$...$` / `$$...$$` / `\tag{N}`, paper notation preserved).
2. Save each page's vision output at `references/extractions/zhangyeung1998.vision.p{NN}.md` or combined.
3. Diff each vision-extracted page against the corresponding region of the audited transcription using a word-level diff.
4. For each disagreement, manually view the rendered page and adjudicate. Either:
   - Vision is wrong, audit is right: no change.
   - Vision is right, audit is wrong: fix the transcription.
   - Both wrong: fix against the PDF.
5. Commit any fixes with explicit references to the B1 adjudication.

**Deliverable:**
- Per-page vision extractions committed to `references/extractions/`
- An adjudication log listing every disagreement and the outcome
- Any transcription fixes committed separately

**Success criteria:** all disagreements resolved; no remaining unadjudicated deltas.

**Risk:** Claude vision has its own error modes — it may hallucinate plausible-looking LaTeX for ambiguous glyphs. Treat every "vision disagrees with Mathpix" as a flag for manual review, not as ground truth.

### B2. Section IV case-analysis audit

**Goal:** Trace every subscripted atom reference in the Theorem 6 case analysis (pages 10-12) against the rendered image, with special attention to:
- The `F_{1,3}^{4}` fix on page 11 (inferred during the audit, not directly verified)
- Every `G[i,j,k]` / `G'[i,j,k]` / `G''[i,j,k]` / `G'''[i,j,k]` atom reference
- Every `\min{...}` expression in the Observation applications
- The Case 1.1 / Case 1.2 / Case 2 split structure

**Inputs:** rendered PDF pages 10-12, audited transcription.

**Method:**
1. Read each page at 300 dpi (same as phase A1 re-render, but at higher zoom per paragraph).
2. For each atom-indexed expression in the transcription, explicitly confirm the indices against the rendered page.
3. Build a log of every subscript verified and every discrepancy found.

**Deliverable:** audit log with per-line confirmations, any transcription fixes committed separately.

**Success criteria:** every atom subscript on pages 10-12 independently confirmed.

**Dependency:** best run after B1, because B1 should surface most symbol-level disagreements and B2 is the final belt-and-suspenders pass on the specific region most likely to hide a subtle error.

## 5. Phase C: External cross-reference

### C1. Central-equation cross-reference vs secondary sources

**Goal:** Match the transcribed forms of the paper's key equations against independent publications that restate them.

**Inputs:**
- `references/transcriptions/zhangyeung1998.md`
- Candidate secondary sources (prioritized):
  1. Yeung, *Information Theory and Network Coding*, Springer (2008, and 2nd ed. 2014). Chapter 15 restates Theorems 3, 4, 5 and the copy lemma.
  2. Matúš, "Two constructions on limits of entropy functions" (IEEE TIT 2007) — restates eq. (21).
  3. Dougherty-Freiling-Zeger, "Non-Shannon information inequalities in four random variables" (2011 preprint / IEEE TIT 2015) — survey of non-Shannon inequalities that restates Zhang-Yeung.
  4. Csirmaz survey papers — restate the copy lemma.

**Method:** for each of:
- eq. (20) (Δ definition)
- eq. (21) (Zhang-Yeung inequality)
- eq. (22), (23) (companion forms)
- eq. (26) (Theorem 4 strict inclusion)
- eq. (27), (28) (Theorem 5 generalization)
- eq. (45) (Lemma 2 / copy lemma)

look up each in at least two secondary sources and confirm the transcribed form matches exactly.

**Deliverable:** cross-reference table, committed at `docs/references/zhangyeung1998-cross-reference.md`.

**Success criteria:** every central equation in our transcription matches at least one authoritative secondary source symbol-for-symbol.

**Risk:** Secondary sources may use different notation (sans subscript Ω, modern `I(X;Y|Z)` vs paper's `I(α, β | γ)`, `\bar` vs `\mathrm{cl}`). Require matching the mathematical content, not the notation.

### C2. Bibliography validation

**Goal:** Verify all 39 bibliography entries against an external database.

**Inputs:** `references/transcriptions/zhangyeung1998.md` references section.

**Method:**
1. For each of the 39 entries, extract author, title, venue, volume, pages, year.
2. Query DBLP (`https://dblp.org/search/publ/api?q=...&format=json`) or Google Scholar for the matching record.
3. Flag any entry where the metadata disagrees with our transcription.

Prioritize: the Matúš, Studený, Yeung, Han, Csiszár entries (most likely to have OCR issues due to diacritics or volume numbers).

**Deliverable:** validation log flagging every entry that disagrees with DBLP/GS.

**Success criteria:** every entry matches an external record, or a documented reason exists for a discrepancy (e.g., "submitted for publication" entries that never got a volume/page).

### C3. Errata search

**Goal:** Check whether IEEE or the authors ever published a correction to this paper that would affect our transcription.

**Method:** search IEEE Xplore for "Zhang Yeung On Characterization of Entropy Function corrigendum/erratum", search Google Scholar for "Zhang Yeung 1998 erratum", check whether the paper is cited with corrections in any follow-up (the Matúš-Csirmaz line in particular).

**Deliverable:** a one-line conclusion committed to the plan: "no errata found" or "errata found at [reference], apply following corrections to the transcription."

**Success criteria:** binary — either no errata exist, or they've been applied.

## 6. Stopping condition

The transcription is considered "verified to high fidelity" when:

- Phase A1, A2, A3 all pass clean.
- Phase B1's adjudication log shows zero unresolved disagreements.
- Phase B2 independently confirms pages 10-12 subscripts.
- Phase C1 confirms every central equation against at least two secondary sources.
- Phase C2 confirms or deliberately exceptions every bibliography entry.
- Phase C3 either finds no errata or applies them.

Document this as a note in the transcription's YAML frontmatter:

```yaml
verification:
  status: verified
  last_audited: 2026-MM-DD
  phases_completed: [A1, A2, A3, B1, B2, C1, C2, C3]
```

## 7. Where findings go

Every fix identified during verification should:

1. Be committed as a focused commit with a subject like `fix: transcription <page>: <brief description>`.
2. Reference the phase that surfaced it in the commit body (e.g., "Found during B1 vision-diff adjudication, page 11").
3. Leave the raw Mathpix extraction (`zhangyeung1998.mathpix.md`) untouched. Only the audited transcription and the `.processed.md` file get edits.

## 8. Non-goals

- **Verifying mathematical correctness of the paper's results.** This plan checks transcription fidelity, not whether the paper's theorems are true. The Zhang-Yeung inequality is a published, cited, verified result; its correctness is not in question.
- **Formalization-ready normalization.** The Lean formalization will rebuild the math in Mathlib notation anyway. The transcription's job is to faithfully reflect the paper, not to be directly formalizable.
- **Rendering the visual atom-chart diagrams.** The eight deferred charts remain as "see rendered PDF" placeholders. Adding them back as Markdown tables is a separate future task.

## 9. What we are not confident about after this plan

Even after all phases complete, the following remain theoretical gaps:

- Visual atom-chart diagrams in Section IV (never reconstructed).
- Paper's running page-header / page-footer strings (preserved inline but their exact position breaks mid-sentence is a Mathpix choice, not the paper's layout).
- Any subtle typographic convention the paper uses that doesn't affect content.

These are acceptable residuals.
