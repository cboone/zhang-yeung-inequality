# References

Source PDF and transcription for the Zhang-Yeung 1998 paper that this repository formalizes.

## Layout

```
references/
  papers/          Source PDF.
  transcriptions/  Verified Pandoc-flavoured Markdown transcription with LaTeX math.
  papers.bib       BibTeX entries keyed by author-year identifiers used across the project.
```

Cite entries by their BibTeX key in Lean docstrings via the `[@key]` syntax expected by Mathlib's documentation conventions (the canonical bibliography file for Lean citations is `docs/references.bib`; this project keeps both views in sync).

## Transcription

`transcriptions/zhangyeung1998.md` is a verbatim transcription of the paper's prose and math, built from a Mathpix OCR extraction and audited page by page against the rendered PDF at 300 dpi. The transcription's YAML frontmatter records its verification status. The equation-numbered blocks use `\begin{equation*}...\tag{N}\end{equation*}` wrappers and Pandoc math delimiters (`$...$` inline, `$$...$$` display), so it builds cleanly through Pandoc to LaTeX.

PDF extraction tools, the Mathpix submission script, verification helpers (Pandoc build, projective-plane arithmetic, structural diff), and the multi-phase verification procedure live in the strength-model repository, not here.

## Current entries

| Key | Paper | Materials |
| --- | --- | --- |
| `zhangyeung1998` | Zhang and Yeung, *On Characterization of Entropy Function via Information Inequalities*, IEEE TIT 44(4), 1998 | [zhangyeung1998.md](transcriptions/zhangyeung1998.md) |
| `zhangyeung1997` | Zhang and Yeung, *A Non-Shannon Type Conditional Inequality of Information Quantities*, IEEE TIT 43(6), 1997 | Source PDF at [zhangyeung1997.pdf](papers/zhangyeung1997.pdf); primary reference for the M1.5 Theorem 2 proof via KL divergence |
| `yeung1997framework` | Yeung, *A Framework for Linear Information Inequalities*, IEEE TIT 43, 1997 | Bibliography only (context for $\Gamma_n$, $\Gamma^*_n$) |
| `yeung2008` | Yeung, *Information Theory and Network Coding*, Springer, 2008 | Bibliography only (cross-reference for Theorem 3 and the copy lemma) |
