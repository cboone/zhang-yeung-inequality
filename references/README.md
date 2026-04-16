# References

External papers referenced by the Zhang-Yeung formalization.

## Layout

```
references/
  papers/           Source PDFs, committed alongside the transcription that cites them.
  extractions/      Plain-text extractions of the source PDFs (one file per tool). Regenerable, committed for reproducibility.
  transcriptions/   Markdown transcriptions with YAML frontmatter pointing back to papers.bib.
  papers.bib        BibTeX entries keyed by author-year identifiers used across the project.
```

Cite entries by their BibTeX key in Lean docstrings via the `[@key]` syntax expected by Mathlib's documentation conventions (the canonical bibliography file for Lean citations is `docs/references.bib`; this project keeps both views in sync).

## Regenerating an extraction

Each extraction file is suffixed with the tool that produced it. Both tools drop math glyphs on two-column IEEE papers, but they fail differently and are useful to compare.

```sh
pdftotext -layout references/papers/<source>.pdf references/extractions/<key>.pdftotext.txt
```

`pdftotext -layout` normalises ligatures to ASCII (`deﬁned` → `defined`) and leaves `U+FFFD` replacement markers where glyphs fail to decode, which flags the gaps visually.

```sh
uv run --with pymupdf python -c '
import sys, pymupdf
doc = pymupdf.open(sys.argv[1]); n = doc.page_count
with open(sys.argv[2], "w") as f:
    for i, p in enumerate(doc, 1):
        f.write(f"<PAGE {i} / {n}>\n{p.get_text()}\n")
' references/papers/<source>.pdf references/extractions/<key>.pymupdf.txt
```

`pymupdf` preserves ligatures as Unicode (`ﬁ`, `ﬂ`) and diacritics on author names, and emits no replacement markers, at the cost of silently dropping math glyphs entirely (so sentences lose variables instead of flagging them).

Two-column IEEE papers typically lose equation bodies in every extraction (only equation numbers survive). Transcriptions flag such gaps with `> **Transcription caveat.**` admonitions, which must be resolved against the source PDF before the corresponding statement is formalized.

## Current entries

| Key | Paper | Transcription |
| --- | --- | --- |
| `zhangyeung1998` | Zhang and Yeung, *On Characterization of Entropy Function via Information Inequalities*, IEEE TIT 44(4), 1998 | [zhangyeung1998.md](transcriptions/zhangyeung1998.md) |
| `zhangyeung1997` | Zhang and Yeung, *A Non-Shannon Type Conditional Inequality of Information Quantities*, IEEE TIT 43(6), 1997 | Bibliography only (not formalized) |
| `yeung1997framework` | Yeung, *A Framework for Linear Information Inequalities*, IEEE TIT 43, 1997 | Bibliography only (context for $\Gamma_n$, $\Gamma^*_n$) |
