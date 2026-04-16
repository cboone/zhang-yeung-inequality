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

Each extraction file is suffixed with the tool that produced it. The math in IEEE papers of this vintage is set in Type 3 fonts with no `ToUnicode` map, so no layout-based extractor can recover the equation content: pdftotext, pymupdf, pdfminer, and pdfplumber all silently drop it. Rendering the pages and running OCR is the only way to get the math back, and even then the symbols come out transliterated rather than as proper Unicode. Keeping one file per tool makes the complementary failure modes visible.

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

```sh
uv run --with pymupdf python -c '
import sys, pathlib, pymupdf
doc = pymupdf.open(sys.argv[1])
out = pathlib.Path("/tmp/pages"); out.mkdir(exist_ok=True)
for i, p in enumerate(doc):
    p.get_pixmap(dpi=300).save(str(out / f"p{i+1:02d}.png"))
' references/papers/<source>.pdf
for p in /tmp/pages/p*.png; do
  tesseract "$p" "${p%.png}" --oem 1 -l eng
done
{ for i in $(seq -f %02g 1 13); do
    printf '<PAGE %d / 13>\n' "${i#0}"
    cat "/tmp/pages/p${i}.txt"
    echo
  done
} > references/extractions/<key>.tesseract.txt
```

Tesseract on rendered pages is the only extraction that captures any equation content at all: Theorem 3, Lemma 2, and the basic inequality (8) come through as recognisable prose. The cost is that Greek letters and math operators are transliterated into visually similar Latin-1 and currency glyphs (`α` → `a`, `Γ` → `T` or `[`, `∈` → `€`, `≥` → `>`, `⊕` → `©`), so the output reads like a first-pass draft and should never be used verbatim. It is most useful as a cross-check against the human transcription.

Transcriptions flag layout-extractor gaps with `> **Transcription caveat.**` admonitions. These should be resolved against either the source PDF or the tesseract extraction before the corresponding statement is formalised.

## Current entries

| Key | Paper | Transcription |
| --- | --- | --- |
| `zhangyeung1998` | Zhang and Yeung, *On Characterization of Entropy Function via Information Inequalities*, IEEE TIT 44(4), 1998 | [zhangyeung1998.md](transcriptions/zhangyeung1998.md) |
| `zhangyeung1997` | Zhang and Yeung, *A Non-Shannon Type Conditional Inequality of Information Quantities*, IEEE TIT 43(6), 1997 | Bibliography only (not formalized) |
| `yeung1997framework` | Yeung, *A Framework for Linear Information Inequalities*, IEEE TIT 43, 1997 | Bibliography only (context for $\Gamma_n$, $\Gamma^*_n$) |
