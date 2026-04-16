# References

External papers referenced by the Zhang-Yeung formalization.

## Layout

```
references/
  papers/           Source PDFs, committed alongside the transcription that cites them.
  extractions/      Extractions of the source PDFs (one file per tool, `.txt` for layout/OCR tools and `.md` for ML tools whose output is Markdown with LaTeX). Regenerable, committed for reproducibility.
  transcriptions/   Markdown transcriptions with YAML frontmatter pointing back to papers.bib.
  papers.bib        BibTeX entries keyed by author-year identifiers used across the project.
```

Cite entries by their BibTeX key in Lean docstrings via the `[@key]` syntax expected by Mathlib's documentation conventions (the canonical bibliography file for Lean citations is `docs/references.bib`; this project keeps both views in sync).

## Regenerating an extraction

Each extraction file is suffixed with the tool that produced it. The math in IEEE papers of this vintage is set in Type 3 fonts with no `ToUnicode` map, so no layout-based extractor can recover the equation content: pdftotext, pymupdf, pdfminer, and pdfplumber all silently drop it. Rendering the pages and running classical OCR (Tesseract) recovers the equation shapes but transliterates symbols into visually similar Latin-1 glyphs. Only ML-based academic-paper extractors (marker) recover the math in machine-readable LaTeX. Keeping one file per tool makes the complementary failure modes visible.

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

Tesseract on rendered pages captures the equation shapes: Theorem 3, Lemma 2, and the basic inequality (8) come through as recognisable prose. The cost is that Greek letters and math operators are transliterated into visually similar Latin-1 and currency glyphs (`α` → `a`, `Γ` → `T` or `[`, `∈` → `€`, `≥` → `>`, `⊕` → `©`), so the output reads like a first-pass draft and should never be used verbatim. It is most useful as a cross-check against the human transcription.

```sh
uv run --with marker-pdf python -c '
import sys
from marker.converters.pdf import PdfConverter
from marker.models import create_model_dict
from marker.output import text_from_rendered
converter = PdfConverter(artifact_dict=create_model_dict())
rendered = converter(sys.argv[1])
text, _, _ = text_from_rendered(rendered)
sys.stdout.write(text)
' references/papers/<source>.pdf > references/extractions/<key>.marker.md
```

Marker is an ML-based academic-paper extractor (layout detection + OCR + equation recognition) whose output is Pandoc-flavoured Markdown with LaTeX math. For this PDF it recovers the core result (Theorem 3, eq. 21) and Lemma 2's eq. 45 as proper LaTeX: `$\Delta(Z, U|X, Y) \le \tfrac{1}{2} [I(X; Y) + \dots]$` and so on. This is the only extraction suitable as a first-pass Pandoc-Markdown transcription rather than a cross-check. Known failure modes: inline math embedded in prose is sometimes dropped (sentences lose variables), and section numbering occasionally drifts. On Apple Silicon, set `TORCH_DEVICE=cpu` to avoid [datalab-to/surya#490](https://github.com/datalab-to/surya/issues/490) (`torch.AcceleratorError` in `unpack_qkv_with_mask`, fixed by the open PR [#493](https://github.com/datalab-to/surya/pull/493)); CPU runtime is roughly four minutes for a 13-page paper.

Transcriptions flag layout-extractor gaps with `> **Transcription caveat.**` admonitions. These should be resolved against the source PDF, the tesseract extraction, or the marker extraction before the corresponding statement is formalised.

## Current entries

| Key | Paper | Transcription |
| --- | --- | --- |
| `zhangyeung1998` | Zhang and Yeung, *On Characterization of Entropy Function via Information Inequalities*, IEEE TIT 44(4), 1998 | [zhangyeung1998.md](transcriptions/zhangyeung1998.md) |
| `zhangyeung1997` | Zhang and Yeung, *A Non-Shannon Type Conditional Inequality of Information Quantities*, IEEE TIT 43(6), 1997 | Bibliography only (not formalized) |
| `yeung1997framework` | Yeung, *A Framework for Linear Information Inequalities*, IEEE TIT 43, 1997 | Bibliography only (context for $\Gamma_n$, $\Gamma^*_n$) |
