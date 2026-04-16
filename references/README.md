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

Each extraction file is suffixed with the tool that produced it. The math in IEEE papers of this vintage is set in Type 3 fonts with no `ToUnicode` map, so no layout-based extractor can recover the equation content: pdftotext, pymupdf, pdfminer, and pdfplumber all silently drop it. Rendering the pages and running classical OCR (Tesseract) recovers the equation shapes but transliterates symbols into visually similar Latin-1 glyphs. Only ML-based academic-paper extractors (Mathpix, marker) recover the math in machine-readable LaTeX. Keeping one file per tool makes the complementary failure modes visible.

Mathpix is the current recommended extraction. Tools are listed below in the order they should be consulted.

### Mathpix (recommended)

```sh
export MATHPIX_APP_ID=...  # from ~/.config/shell/zshrc.secrets
export MATHPIX_APP_KEY=...
bin/extract-mathpix references/papers/<source>.pdf /tmp/mathpix-out
mv /tmp/mathpix-out/<source>.mathpix.md       references/extractions/<key>.mathpix.md
mv /tmp/mathpix-out/<source>.mathpix.lines.json references/extractions/<key>.mathpix.lines.json
```

Mathpix is a paid API that produces Pandoc-flavoured Markdown with LaTeX math. The script requests `include_equation_tags: true`, `math_inline_delimiters: ["$", "$"]`, and `math_display_delimiters: ["$$", "$$"]`, so equations come wrapped in `\begin{equation*} ... \tag{N} \end{equation*}` and drop cleanly into the existing transcription format. Known systematic OCR errors on this paper: the calligraphic `\mathcal{N}_n` is occasionally misread as `\mathcal{V}_n`, and some subscripts lose their underscore (e.g. `X_{i_1}` → `X_{i 1}`). The raw Mathpix output is committed as `<key>.mathpix.md`; a hand-fixed copy is committed as `<key>.mathpix.processed.md` with the systematic errors corrected. Diff them to see the corrections.

### Marker

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

Marker is an open-source ML-based academic-paper extractor (layout detection + OCR + equation recognition via the surya transformer backbone). Its output is Pandoc-flavoured Markdown with LaTeX math. For this PDF it recovers the core result (Theorem 3, eq. 21) and Lemma 2's eq. 45 as proper LaTeX. Compared to Mathpix: marker preserves equation numbers consistently and runs locally without an API subscription, but it silently drops inline math embedded in prose (sentences lose whole variables). Most useful as a cross-reference against Mathpix on equation-number alignment. On Apple Silicon, set `TORCH_DEVICE=cpu` to avoid [datalab-to/surya#490](https://github.com/datalab-to/surya/issues/490) (`torch.AcceleratorError` in `unpack_qkv_with_mask`, fixed by the open PR [#493](https://github.com/datalab-to/surya/pull/493)).

### pdftotext

```sh
pdftotext -layout references/papers/<source>.pdf references/extractions/<key>.pdftotext.txt
```

`pdftotext -layout` normalises ligatures to ASCII (`deﬁned` → `defined`) and leaves `U+FFFD` replacement markers where glyphs fail to decode, which flags the gaps visually. Drops all equation content.

### pymupdf

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

### Tesseract (rendered pages)

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

Tesseract on rendered pages captures the equation shapes: Theorem 3, Lemma 2, and the basic inequality (8) come through as recognisable prose. The cost is that Greek letters and math operators are transliterated into visually similar Latin-1 and currency glyphs (`α` → `a`, `Γ` → `T` or `[`, `∈` → `€`, `≥` → `>`, `⊕` → `©`), so the output reads like a first-pass draft and should never be used verbatim. It is most useful as a cross-check on the shapes rather than the glyphs.

Transcriptions flag layout-extractor gaps with `> **Transcription caveat.**` admonitions. These should be resolved against the source PDF or `.mathpix.processed.md` before the corresponding statement is formalised.

## Current entries

| Key | Paper | Transcription |
| --- | --- | --- |
| `zhangyeung1998` | Zhang and Yeung, *On Characterization of Entropy Function via Information Inequalities*, IEEE TIT 44(4), 1998 | [zhangyeung1998.md](transcriptions/zhangyeung1998.md) |
| `zhangyeung1997` | Zhang and Yeung, *A Non-Shannon Type Conditional Inequality of Information Quantities*, IEEE TIT 43(6), 1997 | Bibliography only (not formalized) |
| `yeung1997framework` | Yeung, *A Framework for Linear Information Inequalities*, IEEE TIT 43, 1997 | Bibliography only (context for $\Gamma_n$, $\Gamma^*_n$) |
