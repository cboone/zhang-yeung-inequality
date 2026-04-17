---
applyTo: "**/*.lean"
---

# Lean PR Review Instructions

- **Entrypoint manifest**: `ZhangYeung.lean` is an explicit manifest that re-exports every public submodule (mirroring Mathlib's root `Mathlib.lean`). Do not flag imports here as redundant or transitive; listing every module explicitly is intentional.
- **No line-length limit**: Lines are not hardwrapped to 100 characters. Do not suggest breaking long lines to fit a column.
- **Single-line comment paragraphs**: Docstrings and comments (`/-- -/`, `/-! -/`, `/- -/`, `--`) use one long line per paragraph with blank lines between paragraphs. Do not suggest hardwrapping comment text.
- **Vendored dependencies**: Files under `.lake/packages/` (PFR, APAP, checkdecls, batteries) are vendored and must not be edited or used as local style references. Mathlib (`.lake/packages/mathlib/`) is the exception: treat it as read-only, but it IS a valid style reference alongside this project's own code under `ZhangYeung/`.
