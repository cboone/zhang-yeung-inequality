---
applyTo: "**/*.lean"
---

# Lean PR Review Instructions

- **Entrypoint manifest**: `ZhangYeung.lean` is an explicit manifest that re-exports every public submodule (mirroring Mathlib's root `Mathlib.lean`). Do not flag imports here as redundant or transitive; listing every module explicitly is intentional.
- **No line-length limit**: Lines are not hardwrapped to 100 characters. Do not suggest breaking long lines to fit a column.
- **Single-line comment paragraphs**: Docstrings and comments (`/-- -/`, `/-! -/`, `/- -/`, `--`) use one long line per paragraph with blank lines between paragraphs. Do not suggest hardwrapping comment text.
- **Vendored dependencies**: Files under `.lake/packages/` (PFR, APAP, checkdecls, batteries) are vendored and must not be edited or used as local style references. Mathlib (`.lake/packages/mathlib/`) is the exception: treat it as read-only, but it IS a valid style reference alongside this project's own code under `ZhangYeung/`.
- **`rw` closes reflexive goals automatically**: Lean 4's `rw` tactic runs `rfl` after rewriting, and Mathlib's `rfl` applies any `@[refl]`-tagged lemma. `le_refl` is `@[refl, simp]` (`Mathlib/Order/Defs/PartialOrder.lean`), so a `rw` block whose rewrites reduce the goal to a reflexive form (`a = a`, `a ↔ a`, `a ≤ a`, etc.) needs no trailing `norm_num`, `simp`, `exact le_rfl`, or similar. Do not flag such `rw` blocks as missing a closing tactic; if the file builds under `lake build`, the proof is complete.
