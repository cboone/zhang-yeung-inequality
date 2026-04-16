# M0: Project Scaffolding

## Context

The zhang-yeung-inequality project currently has only a README, LICENSE, and documentation (roadmap + research survey). No Lean code, no build system, no CI. M0 creates the build infrastructure so that subsequent milestones (M1: Delta lemmas, M2: copy lemma, etc.) can begin immediately.

The project depends on PFR (`teorth/pfr`) for Shannon entropy definitions (`H[X]`, `I[X:Y]`, `I[X:Y|Z]`). PFR is currently on Lean 4.28.0-rc1, while the user's other Lean projects (shannon-entropy, strength-model) are on 4.29.0. Per the user's decision, we will attempt to build PFR against Lean 4.29.0, falling back to 4.28.0-rc1 if that fails.

## Reference projects

- **shannon-entropy** (`~/Development/shannon-entropy`): `lakefile.toml`, Lean 4.29.0, Mathlib 4.29.0, batteries linter, CI via `leanprover/lean-action@v1`
- **strength-model** (`~/Development/strength-model/proofs`): `lakefile.lean`, same versions, depends on shannon-entropy + verso
- **PFR** (`teorth/pfr`): `lakefile.toml`, Lean 4.28.0-rc1, requires APAP + checkdecls (Mathlib transitive)

## Steps

### 1. Determine PFR compatibility with Lean 4.29.0 in the intended root-package layout

- Create a throwaway scratch package that matches this repo's planned dependency shape: a root package with a single direct dependency on `PFR` at `80daaf1`, plus a tiny module importing `PFR.ForMathlib.Entropy.Basic`
- Set its `lean-toolchain` to `leanprover/lean4:v4.29.0`
- Run `lake update && lake exe cache get && lake build`
- If it builds: proceed with 4.29.0 and let Lake resolve `mathlib` transitively through `PFR`
- If it fails: fall back to `leanprover/lean4:v4.28.0-rc1` and still let Lake resolve `mathlib` transitively through `PFR`

This is a throwaway test; nothing from it gets committed. The point is to validate the exact dependency shape we plan to check in here, not PFR in isolation.

### 2. Create `lean-toolchain`

```
leanprover/lean4:v4.29.0
```

(Or `v4.28.0-rc1` if step 1 fails.)

### 3. Create `lakefile.toml`

Follow the pattern from shannon-entropy and PFR. Key choices:

- **Format**: TOML (matches shannon-entropy and PFR; simpler than Lean DSL)
- **Package name**: `ZhangYeung`
- **Default target**: `ZhangYeung`
- **Lint driver**: `batteries/runLinter`
- **Dependencies**: `PFR` pinned at `80daaf1`. Do not add a direct `mathlib` dependency; let Lake resolve it transitively through `PFR` so the root package matches the tested graph.
- **Lean options**: `autoImplicit = false`, `relaxedAutoImplicit = false` (matching PFR's strictness)
- No test driver yet (no test files in M0)

```toml
name = "ZhangYeung"
version = "0.1.0"
defaultTargets = ["ZhangYeung"]
lintDriver = "batteries/runLinter"

[leanOptions]
autoImplicit = false
relaxedAutoImplicit = false

[[require]]
name = "PFR"
git = "https://github.com/teorth/pfr"
rev = "80daaf1"

[[lean_lib]]
name = "ZhangYeung"
```

Note: PFR also depends on APAP, checkdecls, and Mathlib, which Lake resolves transitively. We do not need to list them.

### 4. Create skeleton Lean files

**`ZhangYeung.lean`** (top-level re-export):

```lean
import ZhangYeung.Prelude
```

Minimal module docstring explaining the project.

**`ZhangYeung/Prelude.lean`**:

- Import PFR entropy notation: `import PFR.ForMathlib.Entropy.Basic`
- `open ProbabilityTheory` to bring entropy notation (`H[X]`, `I[X:Y]`, etc.) into scope
- Module docstring explaining this is the import surface for PFR's entropy API
- No definitions yet; this just verifies the PFR import path works

### 5. Create bootstrap script

**`bin/bootstrap-worktree`** (executable shell script):

Following the pattern from shannon-entropy and strength-model. The script:

1. Runs `lake update`
2. Downloads Mathlib cache with `lake exe cache get`
3. Verifies cache was downloaded (check for `.lake/packages/mathlib/.lake/lib/` or equivalent)
4. Runs `lake build`

This is the mandatory first command in a fresh clone or worktree. Direct `lake build` without it would try to compile Mathlib from source.

### 6. Create CI workflow

**`.github/workflows/ci.yml`**:

Follow shannon-entropy's pattern:

```yaml
name: CI

on:
  push:
    branches: [main]
  pull_request:
  workflow_dispatch:

jobs:
  lean:
    name: Build and lint (Lean)
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v5
      - uses: leanprover/lean-action@v1
      - name: Lean lint
        run: lake lint
```

No test job yet (no test files). No markdown lint job yet (can add later).

### 7. Create or update project CLAUDE.md

Document project-specific conventions required by the write-lean-code skill:

- **Bootstrap script**: `bin/bootstrap-worktree`
- **Full local check**: `lake build ZhangYeung && lake lint`
- **Namespace convention**: flat under `ZhangYeung` for now
- **Vendored deps to exclude from style searches**: PFR, APAP, checkdecls, batteries (everything under `.lake/packages/`)
- **Top-level namespace**: `ZhangYeung`

### 8. Build and verify

- Run `bin/bootstrap-worktree` from the project root
- Confirm `lake build` succeeds with no errors
- Confirm `ZhangYeung/Prelude.lean` successfully imports PFR entropy notation
- Confirm `lake lint` passes

### 9. Push and verify CI

- Commit all scaffolding files
- Push the branch
- Verify the GitHub Actions workflow passes

## Deliverable

A green CI build that successfully imports PFR entropy notation, confirming the build infrastructure is ready for M1.

## Files created/modified

| File | Action |
|------|--------|
| `lean-toolchain` | Create |
| `lakefile.toml` | Create |
| `ZhangYeung.lean` | Create |
| `ZhangYeung/Prelude.lean` | Create |
| `bin/bootstrap-worktree` | Create |
| `.github/workflows/ci.yml` | Create |
| `CLAUDE.md` | Create |

## Risks

- **PFR on 4.29.0**: The main unknown. PFR has not been tested on 4.29.0. If it fails, the fallback (4.28.0-rc1) is straightforward but means a version gap with the user's other projects.
- **PFR transitive deps**: APAP and checkdecls may also have version constraints. Lake should resolve these, but version conflicts could surface.
- **PFR build weight**: Even with Mathlib cache, PFR itself must compile. This may be slow on first build. The bootstrap script handles this.

## Verification

- `lake build ZhangYeung` exits 0
- `lake lint` exits 0
- `ZhangYeung/Prelude.lean` imports `PFR.ForMathlib.Entropy.Basic` without errors
- CI workflow runs green on GitHub
