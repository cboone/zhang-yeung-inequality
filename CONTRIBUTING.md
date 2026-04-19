<!--
SPDX-FileCopyrightText: 2026 Christopher Boone
SPDX-License-Identifier: CC-BY-4.0
-->

# Contributing to zhang-yeung-inequality

Thank you for your interest in contributing to zhang-yeung-inequality.

Please note that this project has a [Code of Conduct](CODE_OF_CONDUCT.md). By participating, you are expected to uphold it.

## Reporting Issues

- **Bug reports and feature requests:** Use the [issue tracker](https://github.com/cboone/zhang-yeung-inequality/issues/new/choose)
- **Questions and ideas:** Use [GitHub Discussions](https://github.com/cboone/zhang-yeung-inequality/discussions)
- **Security vulnerabilities:** See [SECURITY.md](.github/SECURITY.md)

## Development Setup

### Requirements

- Lean 4 toolchain (version specified in `lean-toolchain`)
- Lake (bundled with Lean)
- markdownlint-cli2 (Homebrew: `brew install markdownlint-cli2`)
- cspell (Homebrew: `brew install cspell`)

### Getting Started

```bash
# Clone the repository
git clone https://github.com/cboone/zhang-yeung-inequality.git
cd zhang-yeung-inequality

# Bootstrap (downloads Mathlib + PFR artifacts and builds)
bin/bootstrap-worktree

# Run linters
make lint

# Run all checks (lint + lean-lint + build + test)
make check
```

## Code Style

- Run `make check` before committing
- Follow the Lean conventions documented in `AGENTS.md`
- Add domain-specific terms to `cspell-words.txt` when needed
- Every public module added in `ZhangYeung/` must land with a matching `ZhangYeungTest/` module covering it via `example` checks

## Commit Messages

Use [Conventional Commits](https://www.conventionalcommits.org/) format:

```text
<type>: <description>
```

**Types:**

- `feat`: new feature
- `fix`: bug fix
- `docs`: documentation changes
- `refactor`: code refactoring (no functional change)
- `test`: adding or updating tests
- `build`: build system or dependency changes
- `ci`: CI configuration changes
- `chore`: maintenance tasks

**Examples:**

```text
feat: add delta_eq_entropy lemma
fix: correct measurability hypothesis on delta_comm_main
docs: update module layout in AGENTS.md
refactor: split Delta into equational and analytic files
test: add API coverage for form21_iff
chore: update PFR pin
```

## Pull Request Process

1. Fork the repository
1. Create a feature branch
1. Make your changes
1. Ensure all checks pass: `make check`
1. Submit a pull request

### Branch Naming

Use descriptive branch names with a type prefix:

- `feature/*`: new features
- `fix/*`: bug fixes
- `docs/*`: documentation changes
- `refactor/*`: code refactoring
- `test/*`: test additions or fixes
- `formalize/*`: proof milestones (e.g., `formalize/copy-lemma`)

## Contact

For questions not covered by the issue tracker or Discussions, email [contact@snappy.sh](mailto:contact@snappy.sh).
