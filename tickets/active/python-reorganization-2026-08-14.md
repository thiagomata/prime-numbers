# Python Reorganization: From Bag of Scripts to Project Structure

## Goal
Consolidate all Python code (57 files across 4 disconnected groups) into a single
`python/` project with proper packaging, unified test framework (pytest), and
shared `data/` and `charts/` directories at root level.

## Strategy
1. Create `python/` with `src/sieve_sequence/` package, `tests/`, and `tools/`
2. Move all source modules from `empirical/`, `presentations/figures/`, `scripts/`
3. Migrate unique `deferred3` code from `candidates/analysis/`
4. Delete all duplicate files in `candidates/analysis/`
5. Convert all tests to pytest (unified framework)
6. Create unified `pyproject.toml` with all entry points
7. Move chart outputs to root-level `charts/`
8. Update justfile recipes
9. Verify all tests pass

## Current State
- Branch: `feature/python-reorganization`
- All 57 Python files reorganized into `python/` directory
- 197 tests pass via `python/.venv/bin/pytest python/tests/ -v`
- 9 CLI entry points work (sieve-sequence-window, -lineage, -hazard, -deferred3, etc.)
- Chart scripts run correctly via `python -m sieve_sequence.chart_name`
- Chart output goes to root-level `charts/`
- Data reads from root-level `data/` (unchanged, shared with Spark)
- 7 duplicate files deleted from `candidates/analysis/`
- All markdown path references updated

## What is Learned
- `git mv` preserves history and is the correct way to move tracked files
- `python -m sieve_sequence.module` is needed for relative imports to work in chart scripts
- CLI entry points via `pyproject.toml` `[project.scripts]` handle relative imports natively
- The depth `python/src/sieve_sequence/` = 3 levels to root = same as old `presentations/.../figures/` depth, so data path navigation with `"..", "..", ".."` still works
- `pytest` with `pip install -e ".[dev]"` resolves all import paths automatically once the package is installed

## Target Structure (ACHIEVED)
```
python/
  pyproject.toml
  README.md
  src/sieve_sequence/          — 35 modules (computation + visualization)
  tools/                        — 3 repo maintenance scripts
  tests/                        — 15 test files + conftest.py (197 tests)
data/                           — root level, shared with Spark (unchanged)
charts/                         — root level, shared chart output (new)
```

## Failed Paths
(none — all approaches succeeded)

## Open Concerns
- Stale untracked files remain in old locations (`empirical/.../hazard.py`,
  `presentations/.../figures/chart.py`, `charts/old/`) — user can clean with `git clean -f`
- The `empirical/sieve-sequence/` directory retains non-Python docs (FINDINGS.md, etc.)
- The `presentations/sieve-sequence-visualization/` directory retains presentation planning
  markdown docs (01-semantic-zoom-film.md, etc.)
- The old `empirical/sieve-sequence/pyproject.toml` is stale (references removed package)
- `OBJECTS.md` shows unstaged modifications from earlier work (unrelated to this reorg)

## Next Action
Commit the changes and clean up stale directories.

## Learning Log
| Date | Entry |
|------|-------|
| 2026-08-14 | Created ticket, created branch, completed codebase survey |
| 2026-08-14 | Created python/ structure, moved all 57 files with git mv + cp |
| 2026-08-14 | Migrated deferred3, deleted 7 duplicate files |
| 2026-08-14 | Converted 6 empirical tests from stdlib to pytest, updated 7 viz test imports |
| 2026-08-14 | Created unified pyproject.toml, set up venv, 197 tests pass |
| 2026-08-14 | Updated justfile (6 recipes updated, 2 new recipes added) |
| 2026-08-14 | Updated markdown path references in 16+ files |
| 2026-08-14 | Created python/README.md, updated empirical and figures READMEs |
| 2026-08-14 | Verified chart output to charts/ works correctly |
