# Architecture

## Overview

A single Python package (`sieve_sequence`) that computes, visualizes, and
verifies properties of prime sieve sequences. Three layers flow in one
direction: **computation** produces CSV data, **visualization** renders
that data as SVG/PNG charts, and **verification** checks mathematical
claims against the generated data.

```
┌──────────────────────────────────────────────────┐
│  python/src/sieve_sequence/                      │
│                                                  │
│  Computation        Visualization     Primitives  │
│  (numpy, sympy)     (stdlib only)     (svg_kit,  │
│  *_cli.py runners   *_chart.py        png_writer)│
│                     modules                      │
│  generate_gaps.py  verify.py                    │
└──────────────────────────────────────────────────┘
  │                        │
  ▼                        ▼
data/ (CSV, shared         charts/ (SVG/PNG,
  with Spark)                shared output)
```

## Layers

**Computation** — Pure no-I/O libraries (numpy + sympy) that sieve windows,
track lineages, and compute candidate-property columns. Each pairs with a
`*_cli.py` runner that handles argument parsing, CSV I/O, and progress.
Computation modules never touch the filesystem — only the CLI runners do.

**Visualization** — Chart scripts (stdlib only) that render computation
output as static SVG files with embedded PNG rasters for heatmaps. All
drawing goes through two primitive modules (`svg_kit`, `png_writer`); no
third-party plotting library. Charts run as `python -m sieve_sequence.*`
from the `python/` directory and write to `charts/` at the repo root.

**Data & Verification** — A crash-resumable gap-cycle generator
(`generate_gaps.py`) produces the primary dataset, and a re-runnable
verifier (`verify.py`) checks mathematical claims against it.

## Tech Stack

| Component | Technology |
|-----------|------------|
| Language | Python >=3.11 |
| Computation | numpy >=2.0, sympy >=1.13 |
| Visualization | stdlib only (SVG builder, zlib PNG encoder) |
| Testing | pytest >=9.1,<10 — 249 tests |
| Packaging | setuptools, `src/` layout, editable install |
| Orchestration | `just` recipes |

## Shared Directories

Both live at the repository root, shared across Python, Spark, and
markdown articles:

- `data/` — CSV inputs and outputs (measurements, generated gap cycles)
- `charts/` — SVG/PNG chart output (article-ready + full-detail `giant/`)

## Principles

### 1. Empirical data in charts comes from CSVs produced by tested modules

Charts that display measured data (prime counts, destruction rates, survival
ratios, gap populations) must read that data from CSV files. The CSV is
produced by a `*_cli.py` runner whose underlying computation module has pytest
coverage ensuring correctness. This guarantees that numbers shown in
visualizations are never the product of untested code.

Analytic/theoretical curves (formulas like `2(1+ln p)/p`, `prod(1-2/r)`,
modular-cycle identities) may be computed inline in the chart script — they
are mathematics, not measurements. But see principle 2.

### 2. All computation feeding into charts is tested

Whether empirical data flows through a CLI + CSV pipeline or an analytic
curve is computed inline, the computation must have tests. For CLI modules
this means a `test_*.py` covering the computation library. For inline chart
math this means tests of the chart's own `compute_*` / `build_series` helpers
against hand-derived values or known identities.

### 3. Every SVG chart has source annotations

Every SVG output includes an XML comment naming its data sources:
`<!-- Input: data/candidates/...csv -->` for CSV inputs, or formula
descriptions for analytic curves. This makes every chart self-documenting —
a reader can trace any number in the chart back to the code and data that
produced it.

## Current Gaps

| Gap | Principle | Status |
|-----|-----------|--------|
| `deferred3.py` has no test file | 2 | Open — no `test_deferred3.py` exists |
| 4 self-computing charts have no tests for inline math | 2 | Open — `full_cycle_survival`, `full_cycle_destruction`, `full_cycle_hazard`, `stage_transition_diagram` |
| 4 mixed charts have untested inline reference curves | 2 | Open — `gap_heatmap`, `hit_miss_heatmap`, `per_sequence_frontier`, `frontier_comparison_stages` |
| 5 charts have no source annotations | 3 | Open — `four_lines_chart`, `gap_heatmap`, `hit_miss_heatmap`, `stage_transition_diagram`, `spacing_chart` |
| 3 charts have provenance comments but no data source path | 3 | Open — `full_cycle_*` trio |

## Conventions

1. Computation modules have no I/O — only `*_cli.py` runners read/write files.
2. CLI entry points are declared in `pyproject.toml` (`[project.scripts]`).
3. Chart scripts use relative imports — run via `python -m sieve_sequence.*`.
4. All tests are pytest — run via `just empirical-test`.
5. Output is deterministic and reproducible — no timestamps or random seeds.
