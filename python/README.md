# Sieve-Sequence Python Project

Unified Python project for empirical analysis and visualization of sieve-sequence
candidate properties. Combines computation (numpy/sympy), visualization (stdlib SVG/PNG),
and repo maintenance tools in a single installable package.

## Install

From the repository root:

```bash
just python-setup
```

Or manually:

```bash
cd python
python3 -m venv .venv
.venv/bin/pip install -e ".[dev]"
```

## Run the experiments

All CLI entry points are installed as console scripts:

```bash
python/.venv/bin/sieve-sequence-window 1000 data/candidates/window-measurements.csv
python/.venv/bin/sieve-sequence-window --sparse 100 20000 data/candidates/window-measurements-sparse.csv
python/.venv/bin/sieve-sequence-lineage 17 data/candidates/lineage-Q17.csv
python/.venv/bin/sieve-sequence-hazard 17 data/candidates/fixed-lineage-hazard-Q17.csv
python/.venv/bin/sieve-sequence-deferred3 2000 data/candidates/deferred3-measurements.csv
python/.venv/bin/sieve-sequence-four-lines 101 data/candidates/four-lines-Q101.csv
python/.venv/bin/sieve-sequence-spacing 101 data/candidates/spacing-Q101.csv
python/.venv/bin/sieve-sequence-phase-transition-window data/candidates/phase-transition-window.csv
python/.venv/bin/sieve-sequence-phase-transition-head data/candidates/phase-transition-head.csv
```

## Run the charts

Chart scripts are run as modules and output to `charts/` at the repo root:

```bash
cd python
.venv/bin/python -m sieve_sequence.four_lines_chart
.venv/bin/python -m sieve_sequence.spacing_chart
.venv/bin/python -m sieve_sequence.gap_heatmap
.venv/bin/python -m sieve_sequence.hit_miss_heatmap
.venv/bin/python -m sieve_sequence.stage_transition_diagram
.venv/bin/python -m sieve_sequence.verify
.venv/bin/python -m sieve_sequence.full_cycle_destruction_chart
.venv/bin/python -m sieve_sequence.full_cycle_survival_chart
.venv/bin/python -m sieve_sequence.full_cycle_hazard_chart
.venv/bin/python -m sieve_sequence.fixed_lineage_hazard_chart
.venv/bin/python -m sieve_sequence.phase_transition_window_chart
.venv/bin/python -m sieve_sequence.phase_transition_head_chart
.venv/bin/python -m sieve_sequence.frontier_comparison_chart
.venv/bin/python -m sieve_sequence.frontier_comparison_stages_chart
.venv/bin/python -m sieve_sequence.per_sequence_frontier_chart
```

## Tests

```bash
just empirical-test
```

Or directly:

```bash
python/.venv/bin/pytest python/tests/ -v
```

All 249 tests use pytest. They cover:
- Window, lineage, four-lines, spacing, phase-transition, hazard, and deferred3 computation
- SVG kit, PNG writer, gap heatmap, hit-miss heatmap, stage-transition diagram, and verify checks
- generate_gaps full-period computation and trial-division fallback

## Project layout

```
python/
  pyproject.toml              — package metadata, dependencies, entry points
  src/sieve_sequence/
    window.py, window_cli.py           — square-window measurement and CSV runner
    lineage.py, lineage_cli.py         — fixed-window lineage measurement and runner
    four_lines.py, four_lines_cli.py    — trajectory comparison and runner
    spacing.py, spacing_cli.py          — implied-spacing view and runner
    phase_transition.py, *_cli.py       — phase-transition curves and runners
    hazard.py, hazard_cli.py            — fixed-cohort hazard tracking and runner
    deferred3.py, deferred3_cli.py       — deferred-filter-3 measurement and runner
    svg_kit.py, png_writer.py           — stdlib-only SVG/PNG rendering primitives
    generate_gaps.py                    — gap-cycle CSV generator (crash-resumable)
    verify.py                           — re-runnable verification checks
    gap_heatmap.py                      — gap-cycle heatmap visualizations
    hit_miss_heatmap.py                 — hit/miss matrix panels
    stage_transition_diagram.py         — 8-step gap-cycle transition diagram
    four_lines_chart.py                 — four-lines trajectory chart
    spacing_chart.py                    — implied-spacing chart
    full_cycle_*.py, fixed_*.py         — full-cycle and hazard charts
    phase_transition_*_chart.py         — phase-transition charts
    frontier_comparison_*_chart.py     — frontier comparison charts
    per_sequence_frontier_chart.py      — per-sequence frontier chart
  tools/
    check_scala_cycles.py               — Scala dependency-cycle checker
    disable_holds.py                     — batch .holds disabler
    retire_property_numbers.py          — property-number migration tool
  tests/
    conftest.py                         — shared fixtures
    test_*.py                           — 249 pytest tests
```

Generated CSV data belongs under `data/` (root level, shared with Spark).
Generated charts belong under `charts/` (root level, shared output).