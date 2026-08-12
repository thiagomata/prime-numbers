# Sieve-Sequence Empirical Analysis

This Python project generates the empirical data used to evaluate candidate
properties of sieve sequences. It measures square-safe transition windows and
fixed-future-window lineages without compiling or verifying the Scala/Stainless
project.

The measurements are finite experiments. They can refute a proposed finite
inequality, confirm an exact value for a measured case, or expose numerical
trends. They do not turn agreement over finitely many primes into an asymptotic
proof.

## Install

From the repository root, create a project-local virtual environment and install
the package in editable mode:

```bash
python3 -m venv empirical/sieve-sequence/.venv
empirical/sieve-sequence/.venv/bin/python -m pip install -e empirical/sieve-sequence
```

All commands below use explicit virtual-environment paths; shell activation is
not required.

## Run the experiments

The dense window experiment measures every consecutive-prime transition through
`max_prime`:

```bash
empirical/sieve-sequence/.venv/bin/sieve-sequence-window 1000 data/candidates/window-measurements.csv
```

The sparse form measures the early transitions and then one transition per
`stride`, allowing larger-prime drift checks without running every intermediate
window:

```bash
empirical/sieve-sequence/.venv/bin/sieve-sequence-window --sparse 100 20000 data/candidates/window-measurements-sparse.csv
```

The lineage experiment fixes `W_Q = [Q, Q^2)` and tracks its 2-gap population
through every intermediate prime filter below `Q`:

```bash
empirical/sieve-sequence/.venv/bin/sieve-sequence-lineage 17 data/candidates/lineage-Q17.csv
```

Each command creates missing parent directories and replaces the requested CSV.
When the output argument is omitted, paths are resolved relative to the caller's
current directory under `data/candidates/`.

For source-tree development before installation, use the same canonical modules
with an interpreter that has NumPy and SymPy:

```bash
PYTHONPATH=empirical/sieve-sequence/src python3 -m sieve_sequence_empirical.window_cli 1000 data/candidates/window-measurements.csv
PYTHONPATH=empirical/sieve-sequence/src python3 -m sieve_sequence_empirical.window_cli --sparse 100 20000 data/candidates/window-measurements-sparse.csv
PYTHONPATH=empirical/sieve-sequence/src python3 -m sieve_sequence_empirical.lineage_cli 17 data/candidates/lineage-Q17.csv
```

## Tests

After installation, run both destination-owned suites:

```bash
empirical/sieve-sequence/.venv/bin/python empirical/sieve-sequence/tests/test_window.py
empirical/sieve-sequence/.venv/bin/python empirical/sieve-sequence/tests/test_lineage.py
```

These are the destination-owned Python unit gates. Also run the applicable
Python import and CLI checks for the surface changed. Python-only changes do not
require Scala tests or Stainless verification.

## What the experiments measure

The window command sieves `[q, q^2)` for each transition from prime `p` to the
next prime `q`. Its CSV includes the pre-filter 2-gap population, actual and
worst-case destruction, surviving certified twin-prime pairs, local clustering,
run, discrepancy, residue-balance, and endpoint-bias diagnostics. The dense and
sparse commands use the same stable column schema.

The lineage command holds `[Q, Q^2)` fixed and records each filter layer `r<Q`.
It measures actual destruction and survival together with the candidate #12,
#13, and #14 margins and diagnostic fields.

For candidate #14, `sigma_r(k)` is exact for the stable table
`2 <= k <= 10` once `{2, 3, 5, 7}` has been installed. Filtering monotonicity
and the exact sub-wheel give the lower bound; translating an admissible pattern
with the Chinese remainder theorem gives the matching upper bound. Earlier
stages use direct exact enumeration. Agreement with later finite wheels is a
regression check, not the proof.

Full-period diagnostic fields such as `T_r`, `sigma_r(T_r)`, and the cyclic
destroyed run require materializing the relevant gap cycle and are guarded for
large periods. A guarded field is left unmeasured; it does not make the stable
small-`k` values heuristic. Values outside the proved stable profile are
computed only when exact enumeration is tractable and otherwise remain
unmeasured.

## Project layout

- `src/sieve_sequence_empirical/window.py` — pure window measurement core.
- `src/sieve_sequence_empirical/window_cli.py` — dense and sparse CSV runner.
- `src/sieve_sequence_empirical/lineage.py` — pure lineage measurement core.
- `src/sieve_sequence_empirical/lineage_cli.py` — fixed-window lineage runner.
- `tests/test_window.py` — independently pinned window checks.
- `tests/test_lineage.py` — lineage identities and exactness checks.
- `pyproject.toml` — dependencies, package discovery, and console entries.

Generated CSV files belong under `data/candidates/`; they are experiment output,
not proof artifacts.
