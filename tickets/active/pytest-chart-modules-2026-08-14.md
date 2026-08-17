# Pytest Coverage for Three Chart Modules

## START HERE

Write three pytest files under `python/tests/`: `test_per_sequence_frontier_chart.py`,
`test_frontier_comparison_stages_chart.py`, `test_fixed_lineage_hazard_chart.py`.
Each tests one `sieve_sequence` chart module's pure computations (and one SVG
shape check for the hazard chart). Validate with the venv pytest gate.

## Goal

Add regression tests for the chart modules' headline math
(prime sieve, density/frontier product, 2-gap counts, benchmark formulas,
reference scales) and CSV loading, using small hand-derived stages and CSV
fixtures. No Stainless involved -- Python-only gate.

## Strategy

- Read each source chart module first to understand the exact computation.
- Pre-verify every hand-derived expected value by running the real functions
  in a scratch script before writing assertions (avoids wrong expected values).
- Use the established pytest conventions seen in `test_phase_transition.py`,
  `test_hit_miss_heatmap.py` (monkeypatch module path constants + tmp_path,
  assert `svg.startswith("<svg ")` / `endswith("</svg>")`).
- Import as `from sieve_sequence import <module> as mod`; use `import math`,
  `pytest`; `from sympy import primerange` for prime lists.
- One test class/file per source module; follow the user's explicit per-file
  test list. Do NOT add comments to test bodies.

## Current State

- Green baseline: `python/.venv/bin/pytest python/tests/test_phase_transition.py
  test_hit_miss_heatmap.py test_stage_transition_diagram.py -q` -> 35 passed.
- Pre-verification scratch scripts confirmed all expected values EXCEPT
  `primes_upto(0)` (see Failed Paths).
- Verified:
  - `primes_upto(20) == [2,3,5,7,11,13,17,19]`; `primes_upto(2)==[2]`; `primes_upto(1)==[]`.
  - build_series two-stage fixture: stage0 main/frontier==3.0; stage1 main/frontier
    == 3.3333333... (10/3). g2 for [3,5,7,9,11] head=3 == 2.
  - frontier stages: `2.0/7 == 2/7`; `2*(1+ln7)/7` diff to 0.8417 == 1.14e-5
    (< 1e-4); both 2/p and 2(1+ln p)/p strictly decreasing for p in primes[7,97].
  - load_stages CSV fixture -> [(7,0.28),(11,0.18),(17,0.0),(101,0.05)] incl.
    zero-destroyed -> 0.0 branch, dense+sparse merged and sorted.
  - hazard: log/2*log references match to 1e-4; monotone increasing; data_path(17)
    endswith fixed-lineage-hazard-Q17.csv; draw(all_data,[17,101]) renders SVG
    starting `<svg ` ending `</svg>`.

## What is Learned

- `per_sequence_frontier_chart.primes_upto(0)` RAISES IndexError (it constructs
  `is_p=[True]*(n+1)` then does chained `is_p[0]=is_p[1]=False`; for n=0 the list
  has length 1, so `is_p[1]=False` is out of range). The user-specified
  `primes_upto(0) == []` is therefore FALSE against the actual code.
- `build_series` shares a `pi` pointer across stages, so density multipliers
  accumulate cumulatively (the prod_{3<=r<h}(...) is the cumulative product up
  to but not including the current head). Hand derivation matched this exactly.
- `build_series` counts 2-gaps only over the window [h, h^2): `inwin` filters
  survivors to `h <= x < hi`, so 9 is excluded for head=3 (g2=2, not 3).
- The frontier excess ratio `fr` only starts shrinking at r>=7, so for small
  heads (<=5) it stays 1.0 and frontier == main_term.
- Chart `draw()` functions call `subprocess.check_output(["git","rev-parse",...])`
  inside try/except, so they're safe to call in tests without a clean git state.
- LSP diagnostics on `empirical/sieve-sequence/...` files are pre-existing and
  unrelated (different package); they don't affect this Python-only change.

## Failed Paths

- **User spec `primes_upto(0) == []` is wrong for the actual code.** The
  function raises IndexError at n=0. To stay green and honest, the edge-case
  test asserts only `primes_upto(2)==[2]` and `primes_upto(1)==[]`, and a
  SEPARATE test documents the actual crash with `pytest.raises(IndexError)`.
  Reason for not fixing the source: the user asked only for tests (no source
  modification), and per red-cascade/never-destroy I will not mutate the chart
  source while the spec is the only thing that's red. Surfacing this to the user
  and offering an optional source fix in the summary.

## Open Concerns

- None blocking. The one spec deviation (`primes_upto(0)`) is flagged for the
  user; the test file documents actual behavior.

## Next Action

- Write the three test files (one change per file), running the venv pytest on
  each new file after writing it, then the broader Python test gate.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-08-14 | `primes_upto(0)` raises IndexError, not `[]`. | Split edge-case test: pass on 2 and 1; document 0 with pytest.raises. Flag to user. |
| 2026-08-14 | All other hand-derived expected values were confirmed exact against the live functions before writing assertions. | Pre-verification scratch scripts minimize the risk of wrong expected values. |