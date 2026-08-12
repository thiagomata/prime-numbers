# Candidate Stress-Test Analysis

A standalone, stdlib + NumPy/SymPy Python package that sieves the square-safe
window `[q, q^2)` per consecutive-prime transition and measures quantities
associated with the candidate conditions in `candidates/`. The columns have
different evidential power: some directly test a finite-stage antecedent,
while others record an outcome, benchmark, partial diagnostic, or proxy.

It exists to stress-test proposed inequalities, calibrate plausible bounds, and
expose what still has not been measured. It cannot classify every candidate as
alive or dead. This evidence-based role replaces reliance on the verdicts in
`articles/learnings/learnings-capacity-argument.md`, whose cited isolation
lemma and five "established inputs" are not Stainless-verified and whose cited
`verifyGeneralizedGrowth` does not exist in any `.scala` file.

This is **decoupled from the Stainless/Scala/Spark codebase**. It pays no
verification compile tax; iteration is instant.

## Run

There are two experiments in this directory:

### A. Single-transition window stress-test (`measure_candidates.py`)

Sieves `[q,q^2)` per transition and measures the window-measurable candidates.

```bash
python3 -m venv .venv
.venv/bin/python -m pip install -r requirements.txt
.venv/bin/python test_measure.py            # green gate; run before & after any change
.venv/bin/python measure_candidates.py 1000 # writes data/candidates/window-measurements.csv
.venv/bin/python measure_candidates.py --sparse 100 20000  # large-p drift check
```

### B. Fixed-future-window lineage experiment (`run_lineage.py`)

Fixes a window `W_Q=[Q,Q^2)` and tracks its 2-gap population through every
intermediate filter `r<Q` layer by layer (Reading A). Measures the ACTUAL
STATED condition of #4, #10, #12, #13, #14 — correcting the proxies the
single-transition pass used. Small-`k` `sigma_r(k)` is exact: early stages
enumerate their tractable periods, while stages with `{2,3,5,7}` installed use
the proved stable table for `2\le k\le10` without full-period materialization.
The current full-period diagnostics (`T_r`, `sigma_r_T`, and the cyclic
destroyed run) materialize the gap cycle and report `unmeasured` beyond the
guard. Values beyond the proved stable profile remain gated: they are computed
exactly when full-period enumeration is tractable and otherwise left
unmeasured.

```bash
.venv/bin/python test_lineage.py             # green gate for the lineage library
.venv/bin/python run_lineage.py 17           # pilot; writes data/candidates/lineage-Q17.csv
```

See `FINDINGS_lineage.md` for the pilot results and the two general findings
(the `sigma_r` machinery starts at layer 1; `sigma_r(T)=r*(M-max_gap)`, not
`r*M`).

`test_measure.py` and `test_lineage.py` are the empirical analog of
`green-to-green`: stdlib `assert` + exit code, in the style of the presentation
repo's `verify.py`. Every number cited anywhere must come from a run that
passed the relevant gate.

## Test coverage (honest)

Two sieves agreeing (this tool's NumPy sieve + gaps.csv's independent
walk-forward) gives confidence but cannot rule out a shared conceptual error.
The real defense is unit tests that pin specific cases to *independently
hand-derived* ground truth. Current strength:

- **Headline signal** (`G_local`, `destroyed`, `surviving`, `A_worst`, `surplus`,
  `waste_ratio`): pinned to **two** fully hand-derived examples (q=5/p=3 and
  q=11/p=7), plus three independent cross-checks (structural identities over 60
  transitions; `surviving>0` iff twin pair via SymPy `isprime`; independent
  pure-Python sieve; gaps.csv survivor-set match over 8 stages).
- **Candidate columns** (#3, #4, #8): pinned to **two** hand-derived examples
  (q=7/p=5 and q=11/p=7) with exact expected values.
- **#12 residue balance, #13 endpoint bias**: pinned to **exact** hand-derived
  values at q=7/p=5 (0.8 and 1/7 respectively), not just "finite and >= 0".
- **#10 discrepancy**: pinned only to "finite, main_term > 0" -- a weak pin; the
  formula is simple but not hand-verified to an exact value.

Known-thin pin: #10 (`E_q`, `main_term`) is formula-trusted but not hand-pinned
to an exact value. Strengthening it is a deferred follow-up.

## Files

- `lib.py` — pure, no-I/O measurement library (the testable core).
- `test_measure.py` — the green gate.
- `measure_candidates.py` — thin runner (args, prime list, loop, CSV).
- `requirements.txt` — `numpy`, `sympy`.
- `FINDINGS.md` — corrected cross-candidate interpretation of the measurements.

## Convention (article-authoritative)

Per `articles/chapter6/gap-dynamics.md` S9, a transition installs filter `p`
and produces next head `q` (the prime after `p`):

- Window `W = [q, q^2)`. A value `< q^2` coprime to every prime `< q` is
  certified prime.
- Pre-filter survivors = integers in `W` coprime to every prime `< p`.
- Installing `p` removes the pre-filter survivors that are `0 (mod p)`; the
  remainder is coprime to every prime `< q` (the certified-prime pool).
- A 2-gap `(x, x+2)` among post-filter survivors in `W` is a genuine
  twin-prime certificate.
- A 2-gap of pre-filter survivors is destroyed by installing `p` iff
  `x = 0 (mod p)` or `x+2 = 0 (mod p)`. Counted directly from the survivor list.

## Limits of each input file (read before trusting any number)

| File | What it is | Its limits |
|------|------------|------------|
| `data/candidates/window-measurements.csv` (this tool) | per-transition measurements over `W=[q,q^2)`, p to 1000 | **Finite window-scale sample only.** `surplus>0` proves survival in each measured window, but the finite run does not prove that it recurs infinitely often. Whole-period candidates (#5,#6,#7,#9) are NOT measured here. `destroyed<=A_worst` holds only for `p>=5`; at p=3 destruction can reach `2*A_worst`. |
| `data/candidates/window-measurements-sparse.csv` (this tool, `--sparse`) | one transition every 100th prime, p to ~19000 | Large-p drift check. **Sparse sampling**, not every transition, because `[q,q^2)` grows quadratically. Each sampled window is sieved in full. Peak memory ~400MB at the top end. Same window-scale limits as the dense file. |
| `data/empirical/results.csv` (Scala `@extern` runner) | `G_local`, `delta=G_local-p` per transition, p to 997 | Uses window **`[p,p^2)`**, not `[q,q^2)` — so `G_local` is NOT directly comparable. Does not measure actual destruction vs. worst case. |
| `presentations/.../figures/out/gaps.csv` (`generate_gaps.py`) | first 4000 gaps per stage, 200 stages | **Fixed 4000-gap prefix/stage** (its README is stale, says 2000). Important: because gaps are small, the 4000-gap prefix reaches `q^2` for stages up to head ~1123 (187 of 200 stages), so it IS a valid full-window survivor-set cross-check there (verified in `test_cross_check_gaps_csv`). Beyond ~head 1123 the prefix stops reaching `q^2` and coverage becomes partial. Its survivor list is generated by a pure-Python walk-forward path independent of this tool's NumPy sieve, so the match is meaningful. |

## Columns and the candidate each tests (with power)

| Column | Candidate | Power of this measurement |
|--------|-----------|---------------------------|
| `surviving` | #1 Protected-endpoints | direct outcome count; does not test an explanatory mechanism |
| `G_local`, `A_worst`, `surplus` | #2 Local-surplus | direct (sufficient condition: `surplus>0`) |
| `max_cluster_in_width_p` | #3 Protected-cluster | direct |
| `max_cons_destroyed_run` | #4 Bounded-consecutive-destruction | window-linear proxy; does not test cyclic wrap or the full period |
| `d_head` | #8 Distinguished-head-spacer | direct outcome-localization count; weak as a mechanism test |
| `E_q`, `main_term` | #10 Short-window-discrepancy | **mismatch:** `E_q` uses pre-filter `G_local`; the candidate requires post-filter `surviving` |
| `destruction_rate`, `gap_2_over_p` | #11 Random-like-merge-survival | benchmark comparison only; does not test deterministic transference |
| `residue_max_dev` | #12 Local-pattern-residue-balance | partial diagnostic; test the explicit `nu E < N(1-nu/p)` margin instead |
| `endpoint_bias` | #13 Uniform-local-observable-sampling | partial diagnostic; absolute bias loses harmful sign and was not compared with the `N,H,L` margin |
| `destroyed`, `waste_ratio` | #14 Hereditary-shot-spacing | coarse proxy only; does not test the interval `sigma` capacity or hereditary conditioning |

### Out of scope this pass (whole-period / `M_p`-scale, need a deeper pass)
#5 Bounded-post-merge-spacer, #6 Controlled-merge-run, #7 Balanced-spacers,
#9 Forbidden-copy-covered-run (true copy-index view).

## Notes

- `waste_ratio = (A_worst - destroyed) / A_worst`. Near 1 means the filter
  destroyed almost no 2-gaps despite its worst-case count. Near 0 means the
  whole-window count reached that worst case. Neither value tests whether the
  local interval/partial-sum condition in #14 holds.
- The hand checks (`test_hand_check_q5_p3`, `test_hand_check_q7_p5`) are the
  authoritative worked examples; read them to understand any column.
