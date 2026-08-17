# Fixed-Lineage Cumulative-Hazard CSV and Chart

**Created:** 2026-08-12
**Updated:** 2026-08-13
**Status:** Complete (Steps 1-15 done; figures and article integration green)
**Depends on:** `lineage-experiment-2026-07-23.md` (implemented and validated for Q=17 and Q=101)

## START HERE

Establish the current Python green baseline with `just empirical-test`. Then add
one pure fixed-cohort transition function and its identity tests. Do not change
the CSV schema or build the chart until the explicit cohort has been shown to
agree, layer by layer, with the existing Reading A lineage at Q=17 and Q=101.

## Related Tickets

- `lineage-experiment-2026-07-23.md` — established the fixed future window
  `W_Q = [Q,Q^2)`, Reading A, the Python lineage implementation, and validated
  Q=17 and Q=101 runs. Reuse its exact accepted-set semantics and green gate.
- `missing-empirical-charts-2026-08-11.md` — identifies fixed-window lineage as
  the structurally missing chart and warns that the existing Q=17/Q=101 data
  are too thin for a broad empirical conclusion. This ticket must begin with a
  validated single-Q chart and add a modest Q sweep before summarizing a trend.
- `draft-mixed-adversarial-random-companion-2026-08-11.md` — records why the
  current per-sequence and per-transition figures cannot be compounded: they
  use changing square windows rather than one cohort. The new figure should
  eventually replace that limitation with the fixed-cohort measurement, while
  retaining the article's distinction between window survival and head
  recurrence.
- `promote-python-empirical-project-2026-08-04.md` — defines the canonical
  Python package, CLIs, local virtual environment, and root `just` recipes.
  New empirical work belongs there rather than in legacy analysis scripts.

## Goal

Create a reproducible Python CSV and SVG that follow one initial population of
2-gap starts in the fixed window `W_Q = [Q,Q^2)` through every prime filter
`r<Q`. For each layer, compare the real destruction hazard with the neutral
random benchmark `2/r`, accumulate their difference, and show how the measured
effective skew compares with the theoretical head scale `c=1/2` and square-
window scale `c=1`.

The ticket is complete when the cohort calculation is independently tested,
the CSV identities are green, the chart is regenerated from the CSV, a modest
multi-Q sweep has been assessed, and the draft article reports only conclusions
supported by those measurements.

## Strategy

Build on the canonical Python lineage package, but give this observable a new
dedicated output rather than silently changing the historical lineage CSV
schema. Initialize the cohort as all 2-gap starts surviving the already
installed filter 2 in `W_Q`. At each incoming prime `r`, mark a cohort member as
destroyed exactly when either endpoint is divisible by `r`, then remove it from
the active cohort.

Filtering a sorted accepted set only deletes values and merges adjacent gaps;
it cannot create a new gap of size 2. Therefore the explicit active cohort
should equal the existing Reading A 2-gap population before every filter. That
equivalence is the load-bearing regression test, not an assumption to leave
implicit.

Use additive log hazard because it composes across layers. For a layer with
pre-filter count `L_before`, destroyed count `K`, and post-filter count
`L_after`, define

```text
f_real         = K / L_before
f_random       = 2 / r
w_real         = f_real / f_random
h_real         = -log(L_after / L_before)
h_random       = -log(1 - 2/r)
D_real         = cumulative sum of h_real
D_random       = cumulative sum of h_random
excess_hazard  = D_real - D_random
c_eff          = excess_hazard / (2 log r)
survival_real  = L_after / L_initial
survival_random = exp(-D_random)
```

If a layer destroys the whole active cohort, record `h_real`, `D_real`, and
`excess_hazard` as positive infinity, set real survival to zero, and stop
claiming a finite `c_eff`. Do not smooth or discard extinction.

## Current State

- **Steps 1-15 COMPLETE.** Full implementation and article integration:
  - `hazard.py`: `init_fixed_cohort`, `apply_cohort_filter`, `layer_hazard_row`, `build_hazard_run`
  - `hazard_cli.py`: writes `data/candidates/fixed-lineage-hazard-Q{Q}.csv`
  - `test_hazard.py`: cohort equivalence (Q=17/101), hazard partition, survivor-ratio identity,
    random-benchmark identity, CSV round-trip (all green)
  - `just empirical-hazard {Q}` recipe + `just empirical-chart-hazard` chart recipe
  - `fixed_lineage_hazard_chart.py`: two-panel SVG (excess + c_eff) with reference scales
  - CSVs generated for Q=17, 101, 251, 503
  - Chart generated at `out/fixed-lineage-hazard.svg`
- **Fixed-window result:** across Q=17, 101, 251, and 503, signed `c_eff`
  ranges from -0.0353 to 0.00908. The largest positive value is 0.00907
  at Q=251; for Q=251 and Q=503 all absolute values are at most 0.00908.
  Since complete-cycle excess is exactly zero, these deviations are finite
  boundary effects rather than a structural sieve signal.
- **Publication result:** the draft article now uses the full-cycle
  destruction and normalized-survival figures as the exact structural
  references and retains the fixed-window hazard figure as a robustness check.
- All assumptions validated: cohort equivalence (exact set match), partition, hazard identity, random benchmark identity
- `empirical/sieve-sequence/src/sieve_sequence_empirical/lineage_cli.py`
  currently writes `G_r_window`, `destroyed`, `surviving`, and candidate-
  specific diagnostics, but it does not emit cumulative hazard or a fixed-
  cohort identity.
- `empirical/sieve-sequence/tests/test_lineage.py` already checks hand-derived
  Q=17 values, `destroyed + surviving = G_r_window`, and layer-to-layer Reading
  A consistency.
- The stored lineage data cover Q=17 and Q=101. These are suitable for
  regression and a proof-of-concept figure, not by themselves for a stable
  empirical trend.
- The supplied `per-sequence-frontier.svg` and
  `frontier-comparison-stages.svg` measure compatible real-versus-random
  quantities over changing windows. Neither is a cumulative fixed-cohort
  curve.
- The Scala Chapter 7 empirical runner also uses changing square windows and
  is retirement-pending. It is not the primary implementation target for this
  work.

## Expected State

- A pure Python fixed-cohort/hazard module under
  `empirical/sieve-sequence/src/sieve_sequence_empirical/`, with no file I/O.
- A thin CLI that writes
  `data/candidates/fixed-lineage-hazard-Q{Q}.csv` without changing the existing
  lineage CSV contract.
- A root `just` recipe for regenerating one requested Q.
- Tests for the explicit cohort, all per-layer and cumulative identities, the
  random benchmark, and extinction handling.
- Reproducible Q=17 and Q=101 CSVs, followed by a documented runtime-informed
  sweep such as Q=251, Q=503, and Q=1009 if the implementation remains
  practical.
- A chart generator at
  `presentations/sieve-sequence-visualization/figures/fixed_lineage_hazard_chart.py`
  and generated output
  `presentations/sieve-sequence-visualization/figures/out/fixed-lineage-hazard.svg`.
- The draft article updated only after the data and figure gates pass.

## CSV Contract

Each row represents one incoming filter and should include at least:

```text
Q, layer, r,
L_initial, L_before, destroyed, L_after,
f_real, f_random, w_real,
h_real, h_random,
D_real, D_random, excess_hazard, c_eff,
survival_real, survival_random
```

Preserve integers as integers. Write enough floating-point precision for the
cumulative recurrence and product identities to survive a CSV round trip.
Document non-finite values explicitly in the reader and chart tests.

## Chart Contract

Use filter prime `r` on a logarithmic x-axis. Use linear y-axes because the
real-minus-random excess can be negative.

1. **Cumulative excess panel:** plot `D_real-D_random`, with reference curves
   `0`, `log r`, and `2 log r`. The latter two are comparison scales
   corresponding to effective coefficients `c=1/2` and `c=1`; they are not
   fitted claims about the real sieve.
2. **Effective coefficient panel:** plot
   `(D_real-D_random)/(2 log r)`, with horizontal references at `0`, `1/2`, and
   `1`.

Start with separate Q=17 and Q=101 curves. Add further Q curves only after the
single-Q generator and tests are green. Add an aggregate median or band only
if enough comparable Q values exist and its construction is stated in the
caption.

The title and caption must say **fixed-window 2-gap cohort**. They must not say
or imply “head recurrence,” “twin-prime proof,” or “real CRT frontier.”

## Approaches Considered

### Dedicated Python Hazard Dataset

**Status:** RECOMMENDED

Reuse the canonical lineage primitives but create a focused module, CLI, CSV,
and figure for the cumulative observable.

**Strengths:** preserves the existing CSV contract; directly matches the
mathematical product; permits narrow tests; keeps data generation separate from
presentation.

**Risks:** duplicates a few layer fields already present in lineage CSVs; the
two paths could drift without explicit equivalence tests.

**Fallback:** if duplication becomes material, extract one shared pure layer
primitive used by both CLIs, changing and validating one function at a time.

### Extend the Existing Lineage CSV In Place

**Status:** NOT RECOMMENDED

Append the hazard columns to `lineage-Q{Q}.csv`.

**Strengths:** fewer output files and no repeated base columns.

**Risks:** silently changes a historical data contract used by candidate work;
mixes unrelated whole-period diagnostics with the focused cumulative series.

**Fallback:** reconsider only after searching all current consumers and adding
schema-version or backward-compatibility tests.

### Implement the Measurement in Scala

**Status:** PRE-EMPTED

The current Scala empirical runner has changing-window semantics and is marked
for retirement. Porting this experiment there would add a second semantics
problem before validating the statistic itself.

**Fallback:** use Scala only later as an independent small-Q cross-check if a
maintained fixed-window Scala implementation is introduced.

### Infer Cumulative Hazard from Existing Transition Charts

**Status:** REJECTED

Rows from different square windows do not describe one shrinking cohort, so
their survival fractions cannot be multiplied into a lineage probability.

**Fallback:** none without a stable cohort identifier and fixed window.

## Assumptions and Hypotheses

1. **Cohort equivalence.** Deletions cannot create a 2-gap, so explicit active
   cohort size before filter `r` equals existing `G_r_window`.
   **Validation:** compare the exact start sets, not only counts, at every layer
   for Q=17 and Q=101.
2. **Per-layer partition.** Every active 2-gap is either destroyed or survives
   one filter.
   **Validation:** assert `destroyed + L_after = L_before` for every row.
3. **Additive hazard identity.** The cumulative real hazard represents the
   exact remaining cohort fraction.
   **Validation:** within numerical tolerance, check
   `exp(-D_real) = L_after/L_initial` at every non-extinct layer.
4. **Random benchmark identity.** The cumulative random hazard equals the
   product of the neutral factors.
   **Validation:** independently maintain the product of `(1-2/r)` and compare
   it with `exp(-D_random)`.
5. **Useful finite range.** Q values beyond 101 remain cheap enough for a small
   sweep.
   **Validation:** record runtime and peak cohort size for Q=251 before choosing
   larger Q values. Do not promise Q=1009 before this check.
6. **Interpretive hypothesis.** The measured excess remains below one or both
   theoretical reference scales over the finite sweep.
   **Validation:** report the curves and maxima exactly. A crossing is a result,
   not a failed experiment.

## Risks

- A count-only comparison could hide differing cohort identities. Compare
  start sets at the regression Q values.
- Division by zero and logarithm of zero require an explicit extinction path.
- Repeated floating-point summation can drift. Test both the additive hazard
  recurrence and the independent survivor-ratio identity.
- `c_eff` is unstable at very small `r`; keep raw excess visible and do not let
  the normalized panel stand alone.
- A log y-axis would be invalid when excess hazard is negative.
- A few Q curves can look smoother or more universal than the evidence allows.
  Always show the individual curves behind any aggregate.
- Fixed-window survival is closer to the article's window theorem, but it does
  not measure whether the distinguished pair at the head survives infinitely
  often. That transfer still needs head availability and dependence/mixing
  control.

## Validation

Python-only green-to-green applies; do not run Scala tests or Stainless.

1. Before the first Python change, run `just empirical-test` and require all
   existing window and lineage tests to pass.
2. After each pure-function change, run the narrow lineage/hazard test target,
   then `just empirical-test` before moving to the CLI.
3. Verify exact cohort-set equality with current Reading A at every Q=17 and
   Q=101 layer.
4. Verify every CSV row after a write/read round trip:
   - counts are non-negative and monotone;
   - `destroyed + L_after = L_before`;
   - real and random fractions are in their valid ranges;
   - `w_real * f_random = f_real` within tolerance;
   - cumulative columns equal their prior value plus the current hazard;
   - survivor-ratio and independent random-product identities hold;
   - zero destruction adds zero real hazard;
   - extinction produces the documented non-finite values and zero survival.
5. Add figure tests for CSV parsing, reference-series construction, negative
   excess handling, labels, and well-formed SVG output.
6. Regenerate Q=17 and Q=101 through the root CLI recipe and compare their base
   counts with the existing lineage CSVs.
7. Render and visually inspect the SVG for clipped labels, distinguishable
   curves, correct scales, and an honest caption.
8. Run `git diff --check` for each documentation/figure integration change.

## Implementation Plan

Each numbered item is a separate green-to-green micro-cycle.

1. Add an explicit fixed-cohort transition primitive and one hand-derived Q=17
   test.
2. Add exact set-equivalence tests against Reading A for all Q=17 layers.
3. Extend equivalence coverage to Q=101 and record runtime.
4. Add one pure per-layer hazard-row derivation and its partition test.
5. Add real cumulative-hazard recurrence and survivor-ratio tests.
6. Add the random cumulative-product calculation and its independent identity
   test.
7. Add normalized `w_real`, excess hazard, and `c_eff`, one identity at a time.
8. Add and test the explicit extinction branch.
9. Add the dedicated CSV CLI and round-trip test.
10. Add a root `just` recipe and generate Q=17 and Q=101 CSVs.
11. Add the chart's pure series builder and tests.
12. Add SVG rendering for the cumulative-excess panel and validate it.
13. Add the effective-coefficient panel and validate it.
14. Run Q=251, use its measured cost to select at most two larger Q values,
    and record the selection here before running them.
15. Regenerate the final graph, audit its caption, and only then update the
    draft article's empirical section and conclusion.

## Fallback Options

- If explicit set retention is too memory-heavy at larger Q, retain it for the
  Q=17/Q=101 oracle and use a tested boolean mask or sorted integer array for
  the sweep. Do not fall back to unrelated changing-window counts.
- If Q=251 is already expensive, publish the single-Q chart as a
  proof-of-concept and state the data limitation; do not silently reduce
  resolution or sample filters within a lineage.
- If chart-library dependencies complicate reproducibility, use the existing
  repository SVG helpers and retain the CSV as the authoritative artifact.
- If real extinction occurs, plot the finite prefix, mark extinction visibly,
  and report it as the principal result instead of forcing a normalized curve.

## What is Learned

- The existing Python lineage already supplies the correct fixed-window stage
  semantics and exact destruction counts needed as an oracle.
- A coherent cumulative product requires one fixed cohort; the existing two
  real-versus-random charts cannot provide it because their windows change.
- Cumulative log hazard is the natural observable: products become sums and
  the article's logarithmic coefficient frontiers become direct reference
  scales.
- The graph can empirically compare fixed-window behavior with the `c=1/2` and
  `c=1` scales, but only `c=1` is the natural square-window occupancy boundary.
  The `c=1/2` line is a head-recurrence comparison scale, not a conclusion from
  this dataset.
- The `c=1` product is not valid at the smallest primes because
  `2(1+log(r))/r` exceeds one there. Both full-cycle charts therefore use the
  maintained model's first valid plotted filter, r=29, and normalize their
  products at that anchor.
- At r=251, the normalized exact-cycle survival product from r=29 is 0.3733,
  while the normalized `c=1` reference is 0.003676, a ratio of about 102.

## Failed Paths

- **Multiplying existing changing-window transition rates.** Rejected because
  successive rows do not act on the same population; retry only if the source
  data gain a stable cohort and fixed-window identifier.
- **Treating the current Scala empirical runner as the implementation base.**
  Pre-empted because its window semantics differ and it is retirement-pending;
  retry only if a maintained fixed-window Scala path is established.
- **Plotting excess hazard on a logarithmic y-axis.** Rejected because the
  real-minus-random quantity may be zero or negative; retry only for a strictly
  positive transformed observable with a separately justified meaning.
- **Calling the output a direct head-frontier test.** Rejected because the
  cohort is all 2-gaps in a square window, not the distinguished pair at the
  head; retry only with a separate head-pair dataset and a justified temporal
  dependence analysis.
- **Starting the `c=1` survival product at r=3.** Rejected because the first
  factor is negative (`2(1+log(3))/3 > 1`), and the original chart replaced
  that invalid factor with zero, making the frontier identically zero. Retry
  below r=29 only with a separately defined finite-prefix normalization whose
  factors are all valid.

## Open Concerns

- A future direct head experiment would need to track the pair `(Q,Q+2)` over
  many Q values and address dependence between stages. It is outside this
  ticket.
- **CHART UTILITY REVIEW (resolved 2026-08-13):** The fixed-window chart measures cumulative
  excess hazard in the fixed window [Q, Q^2). However, in the full modular
  cycle (modulus M = product of installed primes), the per-layer destruction
  fraction f_real equals f_random = 2/r **exactly, at every layer, for every
  sequence**. This is a provable theorem: when installing prime r on a cycle of
  modulus M (gcd(M,r)=1), each old 2-gap residue expands to r new residues, and
  exactly 2 are destroyed (x ≡ 0 mod r and x ≡ -2 mod r, no overlap since r >= 3).
  Therefore all deviations shown in the chart — the c_eff ~ 0.009 "signal" at
  Q=503, the separation between Q curves, the negative excess at small r — are
  **window-boundary artifacts**, not properties of the sieve. The chart measures
  how [Q, Q^2) cuts through partial cycles, not a structural feature of the
  sieve itself.

  **What the chart does show:**
  - Finite-size robustness: even in non-aligned windows, the boundary noise is
    small (~1% of the reference scales). This is a minor footnote, not a
    contribution.
  - Convergence: larger Q curves converge toward zero excess, consistent with
    the exact-cycle theorem. But this is confirming a theorem, not discovering
    a property.

  **What the chart does NOT show:**
  - A structural excess or deficit of the real sieve relative to random. There
    is none — the full-cycle destruction rate is exactly random.
  - Evidence for or against twin primes. The survival question reduces to
    whether prod(1 - 2/r) stays positive, which is a Mertens-type decay question,
    not an empirical excess question.

  **Alternative that may be more useful:**
  - A **full-cycle per-layer destruction chart**: compute f_real = (old_count *
    r - new_count) / (old_count * r) in the exact cycle, compare to 2/r. This
    would show f_real = f_random exactly, confirming the theorem visually. It
    is a cleaner, more honest graph — but it proves a theorem, not an empirical
    finding. Its value is pedagogical, not evidentiary.
  - A **survival fraction chart**: plot prod(1 - 2/r) vs r to show the
    twin-prime survival decay. This is the quantity that actually matters for
    the overall argument, and it is a pure function of r (no Q dependency, no
    window, no noise).

  **Decision:** Keep the fixed-window chart as a finite-size robustness check,
  and use the full-cycle destruction and normalized-survival charts as the
  primary structural references. The article now states that the window
  deviations are boundary effects and that none of these figures establishes
  head recurrence.

## Next Action

None. The implementation, generated artifacts, validation, and article update
are complete. Any direct head-lineage experiment should begin under a new
ticket with explicit availability and dependence semantics.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-08-12 | Ticket created after reviewing the canonical lineage implementation, the existing Q=17/Q=101 validation, the missing-chart assessment, and the article's changing-window limitation. A dedicated fixed-cohort CSV avoids breaking the historical lineage schema and makes cumulative hazard mathematically coherent. | Establish the Python green baseline, then implement and validate one explicit-cohort transition before adding derived columns or chart code. |
| 2026-08-12 | Step 1 done. Created `hazard.py` with `init_fixed_cohort(Q)` (all 2-gap starts in [Q,Q^2) after filter 2) and `apply_cohort_filter(cohort, r)` (returns destroyed and survivors as sorted lists). `test_hazard.py` passes: exact set-equivalence against Reading A at Q=17 for init and filter 3, hand-derived ground truth (destroyed=18, surviving=27) at filter 5. `just empirical-test` green with all three suites. The explicit cohort tracks the same population as Reading A — cohort equivalence assumption validated for Q=17 layers 2, 3, 5. | Proceed to Step 2: extend set-equivalence coverage to ALL Q=17 layers (filters 3,5,7,11,13). |
| 2026-08-12 | Step 2 done. `test_explicit_cohort_Q17_all_layers` chains explicit cohort through all 5 filters (3,5,7,11,13), verifying exact set equality with Reading A both before and after each filter. All 15 checks pass. Assumption 1 (cohort equivalence) fully validated at Q=17. | Proceed to Step 3: extend equivalence coverage to Q=101 and record runtime. |
| 2026-08-12 | Step 3 done. Q=101: 24 layers verified in 0.01s. Explicit cohort tracking is cheap. | Proceed to Step 4: per-layer hazard-row. |
| 2026-08-12 | Steps 4-8 done. `layer_hazard_row` and `build_hazard_run` compute all derived columns including D_real, D_random, excess_hazard, c_eff, survival_real, survival_random. Identities verified: partition, survivor-ratio (exp(-D_real)=L_after/L_initial), random benchmark (exp(-D_random)=prod(1-2/r)). | Proceed to CLI/CSV generation. |
| 2026-08-12 | Steps 9-10 done. `hazard_cli.py` writes CSVs. `just empirical-hazard` recipe. `pyproject.toml` entry point `sieve-sequence-hazard` registered. CSV round-trip test verifies partition, cumulative consistency, zero-destruction. Q=17, 101 CSVs generated. | Proceed to chart generation. |
| 2026-08-12 | Steps 11-14 done. Two-panel SVG chart (`fixed_lineage_hazard_chart.py`) using stdlib-only `svg_kit.py` — excess panel with log(r)/2log(r) reference scales, c_eff panel with 0/0.5/1 reference lines. `just empirical-chart-hazard` recipe. Q sweep: 17, 101, 251, 503 all run instantly. c_eff peaks at ~0.009 at Q=503 — two orders of magnitude below both reference scales. Excess consistently positive at larger Q. | Proceed to Step 15: article update (user-directed). |
| 2026-08-13 | CHART UTILITY REVIEW. Through discussion with the user, established that in the **full modular cycle** (modulus M = product of installed primes), the per-layer destruction fraction f_real equals f_random = 2/r **exactly, at every layer, for every sequence**. This is a provable theorem: when installing prime r on a cycle of modulus M (gcd(M,r)=1), each old 2-gap residue expands to r new residues mod M*r, and exactly 2 are destroyed (x ≡ 0 mod r and x ≡ -2 mod r, no overlap since r >= 3). Therefore ALL deviations in the chart — the c_eff ~ 0.009 "signal", the Q-curve separation, the negative excess at small r — are window-boundary artifacts of [Q, Q^2) cutting through partial cycles, NOT properties of the sieve. The chart's only valid content is a finite-size robustness footnote. Alternatives proposed: (1) full-cycle per-layer destruction chart showing f_real = f_random exactly (pedagogical, proves a theorem), (2) survival fraction chart showing prod(1-2/r) decay (the quantity that actually matters for the twin-prime argument, pure function of r, no Q dependency). Decision on whether to keep, replace, or retire the current chart is pending team review. Updated Open Concerns with full analysis. | Await team decision on chart direction. |
| 2026-08-13 | Created alternative chart `full_cycle_hazard_chart.py` → `out/full-cycle-hazard.svg`. Two panels: (1) per-layer destruction rate f_real vs f_random=2/r in the exact modular cycle — they overlap exactly, confirming the theorem visually; (2) cumulative survival fraction prod(1-2/r) vs r with a C/(log r)^2 Mertens reference curve. Added `just empirical-chart-full-cycle` recipe. All tests green. Both charts now exist for team comparison: `fixed-lineage-hazard.svg` (window-based, shows boundary noise) and `full-cycle-hazard.svg` (exact cycle, shows the underlying structure). | Team decides whether to keep both, replace, or retire the window-based chart. |
| 2026-08-13 | Split the combined `full-cycle-hazard.svg` into two separate SVGs for clarity: `full-cycle-destruction.svg` (per-layer destruction rate chart) and `full-cycle-survival.svg` (cumulative survival fraction chart). Each is a standalone chart with its own legend, title, and caption. Added c=1 frontier curve to both charts: `2(1+ln r)/r` on the destruction chart and `prod(1-2(1+ln r)/r)` on the survival chart. Updated colors and legend naming to match the existing `frontier_comparison_stages_chart.py` conventions: blue=real, red=random benchmark (dashed), black=c=1 frontier (dashed), green=Mertens (dashed). Added 50% stroke opacity to the empirical blue line on the destruction chart so the red dashed random benchmark shows through the overlap. Three charts now exist: `fixed-lineage-hazard.svg` (window-based), `full-cycle-destruction.svg` (exact cycle per-layer rate), `full-cycle-survival.svg` (exact cycle cumulative survival). | Why the new charts are a better fit for the article (see below). |
| 2026-08-13 | Publication audit found that the original full-cycle survival chart started the c=1 product at r=3, where its factor is invalid, and then zeroed the entire frontier. Both full-cycle charts now use the established valid anchor r=29. Their labels distinguish exact count identities from empirical evidence. CSV inspection corrected the summary: signed c_eff ranges from -0.0353 to 0.00908, with the positive maximum at Q=251, not Q=503. | Regenerated both SVGs, passed `just empirical-test` and XML/link/whitespace checks, updated §8.1, Limitations, and Conclusion, and closed the ticket. |

## Why the Full-Cycle Charts Are a Better Fit

The original `fixed-lineage-hazard.svg` chart measures cumulative excess hazard in
the finite window [Q, Q^2). Through discussion, we established that in the full
modular cycle the per-layer destruction rate is exactly random (f_real = 2/r,
provable theorem). All deviations in the window-based chart are boundary
artifacts. The two new charts show the underlying structure directly:

### `full-cycle-destruction.svg`
- **What it shows:** f_real (blue, semi-transparent) overlaid on the random
  benchmark 2/r (red dashed) and the c=1 frontier 2(1+ln r)/r (black dashed).
- **Why it fits:** Visually confirms the theorem — the empirical and random
  curves overlap exactly. The frontier sits above, showing the margin between the
  real rate and the square-window survival boundary. This is a pedagogical
  chart: it proves a theorem visually, with no window parameter or Q dependency
  to confuse the reader.
- **Matching conventions:** Uses the same color scheme, dash patterns, and
  legend naming as the existing `frontier-comparison-stages.svg` chart already
  referenced in the article (§8.1), so a reader moving between charts sees
  consistent visual language.

### `full-cycle-survival.svg`
- **What it shows:** prod(1-2/r) (blue solid) — the twin-prime survival
  fraction — with the c=1 frontier prod(1-2(1+ln r)/r) (black dashed) and a
  Mertens reference C/(ln r)^2 (green dashed).
- **Why it fits:** This is the quantity that actually matters for the overall
  argument. The article (§3.4–§3.5) proves that if w_r stays below the c=1
  frontier, square windows survive; below c=1/2, head recurrence follows (with
  availability + mixing). The chart shows the real survival fraction sitting
  far above the frontier — the gap is the margin. No Q parameter, no window
  noise, no boundary artifacts. A reader can see exactly how much survival
  margin exists at every filter.
- **Matching conventions:** Blue = real, black = c=1 frontier, green = Mertens —
  consistent with the destruction chart and the existing frontier charts.

### Relationship to the article
The article's §8.1 already has two empirical charts (`per-sequence-frontier.svg`
and `frontier-comparison-stages.svg`) that measure real-vs-random-vs-frontier
over **changing windows**. The new full-cycle charts complement them by showing
the **exact cycle** structure. Together they answer: "Is the real rate at or
below random?" (yes, exactly) and "How much margin does the survival fraction
have above the c=1 frontier?" (two orders of magnitude at r=251). The
window-based `fixed-lineage-hazard.svg` adds only a finite-size robustness
footnote — it may be kept as supplementary material but should not be the
primary chart.
