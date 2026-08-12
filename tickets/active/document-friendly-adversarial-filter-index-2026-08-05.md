# Document the Friendly-to-Adversarial Filter Index

**Created:** 2026-08-05

**Updated:** 2026-08-05

**Status:** Complete

**Related:**

- `document-incremental-danger-annulus-2026-08-05.md` — proves the refined
  annular destruction capacity and records the missing annular population.
- `document-2-gap-merge-survival-candidates-2026-07-23.md` — records the
  random-like survival candidate and its deterministic boundary.
- `empirical-candidate-stress-test-2026-07-23.md` — defines the existing
  full-window measurement program.
- `local-safe-window-capacity-exercise.md` — records the local population versus
  strike-capacity route.
- `algebraic-conditioned-survival-2026-07-27.md` — separates terminal survival
  inequalities from distribution mechanisms.

## START HERE

Documentation is complete. The Filter Adversariality Score property defines the calibrated index and
publishes the audited full-window evidence; candidate #11 and both catalogs are
synchronized. Raw destruction, the random/global benchmark, observed score,
and proved capacity ceiling remain explicitly distinct.

## Goal

Document a declared `0`-to-`1` realized local destruction index where `0`
means no local 2-gap was destroyed, `1/2` means destruction matches the
uniform-random-residue and complete-copy/global benchmark, and `1` means every
local 2-gap was destroyed. State the exact survival and excess-removal limits,
the finite score shown by existing full-window data, and the strongest score
bound supplied by current proofs.

The score describes the realized outcome. It does not infer friendly or
adversarial intent, and matching `1/2` does not prove that a deterministic
filter is random.

## Strategy

For a population `L>0`, destroyed count `K`, raw destruction fraction

```math
f=\frac KL,
```

and benchmark

```math
d_p=\frac2p,
```

define the piecewise-linear adversariality calibration

```math
C_p(f)=
\begin{cases}
\dfrac{f}{2d_p},&0\le f\le d_p,\\[6pt]
\dfrac12+\dfrac{f-d_p}{2(1-d_p)},&d_p\le f\le1.
\end{cases}
```

The value `d_p` has two compatible meanings. It is the expected destruction
fraction when one forbidden residue class is selected uniformly, and it is the
exact complete-copy/global destruction fraction for one inherited 2-gap: two
of its `p` translated copies are destroyed. Neither meaning transfers exactness
to a deterministic short window.

## Current State

- The score documentation, finite full-window evidence, property catalog,
  candidate #11 diagnostic, and candidate catalog are complete and
  synchronized. No code or data was modified.
- Candidate #11 already proves the uniform-random-residue benchmark and
  separates it from deterministic transference.
- the Danger-Annulus Decomposition property proves the refined annular capacity

  ```math
  K_D\le A(p,q)-1\le R_V(p,q)-1.
  ```

- Existing dense and sparse CSVs provide full-window `G_local`, `destroyed`,
  `destruction_rate`, `A_worst`, and `waste_ratio`.
- They do not provide annular `L_D,K_D`, so no observed annular score is
  currently available.
- The permanent [realized filter adversariality score](../../properties/sieve-sequence/realized-filter-adversariality-score.md)
  now proves the abstract `p>2` calibration, anchors, continuity,
  monotonicity, exact survival equivalence, exact integer excess allowance,
  and typed capacity-to-score interfaces. Its concrete full-window and annular
  capacity applications explicitly require consecutive primes `p<q` with
  `p>=5`.
- The independently reviewed merge audit found 192 input rows, 190 rows with
  `p>=5`, four agreeing duplicate `(p,q)` keys, and 186 unique clean
  full-window transitions.
- For the realized full-window score `C_obs=C_p(K/L)`, the verified finite
  summary is: minimum `0`, median `0`, unweighted mean
  `0.044177363545902307`, maximum `21/44` (approximately
  `0.47727272727272724`) at `(p,q)=(7,11)`, and 95 zero-score transitions.
  Exact comparison of `pK` with `2L` classifies all 186 below `1/2`, none equal,
  and none above.
- For the proved full-window capacity ceiling
  `C_cap=C_p(min(1,A/L))`, the verified finite summary is: minimum
  `0.006784399338495748`, median `0.1285745802948713`, unweighted mean
  `0.16908125524560394`, and maximum `0.5545454545454546` at `(7,11)`.
  Exact comparison of `pA` with `2L` gives 177 below `1/2`, one equal, and
  eight above. All 186 ceilings are below `1`, equivalently `A<L` throughout
  the measured full-window sample.
- The permanent score property now contains the audited finite full-window
  evidence: the conflict-free unique-key merge, observed and capacity tables,
  exact midpoint classifications, exact `(7,11)` ratios, and explicit
  separation from annular and randomness claims.
- `properties/sieve-sequence/README.md` now catalogs the score as the Filter Adversariality Score property
  with its abstract and concrete preconditions and finite-evidence boundary.
- Candidate #11 is the appropriate diagnostic cross-link because it owns the
  `2/p` benchmark. The score does not replace or weaken its unresolved
  deterministic-transference hypothesis.
- `candidates/random-like-merge-survival.md` now links the Filter Adversariality Score property,
  distinguishes `C_obs` from `C_cap`, includes the audited finite summary,
  preserves both benchmark models and the transference hypothesis, and makes
  no annular empirical claim. Its stale raw `destruction_rate` maximum location
  is corrected to `(5,7)`; `(7,11)` remains the calibrated-score maximum.

## What is Learned

- The raw fraction `f=K/L` is not the requested calibrated score because its
  random/global reference is `2/p`, not `1/2`.
- `waste_ratio` measures unused accepted-strike capacity and must not be used as
  the random-calibrated score.
- The declared calibration satisfies

  ```math
  C_p(0)=0,
  \qquad
  C_p(d_p)=\frac12,
  \qquad
  C_p(1)=1.
  ```

- It is continuous and monotone. Consequently,

  ```math
  K<L
  \iff
  f<1
  \iff
  C_p(f)<1.
  ```

- If an integer `x` bounds removals beyond the benchmark through

  ```math
  K\le d_pL+x,
  ```

  survival follows for `x<(1-d_p)L`. The largest integer excess that still
  guarantees survival is

  ```math
  x_{max}=\left\lceil(1-d_p)L\right\rceil-1.
  ```

- If a theorem proves `K<=H`, monotonicity supplies the rigorous score bound

  ```math
  C_p(K/L)
  \le
  C_p\!\left(\min\!\left(1,\frac HL\right)\right).
  ```

  The right side is a proved upper bound on adversariality, not an observed
  score. Use `H=A(p,q)` for the full window and `H=A(p,q)-1` for the refined
  annular population. The condition `H<L` proves survival.
- The permanent score property is the source of truth. `C_p(K/L)<1` is an
  exact realized-outcome equivalence, while `K<=H`, `H<L`, and the associated
  score ceiling are sufficient proof interfaces that need not equal observed
  destruction.
- The abstract calibration needs only `p>2`; post-filter-3 full-window and
  annular capacity bounds require `p>=5`. The score measures realized outcome,
  not intent or deterministic randomness.
- Exact benchmark classification should compare `pK` with `2L`, not rounded
  floating-point scores. The closest observed transition to the benchmark is
  `(7,11)`, where `(K/L)/(2/p)=21/22` and the calibrated score is `21/44`.
- `C_obs` and `C_cap` answer different questions. The first is realized
  destruction; the second is a rigorous worst-case ceiling from accepted-
  strike capacity. A ceiling above `1/2` does not imply that observed
  destruction exceeded the benchmark.
- All observed scores are below `1/2`, while eight capacity ceilings are above
  `1/2`; this directly illustrates the difference between realized destruction
  and worst-case capacity. All 186 capacity ceilings remain below `1`, proving
  survival only in those measured full windows.
- The project uses one adversariality calibration anchored at the uniform-
  residue/complete-copy rate `2/p`. The independent-deletion benchmark remains
  documented in candidate #11 as a different model, but no second score is
  introduced.
- The calibrated diagnostic adds interpretation, not a new proof mechanism;
  candidate #11 remains a supporting benchmark and does not change the current
  handoff or priority ordering.

## Expected State

- One standalone permanent mathematical/diagnostic note.
- Proofs of calibration, continuity, monotonicity, survival equivalence, exact
  integer `x_max`, and theorem-to-score conversion.
- A reproducible finite full-window empirical summary based on unique `(p,q)`
  rows.
- Explicit separation of observed score, random/global benchmark, and proved
  score upper bound.
- Explicit statement that no observed annular score or unconditional annular
  score bound below `1` is currently available without a lower bound for
  `L_D`.

## Data Method

- Combine dense and sparse CSV rows by unique `(p,q)` key.
- Exclude `p<5` from the clean capacity-oriented summary.
- Compute `f` from `destroyed/G_local`, not from `waste_ratio`.
- Report unique count, minimum, median, mean, maximum, zero count, and counts
  below, equal to, or above `1/2`.
- Label every reported statistic as full-window evidence.
- Do not regenerate data or modify analysis code unless the existing columns
  prove insufficient.

## Alternatives Considered

- **Use `f` directly:** rejected because random/global destruction is `2/p`,
  not `1/2`.
- **Use `waste_ratio`:** rejected because it measures strike-budget
  utilization, not destruction relative to the random/global benchmark.
- **Call the calibration canonical:** rejected. It is a declared continuous
  piecewise-linear normalization satisfying the requested anchors.
- **Infer an annular score from full-window CSVs:** rejected because the files
  do not contain `L_D,K_D`.

## Assumptions and Validation

- Use `p>2` for the benchmark calibration and `p>=5` when applying post-filter-3
  endpoint-isolation capacity bounds.
- Require `L>0`; the score is undefined for an empty population.
- Fix the uniform-random-residue benchmark `d_p=2/p`. The independent-deletion
  benchmark `2/p-1/p^2` would define a different calibration.
- Validate the three anchors, continuity at `d_p`, and monotonicity on both
  branches.
- Recompute all finite statistics from unique keys and compare with the
  provisional values in Current State.
- Markdown-only changes require `git diff --check`; Python gates apply only if
  empirical code changes.

## Failed Paths

- **Raw destruction as the requested score:** its random anchor moves with
  `p`. Retry only if the user abandons the requested fixed `1/2` anchor.
- **Capacity utilization as random calibration:** random capacity use is not
  fixed at `1/2`. Retry only for a separately named capacity-utilization
  diagnostic.
- **Global `2/p` as an exact local law:** complete-copy exactness does not
  localize to a short deterministic window. Retry only with a proved local
  discrepancy theorem.
- **Annular observed score from present CSVs:** `L_D,K_D` are absent. Retry
  only after an annular measurement is explicitly generated.

## Open Concerns

- An observed annular score requires a measured nonempty population `L_D>0`
  and measured destruction `K_D` for the same typed annulus.
- A proved annular ceiling below `1` requires `L_D>A(p,q)-1`, or another typed
  capacity theorem `K_D<=H<L_D`.
- A deterministic discrepancy/transference theorem remains necessary to
  advance candidate #11 beyond benchmark status.

## Next Action

No documentation action remains for this ticket. The items in `Open Concerns`
are explicit future data or theorem triggers, not unfinished score
documentation. The Filter Adversariality Score property remains a diagnostic and does not change the
#23 -> #24 handoff.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-08-05 | The requested fixed anchors require a declared calibration of `K/L`; `2/p` is both the uniform-residue expectation and the exact complete-copy/global rate, but not an exact short-window law. Existing CSVs support only a unique-key full-window observed score. | Create this focused ticket and define the score algebra before publishing finite statistics. |
| 2026-08-05 | The permanent score property now proves the algebraic calibration and exact `x_max`. Review corrected two boundaries: `K_D<L_D` is exact survival while `L_D>A-1` is only sufficient, and concrete endpoint-isolation capacities require `p>=5` even though the abstract score needs only `p>2`. | Reproduce the unique-key full-window statistics independently before adding numeric evidence. |
| 2026-08-05 | Independent reproduction confirmed 186 unique clean full-window transitions, four agreeing duplicate keys, observed scores all below `1/2`, and capacity ceilings all below `1`. The observed and capacity summaries answer different questions; no annular score is available. The first synchronization patch was a no-op because its expected ticket context was stale; rereading located the fresh section, and the approved same-target retry passed. | Publish the reviewed finite evidence in a clearly marked empirical section of the score note. |
| 2026-08-05 | The permanent score note now publishes the audited finite full-window evidence while preserving the boundary between proved algebra, observed behavior, worst-case capacity, and unavailable annular scores. | Catalog the result as the Filter Adversariality Score property with the same proof/evidence boundary. |
| 2026-08-05 | the Filter Adversariality Score property is cataloged. Candidate #11 is the correct diagnostic cross-link because it defines `2/p`; its transference hypothesis remains unchanged. The project retains one `2/p`-anchored score and leaves the independent-deletion rate as a separately named model only. | Add the diagnostic score cross-link and finite summary to candidate #11. |
| 2026-08-05 | Candidate #11 now links the Filter Adversariality Score property and preserves its transference obligation. Review also corrected the raw destruction-rate maximum from `(7,11)` to `(5,7)` while retaining `(7,11)` as the calibrated maximum. The diagnostic does not justify a handoff or priority change. | Synchronize only candidate #11's numbered catalog entry. |
| 2026-08-05 | Candidate #11's numbered catalog entry now records the diagnostic anchors and finite realized/capacity scope without changing its benchmark role. Final scoped Markdown, link, terminology, and statistic checks passed; no code or data changed. | Mark this ticket complete and retain annular measurement, annular population/capacity, and deterministic-transference results as explicit future triggers. |
