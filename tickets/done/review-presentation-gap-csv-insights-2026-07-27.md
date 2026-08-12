# Review Presentation-Branch Gap CSV Insights

**Created:** 2026-07-27
**Updated:** 2026-07-27
**Status:** Complete

## Goal

Inspect the presentation side branch's giant sieve-sequence CSV and derived
visualizations for sound insights relevant to candidates #17 and #18, without
modifying that branch or confusing prefix observations with fixed-future-window
evidence.

## Strategy

Read the visualization proposal, data contract, generated-figure pipeline,
safe-zone boundary property, and the implementations of lineage tracking and
2-focused compression. Check the local data size and generated outputs. Classify
every finding as proved, empirical, or currently mislabeled.

## Current State

- The presentation dataset exists locally at
  `/Users/thiagomata/github/thiagomata/prime-numbers-presentation/data/sieve-sequence/first_gaps_per_seq.csv`.
  It is approximately 455 MB and contains 200 stages with 100,000 prefix gaps
  per stage.
- The presentation branch was inspected read-only and was not modified.
- The review is complete.

## What is Learned

- **Exact safe boundary.** At a stage with head `p`, the first composite
  survivor is exactly `p^2`. Therefore the generated prefix before that value
  contains no newly rejected survivor and no merge caused by the next filter.
  This gives a structurally forced copy-only prefix, not a random-looking one.
- **Universal but weak survivor bound.** The cited Schroeder bound gives at
  least `floor(2(p^2-1)/p)` accepted values in `[p,p^2)` for every prime
  `p>=11`. This controls total survivors only and is too weak to force the
  required number of 2-gaps.
- **Unproved sharp estimate.** The much better empirical estimate
  `(p^2-p) product_{r<p}(1-1/r)` assumes short-interval localization. It is
  explicitly unproved and is another form of the density gap faced by
  candidates #17 and #18.
- **Exact copy-or-merge lineage.** The visualizer reconstructs each new gap as
  a copied old gap or an exact sum of old gaps. The reported 19.7 million
  comparisons are verification evidence for the implementation, while the
  mathematical copy-or-merge rule is the actual justification.
- **Correct compressed observable.** `compress_around_two` really does sum
  each run of non-2 gaps between 2-gaps. This is the useful observable for
  close-pair spacing and long empty tails.
- **Chart-definition mismatch.** `build_two_gap_run_size_chart` does not use
  the compressed runs. It computes `runs = [g for g in gaps if g != 2]`, so
  its reported average `4 -> about 14` and maximum `114+` describe individual
  non-2 gap values, not summed distances between consecutive 2-gaps. Do not
  cite those values as cluster-spacing evidence until the chart is corrected
  or relabeled.
- **Applicability boundary.** The giant CSV is a fixed-length prefix beginning
  at each stage head. Candidates #17 and #18 condition a fixed future window
  `[Q,Q^2)` through every earlier layer. A stage prefix may fail to reach
  `Q^2`, especially in early rows, so coverage must be checked per `(Q,r)`
  before reusing it.
- **Most useful next extraction.** Where coverage exists, derive actual
  compressed non-2 runs, 2-gap matching counts, filter destructions `H_r`,
  and cumulative capacity increments. These can cross-check the fixed-window
  engine but cannot silently replace it.

## Failed Paths

- **Delayed ticket creation.** The request began as a short README peek but
  expanded into several cross-file inspections before this ticket was created.
  Future side-branch reviews expected to exceed two tool calls must open the
  ticket before expanding beyond the entry document.
- **Missing `giant/` directory.** The README describes a committed
  `presentations/sieve-sequence-visualization/giant/` directory, but that path
  is absent in the checked workspace. The generated article-sized outputs
  exist under `figures/out/`. Do not assume the uncapped artifacts are locally
  available.
- **Treating the cluster-size chart label as its implementation.** The prose
  says “distance between consecutive 2-gaps,” but the chart code measures raw
  non-2 gaps. The implementation, not the label, determines what the numeric
  trend means.

## Open Concerns

- Prefix coverage for fixed windows has not yet been tabulated.
- The correct compressed-run distribution has not been extracted from the
  giant CSV.
- The Schroeder lower bound controls accepted values, not 2-gap density or
  harmful filter hits.
- The sharp local survivor estimate remains unproved and must not be used as
  an algebraic premise.

## Next Action

If this data is used next, first build a read-only coverage table identifying
which `(Q,r)` fixed windows are completely represented. Then compute the exact
compressed-run and cumulative-destruction observables only on covered rows.
Keep uncovered cases explicitly missing.

## Validation

- Read the proposal README, 2-gap lab, data contract, figure pipeline, and
  safe-zone boundary property.
- Read the actual lineage, compression, chart, and verification code.
- Confirmed the giant CSV exists and is approximately 455 MB.
- Visually inspected the generated 2-focused-age and merge maps.
- No source, article, data, or presentation-branch file was changed.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-07-27 | The side branch contains a large exact prefix dataset, an exact `p^2` boundary, and a useful lineage implementation, but its sampling geometry differs from fixed future windows. | Restrict reuse to rows with explicit value-range coverage. |
| 2026-07-27 | The documented cluster-size trend is computed from raw non-2 gaps rather than compressed distances between 2-gaps. | Flagged the mismatch and excluded the `4 -> 14`, `114+` values from proof guidance. |
| 2026-07-27 | The externally proved rough-number lower bound controls only total safe-window survivors and is asymptotically much weaker than the empirically fitted local-density estimate. | Treat it as a boundary fact, not the missing 2-gap-density theorem. |
