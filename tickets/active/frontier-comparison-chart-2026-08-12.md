# Frontier-Comparison Chart: Real Sieve vs Random vs c=1 Frontier

## START HERE

Recreate the four-lines chart focusing on three trajectories: the real
measured empirical survivors, the random projection (w_r=1), and the c=1
square-window frontier projection (w_r=1+log r). Drop friendly and adversarial.

## Goal

Give the draft phase-transition article a real-data-anchored figure that ties
the analytic thresholds (Property III/IV) to actual sieve-sequence numbers.
The existing four-lines chart anchored friendly/random/adversarial projections
at the real lineage Q=101; the recreated chart keeps empirical + random and
adds the c=1 frontier projection, so a reader can see where the real sieve
sits relative to the square-window threshold.

## Strategy

- Add `log_growth_trajectory(n0, rs, c=1.0)` to `four_lines.py`: running
  product of (1 - 2*(1 + c*log(r))/r). c=0 must reproduce random_trajectory
  exactly; c=1 is the frontier.
- Add a `N_frontier` column to `four_lines_cli.py` (additive -- existing
  four-lines/spacing consumers ignore extra columns).
- Add green-gate tests to `test_four_lines.py` (c=0 == random; c=1 < random,
  stays positive, hand-verified against direct math.log computation).
- New `frontier_comparison_chart.py`: empirical solid blue, random dashed
  violet, frontier dashed black (color links to the phase-transition charts'
  black frontier; dash marks it as a projection). Solid = real data, matching
  the four-lines convention; only one solid line.
- Regenerate four-lines-Q101.csv, run the new chart, verify SVG. Python-only
  gates: venv test script + chart script run + CSV/SVG inspection.

## Current State

- DONE. `four_lines.py` gained `log_growth_trajectory(n0, rs, c=1.0)`;
  `four_lines_cli.py` writes the additive `N_frontier` column;
  `test_four_lines.py` gained 3 green-gate tests.
- All five empirical test suites PASS (window, lineage, four_lines, spacing,
  phase_transition).
- `data/candidates/four-lines-Q101.csv` regenerated: N_frontier 361 -> 12.9,
  always strictly below random (194) and empirical (202), staying positive.
- New chart `frontier_comparison_chart.py` -> `out/frontier-comparison-Q101.svg`:
  empirical blue solid (the only solid line), random violet dashed "7,4",
  frontier black dashed "10,3,2,3" (color links to the phase-transition charts'
  black boundary; dashed marks it as a projection). Legend + note explain
  solid=real/dashed=projection.
- Downstream consumers verified: spacing_cli and the existing
  four_lines_chart / spacing_chart still run green with the added column.
- Concurrent session note: the other agent's companions-folder restructure is
  also in this working tree (article retitle/rewrite, candidates->companions
  renames). It preserved this session's two figure embeds in the article.
- Per-sequence variant built: `per_sequence_frontier_chart.py` reads
  `data/sieve-sequence/first_gaps_per_seq.csv` (the giant-heatmap source, 20M
  rows) and draws `out/per-sequence-frontier.svg` -- one empirical point per
  head h in [h,h^2) (188 sequences with full coverage, heads 3..1129), against
  the random expectation (complete-period density = lib.py main_term) and the
  c=1 frontier expectation (main_term * prod_{7<=r<h}(1 - 2 ln r/(r-2))).
  Validation: real counts track the random expectation within ~5%
  (0.94-1.03), while the frontier expectation collapses to ~0.1; the real
  sieve stays ~10^5 above the frontier at head 1129. Scope noted in-plot.

## Alternatives Considered

- Overlay real points on the phase-transition window chart: rejected (scale
  mismatch -- analytic goes to log10(Q)=60, real data only to ~4.3; phase
  transition only resolves at astronomical Q).
- Extend four_lines_chart.py in place: rejected -- user wants a focused
  recreation, not the four-line chart with extra lines; a new script keeps the
  old chart intact.

## Risks, Assumptions, And Hypotheses

- The frontier uses natural log (matching phase_transition.py's math.log).
- f_r = 2(1+log r)/r < 1 for every future filter r>=29 in the lineage chain
  (verified: at r=29 it is ~0.30), so the projection is well-defined.
- Assuming the user wants the c=1 square-window frontier (the article's
  square-window threshold), not the c=1/2 head threshold -- the four-lines
  chart is about square-window survivors.

## Validation Plan

- `empirical/sieve-sequence/.venv/bin/python empirical/sieve-sequence/tests/test_four_lines.py` -> PASS.
- Regenerate four-lines CSV via the four-lines console script; check the
  N_frontier column matches hand-computed values.
- Run frontier_comparison_chart.py; inspect SVG: exactly one solid line
  (empirical), two dashed lines, legend labels correct.

## What is Learned

- The c=1 frontier projection decays fast enough that it is clearly visible
  on a linear scale even on the short real lineage chain (361 -> 12.9),
  making the real-sieve comparison legible without log axes.
- Adding a column to four-lines-Q101.csv is backward compatible: spacing_cli
  and both existing chart scripts ignore it and stay green.
- The same working tree carries a concurrent companions-folder restructure;
  coordinate commits with the user rather than committing the whole tree.
- Chart notes must never generalize a finite measurement into an asymptotic
  verdict. The first note ("the real sieve tracks the random projection and
  stays far above the threshold here") implied a forever statement from 16
  layers of one lineage; it was rewritten to say the trajectory stays above
  the threshold across the measured layers and that nothing beyond the
  measured range is implied.

## Failed Paths

- **Overclaiming note on the real-sieve chart.** The first note text implied
  the real sieve behaves like the random projection "forever" from a single
  finite lineage run. Corrected by scoping the statement to the measured
  range. Any future real-data figure must state its measured scope in the
  figure itself.

## Open Concerns

- None.

## Next Action

- Done pending user review/commit. Offer to embed the new chart in the draft
  article (natural spot: §21 "Relation to the Real Sieve"). Coordinate the
  commit with the concurrent companions-folder work in this tree.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-08-12 | The phase-transition charts replaced the real-anchored four-lines/spacing charts; the real data (lineage-Q101, window-measurements) is still available and chart-ready. | Opened this ticket to recreate the four-lines chart focused on empirical + random + c=1 frontier. |
| 2026-08-12 | The per-sequence data behind the giant heatmaps (`first_gaps_per_seq.csv`, 200 heads) lets the frontier comparison run over 188 full-coverage sequences (heads 3..1129) instead of one lineage. | Built `per_sequence_frontier_chart.py`; real counts track the random expectation to within ~5% and stay ~10^5 above the collapsing c=1 frontier expectation. |
