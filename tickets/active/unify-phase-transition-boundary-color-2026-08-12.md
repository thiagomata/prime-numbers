# Unify Solid Boundary Color Across Phase-Transition Charts

## START HERE

Make the solid boundary line the same color in both phase-transition charts:
head chart's c=0.5 boundary and window chart's c=1 frontier, both solid black
(#111111), then regenerate the SVGs.

## Goal

The user asked for the phase-transition-head and phase-transition-window graphs
to use the same legend, style, and colours. The dashed series for shared
quantities already matched (c=0.0/w=1 blue #2a78d6), but the solid boundary
lines did not: head c=0.5 was dark green #008300, window c=1 frontier was
violet #4a3aa7. The user flagged this ("solid line is blue in one and green
in other") and chose black #111111 for the shared boundary color.

## Strategy

- Change head chart COLORS[3] (#008300 -> #111111) for the solid c=0.5 line.
- Change window chart COLOR_FRONTIER (#4a3aa7 -> #111111) for the solid c=1 line.
- Update both module docstrings and the inline color comments so they describe
  the new scheme accurately (solid black boundary shared across both charts;
  the old claim that head c=1.0 and the c=1 frontier share color is dropped).
- Regenerate both SVGs and verify each contains exactly one solid black
  polyline.
- No tests exist for these two chart scripts; validation is script run +
  SVG inspection. No Scala/Stainless involvement (Python-only change).

## Current State

- DONE. Both scripts edited, both SVGs regenerated and verified.
- Head chart: COLORS[3] for c=0.5 is now #111111; docstring + inline comment
  updated. Window chart: COLOR_FRONTIER now #111111; docstring + comment block
  updated. Both module docstrings now describe the shared solid-black boundary
  and drop the old head c=1.0 <-> frontier color-link claim.
- Regenerated SVGs verified: each has exactly one polyline with no
  stroke-dasharray, stroke #111111, width 2.5; five dashed polylines each,
  colors/dashes unchanged from before.
- `git diff --check` clean. Scripts exit 0. No unit tests exist for these two
  scripts; validation was script run + SVG inspection.
- spacing_chart.py / four_lines_chart.py use these hexes for unrelated
  quantities and are not part of this pair; no change needed there.

## Alternatives Considered

- Violet #4a3aa7 for both: rejected, clashes with head c=1.0 (dashed violet)
  in the same chart.
- Green #008300 for both: rejected, clashes with window w=10 (dashed green).
- Keep per-chart boundary colors: rejected by the user's request.

## Risks, Assumptions, And Hypotheses

- Dropping the head c=1.0 <-> window c=1 frontier color link is acceptable;
  the labels ("c=1.0" / "c=1 frontier") still carry the mapping, and the shared
  solid black boundary gives the visual consistency the user asked for.

## Validation Plan

- Run both scripts; they must exit 0 and write the SVGs.
- Inspect the regenerated SVGs: exactly one polyline with no stroke-dasharray,
  stroke #111111, in each; dashed series colors unchanged.
- `git diff --check` clean.

## What is Learned

- The other agent's "solid is per-chart, not shared" rule (commit bcb6b4a1)
  is exactly what the user did not want; solid = boundary should read the same
  across the two charts.
- All six categorical colors were already consumed by dashed series, so a
  shared solid boundary needs a 7th color or reuse of the ink color.

## Failed Paths

- None. The first approach considered was reusing an existing series color for
  the shared boundary; each candidate clashed with a dashed series in one of
  the two charts, so a 7th color (the ink black) was used instead -- this is a
  rejected alternative, not a failed attempt.

## Open Concerns

- None. B&W-safety verification complete: the colored version is already
  grayscale-safe because every series in each chart has a distinct dash
  pattern (not just color). The user confirmed this is the desired design:
  keep colors, boundary solid (one per chart), all other lines distinct
  dashes, consistent across graphs (baseline c=0.0/w=1 shares "1,4"; boundary
  solid black in both). No further code change required.

## Next Action

- Done. Report to the user; leave the change uncommitted for review.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-08-12 | The user reads the solid boundary line as a shared stylistic element, not a per-chart quantity. | Opened this ticket to unify it to black #111111 in both charts. |
| 2026-08-12 | The other agent's "solid is per-chart, not shared" rule was the exact thing the user rejected. | Replaced it with a shared solid black boundary in both charts; docstrings updated to match. |
| 2026-08-12 | Both SVG generators were already color-coordinated on dashed series; only the boundary color diverged. | Changed two constants, regenerated, and verified one solid black polyline per SVG. |
| 2026-08-12 | The user wants ONE version that works in color AND B&W: keep colors, boundary = the one solid line per chart, all other series distinct dashes, consistent across the two charts. | Verified the current implementation already satisfies this: patterns distinct within each chart, baseline "1,4" and solid black boundary shared across charts. No change needed. |
