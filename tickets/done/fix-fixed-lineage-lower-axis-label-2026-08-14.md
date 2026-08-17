# Fix Fixed-Lineage Lower Axis Label

**Created:** 2026-08-14
**Updated:** 2026-08-14
**Status:** Complete — two-line label implemented and all gates green
**Depends on:** `../done/fix-fixed-lineage-hazard-chart-clarity-2026-08-14.md`

## START HERE

Split the lower panel's single long vertical y-axis label into two short
parallel lines. Do not change formulas, scales, data, colors, or other layout.

## Goal

Make the lower left axis label fit comfortably inside the 300-pixel panel
while preserving the definition of `c_eff`.

## Strategy

Reuse the existing `vertical_text` primitive twice at adjacent x positions:
one line names `effective coefficient c_eff`; the second gives
`excess / (2 log r)`. Lock both phrases in the semantic SVG test.

## Current State

- Full Python baseline is green at `245/245`.
- The lower label is one rotated string:
  `effective coefficient: c_eff = excess / (2 log r)`.
- Its length is too close to the panel height and is visually cramped.
- The surrounding chart layout is already green and must remain unchanged.
- The final SVG places `effective coefficient c_eff` at x=17 and
  `excess / (2 log r)` at x=35, both at 11px, while tick labels end at x=85.
- Focused tests pass `11/11`; the complete Python suite passes `245/245`.
- Consecutive packaged generations produced the identical SHA-256
  `c15dae949bbfffbd2bebb47978712119c3ee55c7065f3f6c8784f0aa605e73e0`.

## What is Learned

- The issue is label layout, not chart scale or mathematical content.
- Two short vertical lines are clearer than shrinking the font.

## Failed Paths

- **One long rotated formula.** It uses too much of the available vertical
  span. Retry only if the panel becomes substantially taller.

## Open Concerns

- The two lines must not collide with each other, the y-axis tick labels, or
  the page edge.

## Validation

1. Run the focused fixed-lineage chart tests.
2. Regenerate the root-level SVG through `just empirical-chart-hazard`.
3. Render and visually inspect the SVG.
4. Run the complete Python test suite.

## Next Action

None. The lower axis label now fits as two lines and the artifact is current.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-08-14 | User review identified that the lower left label needs more space or two lines. The exact source is one long rotated string at the panel center. | Split it into two short vertical lines and verify visually. |
| 2026-08-14 | The first patch attempt was rejected before changing files because it contained an empty separator hunk. | Retry the identical isolated change with valid patch syntax. |
| 2026-08-14 | The lower label is now split across x=17 and x=35, using 11px text, and both phrases are required by the semantic SVG regression. | Run the focused chart gate before regeneration. |
| 2026-08-14 | Focused tests passed `11/11`; SVG geometry leaves clear space before the x=85 tick-label edge; the full suite passed `245/245`; deterministic regeneration hashes match. | Mark complete and move to `tickets/done/`. |
