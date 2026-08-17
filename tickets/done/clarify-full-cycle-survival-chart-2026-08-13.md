# Clarify the Full-Cycle Survival Chart

**Created:** 2026-08-13
**Updated:** 2026-08-13
**Status:** Complete
**Depends on:** `../done/fixed-lineage-cumulative-hazard-chart-2026-08-12.md`

## START HERE

Redesign `full-cycle-survival.svg` around one question: how much of the
normalized complete-cycle 2-gap population remains under the exact `2/r`
destruction law compared with the hypothetical `c=1` damage schedule? Do not
add head-recurrence or twin-prime claims.

## Related Tickets

- `../done/fixed-lineage-cumulative-hazard-chart-2026-08-12.md` — established
  the exact-cycle baseline, fixed-window boundary interpretation, valid r=29
  anchor, and current article integration.

## Goal

Replace the ambiguous three-curve survival figure with a self-explanatory
comparison whose title, axes, direct labels, and endpoint annotation state the
quantity, normalization, result, and limitation without requiring the reader
to reverse-engineer the formulas.

## Strategy

Keep the verified numerical products unchanged. Plot only the exact-cycle and
`c=1` products on a logarithmic y-axis, express the y-axis as the fraction of
the r=29 normalized starting population remaining, label the two curves
directly, and state their r=251 values and ratio. Remove the fitted Mertens
curve because it answers an asymptotic question rather than the chart's finite
comparison.

## Current State

- `compute_layers` is green on the valid range 29 <= r <= 251.
- At r=251 the normalized exact-cycle product is 0.3732537 and the normalized
  `c=1` product is 0.00367570, a ratio of about 101.55.
- The regenerated chart contains only the exact-cycle and `c=1` schedules on
  a log y-axis. It directly states the normalization, endpoint percentages,
  102x endpoint separation, and head-recurrence limitation.
- A compact right-margin legend now matches the line-swatch convention of the
  other frontier charts and defines both product formulas.
- The draft article already cites the chart and states the endpoint values and
  r=29 normalization.

## What is Learned

- The figure's main result is a finite separation between two normalized
  survival schedules, not evidence of random placement or head recurrence.
- A log y-axis is appropriate because both plotted quantities are positive and
  span more than two orders of magnitude.
- Direct curve labels communicate the comparison more efficiently than a
  legend alone; a compact legend is still useful for defining line styles and
  formulas. The two devices serve different roles and can coexist.
- The user's SVG viewer rendered both curves correctly. ImageMagick's local
  rasterization omitted multi-point lines while retaining endpoints, so that
  preview was a renderer limitation rather than an SVG defect.

## Failed Paths

- **Three-curve chart with a fitted Mertens reference.** It mixes a finite
  exact comparison with an asymptotic fit, so the reader cannot tell which
  relationship is primary. Retry only in a separate asymptotic-product figure.
- **Linear y-axis.** It compresses the `c=1` product near zero and hides its
  magnitude. Retry only if the figure shows an additive rather than
  multiplicative quantity.
- **Calling the quantity twin-prime survival.** Complete-cycle abundance does
  not establish head location or recurrence. Retry only for a dataset that
  tracks the distinguished head pair with justified availability and
  dependence semantics.

## Open Concerns

- The phrase “starting population” must make clear that both curves are
  normalized products, not observed counts.
- The endpoint ratio depends on the finite r=29 anchor and must not be
  presented as an invariant constant.
- No open concerns remain for this chart. The finite-anchor and no-head-
  recurrence limitations are visible in the SVG itself.

## Next Action

None. The clarified chart and legend are generated and validated.

## Validation

1. Establish and retain the Python green gate with `just empirical-test`.
2. Assert every plotted value is positive and the endpoint ratio matches the
   annotation.
3. Regenerate `full-cycle-survival.svg` through the root recipe.
4. Parse the SVG as XML and inspect all visible text.
5. Visually render the SVG if the available renderer supports it; otherwise
   record the renderer limitation and inspect geometry/text bounds from source.
6. Run `git diff --check` and verify the article's description remains exact.

## Implementation Plan

1. Simplify and relabel the SVG presentation without changing product values.
2. Regenerate and validate the artifact.
3. Update the article wording only if the revised figure changes a stated
   presentation detail.
4. Record results and close the ticket.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-08-13 | The current chart is mathematically correct after the r=29 repair, but its three curves, linear axis, sidebar, and formula-heavy legend obscure its single useful finite comparison. | Redesign around two directly labeled positive products on a log y-axis. |
| 2026-08-13 | The redesigned SVG states the normalization and limitation, uses two log-scale curves, and labels the r=251 values and 102x separation directly. The user's SVG viewer confirmed that both curves render; ImageMagick's missing curves were a rasterizer-specific preview limitation. | Add a compact line-swatch legend consistent with the other frontier figures. |
| 2026-08-13 | Added the `survival schedules` legend: solid blue is the exact-cycle product and dashed black is the `c=1` product. XML inspection, endpoint identities, `just empirical-test`, and `git diff --check` are green. | Done. |
