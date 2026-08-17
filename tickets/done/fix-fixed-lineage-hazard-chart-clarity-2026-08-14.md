# Fix Fixed-Lineage Hazard Chart Clarity

**Created:** 2026-08-14
**Updated:** 2026-08-14
**Status:** Complete — implementation, artifact, documentation, and all gates green
**Depends on:** `../done/fixed-lineage-cumulative-hazard-chart-2026-08-12.md`, `python-reorganization-2026-08-14.md`

## START HERE

Establish the complete Python baseline, then change one chart concern at a
time. First extract and test the plot geometry so reference and empirical
series cannot silently leave their panels. Then repair the visual layout,
update paths/provenance, regenerate the SVG, and run the complete Python gate.

Preserve the large staged Python reorganization. Do not reset, unstage, or
delete any unrelated work.

## Related Tickets

- [`../done/fixed-lineage-cumulative-hazard-chart-2026-08-12.md`](../done/fixed-lineage-cumulative-hazard-chart-2026-08-12.md) — defines the fixed-window cohort, formulas, chart contract, and interpretation boundary.
- [`python-reorganization-2026-08-14.md`](python-reorganization-2026-08-14.md) — moves the generator into the canonical `python/` package and its output into root-level `charts/`.
- [`../done/clarify-full-cycle-survival-chart-2026-08-13.md`](../done/clarify-full-cycle-survival-chart-2026-08-13.md) — records the shared preference for direct, obvious visual communication.

## Goal

Make `charts/fixed-lineage-hazard.svg` clearly show both the measured
fixed-window boundary effect and its distance from the `c=1/2` and `c=1`
comparison scales. The generator, tests, documentation paths, SVG provenance,
and generated artifact must agree inside the reorganized Python project.

## Strategy

Give each panel one visual role. The upper panel remains a zoomed view of the
measured cumulative excess and keeps only the zero reference. The lower panel
uses the normalized effective coefficient on the full comparison scale with
references at `0`, `1/2`, and `1`. This avoids expanding the upper scale until
the empirical signal becomes unreadable.

Use sparse logarithmic ticks, compact legend labels, and a wider right margin.
Test computed geometry and semantic SVG content rather than merely testing
that XML is well formed. Record repository-relative input paths in the SVG,
update the generator docstring and article image path, then regenerate through
the packaged module.

## Current State

- The root-level SVG exists at `charts/fixed-lineage-hazard.svg`.
- The generator exists at `python/src/sieve_sequence/fixed_lineage_hazard_chart.py`.
- The focused chart gate passes `5/5` tests.
- The complete Python baseline passes `239/239` tests.
- The upper y-range is derived only from empirical excess values, but the
  generator draws `log(r)` and `2 log(r)` on that scale. Their SVG y
  coordinates are thousands of pixels above the visible panel.
- Every prime is labeled on both x-axes, producing overlapping labels.
- The right legend identifies the Q-series and references, but its long labels
  exceed the available margin.
- The generator docstring still names the old direct invocation and `out/`
  destination.
- The draft article still embeds the old presentation-directory SVG path.
- The canonical root-level SVG has been regenerated through
  `just empirical-chart-hazard` with repository-relative source annotations.
- The Python reorganization and chart artifacts are not yet committed; they
  must remain intact throughout this work.
- The focused chart gate now passes `11/11`, including sparse ticks, finite
  data, empty input, semantic legend content, panel coordinate bounds, and
  deterministic provenance.
- The draft article now embeds the root-level `charts/` artifact, and the
  architecture gap catalog no longer lists this chart as untested or missing
  source annotations.
- Visual inspection confirms seven readable logarithmic ticks, separated panel
  roles, unclipped compact legend text, and visible `0`, `1/2`, and `1`
  comparison levels. The lower empirical curves remain intentionally near
  zero; their detailed variation is carried by the upper zoom.
- Final validation passes all `245/245` Python tests.
- Two consecutive packaged generations produced the identical SHA-256
  `93212e4e4bf5a9947a1c75177b09910468a4c0dba5a6dc40025c944e9eebbbc8`.
- Scoped diff and path audits are clean. No live article or generator retains
  the old presentation-directory output path.

## What is Learned

- Showing `log(r)` and `2 log(r)` on the empirical excess scale is structurally
  incompatible with a readable zoom because the measured values are near zero.
- The normalized `c_eff` panel already provides the correct common scale for
  comparing measured excess with the `1/2` and `1` thresholds.
- Well-formed-SVG tests do not detect off-canvas series, label collisions, or
  missing semantic legend entries.
- SVG provenance should be deterministic and repository-relative; absolute
  workstation paths and timestamps undermine reproducibility.

## Failed Paths

- **Plotting `log(r)` and `2 log(r)` on the zoomed empirical panel.** The
  reference coordinates leave the viewport because the scales differ by
  orders of magnitude. Retry only if the panel is intentionally changed to a
  full comparison scale, which would sacrifice its empirical-detail role.
- **Labeling every incoming prime.** Labels collide over the larger Q runs.
  Retry only for an interactive or much wider full-detail chart.

## Open Concerns

- The lower full-scale panel makes the threshold comparison obvious but keeps
  the small empirical variation visually close to zero. The upper panel must
  retain that detail so the pair works together.
- Extinction produces non-finite hazard values. The chart must reject or omit
  them deterministically rather than emitting invalid SVG coordinates.
- A single-layer input has no logarithmic x span and needs an explicit mapping.
- The article source is already staged as part of unrelated work; only the
  image-path line should be changed.

## Validation

1. Baseline: run `python/.venv/bin/pytest python/tests/ -q`.
2. After each chart/test change, run
   `python/.venv/bin/pytest python/tests/test_fixed_lineage_hazard_chart.py -q`.
3. Run the packaged generator into a temporary directory and inspect the SVG
   geometry and semantic labels.
4. Regenerate the canonical root-level SVG with
   `cd python && .venv/bin/python -m sieve_sequence.fixed_lineage_hazard_chart`.
5. Render the final SVG to PNG and inspect it visually.
6. Final gate: run `python/.venv/bin/pytest python/tests/ -q` and the relevant
   chart recipe.

## Next Action

None. The chart clarity repair is complete. Include these files when the
pending Python reorganization is committed.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-08-14 | Audit confirmed that the files exist locally and focused tests pass, but two reference curves are off-canvas, prime ticks collide, paths are stale, and the artifact is behind the generator. | Create this repair ticket and establish the full Python baseline before editing source. |
| 2026-08-14 | The complete reorganized Python suite is green at `239/239`. | Add the pure sparse-log-tick selector as the first isolated source change. |
| 2026-08-14 | The sparse-log-tick helper preserved the existing focused green gate at `5/5`; its representative seven-tick output is `[3, 7, 17, 37, 89, 251, 499]`. | Add one exact-output regression test, then wire the helper into both axes. |
| 2026-08-14 | The exact sparse-tick regression passed, bringing the focused gate to `6/6`. | Replace the hard-coded list used by both x-axes with the tested selector. |
| 2026-08-14 | Both panels use the sparse selector and the focused gate remains green at `6/6`. | Extract finite series centrally so extinction values cannot emit invalid SVG coordinates. |
| 2026-08-14 | Central finite-series extraction preserved the focused green gate at `6/6`. | Add one exact regression covering infinity, NaN, and invalid nonpositive filter positions. |
| 2026-08-14 | The finite-series regression passed and raised the focused gate to `7/7`. | Add explicit empty-data and single-layer x-axis behavior. |
| 2026-08-14 | Empty data now raises a descriptive error and a single observed filter maps to the plot center; existing tests remain green. | Add the explicit empty-input regression before changing final geometry. |
| 2026-08-14 | The explicit empty-input regression passed, bringing the focused gate to `8/8`. | Remove `log(r)` and `2 log(r)` from the zoomed upper panel while retaining the zero baseline. |
| 2026-08-14 | Removing the incompatible upper comparison curves preserved the focused green gate at `8/8`. | Clarify the two panel roles, widen the legend, and use non-overlapping lower comparison ticks. |
| 2026-08-14 | The clarified layout preserved the focused green gate at `8/8`. | Add an SVG semantic regression for panel roles, Q-series labels, and reference-style meanings. |
| 2026-08-14 | The semantic legend and panel-role regression passed, bringing the focused gate to `9/9`. | Add a geometry regression requiring every polyline point to remain inside one plot panel. |
| 2026-08-14 | The coordinate-bound regression passed, bringing the focused gate to `10/10`; it would fail on the former off-canvas `log(r)` curves. | Replace machine-dependent SVG comments with repository-relative input and formula annotations. |
| 2026-08-14 | Deterministic repository-relative provenance and packaged run instructions preserved the focused green gate at `10/10`. | Add one exact provenance regression before documentation updates. |
| 2026-08-14 | The exact provenance regression passed, bringing the focused gate to `11/11`. | Correct the article image path and remove resolved fixed-lineage gaps from the architecture catalog. |
| 2026-08-14 | The packaged recipe regenerated the canonical SVG. Visual inspection confirms sparse ticks, distinct panel roles, readable legend/caption text, and correct threshold placement. | Run complete Python and deterministic-artifact gates. |
| 2026-08-14 | Final gates passed: `245/245` Python tests, deterministic double-generation hash match, and clean scoped diff/path audit. | Mark complete and move this ticket to `tickets/done/`. |
