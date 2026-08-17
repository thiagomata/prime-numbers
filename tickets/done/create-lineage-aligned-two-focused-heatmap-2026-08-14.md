# Create A Lineage-Aligned 2-Focused Heatmap

## START HERE

Complete. Both charts are preserved, the aligned alternative is generated and
documented, all Python and Markdown gates are green, and the article explains
that raw rotation precedes display compression. No further action is required.

## Goal

Add an alternative 2-focused heatmap whose vertical coordinates compensate for
the head advance in compressed rather than raw-gap coordinates. Keep the
existing chart unchanged so the article can compare independent per-row
compression with shared-2 alignment. The work is complete when the pure offset
logic is tested, only new chart assets are generated, both figures are explained
without overstating lineage beyond the shared anchor, and all affected Python
and Markdown gates are green.

## Strategy

Work green-to-green in the Python ecosystem. First run the relevant import and
`test_gap_heatmap.py` gates against the dirty worktree. Research the alignment as
a pure mapping before editing: for a 2-gap start shared by adjacent rows, require

```text
old_offset + old_compressed_index == new_offset + new_compressed_index.
```

Prefer the earliest visible shared 2-gap because the copy-only prefix before the
incoming filter's first real merge is the region the chart is meant to expose.
Add one pure helper or one focused test per change and repeat the relevant gate
after each. Generate only the new SVG/PNG rather than running the all-chart main
entry point. Inspect the rendered asset before documenting it. Finally, keep the
old and new charts together in the article with an explicit comparison of their
coordinate systems and evidence boundaries.

## Current State

- The article currently embeds `charts/gap-heatmap-2focused.svg`, whose rows are
  independently compressed and begin at their own heads.
- `charts/gap-heatmap-staggered.png` successfully uses a one-raw-gap shear to
  compensate the stage-head advance in the uncompressed representation.
- A fixed one-cell shear is not generally valid after 2-focused compression:
  advancing one raw gap may shorten the leading compressed run without removing
  a compressed cell, or may remove a complete run/2-gap cell.
- The existing 2-focused SVG/PNG, generator, tests, and article already contain
  user changes and must be preserved rather than rewritten.
- The Python package import is green and the focused heatmap baseline passes all
  67 tests in 0.15 seconds on the current dirty worktree.
- The actual-data audit covers all 200 stages and 199 adjacent pairs. Every pair
  has a shared visible 2-gap, the earliest such anchor is strictly before the
  old head squared, and every safe shared 2-gap in the pair gives the same
  compressed-index delta.
- The 199 deltas are exactly `0` or `1`: 118 zero-offset transitions and 81
  one-cell transitions. Cumulative offsets range from 0 to 81, so the aligned
  canvas expansion is small and needs no negative-offset normalization.
- `shared_two_gap_offsets` now implements that audited rule as a pure helper. It
  rejects missing safe anchors, inconsistent safe-prefix shifts, and shifts
  outside zero or one instead of silently drawing an ambiguous alignment.
- After adding the helper, the package import remains green and all 67 focused
  heatmap tests pass in 0.16 seconds.
- A hand-built regression now covers all three head effects: shortening a
  leading non-2 run gives no compressed-cell shift, removing that run gives one
  shift, and removing a standalone 2-gap gives another. Its cumulative result
  is `[0, 0, 1, 2]`, and the focused suite passes all 68 tests in 0.19 seconds.
- `build_compressed_grid_png` now accepts an optional exact offset per row,
  validates its length and sign, and otherwise derives the same fixed-stagger
  offsets as before. The focused suite remains 68/68 green after the refactor.
- A raw raster regression now proves that exact offsets `[0, 1]` produce a
  two-cell canvas with the first green 2-gap in column zero and the second in
  column one. The focused suite passes all 69 tests in 0.19 seconds.
- A separate regression proves `stagger=1` still produces that same two-row
  placement. The focused suite passes all 70 tests in 0.18 seconds.
- `build_compressed_heatmap` now accepts and forwards optional exact row offsets
  while preserving every existing call. The focused suite remains 70/70 green.
- A temporary-output spy regression proves the builder forwards offsets
  `[0, 0, 1]` unchanged. The focused suite passes all 71 tests in 0.17 seconds.
- The main entry point now includes a separately named aligned PNG/SVG block
  with an explicit shared-pre-square-2 title. Existing normal and fixed-stagger
  output calls remain in place, and the all-chart main has not been run.
- Isolated generation wrote only the new pair. The PNG is 1481x200 (11 KB), the
  SVG is 1591x940 (30 KB), and the SVG title explicitly states that rows are
  aligned by shared pre-square 2-gaps.
- Visual inspection against both retained references shows the intended result:
  safe-prefix green 2-gap lines are straight and vertical in the aligned chart,
  the independent 2-focused chart retains its curved/diagonal drift, and the raw
  staggered chart is vertical in its different raw-gap coordinate system.
- The article introduction now retains View A and adds View B, defines both
  x-coordinates from zero, explains the zero/one compressed shift and white
  wedge, reports the 118/81 observed split, and limits the aligned claim to the
  safe prefix. All four local source/data/chart links exist and its scoped
  `git diff --check` is green.
- `charts/PREVIEW.md` now lists the aligned chart immediately after the original
  2-focused view, explains its zero/one shift rule, and states that the straight
  lines show checked observed alignment rather than a theorem. Its image target
  exists and its scoped `git diff --check` is green.
- Final validation is green: package import succeeds, the focused heatmap suite
  passes 71/71, the complete Python suite passes 249/249, all old and new chart
  assets exist, and repository-wide `git diff --check` passes after the user
  authorized removal of one unrelated trailing space.
- The user accepted both charts unchanged and requested that the article retain
  the key interpretive result: rotation consumes one raw gap per stage, whereas
  the 2-focused combined cell exists only after display compression.
- The article now includes the correct example
  `$[18,2,\ldots] \to [14,2,\ldots] \to [8,2,\ldots] \to [2,\ldots]$`, explicitly
  identifying the long blue feature as a decreasing raw-run suffix rather than
  one unchanged merged gap. Both chart targets exist and its scoped Markdown
  diff check is green.

## What is Learned

- Horizontal movement inside one 2-focused row traverses the compressed list,
  while a stage transition advances the head through exactly one raw gap. Those
  are different coordinate systems.
- The existing chart is valid as a collection of independent compressed
  snapshots but can mislead if read as vertically aligned stage lineage.
- For a leading raw run `[a1,...,an,2,...]`, successive compressed rows begin
  `[sum(ai),2,...]`, `[sum(ai)-a1,2,...]`, and so on. The leading cell changes
  value but does not disappear until the entire run has been traversed.
- The relevant existing Python behavior is green before implementation, so any
  later focused-test failure can be attributed to this ticket's changes.
- On the real dataset, earliest-shared-2 alignment is not a heuristic: each
  anchor lies in the copy-only prefix and all other shared safe 2-gaps confirm
  the same offset. The number of safe shared anchors per pair ranges from 1 to
  10,229.
- The source helper independently checks every safe shared 2-gap in an adjacent
  pair, so the renderer will consume only offsets whose exact safe-prefix
  agreement has already been established.
- The zero-shift case is now protected explicitly; a renderer cannot safely
  replace this variable alignment with a fixed one-cell shear.
- The rasterizer can now consume the audited offsets without duplicating its
  color or truncation behavior in a second rendering implementation.
- Exact per-row placement is tested below the SVG layer, so any later visual
  movement is attributable to builder geometry rather than raster ambiguity.
- Both coordinate inputs to the rasterizer are now explicit regressions: exact
  offsets for the new view and fixed staggering for the retained old view.
- The SVG builder now exposes the tested raster seam without requiring a second
  copy of its sizing, labeling, legend, or PNG-embedding logic.
- The exact offset computation, raster placement, compatibility path, and SVG
  forwarding are all independently green before adding any committed output.
- Future full regeneration will include both independent-snapshot and aligned
  charts, while this ticket can create the new pair without overwriting older
  user-owned assets.
- The variable left white wedge in the aligned raster is expected display
  padding: cumulative offsets range from zero to 81 and preserve shared safe
  2-gap columns rather than forcing every row to restart at column zero.
- The side-by-side discussion treats the original as a valid collection of
  snapshots rather than calling its data wrong; only the vertical-lineage
  interpretation is rejected.
- The aligned output is now discoverable both from the standalone article and
  from the chart preview index, with consistent evidence boundaries.
- A long blue structure near the head is not one atomic merged gap being reused.
  It is the successively shorter suffix of the same raw non-2 run; it remains in
  one compressed column until its last constituent raw gap has passed the head.
- Rotating a compressed cell once per row would create a coherent alternative
  process, but it would not represent the actual Sieve Sequence transition used
  by these figures.

## Failed Paths

- The first repository-wide `git diff --check` failed on a pre-existing trailing
  space in `tickets/active/python-reorganization-2026-08-14.md`, not on this
  ticket's files. No cascading edit was made. After the user explicitly
  authorized that one-character formatting fix, the repository-wide check
  passed.

## Open Concerns

- An adjacent stage pair may have no shared visible 2-gap inside the sampled
  prefixes.
- A first shared 2-gap might occur after the true first merge at the old head
  squared; if so, it cannot certify alignment of the copy-only prefix.
- Later filtering genuinely destroys some 2-gaps, so the new chart must not be
  described as full lineage identity beyond its anchor and safe region.
- Offsets may become negative or enlarge the canvas; normalize only by a single
  global translation so relative alignment is preserved.
- The full chart generator overwrites many existing assets and must not be used
  merely to create this alternative.
- The worktree is dirty, including the target source, tests, charts, article,
  and active Python reorganization work. Preserve all unrelated edits.

## Next Action

None — complete.

## Validation Plan

- Baseline and repeat the package import and focused heatmap pytest suite.
- Run the broader Python suite only if its baseline is green and no unrelated
  active work makes it non-green.
- Audit all 199 adjacent pairs in the actual 200-stage dataset for a shared
  visible 2-gap, its location relative to the old head squared, offset signs,
  and maximum cumulative canvas expansion.
- Unit-test hand-derived cases where advancing the head shortens a leading run,
  removes a run cell, and removes a standalone 2-gap cell.
- Generate only the new aligned PNG/SVG and visually inspect it beside both
  existing 2-focused variants and the raw staggered chart.
- Verify all new article and README links, exact chart names, and
  `git diff --check`.
- This is a Python-and-Markdown change; Scala tests and Stainless verification
  do not apply.

## Related Tickets

- `tickets/done/evaluate-conditioned-separator-dynamics-2026-07-27.md`
- `tickets/done/review-presentation-gap-csv-insights-2026-07-27.md`
- `tickets/active/missing-empirical-charts-2026-08-11.md`
- `tickets/active/draft-mixed-adversarial-random-companion-2026-08-11.md`
- `tickets/active/python-reorganization-2026-08-14.md`
- `tickets/active/pytest-chart-modules-2026-08-14.md`

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-08-14 | The apparent pre-square noise comes from applying raw head-walk intuition to independently compressed row coordinates. | Opened a dedicated ticket to preserve the original chart and build a separately named, tested alignment rather than silently replacing it. |
| 2026-08-14 | The current dirty Python worktree has a green heatmap baseline: package import succeeds and 67 focused tests pass. | Established the language-scoped baseline before any generator or test edit. |
| 2026-08-14 | All 199 real transitions have a safe earliest shared 2-gap and internally consistent compressed-index delta; the deltas are 118 zeros and 81 ones, with cumulative range 0..81. | Accepted shared-2 alignment as the tested implementation strategy and rejected the need for a fallback heuristic on the current dataset. |
| 2026-08-14 | The pure offset helper can enforce the audited invariant without any rendering dependency; the existing focused suite remains 67/67 green after its addition. | Made malformed or ambiguous safe-prefix alignment an explicit error and moved the next micro-goal to a hand-derived unit test. |
| 2026-08-14 | The hand-derived sequence produces `[0, 0, 1, 2]`, proving that compressed alignment sometimes stays fixed and sometimes advances by one cell; all 68 focused tests pass. | Locked the distinction into a regression test before modifying any rendering path. |
| 2026-08-14 | The existing compressed rasterizer can support exact alignment with one optional per-row-offset seam while retaining its fixed-stagger default; 68 tests remain green. | Added the seam without changing any builder and recorded the missing direct nonzero-stagger regression as a separate obligation. |
| 2026-08-14 | Exact offsets `[0, 1]` place identical 2-gap cells in columns zero and one on a two-cell raster; all 69 focused tests pass. | Verified the new coordinate input at pixel level before connecting it to an SVG builder. |
| 2026-08-14 | The retained `stagger=1` path produces the same expected two-row placement and all 70 focused tests pass. | Closed the compatibility gap before exposing exact offsets through the SVG builder. |
| 2026-08-14 | The existing SVG builder can forward exact row offsets while reusing all current presentation logic; all 70 focused tests remain green. | Exposed the raster seam through one optional builder argument and moved next to a temporary-output forwarding regression. |
| 2026-08-14 | The SVG builder forwards exact offsets unchanged and all 71 focused tests pass. | Completed the tested source pipeline before adding a named output call or touching committed chart assets. |
| 2026-08-14 | The generator now names the aligned chart separately and labels its shared-pre-square-2 coordinate system; all 71 focused tests remain green. | Preserved both existing 2-focused outputs and kept the all-chart entry point unexecuted before isolated generation. |
| 2026-08-14 | The isolated aligned chart shows straight vertical safe-prefix 2-gap lines; the independent chart's drift is therefore a coordinate effect, not changing pre-square gaps. | Kept both assets and moved to an explicit side-by-side article comparison instead of replacing the original evidence. |
| 2026-08-14 | The introduction now explains both charts self-containedly: independent rows show texture, aligned rows show observed safe-prefix stability, and neither proves the later survival thresholds. | Preserved the original chart, added the alternative, and validated every local target plus the scoped Markdown diff. |
| 2026-08-14 | The preview index now documents and embeds the aligned view beside the original, with explicit empirical limits and a green link/diff check. | Completed user-facing discoverability and moved to final language-scoped regression and diff validation. |
| 2026-08-14 | Final validation passes: 71 focused tests, 249 full Python tests, asset checks, and repository-wide whitespace checks are green. The leading blue cell is a decreasing raw-run suffix because raw rotation precedes display compression. | Kept both charts unchanged and moved the newly clarified rotation/compression distinction into the article as the final micro-goal. |
| 2026-08-14 | The article now shows the correct `[18,2] -> [14,2] -> [8,2] -> [2]` countdown and distinguishes it from compressed-cell rotation; scoped links and whitespace checks pass. | Accepted the user's preferred graph unchanged and closed the completed ticket. |
