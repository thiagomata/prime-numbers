# Keep Bending Strip Above Sand

**Created:** 2026-10-01
**Updated:** 2026-10-01
**Status:** Complete
**Depends on:** `tickets/active/create-wheel-from-trace-2026-09-30.md`

## Goal

Keep the v4 strip and its pins visibly above the sand throughout the bend.

## Strategy

Inspect the current bend in the browser and sample its geometry over bend
progress. Correct the smallest geometric cause while preserving arc length,
the full 60-slot circumference, and the final wheel handoff.

## Current State

The user observes the strip entering the floor during step 4. Sampling the
old path after the wheel has rolled found strip vertices below the floor
(for example, bend 0.75 after 32 integer positions reaches about -1.046,
while the floor is -0.055). Rotating around the partial bend radius fixed
that defect; the later work in
`tickets/active/stop-rope-spin-during-bend-2026-10-01.md` removed bend
rotation entirely. The unrotated path also stays above sand. Desktop playback after
rolling shows the partial arc above sand, with no browser errors. Mobile
playback also stayed above sand. The narrow camera now widens and recenters
temporarily during the bend. Both forward and return-path mobile frames keep
the arc clear of the heading, ruler, and controls. Both canvas captures are
nonblank and browser error logs are empty.

## What is Learned

- The strip geometry is separate from the sand plane and from the final
  repeated-wheel mesh.
- The phase is zero on the first pass but becomes nonzero after the completed
  wheel rolls and the user revisits step 4. That is why the defect was easy
  to miss in a forward-only check.
- Rotation around the partial circle's center preserves ground clearance,
  but the later no-spin design makes rotation unnecessary during construction.

## Failed Paths

- Forward-only playback did not reproduce the problem because its phase was
  zero; the wheel must roll in step 5 before replaying step 4.
- The first mobile camera adjustment moved the arc but still let it cross
  the header; target height alone could not frame the full temporary circle.

## Open Concerns

- None for this scoped fix.

## Next Action

Leave the updated v4 page available for the user to review.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-10-01 | The user sees the bending strip enter the floor. | Investigate the actual partial-bend geometry before editing it. |
| 2026-10-01 | Nonzero rolling phase exposed a mismatch between the temporary bend radius and the fixed rotation center. | Rotate around the current bend radius and replay step 4 after rolling the next wheel. |
| 2026-10-01 | The first mobile camera adjustment still let the arc cross the header. | Increase mid-bend view height and target height together, then inspect another partial-bend frame. |
| 2026-10-01 | The widened mobile framing keeps the forward and return arcs visible above sand and outside the header. | Complete browser and canvas checks, then leave the updated page open. |
