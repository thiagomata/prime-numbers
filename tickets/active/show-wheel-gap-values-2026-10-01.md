# Show Gap Values Above Wheel Construction

**Created:** 2026-10-01
**Updated:** 2026-10-01
**Status:** Complete
**Depends on:** `tickets/active/strip-filter-before-bend-2026-10-01.md`

## Goal

Show the numeric gap pattern at the top of every v4 construction step, and
make the filter step's displayed gaps reflect removed pins.

## Strategy

Keep the source wheel's canonical `[2, 4]` cycle. Derive the repeated and
filtered gap prefixes from the same candidate positions and removal state
used by the animation. Present a compact prefix with an ellipsis so it fits
on mobile. Preserve the existing wheel geometry and stage timing.

## Current State

The top header now shows a numeric gap line in every step. The source wheel
shows its canonical `[2, 4]` cycle. Subsequent stages derive gap values from
the candidate positions; the filter stage recomputes them after each pin
disappears. Removing values 25, 35, 55, and 65 leaves a 16-gap cycle
beginning 4, 2, 4, 2, 4, 6, 2, 6. Desktop shows up to 16 values; narrow
viewports show eight plus an ellipsis. JavaScript syntax passes. Browser
screenshots of all five steps fit on desktop and mobile, and both canvases
are nonblank with no browser errors.

## What is Learned

- The source `[2, 4]` is the canonical gap cycle; the visible repeated
  strip starts at 7, so its displayed sequence begins with 4.
- The first 6 in the filtered sequence occurs after 23, where 25 was removed.
- Showing eight gaps plus an ellipsis includes the first changed gap and fits
  the narrow header more readily than the full 16 or 20 gap period.

## Failed Paths

- No implementation attempt yet. A hand-written filtered prefix would be
  fragile because the animation removes four pins progressively.

## Open Concerns

- None for this scoped display change.

## Next Action

Leave the updated v4 page available for user review.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-10-01 | The period derived from candidate positions changes from 20 alternating gaps to 16 gaps after filtering. | Compute the displayed prefix from the positions rather than storing a literal string. |
| 2026-10-01 | The numeric header fits on desktop and mobile; the filtered prefix includes the new 6 after removing 25. | Keep the full 16-gap cycle on desktop and a compact eight-gap prefix on mobile. |
