# Filter the Flat Strip Before Bending

**Created:** 2026-10-01
**Updated:** 2026-10-01
**Status:** Complete
**Depends on:** `tickets/active/create-wheel-from-trace-2026-09-30.md`

## Related Tickets

- `tickets/active/create-wheel-from-trace-2026-09-30.md` records the v3
  five-copy strip, numbered candidate pins, arc-length-preserving bend, and
  phase-aligned handoff.
- `tickets/active/create-wheel-repeat-filter-2026-09-30.md` records the
  four-pin filter of a 60-position repeated pattern.

## Goal

Test whether filtering multiples of 5 while the strip is flat makes the
removal rule clearer than filtering after the strip becomes a wheel.

## Strategy

Keep committed v3 available for comparison. Copy it to a separate v4 page,
then reorder the same five stages to source, repeat, filter flat strip, bend
filtered strip, next wheel. In the filter stage, make candidate values 25, 35,
55, and 65 visibly red before their pins disappear. Keep the strip's 60-slot
length unchanged, recolor the 16 survivors, and bend only those pins into the
large wheel. Preserve the v3 geometry, ruler origin, contact timing, and
camera behavior wherever the stage change does not require an adjustment.

## Current State

The separate v4 page is copied from committed v3. Its order is now repeat,
filter on the flat strip, bend the filtered strip, and roll the next wheel.
Candidate multiples of 5 are derived from the strip values, and the four bad
pins have independent materials so they can be highlighted and removed one at
a time. The strip geometry remains 60 slots long. Desktop shows the whole
strip during filtering; the narrow camera tracks each bad value. JavaScript
syntax passes. Desktop and narrow browser checks showed the four red values,
their pins disappearing, 16 surviving pins turning gold, and the filtered
strip bending into the next wheel. Both canvas captures were nonblank and
browser error logs were empty.

## What is Learned

- The flat 60-slot strip has 20 candidate pins. Values 25, 35, 55, and 65
  are the four candidate multiples of 5; the other 16 remain.
- Filtering must remove pins without compressing the strip; its circumference
  must still match the existing five-times-larger wheel.
- The strip already has per-pin number sprites and the full-strip overview,
  so the cause of each removal can be shown at its numbered position.

## Failed Paths

- The current v3 order removes pins after bending, when the nearby value
  labels are no longer visible. It demonstrates the final result but obscures
  why those four pins were selected.

## Open Concerns

- The page is an experimental v4 for comparison with committed v3; the user
  may prefer a different removal pace or emphasis after trying it.

## Next Action

Show the v4 page to the user for a direct comparison with v3.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-10-01 | The user wants to test filtering while values are readable above the flat strip. | Preserve v3 as a comparison and build a separate v4 with filter before bend. |
| 2026-10-01 | The existing 60-slot geometry can stay unchanged while the four bad pins are removed on the flat strip. | Reorder stage state, add per-pin filter animation, and derive bad positions from their displayed values. |
| 2026-10-01 | Desktop and mobile playback visibly removed only 25, 35, 55, and 65, preserved 16 survivors through the bend, and produced nonblank canvases without browser errors. | Complete the v4 experiment and leave v3 unchanged. |
