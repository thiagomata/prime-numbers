# Stop Rope Spin During Bend

**Created:** 2026-10-01
**Updated:** 2026-10-01
**Status:** Complete
**Depends on:** `tickets/active/keep-bending-strip-above-sand-2026-10-01.md`

## Goal

Keep the v4 strip stationary in orientation while it bends into the wheel.
Returning from the rolling wheel must not make it spin rapidly.

## Strategy

Remove the travel-dependent rotation from the strip bend. When returning
from step 5 to step 4, reset the construction's ruler/travel origin and old
contact marks so the unrotated strip still matches values 7 onward. Let the
formed wheel begin its normal slow roll only in step 5.

## Current State

`tracePoint` now returns the unrotated bend path. Returning from step 5 to
step 4 resets distance, contact counters, and old footprints, so the strip
again starts above 7 on the ruler. The formed wheel resumes slow rolling in
step 5. JavaScript syntax passes. Browser checks show a stationary-orientation
bend and aligned ruler on desktop, a clear bend on mobile, nonblank canvas
captures, and no browser errors.

## What is Learned

- The strip can bend without rotating: its arc length and final 60-slot
  circumference are determined before the phase is applied.
- A static bend should return to the construction's original ruler origin
  before handing off to the rolling wheel.

## Failed Paths

- Keeping the old phase and only fixing its center kept the strip above sand
  but did not address the distracting spin.

## Open Concerns

- None for this scoped behavior change.

## Next Action

Leave the updated v4 page open for user review.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-10-01 | Accumulated rolling distance drives the fast bend spin on replay. | Remove phase and reset the construction origin when returning from step 5. |
| 2026-10-01 | The return path now begins at 7 and forms the wheel without strip rotation. | Verify handoff, desktop/mobile pixels, and browser errors. |
