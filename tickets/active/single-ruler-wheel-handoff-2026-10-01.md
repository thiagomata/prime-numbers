# Single Ruler During Wheel Handoff

**Created:** 2026-10-01
**Updated:** 2026-10-01
**Status:** Complete
**Depends on:** `tickets/active/strip-filter-before-bend-2026-10-01.md`

## Goal

Show only the new wheel's ruler during step 4 and its handoff to step 5.

## Strategy

Keep both wheel geometries visible in step 4. Hide the old wheel's ruler
mesh, ticks, guides, and number sprites while leaving the repeated wheel's
ruler visible. Step 5 already shows only the repeated wheel.

## Current State

Step 4 keeps both wheel geometries but shows only the repeated wheel's ruler.
Dynamic ticks, guides, and labels use the same active ruler visibility. Step 5
continues to show that one ruler. JavaScript syntax passes; browser playback
and screenshots of the bend start, completed bend, and next wheel show one
ruler throughout.

## What is Learned

- Ruler meshes and dynamic tick/label markers use separate visibility paths.
  Both must follow the same active ruler selection.
- Step 5 already uses one ruler; step 4 causes the duplicate.

## Failed Paths

- None attempted for this fix.

## Open Concerns

- None for this scoped fix.

## Next Action

Leave the updated v4 page available for review.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-10-01 | Both visible wheels independently enable a ruler in step 4. | Keep the repeated wheel's ruler through the handoff and suppress the old one. |
| 2026-10-01 | Hiding the mesh alone would leave floating markers. | Bind marker visibility to active ruler lanes; verify the bend and next-wheel screenshots. |
