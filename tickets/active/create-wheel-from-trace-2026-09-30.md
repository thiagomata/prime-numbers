# Create Big Wheel From Repeated Trace

**Created:** 2026-09-30
**Updated:** 2026-10-01
**Status:** Complete
**Depends on:** `tickets/active/create-wheel-repeat-filter-2026-09-30.md`

## Related Tickets

- `tickets/active/create-wheel-repeat-filter-2026-09-30.md` establishes the
  12-position `[2,4]` source, the fivefold expansion, and the filter result.
- `tickets/active/repeat-filter-rotate-cycle-path.md` describes the repeat,
  filter, and next-cycle ordering.

## Goal

Build a separate Three.js page where the small `[2,4]` wheel generates a
repeated flat trace, that trace bends into the surface of a wheel five times as
large, and filtering by 5 leaves the next wheel.

## Strategy

Start from the committed v2 page in a new `create-wheel-v3` directory. Preserve
its ruler, rolling wheels, contact timing, and filter result. Add explicit
construction states for laying out 60 equally spaced positions as five copies
of the 12-position source pattern, then bend the strip into a ring with
curvature rising from zero to `1 / (5 * baseRadius)`. The flat and curved path
use the same arc-length coordinate, so pin spacing is preserved. At closure,
the construction pins meet the existing large wheel pins before filtering.

## Current State

The strip now resets the ruler distance to zero when its stage begins. The
wheel's current angle is captured first for the existing alignment beat; old
contact meshes and per-wheel counters are then cleared so later contacts
restart from the same origin. Browser checks after a 2.2-second stage-0 delay
showed strip pin 7 directly over ruler 7 in both close and full-strip views.
The bend still handed off to the enlarged wheel, and the browser logged no
errors. JavaScript syntax passed. No filtering behavior changed.

Each of the 20 candidate pins now has its value `7 + position` above it on the
flat strip. The sprites reuse the existing number texture and scale with camera
height to keep the text readable at the close and full-strip zooms. Close pairs
are vertically staggered, while each label remains horizontally aligned with
its pin. Labels disappear at the bend step. Desktop full-strip and mobile
tracking views were inspected; mobile screenshot pixel sampling found rendered
label ink and the browser reported no errors. The temporary viewport was reset
and the page remains at the completed-strip step. Filtering order was not
changed. JavaScript syntax passed.

The source wheel now interpolates from its arbitrary stage-0 phase to pin 0
before the strip grows, then makes exactly five turns over 10 seconds. A guide
connects the moving contact to the strip's leading edge, brightening at pin
contacts. Desktop framing tracks the contact at a readable scale, then reveals
the full strip before the bend. Mobile framing keeps the wheel inside the
viewport. The source-wheel ground highlight follows its travel. Browser
inspection confirmed the moving construction, strip overview, large-wheel
handoff, and no console errors; JavaScript syntax checks passed. The temporary
viewport override was reset without changing the user's current step.

The source wheel now rolls beside the strip's leading edge and stops when the
five copies are complete. Its travel and phase derive from the same
`traceProgress * TRACE_LENGTH`; the background ruler distance is held during
strip growth and bending, then resumes for filtering and the resulting wheel.
Desktop and mobile browser checks show the source wheel beside the strip,
the completed strip and bend, and the formed large wheel. Two captured frames
of the stopped wheel had zero mean pixel difference in the wheel region. The
temporary mobile viewport was reset and the page was reopened at step 1.

The separate `create-wheel-v3/index.html` has five stages: source wheel, five
flat trace copies, bending into the enlarged wheel, filtering by 5, and the
resulting wheel. Desktop and narrow mobile views were checked through the
complete forward sequence. The mobile camera follows the leading strip segment
and returns to the completed ring. The viewport test screenshot scales all page
content by `1 / devicePixelRatio`, including DOM buttons, while measured CSS
bounds remain correct; this is a capture artifact rather than a WebGL defect.
The temporary viewport override has been reset. Both viewport screenshots
contain many distinct scene colors and dark wheel pixels, and the browser
reports no console errors. JavaScript syntax and whitespace checks passed.

## What is Learned

- The source has four active pin offsets in 12 slots: `0, 4, 6, 10`.
- Five copies span 60 slots and contain 20 candidate pins. Four candidates
  are multiples of 5; 16 survive.
- The existing large wheel's radius is five times the source radius, so its
  contact circumference has exactly the length of the 60-slot flat strip.
- The v2 step 3 to 4 transition is smooth because it keeps the same wheel
  object; this should be retained after construction.
- A flat path parameterized by arc length and bent with curvature from zero to
  `1 / expandedRadius` places its final 60 slots exactly on the large wheel's
  contact circle. Rotating the curve by the wheel's current phase keeps the
  construction pins aligned at closure.
- On mobile, framing all 60 flat positions at once reduces the source wheel and
  pin marks to tiny shapes. Following the strip's leading end keeps local pin
  spacing readable, then the camera can return to the completed ring.

## Failed Paths

- The v2 presentation makes the large wheel appear fully formed at the repeat
  step. That does not reveal how the repeated trace creates its surface. Reuse
  the resulting wheel geometry only after a visible trace-to-ring construction.
- Zooming to the entire flat strip as soon as its stage begins makes the first
  copied marks too small. Increase camera width as the visible strip grows;
  revisit this only if the growth still clips at its leading edge.
- A full-strip fit on a narrow viewport remains too small even with gradual
  widening because the strip is about 24.5 world units long. Use a tracking
  window for mobile; revisit a full fit only with a separate magnified inset.
- Explicitly sizing the WebGL backing buffer did not change the narrow-view
  screenshot artifact. DOM controls also appear scaled and offset in the
  screenshot despite correct CSS bounds, proving the artifact comes from the
  viewport capture path. Retest actual app sizing only if DOM bounds diverge.

## Open Concerns

- Mobile follows a readable local segment rather than fitting all 60 positions
  simultaneously; an overview plus inset would require a separate design pass.
- The new page is uncommitted pending user review.
- The 0.8-second alignment beat is a visible rotation from the freely spinning
  pose to pin 0 before any trace is drawn.

## Next Action

Present the corrected ruler alignment for user review.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-09-30 | The user wants the large wheel surface to emerge from five copies of the small wheel's trace. | Plan an arc-length-preserving strip that bends into the existing 60-slot wheel. |
| 2026-09-30 | The v2 page already provides continuous filtering and next-wheel rotation. | Copy v2 into a new page, then insert trace and bend stages ahead of filtering. |
| 2026-09-30 | All five stages render. The strip reaches a full 60 slots and bends into a ring that hands off to the large wheel. | Browser check revealed the ground boundary and dense labels in the wide view; refine framing before final QA. |
| 2026-09-30 | Wide desktop framing now shows the strip and sparse ruler labels clearly, but the same full-strip fit makes mobile marks tiny. | Plan a mobile tracking camera that follows the repeated trace and ends on the formed wheel. |
| 2026-09-30 | Mobile screenshots scale the whole page by `1 / devicePixelRatio`; DOM canvas and controls occupy the expected CSS bounds. | Treat the apparent right gap as a capture artifact and restore the renderer's ordinary pixel-ratio setup. |
| 2026-09-30 | The mobile bend closes into the final wheel, filter pins disappear, surviving pins recolor, and pixel samples in both viewport captures are nonblank. | Complete browser QA, reset the viewport override, and leave v3 open for review. |
| 2026-10-01 | The source wheel should stop while the trace is constructed; all rolling motion shares one distance counter. | Pause that counter only during trace and bend stages, then verify the final wheel resumes. |
| 2026-10-01 | The user clarified that the source wheel should spin while travelling beside the growing strip, then stop. | Couple source-wheel travel and phase to trace progress rather than simply freezing it. |
| 2026-10-01 | The coupled wheel reaches the strip end and remains visually fixed while the strip bends. | Verify desktop/mobile handoff, reset the test viewport, and leave v3 at its opening step. |
| 2026-10-01 | Stage 1 inherits an arbitrary phase from stage 0, so source pin contacts do not necessarily line up with the fixed strip pattern; five turns in 3.4 seconds compound the confusion. | Align phase before growth, slow the repeated pass, and add a contact cue. |
| 2026-10-01 | A brief contact flash and a shrinking desktop camera still obscure the relationship. | Keep a visible contact guide during growth, track the wheel closely, then pull back to show all five copies. |
| 2026-10-01 | Mobile tracking lag briefly clipped the wheel mid-pass. | Add lead room, verify the moving wheel and guide remain visible, and reset the test viewport. |
| 2026-10-01 | The distant ruler makes pin values hard to infer. The user wants numbers directly above the flat-strip pins, without changing filtering yet. | Add labels for the 20 candidate pins and verify the full-strip zoom remains readable. |
| 2026-10-01 | Large single-row labels were legible at overview zoom but close values visually crowded together. | Stagger only the adjacent pairs, verify close/full/mobile views, and leave filtering unchanged. |
| 2026-10-01 | The stage-0 distance remains in the ruler while the new strip starts at x = 0, causing its pin 7 to sit over a later ruler value. | Reset ruler distance and contact bookkeeping when stage 1 begins, then verify close and overview alignment. |
| 2026-10-01 | After resetting the stage-1 origin, strip 7 and ruler 7 share x = 0, including after a delayed transition from stage 0. | Browser-check close/overview views and the formed-wheel handoff; leave the user's current step undisturbed. |
