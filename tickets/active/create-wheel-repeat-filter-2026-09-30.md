# Create Wheel Repeat And Filter Visualization

**Created:** 2026-09-30
**Updated:** 2026-09-30
**Status:** In progress
**Depends on:** None

## Related Tickets

- `tickets/active/repeat-filter-rotate-cycle-path.md` — mathematical transition
  is repeat, filter by head, then start at the next head.
- `articles/chapter6/sieve-sequence.md` — §§4.3 and 5 describe repeated-cycle
  invariance and filtering by the current head.

## Goal

Build a separate simple Three.js page based on the walking-wheel animation. Start
from the established `[2,4]` wheel, repeat its 12-position pattern five times,
remove candidate pins hit by 5, and show the larger filtered wheel.

## Strategy

Reuse the walking-wheel's rolling-distance animation, numbered ruler, and
footprints. The 12-position source wheel has four pins with alternating gaps
`[2,4]`. Repeat those positions five times on a carrier with five times the
radius, preserving pin pitch and contact speed. Filter candidates divisible by
5, then show the 60-position filtered wheel. Keep this attempt in a new
`create-wheel-v2` page so the existing draft and walking-wheel reference remain
untouched.

## Current State

The current `create-wheel` page has a stationary two-wheel scene and does not
show repeat/filter construction. `walking-wheel` provides the reference
geometry, fixed ruler labels, and footprint animation. The first v2 draft
incorrectly started at `[1]`, repeated only 2x, and showed `[2]` as the result.
The corrected page now starts at `[2,4]`, repeats its 12-position cycle five
times, marks candidate multiples of 5, and shows the 60-position filtered wheel.
Browser review passed for all four states; source syntax and whitespace checks
pass. In the filter state, rejected pins now fully disappear and surviving pins
change to the next-wheel color; browser review confirms the visual handoff.

## What is Learned

- The `[1] → [2]` and `[2] → [2,4]` transitions remove bad pins without growing
  the displayed wheel. Growth begins after `[2,4]`, repeating by the next head,
  5.
- Repeating the `[2,4]` carrier five times multiplies circumference and
  position count by five while preserving the same arc pitch and linear contact
  speed.
- With a 12-position `[2,4]` source, the five-copy carrier has 20 candidates;
  four of those are multiples of 5, leaving 16 pins in the expanded period.
- Fixed ruler labels avoid changing a pin's printed integer when a visual pool
  recycles.
- The 12- and 24-position carriers need periodic contact rules, not a one-cycle
  index bound, or their footprints stop after the first revolution.

## Failed Paths

- Reassigning labels on recycled blocks made the same apparent pin change its
  number. Do not carry moving/recycled pin labels into this design; number marks
  belong to fixed ruler positions. Reconsider only if a new numbering model
  makes both identity and monotone sequence unambiguous.
- The first visual draft used the wrong transition, a 2x carrier, and an
  incorrectly small `[2]` result. The user clarified that pin removal alone
  models the first two transitions; growth starts after `[2,4]`.
- Scaling rejected pins to zero left thin red slivers. Hide them at the end of
  the removal animation instead.

## Open Concerns

- The gap cycle starts at 7, so the displayed `[2,4]` phase is `[4,2,4,2]`, a
  rotation of the same alternating gap pattern. Keep this phase alignment clear
  if the copy/filter animation is refined further.

## Next Action

No further action is required. The filtered carrier remains in place across the
step 3 → 4 handoff; browser review confirms rotation, ruler lane, and footprints
stay continuous.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-09-30 | User asked to restart from the walking-wheel visual language and show repeat, filter, and next-wheel states simply. | Read the article and existing wheel geometry; implement a separate page so the working reference stays unchanged. |
| 2026-09-30 | Growth must begin after `[2,4]`; the next head is 5, so the example repeats five times before filtering. | Rebuilt the v2 sequence around a 12-position `[2,4]` source and its 60-position filtered expansion. |
| 2026-09-30 | Four of 20 repeated candidate pins are multiples of 5, leaving 16 survivors. | Verified candidate positions from the configured gap phase and visually inspected each stage. |
| 2026-09-30 | User wants the survivors to take on the next wheel's color after bad pins are removed. | Make the recolor the completion cue of the filter animation. |
| 2026-09-30 | Zero-scale pins remain visible as thin slivers in the Three.js view. | Hide removed pins after the shrink animation, then verify the survivors are colored gold. |
| 2026-09-30 | Swapping to a separate wheel clone caused a visual jump at step 3 → 4. | Reuse the filtered carrier as the next wheel and verify its pose and trace continue without a lane change. |
| 2026-09-30 | The separate final-wheel clone jumps to another lane at the step 3 → 4 boundary. | Reuse the filtered repeated wheel as the final wheel so the state transition preserves its motion and position. |
