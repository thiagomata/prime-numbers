# Continuous two-gap focused animation

Created: 2026-10-20
Status: Complete

## START HERE

Create one standalone ManimGL animation linking pair contacts, ordered focused
cells and their separator histogram for the incoming filter 7.

## Goal

Deliver a numerically checked, visually inspected animation and reproducible
source showing exactly how 21 two-gaps become 15 in one expanded period.

## Strategy

Use filters 2,3,5 then incoming 7 on the complete expanded value period
[11,221), length 210. Plot a labeled curve zoom [41,101]; focused cells and
histograms always refer to the complete period. Keep cyclic wrap in separators.
Use the unweighted pair height H(t)+H(t+2), with the activated detector from
the existing scene. At these inputs all relevant filters are fully activated.
Highlight bad separator channels before revealing actual destroyed contacts.

## Related Tickets and Sources

- [Previous animation setup](continuous-complex-sieve-manim.md): temporary
  venv, explicit cache, audioop-lts, GPU escalation, no --fps argument.
- [Continuous construction](../future/continuous-complex-sieve.md).
- [Spectral positional analysis](spectral-positional-filter-analysis-2026-08-18.md):
  records the focused alternation law and the importance of separator values.
- properties/sieve-sequence/two-focused-alternation-law.md.
- properties/sieve-sequence/two-focused-bad-separator-deletion-bound.md.

## Current State

Existing scene --check baseline passes. Exact integer enumeration gives before
21 starts with histogram {4:7,10:14}; after 15 starts with histogram
{4:3,10:8,16:2,28:2}. Standalone two_gap_focused.py added; numerical checks,
compilation and configured scene import pass. Render passed on first attempt:
output/two-gap-focused.mp4 is1920x1080,30fps,750frames,25seconds. Four frames
at4,9,14,24seconds inspected for layout, scope labels, bad-channel highlights,
actual deletion markers and final distribution. Poster saved as
output/two-gap-focused.png; README includes verified scope and render commands.
Output links and git diff --check pass. The established ManimGL venv and
saved configuration exist; previous cache/setup failures will not be retried.

## Assumptions and Validation

- Pair contacts encode actual 2-gaps: filter 2 is installed, inputs are above
  the current head; independently compare numerical zeros with integer gcd.
- The expanded period is valid: 210 is divisible by both 30 and the new filter
  7; cyclic separators include the last-to-first displacement of 210.
- Bad channels are necessary, not sufficient, for double deletion: check every
  neighboring pair independently against integer rejection; compare detector
  values to divisibility of R, R+2 or R+4.
- Focused reconstruction preserves period: check sum(R+2)=210 at both stages.
- Check intended counts against the hand-enumerated histograms above.
- Compile/import, numerical CLI, GPU render, ffprobe and representative frame
  inspection are the Python-only gates. No Scala or Stainless gates apply.

## Alternatives and Risks

A full 210-wide curve makes individual contacts hard to see; a zoom with
explicit full-period labels retains readability without changing statistics.
A histogram alone loses adjacency, so retain the ordered cyclic focused row.
Do not interpret bad separators as actual deletions or claim new survival
theorems from finite data. Small cell labels require 1080p visual inspection.

## What is Learned

Before filter7, all separator values10 are bad and values4 are good, giving
14 bad edges and7 good edges. The cyclic bound guarantees at least4 survivors;
the exact transition leaves15. New merged separators16 and28 appear afterwards.
The existing Manim renderer needs GPU escalation; default integer30fps works.

## Failed Paths

Pre-execution review corrected an incomplete informal zoom-loss list: 89 also
disappears because 91=7*13. Actual source generates all removal markers from
the exact data; it does not hardcode the initial mistaken list. Prior setup failures and solutions are recorded in
the predecessor ticket. Known unsupported Unicode subscripts will be avoided.

## Open Concerns

Scene implemented, numerically checked, rendered and visually inspected.
Badness refers to the pre-filter
expanded population. The same arithmetic test on the resulting histogram is
a diagnostic, not a new filter transition. Analytic construction is not
Stainless-verified.

## Next Action

Done. Deliver animation and source/reproduction notes. Research on stronger
distribution bounds remains separate from this finite demonstration.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-10-20 | Exact incoming7 transition has21 initial and15 final two-gaps. | Recorded complete-period histograms, zoom scope and validation plan. |
| 2026-10-20 | Zoom loses47,77,89; complete period loses six starts. | Critic corrected informal list before implementation; all markers derived from data. |
| 2026-10-20 | Analytic masks agree with independent integer gcd; cyclic histogram and bound match pinned values. | Numerical CLI, compilation and configured import pass; render next. |
| 2026-10-20 | Incoming7 has14 potentially bad separators but only6 actual deletions; histogram redistributes after merging. | First render and four-frame QA pass; saved1080p video/poster and documented reproducible commands. |
