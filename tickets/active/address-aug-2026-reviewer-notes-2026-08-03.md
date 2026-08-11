# Address August 2026 Reviewer Notes

**Created:** 2026-08-03
**Updated:** 2026-08-03
**Status:** Complete
**Baseline:** Markdown-only scope; recorded Stainless result 30 valid,
0 invalid, 0 unknown

## START HERE

Apply the three accepted corrections from
`articles/learnings/reviewer-notes-aug-2026.md`: define `D` locally in
The Filter-Seven Excess Bound property, soften the candidate handoff from one exact frontier to one
primary frontier, and align candidate #25's closure-matrix vocabulary with the
existing README label. Retain the complete 86-row Gap Dynamics v2 appendix as
the requested audit record.

## Related Tickets

- `complete-gap-dynamics-catalog-coverage-2026-08-03.md` — completed the
  86-property article audit and records why the full table is intentional.
- `verify-19-21-escape-wall-2026-07-27.md` — established the properties from Capacity Stability Gap through Copy-Block Excess Control
  and the terminal twin-prime frontier.
- `quantifier-screen-refutation-targets-2026-08-03.md` — established the
  closure matrix and candidate #25 as a distinct analytic program.
- `investigate-final-programs-signed-energy-almost-prime-2026-08-03.md` —
  established candidate #25's exact open method-specific positivity target.

## Goal

Make the reviewed Markdown artifacts self-contained and terminologically
consistent without changing any theorem, candidate quantifier, proof status,
or the published Gap Dynamics v1 article.

## Expected State

- the Filter-Seven Excess Bound property defines `D=Q^2-Q-3` immediately before using `11664/D^2`.
- The handoff describes one **primary** twin-prime frontier while preserving
  the classified supporting routes.
- Candidate #25 uses **Externally known; method-specific proof open** in the
  closure glossary and matrix, matching `candidates/README.md`.
- Gap Dynamics v2 Appendix B remains complete and unchanged.

## Strategy

Make one Markdown correction at a time in reviewer order. Read back the local
claim after every edit and update this ticket continuously. Finish with link,
heading, whitespace, vocabulary, diff, and recorded-baseline checks.

## Alternatives Considered

- **Rename the README label to “Distinct next program”:** rejected because
  the README's descriptive label communicates both external existence and the
  exact project-specific gap.
- **Keep both labels and add a mapping sentence:** valid but weaker than using
  one vocabulary on both index surfaces.
- **Collapse Appendix B:** rejected for this ticket because the user requested
  complete #1--#86 coverage and accepted the recommendation to retain its
  audit function.

## Risks And Assumptions

- Assumption: `D` has exactly the the Capacity Stability Gap property meaning `Q^2-Q-3`; validate
  against both #81 and the ratio in #82 before editing.
- Assumption: “primary” preserves the intended strategic ranking without
  implying other open routes are closed; validate against the matrix rows.
- Risk: changing only candidate #25's row but not the glossary would preserve
  the vocabulary mismatch; update and search both surfaces in one terminology
  micro-goal.
- Risk: wording could imply Chen-pair existence proves this project's weight
  positivity; retain the explicit method-specific-open qualifier.

## Current State

- Reviewer independently confirmed all mathematics and cross-references.
- the Filter-Seven Excess Bound property now defines `D=Q^2-Q-3` before the reviewed ratio and links
  The Capacity Stability Gap property as the source of the capacity-envelope comparison.
- `INVESTIGATION_STATUS.md` now says “one primary twin-prime frontier,”
  matching its supporting and deferred open-route classifications.
- `candidates/README.md`, the closure glossary, and candidate #25's matrix row
  now all use “Externally known; method-specific proof open.”
- Appendix B is accurate; its visual weight is optional presentation feedback,
  not a correctness defect.
- Final validation passes for both corrected public files; both Gap Dynamics
  articles were preserved, with Appendix B still containing 86 continuous
  property rows.

## What Is Learned

- The reviewer found no mathematical correction: all accepted changes are
  self-containment or framing/vocabulary fixes.
- Candidate #25's most informative status vocabulary already exists in the
  primary candidate README, so alignment has a canonical direction.

## Failed Paths

- **Item 2 ticket update skipped its visible pre-execution gate:** the update
  contained only already validated state and was audited immediately, but the
  pipeline order was wrong. Emit Worker, Critic, and Monitor pre-execution
  output before every later modification, including ticket-only edits.
- **Initial `D` placement followed the review literally but not the stricter
  ticket criterion:** it defined `D` before the ratio but after the preceding
  capacity-charge formula. Final validation caught the earlier use, and the
  same definition was moved above both formulas.

## Open Concerns

- None for this reviewer-fix ticket. The underlying arithmetic programs remain
  open exactly as their candidate notes state.

## Validation

- the Filter-Seven Excess Bound property defines `D` at line 207 before its first `D^2` use at line 216.
- Both corrected public files have all links resolved, balanced fences, unique
  headings, and no trailing whitespace.
- The old exact-frontier and distinct-next phrases are absent; the primary
  frontier appears once and the preferred candidate #25 label appears in both
  closure-matrix locations.
- Gap Dynamics v2 Appendix B remains 86 continuous unique rows; published
  `gap-dynamics.md` has a zero-byte diff.
- Markdown-only changes did not rerun Stainless; recorded baseline remains
  30 valid, 0 invalid, 0 unknown.

## Implementation Plan

1. Define `D` in the Filter-Seven Excess Bound property.
2. Change “one exact” to “one primary” in the handoff verdict.
3. Align candidate #25's matrix row and closure glossary with the README.
4. Run final validation and close this ticket.

## Next Action

None for this ticket. The corrected Markdown artifacts are ready for review.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-08-03 | Reviewer feedback contains three substantive Markdown fixes and one optional appendix presentation suggestion. The README already has the preferred candidate #25 vocabulary. | Retain Appendix B; apply the three accepted fixes one at a time. |
| 2026-08-03 | The Filter-Seven Excess Bound property's `D` is exactly the Capacity Stability Gap property's eligible-window proxy `Q^2-Q-3`; the energy calculation itself was already correct. | Defined `D` locally before the ratio and linked the Capacity Stability Gap property. |
| 2026-08-03 | The #23--#24 chain is the primary frontier, not the only remaining open route. | Replaced “one exact” with “one primary” and confirmed the surrounding classifications remain intact. |
| 2026-08-03 | Candidate #25's README label is the most informative canonical vocabulary because it separates classical existence from this method's open positivity proof. | Applied that label to the closure glossary and matrix row; removed the old “Distinct next” labels. |
| 2026-08-03 | Self-containment means defining notation before its first displayed use, not merely before the expression highlighted by a reviewer. | Moved `D` above both formulas, reran all preservation checks, and marked the ticket complete. |
