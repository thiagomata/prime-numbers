# Review: articles/gap-dynamics.md

## Source

- Article: `articles/gap-dynamics.md`
- Current role: Research-frontier article

## Verdict

Major revision required before publication. The framing around the open local density question is good, but the article currently overclaims Stainless verification.

## Must Fix

- Remove or qualify the abstract claim that all four global properties are verified in Stainless unless the exact functions exist in current source.
- The cited functions `verifyGeneralizedGrowth`, `assertNoAdjacentTwoGaps`, `countDeletionsAtIndex`, and `assertSafeZoneStability` were not found in `src/main/scala/` during review.
- Mark unverified mathematical claims as "Draft - mathematically proven, Stainless verification pending" if keeping them.
- Fix the safe-zone stability proof: as written, `newPosition = gapPosition - currentPrime` need not satisfy `newPosition >= nextPrime` from the listed preconditions.
- Replace the deprecated empirical reference path with the actual canonical empirical article location if one exists.

## Missing Proof Notes

The following lemmas are expressed as validated or Stainless-verified in the article, but no matching current source proof was found during review:

- `verifyGeneralizedGrowth`
- `assertNoAdjacentTwoGaps`
- `countDeletionsAtIndex`
- `assertSafeZoneStability`

Recommended fix: either implement these as real `.holds` proofs and verify them with `just verify`, or downgrade the article language to distinguish:

- `[Verified]` for current source-backed `.holds` lemmas
- `[Mathematically argued]` for proof sketches without Stainless code
- `[Empirical]` for computed observations
- `[Open]` for the local density question and anything equivalent to it

The current "All properties are verified in the Stainless system" abstract language should not remain unless all four functions are present in current source and appear in the green verification run.

## Should Fix

- Keep the excellent open-question section, but make it the article's organizing boundary.
- Add an explicit table separating `[Verified]`, `[Mathematically argued]`, `[Empirical]`, and `[Open]`.
- Cross-reference `learnings-capacity-argument.md` Section 16 for the final catalog.
- Avoid language like "cannot focus fire" unless it is backed by a precise lemma.

## Validation

- Search source for every cited `.holds` function.
- Run `just verify` or confirm the latest `verify.log`.
- Create tickets for any missing Stainless proofs before publishing.
- Re-check `articles/learnings/learnings-capacity-argument.md` Section 16 before finalizing the status table.
