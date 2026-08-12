# Clarify Refuted Candidate Count And Quantifier Scope

**Created:** 2026-07-29
**Status:** Complete
**Related:** `tickets/done/create-refuted-candidate-catalog-2026-07-27.md`

## START HERE

Four negative results are visible in the candidate documentation:

1. candidate #3 fails at the transition `(5,7)`;
2. monotone separator reconstruction around #18 is refuted;
3. accepted-strike boundary sign laws around #23 are refuted;
4. centered conductor-block orthogonality around #22 is refuted.

The last three are cataloged auxiliary statement families. Candidate #3's
main hypothesis asks only for success at infinitely many transitions, so one
failed transition refutes an all-transitions strengthening but not that main
hypothesis.

Correct the documentation so a reader does not have to reconstruct this
quantifier distinction.

## Goal

Make the main candidate README, candidate #3, and the refuted-statements
catalog agree that four negative results are visible, while only three are
cataloged auxiliary statement families and none currently refutes the main
hypothesis of a numbered candidate.

## Strategy

Use quantifier-first wording:

1. count the three auxiliary families explicitly;
2. state candidate #3's separate `(5,7)` all-transitions counterexample;
3. name the actual infinitely-many hypothesis that remains open;
4. avoid the ambiguous phrase “the candidate as stated is not universally
   true.”

This is preferable to moving candidate #3 into `candidates/refuted/`, because
its main hypothesis is not universal and is not defeated by one failure.

## Current State

- The inconsistency is confirmed in current source.
- `candidates/README.md` now explicitly counts four negative results:
  candidate #3's quantifier-scoped failure plus three refuted auxiliary
  statement families. It states why none defeats a numbered candidate's main
  hypothesis.
- `candidates/protected-cluster.md` now consistently says `(5,7)` refutes the
  all-transitions strengthening while leaving its infinitely-many main
  hypothesis open.
- `candidates/refuted/README.md` is now titled “Refuted Research Statements,”
  retains exactly three indexed auxiliary families, and explains candidate
  #3 as the separate fourth negative result.
- Final validation passes.

## What is Learned

- A finite failure refutes a universal all-transitions statement.
- It does not refute an infinitely-many or eventual statement unless that
  statement itself is defeated.
- The reader's count of four negative results is correct:
  one quantifier-scoped failure around #3 plus three refuted auxiliary
  statement families.
- “No numbered candidate's main stated hypothesis is currently refuted” is
  the precise surviving claim. It must be accompanied by the four-result
  count, not presented as “nothing failed.”

## Failed Paths

- **Treat all four as fully refuted numbered candidates:** rejected because
  the main #3 hypothesis has an infinitely-many quantifier and the other three
  statements are explicitly stronger auxiliary laws around live candidates.
  Reconsider only if a counterexample defeats a numbered candidate's actual
  main quantifier.
- **Ticket move attempt 1:** the patch tool rejected a move with an empty
  update hunk. No file changed. Retry with one confirmed context line in the
  move hunk.

## Open Concerns

- Do not weaken the visibility of genuine counterexamples merely to preserve
  the live-candidate classification.
- Do not imply that finite recovery proves candidate #3's infinitely-many
  hypothesis.
- Preserve the three-entry refuted catalog's admission rule.

## Next Action

Move this completed ticket to `tickets/done/`.

## Validation

- Read the corrected status summary as a standalone explanation.
- [Passed] Candidate #3's hypothesis still says “infinitely many
  transitions.”
- [Passed] The refuted catalog still has exactly three indexed auxiliary
  statement families.
- [Passed] All three files consistently count four visible negative results.
- [Passed] `git diff --check`.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-07-29 | Four negative results are visible, but only three are cataloged auxiliary statement families; #3's `(5,7)` failure refutes an all-transitions strengthening, not its infinitely-many main hypothesis. | Opened this correction ticket and selected the main candidate README as the first edit. |
| 2026-07-29 | The main candidate README now counts all four negative results and distinguishes the failed all-transitions strengthening of #3 from the three cataloged auxiliary families. | Correct candidate #3's internal “candidate as stated” wording. |
| 2026-07-29 | Candidate #3 now consistently identifies `(5,7)` as a counterexample to the all-transitions strengthening while preserving the infinitely-many main hypothesis as open. | Add the four-result scope clarification to the refuted catalog. |
| 2026-07-29 | The refuted catalog is retitled and now explains why its three indexed auxiliary families coexist with four documented negative results. Cross-file validation passes. | Mark the ticket complete and move it to `tickets/done/`. |
| 2026-07-29 | The first lifecycle move attempt changed nothing because the patch contained no context hunk. | Retry the move with a confirmed title context line. |
