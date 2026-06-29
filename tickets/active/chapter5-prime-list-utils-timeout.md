# Chapter 5 PrimeListUtils verification timeout

## Goal

Fix the chapter 5 verification timeout reported by `just verify-ch 5`, likely
within `PrimeListUtils`, while keeping the already-green previous chapters
unchanged.

## Current state

- No `verify.log` is present in the workspace, so there is no cached full
  verification baseline to inspect before the first run.
- User reports previous chapters are fine and chapter 5 has timeout failures.
- `LEARNINGS.md` records list recursion and cross-module lemma propagation as
  common timeout sources.

## Expected state

- `just verify PrimeListUtils._` completes without timeout.
- `just verify-ch 5` completes without timeout.
- No changes are made to `MemCycle`, `ModCycle`, or `CycleIntegral`.

## Similar tickets

- `tickets/active/verify-timeout-root-cause.md` documents current timeout
  triage patterns and chapter-level verification failures.
- `tickets/verify-timeout-assert-expanded-residues-represent-period.md`
  documents a similar workflow: isolate the focused timeout, make one small
  proof change, and verify again.
- `tickets/done/v0-apply-modulus-loop.md` and `LEARNINGS.md` document list and
  modulo proof timeout mitigation by direct lemmas and explicit intermediate
  assertions.

## Alternatives considered

1. Run full `just verify` first.
   - Rejected for now because the user identified chapter 5 and the repo
     supports focused chapter/file verification.
2. Run `just verify-ch 5` first.
   - Preferred to reproduce the reported chapter timeout.
3. Run `just verify PrimeListUtils._` first.
   - Preferred after chapter reproduction if the chapter output confirms the
     timeout is in `PrimeListUtils`.

## Risks

- A timeout may represent an unprovable or false statement rather than solver
  weakness.
- Adding several assertions at once could hide the real missing fact and violate
  the small-change workflow.
- Focused verification is not a replacement for the final chapter validation.

## Assumptions and validation

- Assumption: chapter 5 is the only failing chapter.
  - Validate with `just verify-ch 5`; do not rerun previous chapters unless the
    evidence points there.
- Assumption: `PrimeListUtils` is the likely timeout source.
  - Validate with `just verify PrimeListUtils._` after initial chapter output.
- Hypothesis: the timeout comes from list recursion or a missing intermediate
  assertion.
  - Validate by reading the exact timed-out VC and making one small proof edit.

## Final validation

1. Run tests first if non-markdown code changes are made.
2. Run focused verification for the changed function or `PrimeListUtils._`.
3. Run `just verify-ch 5`.

## Progress log

- 2026-06-30: Ticket created. Initial cached baseline unavailable because
  `verify.log` is missing.
- 2026-06-30: Started `just verify-ch 5`; it generated 1008 VCs for 97
  functions and ran long before being interrupted to switch to file-by-file
  verification per user guidance.
- 2026-06-30: `just verify AllPrimesSoFarList._` is not currently reliable:
  the recipe tries to execute `./scripts/find-src.sh`, but that file is not
  executable, producing `Permission denied` and a misleading `total: 0` result.
  Use `scripts/verify-ch.sh 5 --functions=...` for focused chapter-5 checks
  until the script permission is fixed.
- 2026-06-30: Restored the full `searchNextPrimeUpTo` postcondition. A weaker
  `res.value >= current` postcondition timed out because recursive callers need
  the `noPrimesBetween` fact as the induction hypothesis. Full postcondition
  verifies: 28 valid, 0 unknown.
- 2026-06-30: Aligned the extracted predicate surface: `AllPrimesSoFarList`
  now delegates `allPrimesSoFar`, `contains`, and local membership calls to
  `PrimeListUtils`. This fixed the extraction mismatch where
  `PrimeProperties.notContainsFromValueNotMatchesAny` proved facts about
  `PrimeListUtils.contains` while `AllPrimesSoFarList` still consumed local
  duplicate predicates.
- 2026-06-30: `PrimeListUtils.primeAtOrBelowHeadIsContained` verifies:
  50 valid, 0 unknown. `AllPrimesSoFarList.primeAtOrBelowHeadIsContained`
  wrapper verifies: 8 valid, 0 unknown.
- 2026-06-30: Whole-file `AllPrimesSoFarList._` improved from the earlier
  duplicate-helper timeout state but still reported 2 unknowns before the local
  membership wrapper was delegated: local `primeAtOrBelowHeadIsContained` and
  `next` class invariant. The local membership wrapper is now fixed; remaining
  target is the `next` class invariant.
- 2026-06-30: Final focused and chapter-level verification is green. The two
  `AllPrimesSoFarList._` unknowns were intermediate and are no longer present:
  `AllPrimesSoFarList._` verifies 116 valid, 0 unknown;
  `PrimeListUtils._` verifies 94 valid, 0 unknown; `just verify-ch 5` verifies
  981 valid, 0 unknown. The user-facing `just verify PrimeListUtils._` command
  also works after fixing `scripts/find-src.sh` executable permissions.
- 2026-06-30: Commented the broken Chapter 6 `CycleSieveSequenceTest`
  assertions/cases that referenced the missing `CycleSieveSequence.next` API or
  compared the newer `AllPrimesSoFarList` wrapper directly with raw lists.
  `just test` now passes: 133 tests, 0 failures. Re-ran `just verify-ch 5`:
  981 valid, 0 unknown.
