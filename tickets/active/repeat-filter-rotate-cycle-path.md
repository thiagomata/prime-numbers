# Repeat-Filter-Rotate Cycle Path

**Created:** 2026-07-14
**Status:** Active
**Owner:** Side-by-side cycle construction matching the spec proof checkpoints

## START HERE

Micro-goal: add a new cycle transition path beside the existing one. Do not
replace or edit the current `next()` / residue pipeline. The new path should
make the proof checkpoints explicit:

```text
repeat old period -> filter by old head -> rotate/start at next head
```

## Goal

Create a new construction lane that mirrors the spec-side argument:

1. Repeat the current gap period `head` times.
2. Prove or expose that the repeated cycle generates the same values as the
   original cycle over the scan window.
3. Filter the repeated/generated values by `head`.
4. Prove or expose that the filtered survivors match the `SpecSieveSequence.next`
   accepted values.
5. Rotate or choose the scan start so the resulting gap cycle starts at the next
   head.

The current path remains in place as legacy machinery until the new path is
verified and easier to trust.

## Current State

- Latest full verification is green: `14030 valid`, `0 invalid`, `0 unknown`.
- `CycleSieveSequence.next()` currently delegates to
  `SieveSequenceNextLevel.nextGapsWalk(this)`.
- `CycleSieveSequence.nextFromWindow()` already scans a concrete window from
  `integral(0) == apply(1)`, filters values by `head`, and builds gaps from the
  survivors.
- `SpecDerivedSieveSequence.repeatedCycle(times)` already builds repeated gap
  storage and has verified equality lemmas showing repeated storage preserves
  cycle values.
- `SpecSieveSequence.assertNextAcceptsMatchesHeadFilterForAcceptedValue(v)` is a
  verified leaf bridge for the filter checkpoint, but the main proof should be
  construction-level, not only predicate-level.

## Similar Tickets

- `tickets/active/base-one-prime-spec-filter-equivalence.md`
  - Contains the verified singleton filter lemma and the new leaf predicate
    bridge.
- `tickets/active/m-interval-density-and-sieve-sequence-v2.md`
  - Tracks the broader size and M-interval reasoning.
- `tickets/active/remove-redundant-expandresidues-density-surface.md`
  - Relevant because this new path should avoid growing the old
    `nextResidues -> nextExpanded -> nextFiltered` proof surface.
- `tickets/done/spec-same-head-filter-density.md`
  - Proved the spec-local count theorem that the new cycle path should consume.

## Plan

1. Add a side-by-side helper to `CycleSieveSequence` for repeating the current
   gap storage. Keep it separate from `next()`.
2. Add a side-by-side transition helper that uses repeated storage and a filtered
   window, keeping the current path untouched.
3. Verify each helper independently before adding proof bridges.
4. Add proof checkpoints one by one: repeat equality, filter equality, then
   rotate/start alignment.

## Risks

- Reusing `nextFromWindow()` blindly may hide whether the repeat step is part of
  the construction or only an equivalent implementation detail.
- Starting from `integral(0)` may make rotation unnecessary for the window path;
  if so, document the alignment instead of forcing a synthetic rotate.
- The existing residue pipeline should not be edited during this work.

## Validation

- Focused validation after each helper: `just verify <functionName>`.
- Final validation after non-markdown changes: `just verify`.

## Learning Log

- 2026-07-14: Ticket created after user directed that the current path should not
  be updated. New path must be built side-by-side, with old machinery removed
  only later.
- 2026-07-14: Added `CycleSieveSequence.repeatedCycle(times)` as the first
  side-by-side helper. It physically repeats the current gap storage and
  constructs a new `CycleSieveSequence` with the same primes. Focused
  verification passed: `28 valid`, `0 invalid`, `0 unknown`. Full verification
  passed: `14044 valid`, `0 invalid`, `0 unknown`.
- 2026-07-14: Added
  `CycleSieveSequence.assertRepeatedCycleApplyMatches(times,position)`. This is
  the first equality checkpoint: before any head filter is applied, the repeated
  physical cycle emits the same value as the original cycle at every
  non-negative position. Focused verification passed: `49 valid`, `0 invalid`,
  `0 unknown`. Full verification passed: `14062 valid`, `0 invalid`,
  `0 unknown`.
- 2026-07-14: Added
  `SpecSieveSequence.assertExpandedGeneratedHeadMultipleCount(period)` as a
  public wrapper around the existing private generated head-multiple count
  proof. This exposes the spec-side rule needed by the repeated cycle path:
  after walking an expanded prefix of `period * head`, exactly `period`
  generated values are multiples of `head`. Focused verification passed:
  `8 valid`, `0 invalid`, `0 unknown`. Full verification passed:
  `14070 valid`, `0 invalid`, `0 unknown`.
- 2026-07-14: Added
  `SpecDerivedSieveSequence.assertNextPeriodMatchesExpandedFilterCount()`. This
  is the derived-level pressure test: it first exposes
  `spec.assertExpandedGeneratedHeadMultipleCount(period)`, then proves the
  actual post-filter `nextPeriod()` is the expected magic number
  `period * (head - 1)`. Focused verification passed: `10 valid`,
  `0 invalid`, `0 unknown`. Full verification passed: `14080 valid`,
  `0 invalid`, `0 unknown`.
- 2026-07-14: Added
  `SpecDerivedSieveSequence.assertRepeatedCycleMatchesSpecPrefix(times,count)`.
  This is the value-by-value walking proof: for a bounded prefix, the physically
  repeated cycle and the spec sequence emit the same values before any filter is
  applied. The recursion decreases on `count`, so it is structurally bounded.
  Focused verification passed: `31 valid`, `0 invalid`, `0 unknown`. Full
  verification passed: `14118 valid`, `0 invalid`, `0 unknown`.
- 2026-07-14: Added
  `SpecDerivedSieveSequence.assertRepeatedCycleMatchesSpecFirstExpandedPeriod()`
  as the caller-facing wrapper requested for only the first period expansion:
  repeat the cycle `head` times and walk exactly `period * head` generated
  values. This proves the repeated-cycle side and the spec side match on the
  scan window that will feed the head filter. Focused verification passed:
  `6 valid`, `0 invalid`, `0 unknown`. Full verification passed:
  `14126 valid`, `0 invalid`, `0 unknown`.
- 2026-07-14: Added
  `SpecDerivedSieveSequence.assertRepeatedCycleNextAcceptsMatchesHeadFilterFirstExpandedPeriod(count)`.
  This is the first filter-decision bridge for the side-by-side path. It walks
  the first expanded integral window, starting at `integral(0) == cycle(1)` so
  the raw current head is not part of the comparison, and proves each repeated
  value is accepted by `spec.next` iff it survives the current head filter.
  Focused verification passed: `56 valid`, `0 invalid`, `0 unknown`. Full
  verification passed: `14182 valid`, `0 invalid`, `0 unknown`.
- 2026-07-14: Added
  `SpecDerivedSieveSequence.assertRepeatedCycleNextAcceptsMatchesHeadFilterFullFirstExpandedPeriod()`
  as the caller-facing full-window wrapper for the bounded filter-decision
  bridge. It instantiates the count as `period * head`, matching the first
  expanded scan window. Focused verification passed: `6 valid`, `0 invalid`,
  `0 unknown`. Full verification passed: `14188 valid`, `0 invalid`,
  `0 unknown`.
- 2026-07-14: Added
  `SpecDerivedSieveSequence.assertRepeatedCycleFullFirstExpandedEndpointRejected()`.
  This closes the off-by-one alignment for the first expanded integral window:
  the window ends at `head + head * tailPrimorial`, a head multiple, so the
  endpoint replacing the raw lower head is also rejected by `spec.next`.
  Focused verification passed: `42 valid`, `0 invalid`, `0 unknown`. Full
  verification passed: `14230 valid`, `0 invalid`, `0 unknown`.
- 2026-07-14: Added
  `SpecDerivedSieveSequence.assertSpecHeadRejectedByHeadFilter()`. This is the
  lower-endpoint companion to the expanded endpoint lemma: the raw `head` is
  outside the next-spec domain, so the useful fact is that the current head
  filter rejects it by `mod(head, head) == 0`. Focused verification passed:
  `7 valid`, `0 invalid`, `0 unknown`. Full verification passed:
  `14237 valid`, `0 invalid`, `0 unknown`.
- 2026-07-15: Added
  `SpecSieveSequence.assertCountAcceptedHeadNonMultiplesBetweenAppend(from,middle,until)`.
  This private counter append helper is the missing arithmetic tool for the
  shifted first-window count: it lets the proof split and rejoin the existing
  spec-side accepted-non-head-multiple counter around the rejected endpoints.
  Focused verification passed: `22 valid`, `0 invalid`, `0 unknown`. Full
  verification passed: `14259 valid`, `0 invalid`, `0 unknown`.
- 2026-07-15: Added
  `SpecSieveSequence.assertSameHeadShiftedWindowCount(period)`. This exposes
  the count bridge needed by the repeated integral scan: the existing spec
  theorem counts `[head, head + head*M)`, while the repeated scan window covers
  `(head, head + head*M]`; both swapped endpoints are head multiples, so the
  accepted non-head-multiple count is still `period * (head - 1)`. Focused
  verification passed: `51 valid`, `0 invalid`, `0 unknown`. Full verification
  passed: `14310 valid`, `0 invalid`, `0 unknown`.
- 2026-07-15: Added
  `SpecDerivedSieveSequence.assertNextPeriodMatchesShiftedWindowCount()`. This
  derived-level wrapper consumes the shifted first-window count proof in the
  same object that owns `nextPeriod()`, giving the rotate/start-alignment lane a
  local fact that the repeated integral scan has the expected next-period size.
  Focused verification passed: `10 valid`, `0 invalid`, `0 unknown`. Full
  verification passed: `14320 valid`, `0 invalid`, `0 unknown`.
- 2026-07-15: Added
  `SpecDerivedSieveSequence.assertRepeatedFirstWindowStartsAtSpecNextHead()`.
  This is the first value-level shifted-window anchor: the repeated cycle's
  first integral scan value equals `spec.next(0)` and survives the current head
  filter. Focused verification passed: `30 valid`, `0 invalid`, `0 unknown`.
  Full verification passed: `14350 valid`, `0 invalid`, `0 unknown`.
- 2026-07-15: Checked `articles/chapter4/integral-cycle.md` after the user
  pointed out its shift section. The important linked theorem is
  `GapProperties.assertRotateOneCycleIntegralShiftsByOne`: rotating the backing
  cycle by one and advancing the initial value by the first gap preserves
  values by shifting the integral one position. This confirms the next proof
  cannot stop at counts; it needs a value-by-value shift bridge. The current
  verified anchor is only the first value of that bridge.
- 2026-07-15: Added
  `SpecDerivedSieveSequence.assertRepeatedFirstWindowFilteredCIMatchesSurvivors(newCI,position)`.
  This instantiates the existing generic rebuild theorem
  `CycleIntegralFilterProperties.assertNewCIMatchesSurvivors` for the repeated
  first-window survivor list: if a `CycleIntegral` uses the survivor head and
  `gapsFromValues(survivors)`, then it reconstructs the survivor values by
  `newCI(position) == survivors(position + 1)`. Focused verification passed:
  `17 valid`, `0 invalid`, `0 unknown`. Full verification passed:
  `14367 valid`, `0 invalid`, `0 unknown`.
- 2026-07-15: Added
  `SpecDerivedSieveSequence.assertRepeatedIntegralMatchesShiftedSpec(index)`.
  This is the explicit apply-matching spine the plan was missing:
  `repeatedCycle(head).integral(index) == spec(index + 1)`. It factors out the
  representation shift where moving from sequence `apply` to `integral` has
  already consumed the current head. Focused verification passed: `20 valid`,
  `0 invalid`, `0 unknown`. Full verification passed: `14387 valid`,
  `0 invalid`, `0 unknown`.
- 2026-07-15: Adjusted the proof-loop cadence for this micro-goal: focused
  verification is enough after each new lemma in the same file, and the full
  `just verify` run is reserved for the end of the micro-goal / step.
- 2026-07-15: Added
  `SpecDerivedSieveSequence.assertRepeatedFirstWindowSurvivorsHeadMatchesSpecNext()`.
  This connects the repeated first-window filter to the next spec head at the
  survivor-list level: since the first repeated integral value is `spec.next(0)`
  and it survives the head filter, the first filtered survivor is also
  `spec.next(0)`. Focused verification passed: `27 valid`, `0 invalid`,
  `0 unknown`. Full verification intentionally deferred until the end of the
  micro-goal / step.
- 2026-07-15: Found an important values-vs-gaps alignment issue. Scanning
  `period * head` integral values is enough for the post-filter survivor count,
  but a gap list of that size needs one extra survivor value because
  `gapsFromValues(survivors).size == survivors.size - 1`. For the
  `[2, 2, 2] -> [2, 4]` example, the survivor values are `[5, 7, 11]`, not only
  `[5, 7]`; the rejected old endpoint `9` is not the closing survivor.
- 2026-07-15: Added
  `SpecDerivedSieveSequence.assertRepeatedExtendedWindowSurvivorsHeadMatchesSpecNext()`.
  This anchors the extended gap-reconstruction scan
  `period * head + 1` at the same first survivor, `spec.next(0)`, without
  replacing the count-window lemma. Focused verification passed: `27 valid`,
  `0 invalid`, `0 unknown`. Full verification intentionally deferred until the
  end of the micro-goal / step.
- 2026-07-15: Added
  `SpecDerivedSieveSequence.assertRepeatedExtendedWindowFilteredCIMatchesSurvivors(newCI,position)`.
  This is the extended-window version of the generic CI rebuild wrapper: if a
  `CycleIntegral` starts at the extended survivor head and stores
  `gapsFromValues(survivors)`, then its `position` value is the next survivor
  value at `position + 1`. Focused verification passed: `17 valid`,
  `0 invalid`, `0 unknown`. Full verification intentionally deferred until the
  end of the micro-goal / step.
- 2026-07-15: Added
  `SpecDerivedSieveSequence.assertRepeatedExtendedWindowGapMatchesSpecNextGapAt(index)`.
  This is the conditional values-to-gaps bridge: once adjacent extended
  survivors are known to equal `spec.next(index)` and `spec.next(index + 1)`,
  `gapsFromValues(survivors)(index)` equals the corresponding
  `spec.next.gapList(0, index + 1)(index)`. First focused attempt hit
  `unknown` because `gapsFromValues(survivors)` was computed before Stainless
  could see `survivors.nonEmpty`; moving that val after the requirements fixed
  it. Focused verification passed: `37 valid`, `0 invalid`, `0 unknown`. Full
  verification intentionally deferred until the end of the micro-goal / step.
- 2026-07-15: Added
  `SpecDerivedSieveSequence.assertRepeatedExtendedWindowNextValueFromGapAt(index)`.
  This is the conditional induction step suggested by the user: if
  `survivors(index) == spec.next(index)` and the `index` gap from
  `gapsFromValues(survivors)` equals the corresponding `spec.next` gap, then
  `survivors(index + 1) == spec.next(index + 1)`. The first focused attempt got
  stuck on list-index bounds for `gaps(index)` and `specGaps(index)`; making
  those bounds explicit fixed it. Focused verification passed: `41 valid`,
  `0 invalid`, `0 unknown`. Full verification intentionally deferred until the
  end of the micro-goal / step.
- 2026-07-15: Added
  `SpecDerivedSieveSequence.repeatedExtendedWindowGapsMatchSpecNextPrefix(count)`
  and
  `SpecDerivedSieveSequence.assertRepeatedExtendedWindowValuesMatchSpecNextFromGapPrefix(count)`.
  This packages the user's conditional idea into a bounded induction: the base
  survivor value is already `spec.next(0)`, and each matching gap advances the
  survivor/spec-next value equality by one position. Focused verification
  passed: `59 valid`, `0 invalid`, `0 unknown`. Full verification intentionally
  deferred until the end of the micro-goal / step.
- 2026-07-15: Added
  `SpecDerivedSieveSequence.assertRepeatedExtendedWindowFilteredCIMatchesSpecNextFromGapPrefix(newCI,position)`.
  This connects the gap-prefix induction to an actual rebuilt `CycleIntegral`:
  if `newCI` is built from the extended survivor gaps and the corresponding gap
  prefix matches `spec.next`, then `newCI(position) == spec.next(position + 1)`.
  Focused verification passed: `33 valid`, `0 invalid`, `0 unknown`. Full
  verification intentionally deferred until the end of the micro-goal / step.
- 2026-07-15: Added
  `SpecDerivedSieveSequence.assertSpecNextValueAppearsInRepeatedExtendedWindowSurvivors(k)`.
  This is a construction-level membership bridge for the real `spec.next`
  path: if the old `spec.indexOfAccepted(spec.next(k))` lies inside the
  extended repeated-integral scan, then `spec.next(k)` appears in the extended
  survivor list. It uses `assertRepeatedIntegralMatchesShiftedSpec` plus
  `GapProperties.assertSurvivorValuesContainsNonMultipleAtPosition`. Focused
  verification passed: `47 valid`, `0 invalid`, `0 unknown`. Full verification
  intentionally deferred until the end of the micro-goal / step.
- 2026-07-15: Added
  `SpecSieveSequence.assertIndexOfAcceptedAtMost(value,bound)`. This public
  wrapper exposes the private monotonicity fact needed by the repeated-window
  path: once an accepted value is numerically bounded by `spec(bound)`, its
  generated stream index is at most `bound`. Focused verification passed:
  `15 valid`, `0 invalid`, `0 unknown`. Full verification intentionally
  deferred until the end of the micro-goal / step.
- 2026-07-15: Added
  `SpecDerivedSieveSequence.assertSpecNextValueAppearsInRepeatedExtendedWindowSurvivorsFromValueBound(k)`.
  This removes the caller-facing old-index precondition from the membership
  bridge: if `spec.next(k)` is below the extended repeated scan endpoint, then
  the old accepted index is inside the scan and the value appears in the
  extended survivor list. Focused verification passed: `32 valid`, `0 invalid`,
  `0 unknown`. Full verification intentionally deferred until the end of the
  micro-goal / step.
- 2026-07-15: Tried a combined real-next lemma
  `assertOldGeneratedValueBetweenNextValuesIsHeadMultiple(k,oldIndex)` to prove
  directly that an old generated value strictly between `next(k)` and
  `next(k + 1)` must be an old-head multiple. The idea is right, but the
  combined contradiction branch was too large for Stainless: first attempt
  ended at `17 valid`, `0 invalid`, `5 unknown`; after adding the missing
  `next` precondition it still ended at `21 valid`, `0 invalid`, `2 unknown`.
  The lemma was removed to restore the green baseline.
- 2026-07-15: Added
  `SpecSieveSequence.assertNoAcceptedValueBetweenGeneratedValues(k,value)`.
  This smaller public wrapper exposes the already-verified skipped-interval
  fact: if `apply(k) < value < apply(k + 1)`, then `value` is not accepted by
  that sequence. This should let the real-next head-multiple bridge be rebuilt
  as a composition instead of one large contradiction VC. Focused verification
  passed: `19 valid`, `0 invalid`, `0 unknown`. Full verification
  intentionally deferred until the end of the micro-goal / step.
- 2026-07-15: Retried the combined real-next head-multiple bridge using
  `assertNoAcceptedValueBetweenGeneratedValues` as the contradiction half. This
  still got stuck at the same bridge point,
  `assertNextAcceptsMatchesHeadFilterForAcceptedValue(value)`, with `21 valid`,
  `0 invalid`, `2 unknown`. Removed the unverified combined lemma again and
  re-ran the retained wrapper successfully: `19 valid`, `0 invalid`,
  `0 unknown`. Per the three-attempt rule, stop trying this exact combined
  bridge shape; the next route needs a smaller exported head-filter direction
  or a different caller shape.
- 2026-07-15: Added
  `SpecSieveSequence.assertOldAcceptedHeadNonMultipleAcceptedByNext(v)`. This
  is the tiny forward-direction helper the failed combined bridge was missing:
  if an old accepted value is already in the `next` domain and is not divisible
  by the old head, then `next.accepts(v)` holds. Focused verification passed:
  `14 valid`, `0 invalid`, `0 unknown`. Full verification intentionally
  deferred until the end of the micro-goal / step.
- 2026-07-15: Added
  `SpecSieveSequence.assertOldAcceptedRejectedByNextIsHeadMultiple(v)`. This is
  the dual branch-free bridge: if an old accepted value is in the `next` domain
  but `next` rejects it, then the old head divides it. It uses the existing
  iff-style head-filter lemma in a tiny standalone proof instead of inside a
  large contradiction branch. Focused verification passed: `17 valid`,
  `0 invalid`, `0 unknown`. Full verification intentionally deferred until the
  end of the micro-goal / step.
- 2026-07-15: Re-added and verified
  `SpecSieveSequence.assertOldGeneratedValueBetweenNextValuesIsHeadMultiple(k,oldIndex)`
  in a branch-free shape. The proof now composes two small facts: first
  `next.assertNoAcceptedValueBetweenGeneratedValues(k,value)` shows the value is
  rejected by `next`, then `assertOldAcceptedRejectedByNextIsHeadMultiple(value)`
  converts that rejection into `mod(value, head) == 0`. Focused verification
  passed: `33 valid`, `0 invalid`, `0 unknown`. Full verification intentionally
  deferred until the end of the micro-goal / step.
- 2026-07-15: Added
  `SpecSieveSequence.assertApplyStrictlyIncreasesBetween(from,until)`. This
  public wrapper exposes the existing private strict index-order proof so
  derived proofs can show that an old index strictly between two
  `indexOfAccepted` witnesses has a value strictly between the corresponding
  generated values. Focused verification passed: `6 valid`, `0 invalid`,
  `0 unknown`. Full verification intentionally deferred until the end of the
  micro-goal / step.
- 2026-07-15: Added
  `SpecSieveSequence.assertIndexOfAcceptedStrictlyIncreasesForAcceptedValues(lowerValue,upperValue)`.
  This exposes the monotone inverse fact for accepted values: if two accepted
  values satisfy `lowerValue < upperValue`, then their `indexOfAccepted`
  witnesses have the same strict order. The proof reuses
  `assertIndexOfAcceptedAtMost` for the non-strict bound and rules out equality
  through the two `apply(index)` postconditions. Focused verification passed:
  `22 valid`, `0 invalid`, `0 unknown`. Full verification intentionally
  deferred until the end of the micro-goal / step.
- 2026-07-15: Added
  `SpecDerivedSieveSequence.assertRepeatedIntegralSkippedRangeBetweenSpecNextValuesAllMultiples(k,fromPos,untilPos)`.
  This is the repeated-integral skipped-prefix bridge: for the old positions
  between `spec.next(k)` and `spec.next(k + 1)`, every repeated integral value
  in the half-open prefix is removed by the current head filter. The proof uses
  the branch-free old-generated-between-next-values bridge and the shifted
  repeated-integral equality. Focused verification passed: `75 valid`,
  `0 invalid`, `0 unknown`. Full verification intentionally deferred until the
  end of the micro-goal / step.
- 2026-07-15: Added
  `SpecDerivedSieveSequence.assertRepeatedExtendedWindowTailHeadMatchesSpecNextSuccessor(k)`.
  This consumes the skipped-prefix bridge with
  `GapProperties.assertFirstSurvivorAtPosition`: when the old index of
  `spec.next(k + 1)` is inside the extended repeated scan and after the old
  index of `spec.next(k)`, the filtered tail scan beginning just after
  `spec.next(k)` has head `spec.next(k + 1)`. First focused attempt timed out
  only on a redundant `survivors.head` assertion; removing that assertion made
  the focused verification pass: `72 valid`, `0 invalid`, `0 unknown`. Full
  verification intentionally deferred until the end of the micro-goal / step.
- 2026-07-15: Strengthened
  `SpecDerivedSieveSequence.assertRepeatedExtendedWindowTailHeadMatchesSpecNextSuccessor(k)`
  so it no longer requires `nextOldIndex > currentOldIndex`. The lemma now
  proves that ordering internally from `spec.next.applyStrictlyIncreases(k)` and
  `SpecSieveSequence.assertIndexOfAcceptedStrictlyIncreasesForAcceptedValues`.
  Focused verification passed: `93 valid`, `0 invalid`, `0 unknown`. Full
  verification intentionally deferred until the end of the micro-goal / step.
- 2026-07-15: Added
  `SpecDerivedSieveSequence.assertRepeatedExtendedWindowTailHeadMatchesSpecNextSuccessorFromValueBound(k)`.
  This replaces the caller-facing old-index scan bound with the cleaner value
  bound `spec.next(k + 1) <= spec(steps)`, where
  `steps = period * spec.head.value + 1`. The proof converts that value bound
  with `SpecSieveSequence.assertIndexOfAcceptedAtMost`, then delegates to the
  strengthened tail-head lemma. Focused verification passed: `48 valid`,
  `0 invalid`, `0 unknown`. Full verification intentionally deferred until the
  end of the micro-goal / step.
