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
