# Next Constructor Requirement Assertions

**Created:** 2026-06-15
**Status:** In progress
**Depends on:** `remove-extern-from-next.md`

---

## Goal

Add explicit, named assertions for every `CycleSieveSequence` constructor
requirement before using those values to build the next sequence.

The immediate purpose is diagnostic: when `@extern` is removed from
`CycleSieveSequence.next()`, Stainless should fail at a clear named requirement
instead of inside the constructor call.

---

## Current State

- `just verify` passes: 5303 valid, 0 invalid, 0 unknown.
- `CycleSieveSequence.next()` is still `@extern`.
- `remove-extern-from-next.md` says the last removal attempt timed out on
  `gaps.nonEmpty` inside `nextGapCycleV2`.

---

## Expected State

Add one helper assertion at a time in `SieveSequenceNextLevel`, verifying after
each change. Each helper should correspond to one constructor requirement of
`CycleSieveSequence(newHead :: seq.primes, newGapCycle)`.

---

## Related Tickets

- `remove-extern-from-next.md` — active work to remove `@extern` from
  `CycleSieveSequence.next()`.
- `next-level-requirements.md` — superseded for old sequence shape, but its
  lesson still applies: prove each constructor requirement in isolation, then
  compose.
- `gap-positivity-proof.md` and `gap-positivity-proof-detailed.md` — analyze
  positivity and non-empty gap-cycle requirements.

---

## Risks

- Calling `nextGapCycleV2(seq)` inside every requirement helper could duplicate
  the hard `gaps.nonEmpty` VC. Prefer helpers that take `newHead`,
  `newGapCycle`, or `newPrimes` as parameters once the diagnostic shape is
  clear.
- Some requirements may need dedicated mathematical lemmas rather than direct
  `assert(...)` statements.

---

## Assumptions And Validation

- Assumption: constructor requirements can be isolated into named helpers
  without worsening solver performance.
  - Validate by adding one helper and running `just verify`.
- Assumption: the first remaining blocker will be the `newGapCycle` construction
  or a later non-empty/coprimality requirement.
  - Validate by removing `@extern` only after the helper chain is green.
- Final validation: tests first, then `just verify`, with the valid count same
  or higher than 5303.

---

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-06-15 | Started diagnostic helper pass after current green verification at 5303 valid. | Add one constructor-requirement assertion at a time. |
| 2026-06-15 | Added `assertNextPrimesNonEmpty`; sieve tests passed and `just verify` reached 5306 valid. | Continue with positivity requirements. |
| 2026-06-15 | Added `assertNextHeadPositive`; sieve tests passed and `just verify` reached 5314 valid. | The head positivity bridge verifies cleanly through `CycleIntegralProperties.assertCycleIntegralPositive`. |
| 2026-06-15 | Added `assertNextPrimesPositive`; sieve tests passed and `just verify` reached 5317 valid. | Constructor positivity for `newHead :: seq.primes` verifies when the head positivity bridge is asserted first. |
| 2026-06-15 | Added `assertNextHeadBiggerThanOne`; sieve tests passed and `just verify` reached 5325 valid. | `SieveSequenceProperties.assertStrictlyIncreasing(seq, 0)` is enough to bridge `seq.apply(1) > seq.head`, and the existing constructor gives `seq.head > 1`. |
| 2026-06-15 | Added `assertNextPrimesBiggerThanOne`; sieve tests passed and `just verify` reached 5328 valid. | The constructor `> 1` list requirement verifies by asserting the new head bridge; the tail follows from the existing sequence invariant. |
| 2026-06-15 | Added `assertNextTailProductEqualOrBiggerThanElements`; sieve tests passed and `just verify` reached 5334 valid. | The product-bound requirement for `newPrimes.tail` reduces cleanly to the already-verified product bound on `seq.primes`. |
| 2026-06-15 | Added `assertNextHeadCoprimeToPrimes`; sieve tests passed and `just verify` reached 5340 valid. | The first new constructor coprime requirement verifies once `seq.apply(1)` is bridged to `seq.primes.head + seq.gapCycle.memCycle(0)`. |
