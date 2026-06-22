# Step 4: Wire assertHeadIsPrime into SieveSequenceProperties

**Created:** 2026-06-13
**Status:** In Progress
**Depends on:** `prime-foundations-and-gap-proof.md` (✅ verified)

---

## Goal

Add `assertHeadIsPrime(seq: CycleSieveSequence): Boolean` to `SieveSequenceProperties.scala` that proves `Prime.isPrime(seq.head)` by calling `PrimeProperties.assertHeadIsPrime(seq.head, seq.primes.tail)`.

## Current State

- **Verification:** 4977 valid, 0 invalid, 0 unknown
- `SieveSequenceProperties.scala` has Steps 1-3 (assertStrictlyIncreasing, assertHeadIsMinimum, assertAllValuesPositive)
- `PrimeProperties.assertHeadIsPrime(head, primesTail)` is verified and ready at line 408

## Expected State

- `SieveSequenceProperties.assertHeadIsPrime(seq)` added and verified
- Verification count increases (at least same or higher)

## Result: ✅ Completed

- Added `assertHeadIsPrime(seq: CycleSieveSequence)` at line 60 of `SieveSequenceProperties.scala`
- Verification: **5001 valid, 0 invalid, 0 unknown** (+24 from 4977)
- Two `require` preconditions: `isCoprime(seq.head, seq.primes.tail)` and `assertAllNotCoprimeInRange(seq.head, 2, seq.primes.tail)`
- Class invariants provide `seq.head > 1` and `checkAllPositive(seq.primes.tail)` — no explicit requires needed

## Assumptions

- `SieveUtils.isCoprime(seq.head, seq.primes.tail)` must be assumed as precondition (Step 5 will prove from sieve construction)
- `SieveUtils.assertAllNotCoprimeInRange(seq.head, 2, seq.primes.tail)` — completeness assumption, required as precondition
- Class invariants of `CycleSieveSequence` provide `seq.head > 1` and `checkAllPositive(seq.primes.tail)`

## Risks

- If Stainless cannot discharge `seq.head > 1` from class invariant, add explicit `require`

## Validation

- `just verify` must pass (green-to-green)
- Verification count must not decrease
- 9/9 tests must still pass

---

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-06-13 | Started Step 4 wiring | |
| 2026-06-13 | ✅ Completed Step 4. 5001 valid. Class invariants sufficient for `head > 1` and `checkAllPositive`. | Proceed to Step 5 |
