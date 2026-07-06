# Verify Timeout Root Cause Analysis

**Created:** 2026-06-29
**Updated:** 2026-06-29
**Status:** In progress
**Depends on:** none

## Related Tickets

- `sieve-sequence-proof.md` — Sieve equivalence proof (active). The timeout blocks progress on all sieve verification.

## Goal

Identify and eliminate the root cause(s) of `just verify` timing out after changes introduced between commit `26760e08` (working) and `a60324d9` (broken). Each hypothesis is tested by reverting ONE change at a time and checking if verify completes.

## Current State

`just verify` times out even after hours of execution. Last working commit: `26760e08` ("CycleSieveSequence equality proved"). Two subsequent commits broke it:
- `1959fc0d` ("broken 1")
- `a60324d9` ("broken 2 - timing out")

## Expected State

`just verify` completes successfully within reasonable time.

## Suspected Root Causes (ranked by probability)

### 1. SieveSequenceProperties.assertHeadIsPrime — proof strategy changed

**File:** `SieveSequenceProperties.scala:57-63`

**Old** (required a bounded precondition + delegated to existing verified lemma):
```
require(SieveUtils.assertAllNotCoprimeInRange(seq.head, 2, seq.primesTailValues))
PrimeProperties.assertHeadIsPrime(seq.head, seq.primesTailValues)
Prime.isPrime(seq.head)
```

**New** (tries to prove Prime.isPrime inline via assertions):
```
assert(seq.primes.head.value == seq.head)
assert(Prime.isPrime(seq.primes.head.value))
Prime.isPrime(seq.head)
```

**Why it would timeout:** Old version pushed the heavy proof into a separate `.holds` function (`PrimeProperties.assertHeadIsPrime`) with a bounded range precondition (`assertAllNotCoprimeInRange`). The new version requires Stainless to prove `Prime.isPrime` from scratch via equality substitution, forcing the solver to fully unfold the recursive primality check.

### 2. New require preconditions in CycleSieveSequence next methods

**File:** `CycleSieveSequence.scala:52-54, 74-76, 97-99`

3 new `require` preconditions added to `nextWithGapCycle`, `nextFromWindow`, and `next`:
```
require(primes.next.isEmpty == false)
require(primes.next.head.value == newHead)
require(Calc.mod(PrimeUtils.primorial(primes.next.list.tail.list), ...) != 0)
```

**Why it would timeout:** The third require involves `PrimeUtils.primorial` (recursive product over `List[Prime]`). Every call site must discharge this precondition, distributing the solver effort across the entire proof tree.

### 3. CycleSieveSequence constructor require changed

**File:** `CycleSieveSequence.scala:18`

Changed `primes.list.list` to `primes.list.tail.list`:
```
require(Calc.mod(PrimeUtils.primorial(primes.list.tail.list), ...) != 0)
```

### 4. New require in SieveSequenceNextLevel.nextGaps

**File:** `SieveSequenceNextLevel.scala:33-34, 193-194`

Added `seq.head > 0` and `seq.modulus > 0` requires to `nextGaps` and `assertNextGapsNonEmpty`.

### 5. New recursive primorialMatchesSieveProduct lemma

**File:** `SpecCycleSieveEquivalence.scala:24-34`

Inductive lemma relating `PrimeUtils.primorial` to `SieveUtils.product`. Called in `assertValueAcceptance`.

### 6. More expensive require comparisons in SpecCycleSieveEquivalence

**File:** `SpecCycleSieveEquivalence.scala:45, 65, 286`

Changed `cycle.primes == ...` to `PrimeUtils.primeValues(...) == PrimeUtils.primeValues(...)`, adding recursive function evaluations on both sides.

### 7. assertModPreservesCoprime made public

**File:** `SpecCycleSieveEquivalence.scala:614`

Changed from `private` to `def`, making full contract validation public.

## Assumptions

- The timeout is caused by changes in commits `1959fc0d` and `a60324d9`
- Reverting individual changes will isolate which one(s) caused the timeout
- The bloop cache deletion in `1959fc0d` is a one-time cost, not the persistent cause

## Validation

For each fix:
1. Revert ONE change in ONE file
2. Run `just verify` with a reasonable timeout (e.g. 20 min)
3. If it completes, the reverted change was a root cause
4. If it still times out, preserve the fix and try the next

## Implementation Plan

1. Fix 1: Revert `SieveSequenceProperties.assertHeadIsPrime` to require-based version — `SieveSequenceProperties.scala`
2. Test after Fix 1
3. Fix 2: Revert new requires in `CycleSieveSequence` next methods — `CycleSieveSequence.scala`
4. Test after Fix 2
5. Fix 3: Revert new requires in `SieveSequenceNextLevel` — `SieveSequenceNextLevel.scala`
6. Test after Fix 3
7. Fix 4: Revert/remove `primorialMatchesSieveProduct` and new assertions in `assertValueAcceptance` — `SpecCycleSieveEquivalence.scala`
8. Test after Fix 4
9. Fix 5: Revert assertModPreservesCoprime to private — `SpecCycleSieveEquivalence.scala`
10. Test after Fix 5

## Fallback Options

If single-revert doesn't resolve: try reverting ALL changes in commit `1959fc0d` wholesale, then `a60324d9`, to isolate which commit introduced the regression.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-06-29 | Ticket created. Full diff between good (26760e08) and broken (a60324d9) analyzed. 7 potential root causes identified in 4 files. | Start Fix 1. |
| 2026-06-30 | **Root cause #1: Circular ch5 ↔ ch6 dependency.** ch5 imported SieveUtils from ch6, and ch6 imported Prime/PrimeUtils from ch5. This forced all 6 chapters to be verified together, creating too many VCs for the solver. | Created `CoprimeUtils.scala` in ch5, copied 10 utility functions from ch6 SieveUtils, updated all ch5 imports. ch5 no longer imports from ch6. Verify-ch 5 runs 5678 VCs in 47s. |
| 2026-06-30 | **Root cause #2: Z3 JNI library not found.** `libz3java.dylib` was built but macOS strips `DYLD_LIBRARY_PATH` from subprocesses, so the dynamic linker couldn't find `libz3.dylib` dependency. | Used `install_name_tool -change libz3.dylib <absolute-path>` to embed the absolute path in `libz3java.dylib`. Still getting fallback warning but smt-z3 works ~83 VCs/s. |
| 2026-06-30 | **Root cause #3: 3 timeout VCs.** `SieveSequenceProperties.assertHeadIsPrime`, `SpecCycleSieveEquivalence line 246 assert`, `CycleSieveSequence line 63 constructor call`. All commented out for now. | Need to uncomment and fix one by one with focused verify. |

