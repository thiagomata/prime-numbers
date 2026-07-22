# GapCycle Integration into SieveSequence

**Created:** 2026-06-08
**Status:** Complete ✅
**Depends on:** `gap-cycle.md` (GapCycle exists, 4240 valid)

---

## Goal

Create `CycleSieveSequence` as a side-by-side alternative to `SieveSequence` that uses `GapCycle` as a first-class field, encoding the strictly-positive gap invariant at the type level from construction onward.

This replaces the mutation-based approach from v1 of this ticket (add `gapCycle` alongside `integral`) after review identified a critical issue: GapCycle constructor only stores `checkPositiveOrZero` (>= 0), not `allGreaterThan` (> 0), so Phase 3 removal of `checkAllPositive` require was unsound. The V2 approach starts clean with `allGreaterThan` as a structural invariant.

---

## Current State (before)

- `SieveSequence` has fields `primes: List[BigInt]` and `integral: CycleIntegral`
- Gap invariants are enforced by 3 `require`s on the V1 constructor
- `SieveSequenceNextLevel.nextCycle` returns bare `MemCycle` with 2 `require` assumptions
- `GapCycle` constructor stores `checkPositiveOrZero` (>= 0) but not `allGreaterThan` (> 0)
- **Total valid:** 4240

---

## Expected State (after)

### Prerequisite — Strengthen GapCycle (1 verify cycle)

Add `require(ListBoundUtils.allGreaterThan(values.list, BigInt(0)))` to GapCycle constructor.
The `checkPositiveOrZero` require becomes redundant but is kept (harmless).

### Phase 1 — CycleSieveSequence skeleton (2-3 verify cycles)

Create `CycleSieveSequence` with:
- Fields: `primes: List[BigInt]`, `gapCycle: GapCycle`
- Derived `val integral: CycleIntegral = CycleIntegral(primes.head, gapCycle.memCycle)`
- Same requires as V1 minus the gap ones (covered by gapCycle)
- Accessors: `head`, `modulus`, `cycle`, `apply`
- Factories: `S_0V2()`, `S_1V2()`

### Phase 2 — nextGapCycle + next() (2-3 verify cycles)

- Add `nextGapCycle(seq: SieveSequence): GapCycle` to `SieveSequenceNextLevel`
  - Same pipeline logic as `nextCycle` but returns `GapCycle` with `require(allGreaterThan(gaps, 0))`
- Add `next(): CycleSieveSequence` (marked `@extern`) to `CycleSieveSequence`
  - Creates temporary `SieveSequence` to pass to `nextGapCycle` (pragmatic since `@extern`)

### Phase 3 — Verify equivalence (2-4 verify cycles)

Prove V2 produces the same primes as V1 for base cases.

### Phase 4 — Tests (1-2 verify cycles + test runs)

- `CycleSieveSequenceTest.scala`: construction, apply, next, equivalence with V1
- Confirm all V1 tests still pass

---

## Build Phases (Detailed)

### Prerequisite: Strengthen GapCycle

**Cycle 1:** Add `require(ListBoundUtils.allGreaterThan(values.list, BigInt(0)))` to `GapCycle` case class. Add test. Verify.

### Phase 1a: CycleSieveSequence case class

Create `CycleSieveSequence.scala` with requires + derived `integral` val. Verify.

### Phase 1b: Add accessors + factories

Add `apply()`, `head`, `modulus`, `cycle`, `size`, `sum`. Add `S_0V2()`, `S_1V2()`. Verify.

### Phase 2a: Add nextGapCycle to SieveSequenceNextLevel

```scala
def nextGapCycle(seq: SieveSequence): GapCycle = {
  val gaps = nextRotatedGaps(seq)
  require(gaps.nonEmpty)
  require(ListBoundUtils.allGreaterThan(gaps, BigInt(0)))
  GapCycle(gaps)
}
```

Verify.

### Phase 2b: Add next() to CycleSieveSequence

```scala
@extern
def next(): CycleSieveSequence = {
  val newHead = apply(BigInt(1))
  val v1 = SieveSequence(primes, integral)
  val newGapCycle = SieveSequenceNextLevel.nextGapCycle(v1)
  CycleSieveSequence(newHead :: primes, newGapCycle)
}
```

Compile-check only (`@extern`).

---

## Risks

1. **V2 compiling without V1 changes**: Pipeline functions take `SieveSequence` — V2's `next()` creates a temporary V1. Since `next()` is `@extern`, this is fine at runtime. Compile-only concern.
2. **Phase 3 equivalence proofs**: May need bridging lemmas between V1 and V2 requires. If too complex, defer to runtime tests only.
3. **GapCycle strengthening**: Adding `allGreaterThan` to constructor should verify trivially since the factory already requires it. Risk: low.
4. **`allGreaterThan(gaps, 0)` in `nextGapCycle` remains unproven from pipeline**: This is the same unsolved problem from `r3-r5-r12`. GapCycle wraps the assumption; it doesn't prove it.

## Related Tickets

- `gap-cycle.md` — GapCycle standalone construction (COMPLETED)
- `gap-cycle-integration-review.md` — Review report recommending V2 approach
- `sieve-sequence-ticket.md` — SUPERSEDED
- `next-level-requirements.md` — SUPERSEDED
- `r3-r5-r12-gaps-nonempty-positive.md` — SUPERSEDED

## Validation

- `just verify` after each cycle
- Total valid count >= 4240
- V1 tests unchanged and passing
- `CycleSieveSequence.S_0V2().primes == SieveSequence.S_0().primes` (runtime)
- `CycleSieveSequence.S_0V2().next().primes == SieveSequence.S_0().next().primes` (runtime)

## Files

| File | Action |
|------|--------|
| `src/main/scala/v1/chapter4/cycle/gap/GapCycle.scala` | Modify: add `allGreaterThan` require |
| `src/main/scala/v1/chapter6/seq/sieve/CycleSieveSequence.scala` | Create: new case class |
| `src/main/scala/v1/chapter6/seq/sieve/SieveSequenceNextLevel.scala` | Modify: add `nextGapCycle` |
| `src/test/scala/v1/seq/sieve/CycleSieveSequenceTest.scala` | Create: tests |

No changes to `SieveUtils.scala`, `SieveSequence.scala`, or existing V1 tests.

## Progress Log

### 2026-06-08 — Prerequisite Complete ✅
- Added `require(ListBoundUtils.allGreaterThan(values.list, BigInt(0)))` to GapCycle constructor
- Verifies trivially (factory already requires `allGreaterThan`)
- 4240 valid, 0 invalid (unchanged count)

### 2026-06-08 — Phase 1 Complete ✅
- Created `CycleSieveSequence` with: `primes`, `gapCycle` fields, derived `integral` val
- Requires: `primes.nonEmpty`, `checkAllPositive(primes)`, `checkAllBiggerThanValue(primes, 1)`, `assertProductEqualOrBiggerThanElements(primes.tail)`
- Gap invariants structural via `GapCycle` type (no gap-related requires needed)
- Accessors: `head`, `modulus`, `cycle`, `apply`, `first`, `knownPrimeLimit`, `nextPrime`, `nextHead`
- Factories: `S_0V2()`, `S_1V2()`
- 4253 valid, 0 invalid (+13)

### 2026-06-08 — Phase 2-3 Complete ✅
- Added `nextGapCycle(seq: SieveSequence): GapCycle` to `SieveSequenceNextLevel`
  - Requires: `gaps.nonEmpty`, `ListBoundUtils.allGreaterThan(gaps, BigInt(0))`
  - Verified: 4255 valid, 0 invalid (+2)
- Added `next(): CycleSieveSequence` (`@extern`) — creates temp V1, calls `nextGapCycle`
- Added equivalence lemmas: `assertS0V2MatchesS0`, `assertS1V2MatchesS1`
  - Verified: 4257 valid, 0 invalid (+2)

### 2026-06-08 — Phase 4 Complete ✅
- Created `CycleSieveSequenceTest.scala` — 12 tests
  - Construction, apply, next for S_0, S_1, S_2
  - Equivalence with V1 for S_0, S_1, S_2
  - `nextGapCycle` produces correct GapCycle
- All 150 tests pass (up from 138), no regressions
- V1 tests unchanged
