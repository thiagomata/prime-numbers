# Ticket: R3 (gaps.nonEmpty) and R5/R12 (gaps positive or zero)

**Created:** 2026-06-07
**Status:** In progress
**Depends on:** `cycle-sum-lemma.md` (assertCalculateGapsSum verified)

---

## Goal

Prove two pipeline-dependent lemmas needed for `next()`:

1. **R3**: `nextGaps(seq).nonEmpty` → `nextRotatedGaps(seq).nonEmpty` → `MemCycle` constructor passes
2. **R5/R12**: `CycleUtils.checkPositiveOrZero(nextGaps(seq))` → all gaps are >= 0

## Current State

- 3786 valid, 0 invalid — green
- `assertNewCycleSumEqualsProduct` (R10) verified ✅
- Pipeline functions (`nextResidues` → `nextExpanded` → `nextFiltered` → `nextSorted` → `nextGaps`) all defined
- `nextCycle(seq): MemCycle` has `require(gaps.nonEmpty)` and `require(CycleUtils.checkPositiveOrZero(gaps))`
- `next()` has `@extern`

## Challenge

Pipeline functions produce outputs whose properties cannot be reasoned about without inlining, which causes timeout. Previous approach for R10 avoided this by making `assertCalculateGapsSum` vacuously true for empty sorted.

For R3 and R5/R12, we can't make them vacuously true — `MemCycle` genuinely needs non-empty, positive gaps.

## Strategy

### Phase 1: Add postconditions to individual pipeline functions

Adding `.ensuring` to individual functions keeps each VC small. The caller can then use the postcondition without inlining.

1. `calculateGaps(sorted, modulus)`: `.ensuring(res => sorted.isEmpty || res.nonEmpty)` — trivially true since the `size==1` and `size>1` branches both return non-empty
2. `sortFiltered(list)`: `.ensuring(res => list.isEmpty || res.nonEmpty)` — trivially true since insertion sort always produces non-empty from non-empty
3. `pairwiseGaps(list)`: already fine for positivity (differences of sorted values are >= 0)
4. `residues(modulus, primes)`: `.ensuring(_.nonEmpty)` — prove 1 is always coprime
5. `expandResidues(residues, mod, p)`: `.ensuring(res => residues.isEmpty || res.nonEmpty)`

### Phase 2: Try R3 lemma

```scala
def assertNextGapsNonEmpty(seq: SieveSequence): Boolean = {
  nextGaps(seq).nonEmpty
}.holds
```

With the postconditions from Phase 1, Stainless may be able to chain them without inlining.

### Phase 3: Try R5/R12 lemma

```scala
def assertNextGapsPositiveOrZero(seq: SieveSequence): Boolean = {
  CycleUtils.checkPositiveOrZero(nextGaps(seq))
}.holds
```

Need to prove gaps are non-negative. From `calculateGaps`:
- Inner gaps: `sorted[i+1] - sorted[i]` — since sorted is (assumed) ascending, diff >= 0
- Wrap gap: `modulus - sorted.last + sorted.head` — sorted.head >= 0, sorted.last < modulus, so wrap > 0

### Phase 4: Fallback (if timeout)
If postconditions don't work, alternative approaches:
- Make `assertNextGapsNonEmpty` vacuously true (change `calculateGaps` for empty sorted to return `[modulus]`)
- Prove positivity differently (without requiring sorted ascending)

## Assertion Inventory (created 2026-06-07)

All lemmas in `SieveUtils.scala` and `v1.seq.sieve.CycleUtils` (seq.sieve).

| # | Function | File | VCs | Status | Notes |
|---|----------|------|-----|--------|-------|
| 1 | `assertInsertSortedAscending` | SieveUtils | +13 | VERIFIED | |
| 2 | `assertSortFilteredAscending` | SieveUtils | +13 | VERIFIED | |
| 3 | `assertAddOffsetNonNegative` | SieveUtils | +16 | VERIFIED | |
| 4 | `assertAddOffsetAllLessThan` | SieveUtils | +16 | VERIFIED | |
| 5 | `assertAllLessThanAppend` | CycleUtils (seq.sieve) | +12 | VERIFIED | |
| 6 | `assertCheckNonNegativeAppend` | CycleUtils (seq.sieve) | +12 | VERIFIED | |
| 7 | `assertExpandSingleRange` | SieveUtils | +42 | VERIFIED | |
| 8 | `assertExpandResiduesRange` | SieveUtils | +42 | VERIFIED | |
| 9 | `assertFilterListNonNegative` | SieveUtils | +10 | VERIFIED | |
| 10 | `assertFilterListAllLessThan` | SieveUtils | +10 | VERIFIED | |
| 11 | `assertInsertSortedNonNegative` | SieveUtils | +10 | VERIFIED | |
| 12 | `assertSortFilteredNonNegative` | SieveUtils | +14 | VERIFIED | |
| 13 | `assertInsertSortedAllLessThan` | SieveUtils | +10 | VERIFIED | |
| 14 | `assertSortFilteredAllLessThan` | SieveUtils | +14 | VERIFIED | |
| 15 | `assertCalculateGapsNonNegative` | SieveUtils | — | DELETED (accident) | Same structure as #16 — likely timed out too |
| 16 | `assertCalculateGapsPositiveOrZero` | SieveUtils | — | DELETED (accident) | Intended target — timed out |
| 17 | `assertNextGapsNonEmpty` (R3) | SieveSequenceNextLevel | — | COMMENTED OUT (accident) | Was verified, should be restored |
| 18 | `assertNextGapsPositiveOrZero` | SieveSequenceNextLevel | — | STILL ACTIVE | The current timeout — should be removed/commented |

### Code for missing/affected assertions

**#15 — `assertCalculateGapsNonNegative` — DELETED**
```scala
  def assertCalculateGapsNonNegative(sorted: List[BigInt], modulus: BigInt): Boolean = {
    require(modulus > 0)
    require(sorted.isEmpty || sorted.head >= 0)
    require(sorted.isEmpty || sorted.last < modulus)
    require(isAscending(sorted))
    CycleUtils.checkNonNegative(calculateGaps(sorted, modulus))
  }.holds
```

**#16 — `assertCalculateGapsPositiveOrZero` — DELETED**
```scala
  def assertCalculateGapsPositiveOrZero(sorted: List[BigInt], modulus: BigInt): Boolean = {
    require(modulus > 0)
    require(sorted.isEmpty || sorted.head >= 0)
    require(sorted.isEmpty || sorted.last < modulus)
    require(isAscending(sorted))
    CycleCycleUtils.checkPositiveOrZero(calculateGaps(sorted, modulus))
  }.holds
```

**#17 — `assertNextGapsNonEmpty` — COMMENTED OUT (should be restored)**
```scala
  def assertNextGapsNonEmpty(seq: SieveSequence): Boolean = {
    nextGaps(seq).nonEmpty
  }.holds
```

**#18 — `assertNextGapsPositiveOrZero` — STILL ACTIVE (should be removed)**
```scala
  def assertNextGapsPositiveOrZero(seq: SieveSequence): Boolean = {
    val newMod = seq.modulus * seq.head
    val residues = SieveUtils.residues(seq.modulus, seq.primes.tail)
    val expanded = SieveUtils.expandResidues(residues, seq.modulus, seq.head)
    val filtered = SieveUtils.filterList(expanded, seq.head)
    val sorted = SieveUtils.sortFiltered(filtered)
    SieveUtils.assertExpandResiduesRange(residues, seq.modulus, seq.head)
    SieveUtils.assertFilterListNonNegative(expanded, seq.head)
    SieveUtils.assertFilterListAllLessThan(expanded, newMod, seq.head)
    SieveUtils.assertSortFilteredNonNegative(filtered)
    SieveUtils.assertSortFilteredAllLessThan(filtered, newMod)
    SieveUtils.assertSortFilteredAscending(filtered)
    CycleUtils.checkPositiveOrZero(SieveUtils.calculateGaps(sorted, newMod))
  }.holds
```

## Key Problem: why #15, #16, #18 timeout

All three try to prove `checkNonNegative`/`checkPositiveOrZero(calculateGaps(sorted, modulus))`
given `isAscending(sorted)`, `sorted.head >= 0`, `sorted.last < modulus`.

`calculateGaps` inlines `pairwiseGaps` (recursive) and computes `wrapGap`.  
The proof needs:
1. For `sorted.size > 1`: each `sorted(i+1) - sorted(i) >= 0` from `isAscending(sorted)` — requires induction
2. `modulus - sorted.last + sorted.head >= 0` from `sorted.head >= 0` and `sorted.last < modulus`

Induction + inlining of `pairwiseGaps` + inlining of `checkNonNegative`/`checkPositiveOrZero` 
creates a VC too large for Z3 within the timeout.

**Suspected root cause:** no dedicated lemma for `pairwiseGaps` non-negativity under `isAscending`.  
Without it, `calculateGaps` carries the full induction burden every time it's inlined.

## Next Direction

Instead of re-proving the same thing, consider a `SortedResidues` wrapper class 
that encodes invariants at construction and exposes `.gaps` with postcondition:

```scala
case class SortedResidues(values: List[BigInt], modulus: BigInt) {
  require(modulus > 0)
  require(values.isEmpty || values.head >= 0)
  require(values.isEmpty || values.last < modulus)
  require(isAscending(values))

  def gaps: List[BigInt] = {
    calculateGaps(values, modulus)
  }.ensuring(res => checkPositiveOrZero(res))
}
```

The invariants are proven **once** at construction (using the range lemmas).  
`.gaps` then proves positivity trivially using those invariants — small VC, no pipeline inlining.

## Validation
- `just verify` passes after each small change
- Incremental: one `.ensuring` or lemma per verify cycle
- First step: restore `assertNextGapsNonEmpty` (#17) and remove `assertNextGapsPositiveOrZero` (#18) to get green
