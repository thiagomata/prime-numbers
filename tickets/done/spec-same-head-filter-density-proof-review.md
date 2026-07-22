# Same-Head Filter Size Proof Review

**Created:** 2026-07-14
**Status:** Review note
**Primary source:** `src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala`
**Verified baseline:** `14463 valid`, `0 invalid`, `0 unknown`

## Scope

This document explains the verified proof of the same-head expanded filter size
property in human and mathematical terms. It is an internal review note for the
Stainless proof surface, not a published article.

The theorem proved is spec-local:

```text
SpecSieveSequence.assertSameHeadExtendedFilterCount(period)
```

It does not yet prove the full real `seq.next.size` theorem. It proves the
same-head filter step that the real-next/cycle proof must later consume.

The proof deliberately avoids:

- sorting;
- rotation;
- the cycle pipeline;
- actual `seq.next.head`;
- filtering before expansion.

The object under proof is the current `SpecSieveSequence`, whose `apply(k)`
enumerates accepted integer values. The same-head extension is represented by
counting accepted values that are not multiples of the current `head`.

## Final Statement

Let:

```text
h = head.value
M = tailPrimorial
p = period
```

The theorem assumes:

```text
p > 0
apply(p) == h + M
Calc.mod(M, h) != 0
```

The verified conclusion is:

```text
countAcceptedHeadNonMultiplesBetween(h, h + h * M) == p * (h - 1)
```

In words: over the expanded interval of length `h * M`, the old sequence accepts
`p * h` values, exactly `p` of those accepted values are multiples of the
current head, and therefore the same-head extension keeps exactly
`p * (h - 1)` values.

Mathematically:

```text
oldAccepted = countAcceptedBetween(h, h + h*M)
removed     = countAcceptedHeadMultiplesBetween(h, h + h*M)
survivors   = countAcceptedHeadNonMultiplesBetween(h, h + h*M)

oldAccepted = p*h
removed     = p
oldAccepted = removed + survivors

therefore:

survivors = oldAccepted - removed
          = p*h - p
          = p*(h - 1)
```

## Proof Shape

The proof has five layers.

```text
1. Old accepted count
   [h, h + h*M) contains p*h old accepted values.

2. Generated removed-count surface
   Count, among the first p*h generated old values, which are divisible by h.

3. Transpose generated indices
   The prefix [0, p*h) can be counted row-major or column-major.

4. One removal per old period offset
   For every old offset r in [0, p), the h lifted values
   apply(r), apply(r+p), ..., apply(r+(h-1)*p)
   contain exactly one multiple of h.

5. Survivor algebra
   Old accepted count minus removed count gives the same-head survivor count.
```

The hard part is layers 2-4. Earlier attempts had the right one-per-column
intuition but missed the verified bridge from prefix order to column order. The
current proof closes that bridge with a bounded row-major/column-major
transpose.

## Required Lemmas

### 1. `assertGeneratedPrefixCount(k)`

Human statement:

The first `k` generated values are exactly the accepted values in the integer
interval from `head` up to `apply(k)`.

Mathematical statement:

```text
countAcceptedBetween(h, apply(k)) == k
```

Why it is required:

The size theorem is about integer intervals, but the one-per-column argument is
easier over generated indices. This lemma connects generated-index length back
to interval accepted-count.

Used by:

```text
assertExpandedOldAcceptedCount(period)
```

### 2. `assertBlockShiftMultiple(offset, i, period)`

Human statement:

If `apply(period) == h + M`, then jumping forward by `period` generated indices
adds one full old modulus `M` to the generated value.

Mathematical statement:

```text
apply(offset + i*period) == apply(offset) + i*M
```

Why it is required:

The proof needs the expanded copies of each old accepted position. This lemma
turns generated-index strides into arithmetic lifts by `M`.

Used by:

```text
assertGeneratedHeadMultiplesStrideMatchesZeroOffsets
assertExpandedOldAcceptedCount
assertExpandedHeadMultipleCountFromGeneratedCount
```

### 3. `assertExpandedOldAcceptedCount(period)`

Human statement:

The expanded interval contains `h` copies of the old period, so the old filter
accepts `p*h` values in that interval.

Mathematical statement:

```text
expandedIndex = p*h
expandedEnd   = h + h*M

apply(expandedIndex) == expandedEnd
countAcceptedBetween(h, expandedEnd) == expandedIndex

therefore:

countAcceptedBetween(h, h + h*M) == p*h
```

Why it is required:

The final survivor count needs the starting total before the current head is
added as a new filter.

Used by:

```text
assertSameHeadExtendedFilterCountFromRemovedCount(period)
```

### 4. `countGeneratedHeadMultiplesPrefix(k)`

Human statement:

This recursive counter counts how many of the first `k` generated old values are
multiples of the current head.

Mathematical statement:

```text
countGeneratedHeadMultiplesPrefix(k)
  = |{ i | 0 <= i < k and Calc.mod(apply(i), h) == 0 }|
```

Why it is required:

It creates the generated-index counterpart of the interval removed count. The
final proof needs to show this count is `p` when `k = p*h`.

Used by:

```text
assertGeneratedHeadMultiplesPrefixExpandedCount(period)
assertGeneratedHeadMultiplePrefixCount(k)
```

### 5. `generatedHeadMultipleIndicator(index)`

Human statement:

One generated index contributes `1` exactly when its generated value is divisible
by the current head; otherwise it contributes `0`.

Mathematical statement:

```text
indicator(index) =
  if Calc.mod(apply(index), h) == 0 then 1 else 0
```

Why it is required:

The transpose proof needs a common one-cell contribution so row counts and
column counts can be related structurally.

Used by:

```text
assertGeneratedHeadMultiplesRangeFront
assertGeneratedHeadMultiplesStrideUntilStep
assertGeneratedHeadMultiplesByStrideOffsetsUntilStep
```

### 6. `countGeneratedHeadMultiplesRange(from, count)`

Human statement:

This counts generated head-multiples in a contiguous generated-index range.

Mathematical statement:

```text
countGeneratedHeadMultiplesRange(from, count)
  = |{ i | from <= i < from + count
          and Calc.mod(apply(i), h) == 0 }|
```

Why it is required:

The prefix counter is recursive from the front, while the transpose needs
subranges and row suffixes. This range counter is the bridge shape.

Used by:

```text
assertGeneratedHeadMultiplesPrefixMatchesRange(k)
assertGeneratedHeadMultiplesRangeAppend
assertGeneratedHeadMultiplesRangeMatchesStrideOffsetsUntil
```

### 7. `assertGeneratedHeadMultiplesPrefixMatchesRange(k)`

Human statement:

Counting the first `k` generated values is the same as counting the generated
range starting at index `0` with length `k`.

Mathematical statement:

```text
countGeneratedHeadMultiplesPrefix(k)
==
countGeneratedHeadMultiplesRange(0, k)
```

Why it is required:

The final removed-count goal is stated with the prefix counter, but the
transpose is proved over ranges.

Used by:

```text
assertGeneratedHeadMultiplesRangeMatchesStrideOffsets(period)
assertGeneratedHeadMultiplesPrefixExpandedCount(period)
```

### 8. `assertGeneratedHeadMultiplesRangeFront(from, count)`

Human statement:

A non-empty range count splits into the contribution of its first index plus the
remaining tail.

Mathematical statement:

```text
count > 0

countRange(from, count)
==
indicator(from) + countRange(from + 1, count - 1)
```

Why it is required:

The column-height step adds a row suffix. Stainless needs this front-split fact
to align the recursive definitions cell by cell.

Used by:

```text
assertGeneratedHeadMultiplesByStrideOffsetsUntilStep(offset, limit, period)
```

### 9. `assertGeneratedHeadMultiplesRangeAppend(from, left, right)`

Human statement:

Generated range counts are additive over adjacent ranges.

Mathematical statement:

```text
countRange(from, left + right)
==
countRange(from, left) + countRange(from + left, right)
```

Why it is required:

The bounded transpose grows by complete rows. This lemma lets the row-major
range count append one new row of length `period`.

Used by:

```text
assertGeneratedHeadMultiplesRangeMatchesStrideOffsetsUntil(limit, period)
```

### 10. `countGeneratedHeadMultiplesStrideFrom(offset, i, period)`

Human statement:

For one old-period offset, count the generated values in that column from height
`i` through height `h - 1`.

Mathematical statement:

```text
countStrideFrom(offset, i, p)
  = |{ j | i <= j < h
          and Calc.mod(apply(offset + j*p), h) == 0 }|
```

Why it is required:

This is the column count in the expanded window. It is the precise code form of
"for one old accepted value, inspect its `h` lifted copies."

Used by:

```text
countGeneratedHeadMultiplesByStrideOffsets(offset, period)
assertGeneratedHeadMultiplesStrideMatchesZeroOffsets(offset, i, period)
```

### 11. `countGeneratedHeadMultiplesStrideUntil(offset, i, limit, period)`

Human statement:

This is the bounded-height version of the stride count: it counts only heights
from `i` to `limit - 1`.

Mathematical statement:

```text
countStrideUntil(offset, i, limit, p)
  = |{ j | i <= j < limit
          and Calc.mod(apply(offset + j*p), h) == 0 }|
```

Why it is required:

The direct transpose over the full `h` height timed out. The bounded version
lets the proof grow the matrix one row at a time.

Used by:

```text
assertGeneratedHeadMultiplesStrideUntilStep
assertGeneratedHeadMultiplesStrideFromMatchesUntil
countGeneratedHeadMultiplesByStrideOffsetsUntil
```

### 12. `assertGeneratedHeadMultiplesStrideUntilStep(offset, i, limit, period)`

Human statement:

Increasing a bounded stride from height `limit` to `limit + 1` adds exactly the
new cell at index `offset + limit * period`.

Mathematical statement:

```text
countStrideUntil(offset, i, limit + 1, p)
==
countStrideUntil(offset, i, limit, p)
  + indicator(offset + limit*p)
```

Why it is required:

The transpose's column-major side must account for exactly the same new row that
the row-major side appends.

Used by:

```text
assertGeneratedHeadMultiplesByStrideOffsetsUntilStep(offset, limit, period)
```

### 13. `assertGeneratedHeadMultiplesStrideFromMatchesUntil(offset, i, period)`

Human statement:

The old full-height stride counter equals the bounded-height stride counter when
the bound is `head`.

Mathematical statement:

```text
countStrideFrom(offset, i, p)
==
countStrideUntil(offset, i, h, p)
```

Why it is required:

The bounded transpose proves facts about `countStrideUntil`; the one-per-column
count was already expressed through the full-height `countStrideFrom`. This
lemma connects those two shapes.

Used by:

```text
assertGeneratedHeadMultiplesByStrideOffsetsMatchesUntil(offset, period)
```

### 14. `assertGeneratedHeadMultiplesStrideMatchesZeroOffsets(offset, i, period)`

Human statement:

The generated stride count for one offset equals the arithmetic count of zero
modulo `h` among the lifted values:

```text
apply(offset), apply(offset) + M, ..., apply(offset) + (h - 1)*M
```

Mathematical statement:

```text
countStrideFrom(offset, i, p)
==
SieveUtils.countZeroOffsets(apply(offset), M, h, i)
```

because:

```text
apply(offset + j*p) == apply(offset) + j*M
```

Why it is required:

This is the exact bridge from generated-index columns to ordinary modular
arithmetic.

Used by:

```text
assertGeneratedHeadMultiplesStrideOne(offset, period)
```

### 15. `assertGeneratedHeadMultiplesStrideOne(offset, period)`

Human statement:

For each old-period offset, among the `h` lifted generated values in that
column, exactly one is divisible by `h`.

Mathematical statement:

```text
Calc.mod(M, h) != 0

countStrideFrom(offset, 0, p) == 1
```

Expanded:

```text
|{ j | 0 <= j < h
      and Calc.mod(apply(offset + j*p), h) == 0 }| == 1
```

Why it is required:

This is the central one-over-head removal fact, but stated for one generated
column. It proves "one removed copy per old accepted position."

Used by:

```text
assertGeneratedHeadMultiplesByStrideOffsetsCount(offset, period)
```

### 16. `countGeneratedHeadMultiplesByStrideOffsets(offset, period)`

Human statement:

This sums all full-height column counts from `offset` to `period - 1`.

Mathematical statement:

```text
countByOffsets(offset, p)
  = sum_{r=offset}^{p-1} countStrideFrom(r, 0, p)
```

Why it is required:

This is the column-major count over the expanded `period * head` generated
matrix.

Used by:

```text
assertGeneratedHeadMultiplesByStrideOffsetsCount
assertGeneratedHeadMultiplesRangeMatchesStrideOffsets
```

### 17. `countGeneratedHeadMultiplesByStrideOffsetsUntil(offset, limit, period)`

Human statement:

This is the bounded-height column-major count: sum each column only up to
height `limit`.

Mathematical statement:

```text
countByOffsetsUntil(offset, limit, p)
  = sum_{r=offset}^{p-1} countStrideUntil(r, 0, limit, p)
```

Why it is required:

It is the column-major side of the bounded transpose. Without it, the proof has
to jump directly from row-major prefix order to full-height column order, which
was the timeout shape.

Used by:

```text
assertGeneratedHeadMultiplesByStrideOffsetsUntilStep
assertGeneratedHeadMultiplesByStrideOffsetsUntilZero
assertGeneratedHeadMultiplesRangeMatchesStrideOffsetsUntil
```

### 18. `assertGeneratedHeadMultiplesByStrideOffsetsMatchesUntil(offset, period)`

Human statement:

The full column-major counter equals the bounded column-major counter at height
`head`.

Mathematical statement:

```text
countByOffsets(offset, p)
==
countByOffsetsUntil(offset, h, p)
```

Why it is required:

After proving the bounded transpose at `limit = h`, this lemma returns to the
original full column-major count.

Used by:

```text
assertGeneratedHeadMultiplesRangeMatchesStrideOffsets(period)
```

### 19. `assertGeneratedHeadMultiplesByStrideOffsetsUntilZero(offset, period)`

Human statement:

The bounded column-major count at height zero is zero.

Mathematical statement:

```text
countByOffsetsUntil(offset, 0, p) == 0
```

Why it is required:

This is the base case for the bounded transpose induction.

Used by:

```text
assertGeneratedHeadMultiplesRangeMatchesStrideOffsetsUntil(0, period)
```

### 20. `assertGeneratedHeadMultiplesByStrideOffsetsUntilStep(offset, limit, period)`

Human statement:

Increasing the bounded column-major height by one adds exactly the row suffix
from index `limit * period + offset` through the end of that row.

Mathematical statement:

```text
countByOffsetsUntil(offset, limit + 1, p)
==
countByOffsetsUntil(offset, limit, p)
  + countRange(limit*p + offset, p - offset)
```

Why it is required:

This is the column-major counterpart to row-major append. It lets the transpose
induction prove that both views add the same row at each height.

Used by:

```text
assertGeneratedHeadMultiplesRangeMatchesStrideOffsetsUntil(limit, period)
```

### 21. `assertGeneratedHeadMultiplesRangeMatchesStrideOffsetsUntil(limit, period)`

Human statement:

For any bounded height `limit`, counting the generated matrix row-major over the
prefix range is equal to counting it column-major over bounded stride offsets.

Mathematical statement:

```text
countRange(0, p*limit)
==
countByOffsetsUntil(0, limit, p)
```

Why it is required:

This is the verified transpose. It is the missing bridge that makes the proof
more than a narrated intuition. It connects:

```text
prefix/repeat order
```

to:

```text
per-old-offset lifted-copy order
```

Used by:

```text
assertGeneratedHeadMultiplesRangeMatchesStrideOffsets(period)
```

### 22. `assertGeneratedHeadMultiplesByStrideOffsetsCount(offset, period)`

Human statement:

Since every column removes exactly one value, the column-major count from
`offset` through the end is exactly the number of remaining columns.

Mathematical statement:

```text
countByOffsets(offset, p) == p - offset
```

In particular:

```text
countByOffsets(0, p) == p
```

Why it is required:

The transpose only says row-major and column-major counts are equal. This lemma
computes the column-major count.

Used by:

```text
assertGeneratedHeadMultiplesRangeMatchesStrideOffsets(period)
assertGeneratedHeadMultiplesPrefixExpandedCount(period)
```

### 23. `assertGeneratedHeadMultiplesRangeMatchesStrideOffsets(period)`

Human statement:

Over the full expanded generated prefix of length `p*h`, row-major range
counting equals full column-major stride counting.

Mathematical statement:

```text
countRange(0, p*h)
==
countByOffsets(0, p)
```

Why it is required:

This is the final bridge from the prefix order used by `apply` to the
one-per-column result.

Used by:

```text
assertGeneratedHeadMultiplesPrefixExpandedCount(period)
```

### 24. `assertGeneratedHeadMultiplesPrefixExpandedCount(period)`

Human statement:

Among the first `p*h` generated old values, exactly `p` are multiples of the
current head.

Mathematical statement:

```text
countGeneratedHeadMultiplesPrefix(p*h) == p
```

Why it is required:

This is the exact generated removed-count theorem needed by the interval proof.
It is the point where transpose plus one-per-column counting become the desired
one-over-head removal count.

Used by:

```text
assertSameHeadExtendedFilterCount(period)
```

### 25. `countNoAcceptedHeadMultiplesBetween(from, until)`

Human statement:

If an interval contains no accepted old values, then it also contains no
accepted old values that are multiples of the current head.

Mathematical statement:

```text
noAcceptedBetween(from, until)
==>
countAcceptedHeadMultiplesBetween(from, until) == 0
```

Why it is required:

`apply(k)` skips rejected integer candidates. This lemma proves skipped gaps
contribute zero removed values when converting generated-prefix counts into
integer-interval counts.

Used by:

```text
assertGeneratedHeadMultiplePrefixCount(k)
```

### 26. `assertCountAcceptedHeadMultiplesBetweenAppend(from, middle, until)`

Human statement:

Accepted-head-multiple interval counts are additive over adjacent intervals.

Mathematical statement:

```text
countAcceptedHeadMultiplesBetween(from, until)
==
countAcceptedHeadMultiplesBetween(from, middle)
  + countAcceptedHeadMultiplesBetween(middle, until)
```

Why it is required:

The generated-to-interval proof extends one generated value at a time and must
append the interval up to the next generated value.

Used by:

```text
assertGeneratedHeadMultiplePrefixCount(k)
```

### 27. `assertGeneratedHeadMultiplePrefixCount(k)`

Human statement:

The number of accepted multiples of `head` in the integer interval
`[head, apply(k))` is exactly the generated-prefix count for the first `k`
generated values.

Mathematical statement:

```text
countAcceptedHeadMultiplesBetween(h, apply(k))
==
countGeneratedHeadMultiplesPrefix(k)
```

Why it is required:

The removed-count proof must end over integer intervals, not only generated
indices. This lemma is the interval bridge.

Used by:

```text
assertExpandedHeadMultipleCountFromGeneratedCount(period)
```

### 28. `assertExpandedHeadMultipleCountFromGeneratedCount(period)`

Human statement:

If the generated prefix of length `p*h` contains exactly `p` head-multiples,
then the expanded integer interval contains exactly `p` accepted head-multiples.

Mathematical statement:

```text
require countGeneratedHeadMultiplesPrefix(p*h) == p

countAcceptedHeadMultiplesBetween(h, h + h*M) == p
```

Why it is required:

This consumes the generated removed-count theorem and produces the actual
removed-count fact for the interval used by the same-head filter.

Used by:

```text
assertSameHeadExtendedFilterCount(period)
```

### 29. `assertAcceptedCountSplitByHead(from, until)`

Human statement:

Every accepted value in an interval is either divisible by the current head or
not divisible by the current head, and the two counts add to the total accepted
count.

Mathematical statement:

```text
countAcceptedBetween(from, until)
==
countAcceptedHeadMultiplesBetween(from, until)
  + countAcceptedHeadNonMultiplesBetween(from, until)
```

Why it is required:

The same-head extension keeps exactly the non-multiples of the current head, so
the final algebra needs this split.

Used by:

```text
assertSameHeadExtendedFilterCountFromRemovedCount(period)
```

### 30. `assertSameHeadExtendedFilterCountFromRemovedCount(period)`

Human statement:

If the expanded interval contains `p*h` old accepted values and exactly `p` of
them are removed by the head filter, then the same-head extension keeps
`p*(h - 1)` values.

Mathematical statement:

```text
require countAcceptedHeadMultiplesBetween(h, h + h*M) == p

countAcceptedHeadNonMultiplesBetween(h, h + h*M)
==
p * (h - 1)
```

Why it is required:

This isolates the final arithmetic from the hard counting proof. Once removed
count is known, the size formula is direct.

Used by:

```text
assertSameHeadExtendedFilterCount(period)
```

### 31. `assertSameHeadExtendedFilterCount(period)`

Human statement:

This is the final verified same-head size theorem. It combines the old accepted
count, generated removed-count, interval removed-count, and survivor split.

Mathematical statement:

```text
p > 0
apply(p) == h + M
Calc.mod(M, h) != 0

countAcceptedHeadNonMultiplesBetween(h, h + h*M)
==
p * (h - 1)
```

Why it is required:

This is the proof result the later real-next/cycle-size proof should consume.
It establishes the exact size effect of adding the current head as a filter over
the expanded spec interval.

Used by:

```text
future real-next / cycle-size bridge
```

## Composition Diagram

```text
assertSameHeadExtendedFilterCount(period)
  |
  |-- assertGeneratedHeadMultiplesPrefixExpandedCount(period)
  |     |
  |     |-- assertGeneratedHeadMultiplesRangeMatchesStrideOffsets(period)
  |     |     |
  |     |     |-- assertGeneratedHeadMultiplesRangeMatchesStrideOffsetsUntil(h, period)
  |     |     |     |
  |     |     |     |-- assertGeneratedHeadMultiplesByStrideOffsetsUntilZero
  |     |     |     |-- assertGeneratedHeadMultiplesRangeAppend
  |     |     |     |-- assertGeneratedHeadMultiplesByStrideOffsetsUntilStep
  |     |     |           |
  |     |     |           |-- assertGeneratedHeadMultiplesStrideUntilStep
  |     |     |           |-- assertGeneratedHeadMultiplesRangeFront
  |     |     |
  |     |     |-- assertGeneratedHeadMultiplesByStrideOffsetsMatchesUntil
  |     |     |-- assertGeneratedHeadMultiplesByStrideOffsetsCount
  |     |
  |     |-- assertGeneratedHeadMultiplesPrefixMatchesRange(p*h)
  |
  |-- assertExpandedHeadMultipleCountFromGeneratedCount(period)
  |     |
  |     |-- assertBlockShiftMultiple(0, h, period)
  |     |-- assertGeneratedHeadMultiplePrefixCount(p*h)
  |
  |-- assertSameHeadExtendedFilterCountFromRemovedCount(period)
        |
        |-- assertExpandedOldAcceptedCount(period)
        |     |
        |     |-- assertBlockShiftMultiple(0, h, period)
        |     |-- assertGeneratedPrefixCount(p*h)
        |
        |-- assertAcceptedCountSplitByHead(h, h + h*M)
```

The arithmetic computation inside `assertGeneratedHeadMultiplesByStrideOffsetsCount`
depends on:

```text
assertGeneratedHeadMultiplesStrideOne(offset, period)
  |
  |-- assertGeneratedHeadMultiplesStrideMatchesZeroOffsets(offset, 0, period)
  |-- SieveUtils.assertCountZeroOffsetsOne(apply(offset), M, h)
```

## Why This Proves The Size Property

The same-head extension keeps old accepted values whose value is not divisible
by the current head. Therefore, to compute its size over the expanded interval,
the proof needs only two exact counts:

```text
total old accepted values
removed old accepted values divisible by h
```

The first count is generated-prefix counting:

```text
apply(p) == h + M
apply(p*h) == h + h*M
countAcceptedBetween(h, apply(p*h)) == p*h
```

So:

```text
oldAccepted = p*h
```

The second count is harder because it cannot be obtained by saying "one in
every h integers"; old accepted values are not all integers. The proof instead
uses the generated old sequence itself. It arranges the first `p*h` generated
values as a matrix:

```text
row-major index:    i = row*p + offset
column offset:      offset in [0, p)
column height:      row in [0, h)
generated value:    apply(offset + row*p)
```

Using `apply(p) == h + M`, each column becomes:

```text
apply(offset)
apply(offset) + M
apply(offset) + 2*M
...
apply(offset) + (h - 1)*M
```

Because `Calc.mod(M, h) != 0` and `h` is prime, those `h` lifts hit exactly one
zero residue modulo `h`. Therefore each column removes one value:

```text
countStrideFrom(offset, 0, p) == 1
```

There are `p` columns, so the column-major removed count is:

```text
countByOffsets(0, p) == p
```

The bounded transpose proves this is the same as the generated prefix count:

```text
countGeneratedHeadMultiplesPrefix(p*h) == p
```

Then the generated-prefix removed count is converted back to the integer
interval:

```text
countAcceptedHeadMultiplesBetween(h, h + h*M) == p
```

Finally:

```text
countAcceptedHeadNonMultiplesBetween(h, h + h*M)
==
countAcceptedBetween(h, h + h*M)
  - countAcceptedHeadMultiplesBetween(h, h + h*M)
==
p*h - p
==
p*(h - 1)
```

## Review Boundaries

This proof is enough to review the same-head filter-size property. It is not yet
the complete next-sequence theorem.

## Progress Updates (2026-07-14)

### Verified additions
- `assertHeadPlusTailPrimorialAccepted()` — proves `accepts(h + M)` (discharges `size()`'s former require)
- `size()` — require-free, returns `indexOfAccepted(h + M)` as canonical period
- `sameHeadSurvivorCount(period)` — body scans expanded interval, ensuring proves `= p*(h-1)` via the counting lemma
- `nextCycleSize()` on SpecDerivedSieveSequence — wraps counting method with lemma in ensuring
- `assertCycleSizeEqualsPeriod()` on SpecDerivedSieveSequence — gap cycle size = period
- `assertSurvivorAcceptedByNext(v)` — acceptance bridge: `accepts(v) && mod(v,h) != 0` ⇒ `next.passesFilter(v)` (verified)
- Removed 16 redundant `expandResidues` density lemmas from SieveUtils + SieveSequenceNextLevel

### Attempted but stuck
- `assertNextSizeFormula()` — `next.size() == p*(h-1)`. Postcondition times out because `size()` expands to `indexOfAccepted()` which recursively scans — SMT can't reduce it.
  - Requires proving `next.apply(p*(h-1)) == next.head + h*M` without using `indexOfAccepted`.
  - Needs lemma: `apply(1) == nextPrime.value` (first survivor = next head) — the existing `assertApplyOneIsPrimeIfBelowHeadSq` is private but proves `apply(1)` IS prime; it doesn't directly assert equality with `nextPrime.value`.
  - Once that lemma exists, the interval gap can be closed by block-shift reasoning, and the survivor count directly implies `next.size() == p*(h-1)`.

### Architecture note
- The cycle-side size theorem (`|G'| = |G|*(h-1)`) follows mechanically once the spec bridge is done — no new counting needed on the cycle side.
- `SpecDerivedSieveSequence(spec.next, p*(h-1))` only needs the construction require `spec.next.apply(p*(h-1)) == spec.next.head + spec.next.tailPrimorial` to be valid, which is exactly the same lemma as above.

Still pending for later work:

- Connect the same-head non-multiple interval count to the concrete real
  `seq.next` object.
- Handle the real head change from current `head` to the next prime.
- Connect the spec-local size theorem to the cycle/gap object.
- Only then discuss sorting/rotation/cycle pipeline size.

The important review question for this proof is not whether the real `next`
theorem is finished. It is whether the verified same-head theorem really proves:

```text
old expanded count = p*h
removed by current head = p
survivors = p*(h - 1)
```

The current Stainless result says yes for the spec-local same-head theorem.

## Next-Period Formula — Gap-Preservation Approach (promising, untried)

**Goal:** Prove `next.period() == period() * (head.value - 1)` on `SpecSieveSequence`.

**Key insight:** The value and order correspondence between `this.apply` and `next.apply` is already fully proven. The gap lemma `assertConsecutiveAcceptedByNextPreservesGap` (public, line 2712) proves that consecutive survivor gaps are identical in both sequences. Combined with:

1. **Starting point** — `assertApplyOneEqualsNextPrime`: `apply(1) == next.head` = `next.apply(0)` = first survivor
2. **Gap preservation** — `assertConsecutiveAcceptedByNextPreservesGap`: each gap between consecutive survivors is copied from `this.apply` to `next.apply`
3. **Count** — `sameHeadSurvivorCount(p) == expected`: exactly `expected` survivors
4. **Monotonicity** — `applyStrictlyIncreases`: both sequences are strictly increasing

By induction over all survivor pairs, `next.apply(k)` = k-th survivor for k = 0..expected-1. The `expected`-th position lands on the boundary `next.head + h*M`. Since `next.apply(next.period()) == next.head + next.tailPrimorial` (postcondition of `period()`), and `next.apply` is injective, `next.period() == expected`.

**What to try:**
- Uncomment `assertNextPeriodEqualsExpected`
- Replace the stuck `assert(next.apply(expected) == nextBoundary)` with an induction using `assertConsecutiveAcceptedByNextPreservesGap` chained from k=0 to k=expected-2
- The induction base uses `assertApplyOneEqualsNextPrime` for the starting point
- The induction step uses the gap lemma for each survivor pair

**What already works (verified):**
- `assertBlockShift` — public (line 2466)
- `assertBlockShiftMultiple` — public (line 2759)
- `assertSurvivorAcceptedByNext` — public (line 755)
- `assertNextValueAcceptedByThis` — public (line 724)
- `assertConsecutiveAcceptedByNextPreservesGap` — public (line 2712)
- `assertApplyOneEqualsNextPrime` — public (line 3996)
- `sameHeadSurvivorCount` — public (line ~1830)

**Status:** Method exists (commented out at line ~782). All required lemmas are public. No new lemmas needed — just composition of existing verified lemmas.

## Gap-Preservation Attempt — Results (2026-07-14)

All 33 body assertions pass. The proof logic is COMPLETE:

```text
Block shift:         apply(h*period) == head+h*M
Block shift:         apply(h*period+1) == next.head+h*M == nextBoundary
Gap:                 nextDoesNotPassAcceptedValue(h*period, nextBoundary)
Boundary:            next.apply(next.period()) == nextBoundary
Counting:            sameHeadSurvivorCount(p) == expected
```

**STUCK:** Stainless/Z3 cannot derive `nextSeq.period() == expected` from
these assembled facts. Root cause: `indexOfAccepted`'s postcondition is
`apply(res) == value` — it does not express minimality (`forall k < res,
apply(k) < value`). Without minimality, Stainless can't connect "expected
values below boundary" to "indexOfAccepted returns expected".

**Fix options (in order of feasibility):**

1. **Add minimality postcondition to `indexOfAccepted`/`findIndexForAcceptedFrom`**
   at line 2342, change:
   ```
   .ensuring(res => res >= k && apply(res) == value)
   ```
   to:
   ```
   .ensuring(res => res >= k && apply(res) == value && (forall j: BigInt). j >= 0 && j < res ==> apply(j) < value)
   ```
   This is the smallest change that closes the gap. The quantifier is
   supported by Stainless/Z3 and the recursive structure of
   `findIndexForAcceptedFrom` should make it easy to prove internally.

2. **Prove a count-to-index bridge lemma** — "if `countBelow(target) == n`
   and `apply(n) == target`, then `indexOfAccepted(target) == n`". Requires
   a new lemma that connects a counting function to `indexOfAccepted`.

3. **Prove `next.apply(expected) == nextBoundary` directly** — needs a
   bridge between `this.apply` and `next.apply` scan positions (the full
   gap-preservation induction using `assertConsecutiveAcceptedByNextPreservesGap`).
   Most complex option.

Option 1 is the most promising next step.
