# MinBoundList / MaxBoundList Abstraction

## Goal
Create `MinBoundList` and `MaxBoundList` case classes in `v1.list` that encode element
constraints at the type level — mirroring the `SortedList` pattern.

## Current State
- `ListUtils.checkAllBiggerThanValue(list, value)` — core "all > value" predicate (in `v1.list`)
- `v1.seq.sieve.CycleUtils.checkNonNegative(list)` — "all >= 0" (in `v1.seq.sieve`)
- `v1.seq.sieve.CycleUtils.allLessThan(list, bound)` — "all < bound" (in `v1.seq.sieve`)
- SieveUtils has preservation lemmas for `addOffset`, `filterList`, `insertSorted`, `sortFiltered`
- **Total valid: 4035**

## Expected State
- **`ListBoundUtils`** in `v1.list` — holds `checkNonNegative`, `allLessThan`,
  `assertAllLessThanTransitive`, `assertAllLessThanAppend`, `assertCheckNonNegativeAppend`
  (copied from `v1.seq.sieve.CycleUtils`; originals stay as dead code)
- **`MinBoundList(list, lowerBound)`** — requires `checkAllBiggerThanValue(list, lowerBound)`.
  Methods: `isEmpty`, `size`, `head`, `last`, `apply`, `tail` (with lemma), `filter` (with lemma).
- **`MaxBoundList(list, upperBound)`** — requires `allLessThan(list, upperBound)`.
  Methods: `isEmpty`, `size`, `head`, `last`, `apply`, `tail` (with lemma), `filter` (with lemma).
- `SortedList` untouched.

## Build Order

One lemma per verify cycle.

### Phase 1 — `ListBoundUtils` (3-4 cycles)
1. Create `ListBoundUtils` with `checkNonNegative` (copied from `v1.seq.sieve.CycleUtils`)
2. Add `allLessThan` to `ListBoundUtils`
3. Add `assertAllLessThanTransitive` to `ListBoundUtils`
4. Add `assertAllLessThanAppend` + `assertCheckNonNegativeAppend` to `ListBoundUtils`

### Phase 2 — `MinBoundList` (3 cycles)
5. Create `MinBoundList` skeleton: case class + require + tail lemma
6. Add filter method + filter lemma
7. Add accessors (isEmpty, size, head, last, apply)

### Phase 3 — `MaxBoundList` (3 cycles)
8. Create `MaxBoundList` skeleton: case class + require + tail lemma
9. Add filter method + filter lemma
10. Add accessors

## Alternatives Considered
- Single type with both bounds — rejected; bounds are orthogonal invariants
- Named types (PositiveList, NonNegativeList) — rejected; parameterized is more reusable
- Moving predicates FROM CycleUtils — rejected (never remove methods); copy instead

## Risks
- `SortedList` already has `tail` with lemma; `MinBoundList`/`MaxBoundList` need similar but for different predicates
- `filter` lemma needs to prove list.filter(pred) preserves bound — straightforward recursively
- No changes to `SieveUtils`, `CycleUtils`, or existing files needed (new files only + copies)

## Related Tickets
- `tickets/sorted-list-abstraction.md` — established the pattern this ticket follows

## Result (2026-06-08)

All phases completed successfully. Final verify: **4115 valid, 0 invalid**.

### Files created
- `src/main/scala/v1/list/ListBoundUtils.scala` — `checkNonNegative`, `allLessThan`,
  `assertAllLessThanTransitive`, `assertAllLessThanAppend`, `assertCheckNonNegativeAppend`
- `src/main/scala/v1/list/MinBoundList.scala` — `MinBoundList(list, lowerBound)` with
  `require(checkAllBiggerThanValue)`. Methods: `isEmpty`, `size`, `head`, `last`, `apply`, `tail`.
  Companion: `assertTailMinBound`.
- `src/main/scala/v1/list/MaxBoundList.scala` — `MaxBoundList(list, upperBound)` with
  `require(allLessThan)`. Methods: `isEmpty`, `size`, `head`, `last`, `apply`, `tail`.
  Companion: `assertTailMaxBound`.

### Changes from original plan
- `filter` method skipped (not needed immediately; predicate filter not cleanly supported in Stainless)
- Identical structure to `SortedList` — accessors + tail + companion lemma

### Predicates copied from `v1.seq.sieve.CycleUtils` (originals remain)
- `checkNonNegative`, `allLessThan` — now also in `ListBoundUtils`
- `assertAllLessThanTransitive`, `assertAllLessThanAppend`, `assertCheckNonNegativeAppend` — ditto

### No existing files modified
- `SieveUtils`, `CycleUtils`, `SortedList` all untouched
