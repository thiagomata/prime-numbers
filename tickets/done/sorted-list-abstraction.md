# SortedList Abstraction

## Goal
Create a `SortedList` case class in `v1.list` that encodes the ascending invariant at the type level,
moving proof burden from scattered `SieveUtils` lemmas to construction boundaries.

## Current State
- `SieveUtils` has `isAscending`, `insertSorted`, `sortFiltered`, and lemmas proving they preserve
  ascending order (`assertInsertSortedAscending`, `assertSortFilteredAscending`).
- `SieveSequenceNextLevel.nextSorted` returns `List[BigInt]` with no type-level guarantee of sortedness.
- All 5 previously-commented lemmas (`assertFilterListAllLessThan`, `assertInsertSortedNonNegative`,
  `assertSortFilteredNonNegative`, `assertInsertSortedAllLessThan`, `assertSortFilteredAllLessThan`)
  have been restored and verified.
- **Total valid: 3972**

## Expected State
- `SortedList(list: List[BigInt])` with `require(isAscending(list))` on the constructor.
- `SortedList` companion contains: `isAscending`, `assertTailAscending`, `insertSorted`,
  `assertInsertSortedAscending`, `sortFiltered`, `assertSortFilteredAscending`, `fromUnsorted`, `empty`.
- `SortedList` methods: `isEmpty`, `size`, `head`, `last`, `apply`, `tail`, `insert`.
- `SieveSequenceNextLevel.nextSorted` returns `SortedList`.
- Gap functions (`calculateGaps`, etc.) remain in `SieveUtils` — not sorted-list-specific.
- Old `SieveUtils` methods remain (never remove methods rule).
- **Scope: ascending invariant only** (non-negative/all-less-than lemmas stay in `SieveUtils` for now).

## Plan

### Phase 1 — Create `SortedList.scala` (10 verify cycles)

One lemma per cycle. Order:

1. Create skeleton: `case class SortedList` + `require(isAscending)`. Companion with `isAscending`. Minimal — no methods yet.
2. Add `assertTailAscending` lemma to companion.
3. Add `insertSorted` helper to companion.
4. Add `assertInsertSortedAscending` lemma to companion.
5. Add `sortFiltered` helper to companion.
6. Add `assertSortFilteredAscending` lemma to companion.
7. Add `fromUnsorted` factory + `empty` value.
8. Add `tail` method on case class (uses `assertTailAscending`).
9. Add `insert` method on case class.
10. Add remaining convenience methods: `isEmpty`, `size`, `head`, `last`, `apply`.

### Phase 2 — Update `SieveSequenceNextLevel` (3 verify cycles)

1. Change `nextSorted` return type to `SortedList`, use `SortedList.fromUnsorted`.
2. Update `nextGaps`, `nextHeadResidueIndex` to pass `.list` to `SieveUtils` functions.
3. Update `assertNewCycleSumEqualsProduct` to use `.list`.

### Phase 3 — Update `SieveSequenceTest` (1 verify cycle)

Change `sorted should be(...)` to `sorted.list should be(...)`.

## Alternatives Considered
- Moving gap functions into `SortedList` — rejected as misplaced (gaps are sieve-specific).
- Adding overloads to `SieveUtils` taking `SortedList` params — rejected to keep `SieveUtils` untouched.
- Including non-negative/all-less-than invariant in `SortedList` — deferred to follow-up.

## Risks
- `assertTailAscending` recurrence: need to make sure recursive call goes through.
- `tail` method `require(list.nonEmpty)` + lemma call: Stainless must accept the assert proof.
- `insert` method: calls `assertInsertSortedAscending` before `SortedList(...)` construction.
