# GapCycle — Type-Level Gap Invariant Wrapper

**Created:** 2026-06-08
**Status:** Complete ✅

---

## Goal

Create a `GapCycle` case class in `v1.cycle.gap` that wraps a strictly-positive list of gaps as a
`MinBoundList(lowerBound=0)` and provides both gap access and cumulative-sum access via an internal
`CycleIntegral(0, MemCycle)`. This mirrors the `SortedList` / `MinBoundList` / `MaxBoundList` pattern
— encoding "all gaps > 0" at the type-constructor level.

## Current State (before)

- Gaps in `SieveSequence` flow as bare `List[BigInt]` through the pipeline
  (`nextGaps → nextRotatedGaps → nextCycle → MemCycle`).
- `MemCycle` requires `checkPositiveOrZero` (≥ 0) and `nonEmpty`, but these are **scattered runtime
  checks** in `SieveSequenceNextLevel.nextCycle(seq)`.
- No standalone abstraction represents "a cycle of positive gaps with a cumulative-sum integral".
- The gap-sum property (`sum = modulus`) is verified case-by-case via `assertCalculateGapsSum`.
- **Total valid: 4178**

## Expected State (after)

New `GapCycle` class with:
- `MinBoundList(list, lowerBound=0)` — enforces `allGreaterThan(list, 0)` (all values > 0)
- Own `require(values.list.nonEmpty)` — at least one gap
- Derived `memCycle: MemCycle` — bridges `allGreaterThan` to `checkPositiveOrZero` via lemma
- Derived `integral: CycleIntegral(0, memCycle)` — cumulative sum from 0
- Accessors: `gap(index)`, `cumulativeSum(index)`, `size`, `sum`
- Lemmas: cumulative sum non-negative, cumulative sum strictly increasing

**SieveSequence integration:** See `gap-cycle-integration.md` (Phase 1-2 planned).

## Build Phases

One lemma / one method per verify cycle.

### Phase 1 — Lemma: `allGreaterThan(list, 0) ⇒ checkPositiveOrZero(list)` ✅
- Added `assertAllGreaterThanImpliesCheckPositiveOrZero` lemma in `GapCycle` companion.

### Phase 2 — GapCycle skeleton (case class + require + companion factory) ✅
- Case class with 3 requires: `lowerBound == 0`, `list.nonEmpty`, `checkPositiveOrZero(list)`.
- Companion `apply(list: List[BigInt])` factory with `require(allGreaterThan(list, 0))` + `assert(lemma)`.

### Phase 3 — Add `memCycle` and `integral` vals ✅
- Used `require(CycleUtils.checkPositiveOrZero(values.list))` on constructor (Stainless doesn't support `assert` in class body).
- `val memCycle: MemCycle = MemCycle(values.list)` — requires satisfied by the 3rd require.
- `val integral: CycleIntegral = CycleIntegral(BigInt(0), memCycle)`.

### Phase 4 — Add accessors ✅
- `gap(index)`, `cumulativeSum(index)`, `size`, `sum`.
- Simple delegates to `memCycle`, `integral`, `values`.

### Phase 5+6 — Lemma: cumulative sum positive ✅
- Added `assertCycleValuePositive` to `CycleIntegralProperties` — proves `ci.cycle(pos) > 0`
  given `allGreaterThan(values, 0)`. Uses `MemCycleProperties.findValueInCycle` for
  `cycle(pos) == values(idx)` and `ListBoundUtils.assertGreaterThanAtIndex` for `values(idx) > 0`.
- Added `assertCycleIntegralPositive` to `CycleIntegralProperties` — proves `ci(pos) > 0`
  by induction on pos using `assertCycleValuePositive` + `assertNextPosition`.
- Added `assertCumulativeSumPositive` to `GapCycle` companion — calls `assertCycleIntegralPositive`.
- **Lesson**: Proving positivity of cycle values requires bridging through `findValueInCycle`
  (equality) + `assertGreaterThanAtIndex` (> 0). Putting lemmas in `CycleIntegralProperties`
  is the right place — they generalize beyond GapCycle.
- Skipped strict-increasing lemma (not needed for current use cases).

### Phase 7 — Unit tests ✅
- Test file: `src/test/scala/v1/cycle/gap/GapCycleTest.scala`
- 7 tests: construction, gap access, cumulative sum, wrap-around, S_2 and S_3 gaps.
- All tests pass.

## Files

| File | Purpose |
|------|---------|
| `src/main/scala/v1/chapter4/cycle/gap/GapCycle.scala` | Main class + companion |
| `src/test/scala/v1/cycle/gap/GapCycleTest.scala` | Unit tests |

No existing files modified.

## Related Tickets
- `tickets/minbound-maxbound-abstraction.md` — MinBoundList pattern
- `tickets/sorted-list-abstraction.md` — SortedList pattern
- `tickets/next-level-requirements.md` — eventual consumer

---

## Progress Log

### 2026-06-08 — Phases 1-4 Complete
- Verified green: 4178 valid, 0 invalid.
- Created ticket.
- Created `v1.cycle.gap` package directories.
- **Phase 1**: Bridge lemma in GapCycle companion. Verified.
- **Phase 2**: Case class with 3 requires + companion factory. Verified.
- **Phase 3**: `memCycle` + `integral` vals. Used `require` (not `assert`) in class body per Stainless limitation. Verified at 4195.
- **Phase 4**: Accessors (`gap`, `cumulativeSum`, `size`, `sum`). Verified at 4197.
- **Lesson**: Stainless doesn't support `assert` in class body. Use `require` on constructor instead.
- **Lesson**: `.holds` lemmas in companion can be called from factory `apply` with `assert()` to prove constructor `require`s.

### 2026-06-08 — Phases 5-7 Complete
- **Phase 5+6**: Added `assertCycleValuePositive` and `assertCycleIntegralPositive` to
  `CycleIntegralProperties`. Also added `assertCumulativeSumPositive` back to GapCycle.
  Verified at 4240.
- **Phase 7**: Unit tests written and all 7 passing.
- **Lesson**: Proving `cycle(pos) > 0` requires bridging `findValueInCycle` (equality) +
  `assertGreaterThanAtIndex` (> 0). The right place for these lemmas is
  `CycleIntegralProperties`, not GapCycle — they're general-purpose.
- **Lesson**: The first attempt at `assertCumulativeSumNonNegative` in GapCycle got stuck
  because it needed `gc.gap(pos) >= 0`. The fix was to add a proper lemma in
  `CycleIntegralProperties` that proves `ci.cycle(pos) > 0` before using it.

## Result

- **Final verify: 4240 valid, 0 invalid** (up from 4178 = +62)
- **Phases completed**: All 7 phases
- **Files created**:
  - `src/main/scala/v1/chapter4/cycle/gap/GapCycle.scala` — case class + companion (63 lines)
  - `src/test/scala/v1/cycle/gap/GapCycleTest.scala` — 7 unit tests
- **Files modified**:
  - `src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala` — added `assertCycleValuePositive` and `assertCycleIntegralPositive` lemmas
- **Deviations from plan**:
  - Phase 3: Used `require` (not `assert`) in class body since Stainless doesn't support `assert` in constructor scope
  - Phase 5+6: Combined into positivity lemmas in `CycleIntegralProperties` (stronger than originally planned non-negative), skipped strict-increasing lemma as not needed
  - Phase 7: No deviations
