# Cycle Integral Filter-Merge Theorem

**Created:** 2026-06-25
**Updated:** 2026-06-25
**Status:** Plan phase
**Depends on:** None (builds on existing CycleIntegral verified properties)

## Related Tickets

- `tickets/active/canonical-next-strategy.md` — Leg 3 gap-copy and merge rules transferred from Spec to Canonical (complete at 9472 valid). Demonstrates the transfer pattern but is tied to Spec's `indexOfAccepted`/`accepts` framework.
- `tickets/done/v0-gap-list-cycle-formalization.md` — Spec-level `mergedGapPrefix` and `assertMergedGapPrefixMatchesNext` proven. The algorithm exists but only for SpecSieveSequence.
- `tickets/superseded/v0-skip-multiples-until-nonmultiple.md` — Proves `assertSkipUntilNonMultiple` for finding the first survivor after a multiple within one period. Spec-level, not CycleIntegral-level.
- `tickets/active/remove-extern-from-next.md` — Walk-based `collectGaps` has opacity issues. The filter-merge at CycleIntegral level provides a structural alternative.

## Goal

Prove the **Filter-Merge Theorem** at the CycleIntegral level — a general property that connects filtered cumulative sums to merged gap cycles, independent of any sieve-specific concepts (primes, `accepts`, `indexOfAccepted`).

**The theorem:** Given a cycle of positive integers L (gaps), an initial value init, and a filter value v > 1, the merged gap list L' constructed by skipping positions where the cumulative sum is a multiple of v satisfies:

`CycleIntegral(L', init)(k) = CycleIntegral(L, init)(survivorPosition[k])`

where survivorPosition[k] is the k-th position whose cumulative sum is not a multiple of v.

The SieveSequence is the special case where v = head (the current prime), init = head, and we iterate this construction.

## Current State

- **Verification:** 9531 valid, 0 invalid, 0 unknown (green)
- **SpecSieveSequence** has `mergedGapPrefix`/`nextMergedGapOldIndex`/`sumGap` — fully verified filter-merge algorithm, but tied to the Spec model (uses `accepts`, `indexOfAccepted`, `apply` via linear scan)
- **CanonicalCycleSieve** transfers Spec's merge facts through `assertApplyMatches` (Leg 3 complete)
- **CycleIntegralProperties** has foundational lemmas: `assertDiffEqualsCycleValue`, `assertCycleIntegralIncreasing`, `assertConsecutiveGapSumEqualsDiff`, `assertSameDiffAfterCycle`
- **No CycleIntegral-native filter-merge theorem exists**

## Expected State

New file: `CycleIntegralFilterProperties.scala` under `src/main/scala/v1/chapter4/cycle/integral/recursive/properties/` containing:

1. **`isNonMultiple(ci, v, pos)`** — helper: `Calc.mod(ci(pos), v) != 0`
2. **`nextSurvivorIndex(ci, v, from)`** — smallest k > from where `ci(k) mod v != 0`, bounded by `from + v * ci.size` (periodicity guarantee)
3. **`mergedGapList(ci, v, from, count)`** — computes gaps between consecutive survivors, recursively building the merged gap list
4. **`assertMergedGapPositive(ci, v, from, count)`** — all merged gaps > 0 (since CI is strictly increasing)
5. **`assertMergedGapSumEqualsCI(ci, v, from)`** — each merged gap equals `ci(nextSurvivor(from)) - ci(from)` = sum of skipped + current gaps
6. **`assertMergedCycleIntegralMatchesFiltered(ci, v, count)`** — the main theorem: CI' built from merged gaps equals CI filtered to non-multiples
7. **`assertSurvivorExists(ci, v)`** — if `ci(0) mod v != 0`, there is at least one survivor; otherwise check within first v*n positions

## Approaches Considered

### Approach A: Direct CycleIntegral induction (RECOMMENDED)

Mirror the Spec's `mergedGapPrefix` algorithm but using pure CycleIntegral arithmetic instead of `indexOfAccepted`/`accepts`.

**Algorithm:**
```
nextSurvivorIndex(ci, v, from):
  if ci(from+1) mod v != 0: return from+1           // copy case
  else: search k ∈ (from+1, from+v*ci.size]          // merge case
    where ci(k) mod v != 0; return k

mergedGapList(ci, v, from, count):
  if count == 0: []
  else:
    next = nextSurvivorIndex(ci, v, from)
    gap = ci(next) - ci(from)                       // sum of skipped gaps
    gap :: mergedGapList(ci, v, next, count - 1)
```

**Key lemmas building on verified CycleIntegralProperties:**
- `assertDiffEqualsCycleValue`: `ci(k+1) - ci(k) == ci.cycle(k+1)` — single-gap identity
- `assertCycleIntegralIncreasing`: `b > a → ci(b) > ci(a)` — ensures gap positivity
- `assertSameDiffAfterCycle`: diffs repeat every period — enables search bound

**Strengths:** Pure cycle arithmetic, no Spec dependencies, directly reusable by any cycle integral context
**Risks:** The search loop within `nextSurvivorIndex` may timeout (see walk opacity issues in `remove-extern-from-next`). The difference: this search only unwinds within a bounded range (v*n), not head*n positions.
**Fallback:** Approach B

### Approach B: Bounded-index induction

Instead of a searching loop, use an explicit recursive function with `decreases` that steps one position at a time:

```
nextSurvivorRec(ci, v, from, step):
  decreases(v * ci.size - step)
  if step > v * ci.size: from + step  // sentinel: no survivor
  else if ci(from + step) mod v != 0: from + step
  else: nextSurvivorRec(ci, v, from, step + 1)
```

**Strengths:** Structurally recursive, no opaque loops, Stainless-friendly
**Risks:** The `decreases` measure may not be obvious to the solver if `ci.size` is not statically known
**Fallback:** Approach C

### Approach C: Spec transfer bridge

Accept that the filter-merge theorem lives on Spec, and prove a transfer lemma that any CycleIntegral whose cycle matches Spec's gap cycle inherits the merge property.

**Strengths:** Reuses fully verified Spec lemmas, minimal new code
**Risks:** Defeats the purpose of having CycleIntegral as an independent layer; still ties the proof to Spec
**Fallback:** N/A (last resort)

## Assumptions

1. `ci.cycle.values` are all strictly positive (> 0) — this is the `GapCycle` invariant
2. `v > 1` (filter value; v = 1 would filter nothing)
3. `ci.size > 0` (non-empty cycle)
4. `Calc.mod(ci(k), v) != 0` for at least one k in `[0, v*ci.size)` — at least one survivor exists
5. `assertCycleIntegralIncreasing` and `assertDiffEqualsCycleValue` are available (already verified)

## Risks

1. **Search-loop timeout:** The bounded search in `nextSurvivorIndex` may cause VC explosion similar to `collectGaps`. Mitigation: use Approach B (explicit recursion with decreases) instead.
2. **Periodicity proof:** Proving that `ci(k + v*n) mod v == ci(k) mod v` requires `assertSameDiffAfterCycle` composed v times. May need a helper lemma.
3. **Modulo arithmetic in `assert` blocks:** Must use `Calc.mod`, never `%`. May need to assert intermediate `Calc.mod` lemmas for the solver.
4. **List construction opacity:** Building `mergedGapList` and then constructing a `CycleIntegral` from it may hit the same `MemCycle` construction opacity that caused timeouts in `repeatList` attempts (CycleIntegralProperties.scala lines 379-472).

## Validation

- `green-to-green`: verify before and after each change
- `small-changes`: ONE lemma per verify cycle
- `stop-and-ask`: 3 failed attempts → stop
- Target location: `src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralFilterProperties.scala`

## Implementation Plan

1. Create `CycleIntegralFilterProperties.scala` with package/imports, verify compiles
2. Add `assertIsNonMultiple` (wrapper lemma: `Calc.mod(ci(pos), v) != 0`)
3. Add `assertNextSurvivorBounded` — proves that within `[from+1, from+v*ci.size]` there's a non-multiple (or none exist)
4. Add `nextSurvivorRec` — recursive bounded search for next non-multiple position
5. Add `mergedGapList` — recursive construction of merged gap list
6. Add `assertMergedGapPositive` — each merged gap > 0
7. Add `assertMergedGapSum` — merged gap = `ci(next) - ci(from)`
8. Add `assertMergedCycleIntegralMatchesFiltered` — main theorem
9. Update `OBJECTS.md`

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-06-26 | All lemmas verified, renamed with descriptive variable names, full javadoc with math added. 9716 valid. Main theorem `assertNewCIGeneratesFiltered` connects CI-level filter-merge: given filteredIntegral built from survivor values of the old CI, the new CI matches the old CI's filtered sequence. | Update OBJECTS.md with new properties. |
