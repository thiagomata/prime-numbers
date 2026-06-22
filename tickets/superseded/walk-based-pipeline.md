# Walk-Based V2 Pipeline (Replace Residue Pipeline)

**Created:** 2026-06-08
**Status:** Complete — 4302 valid, 0 invalid, all 26 tests pass
**Depends on:** `gap-cycle-integration.md` (V2 skeleton exists)

---

## Goal

Replace the residue-based V2 pipeline with a walk-based approach that directly walks through the integral, filters multiples of head, and computes gaps — removing the need for the `rotateAt` step and the `SortedResidues` wrapper.

---

## Current State (2026-06-08, after 2 sessions)

### What's in the code

The walk-based functions are **saved in the file** (`SieveSequenceNextLevel.scala`):

- `collectGapsV2(seq, lastSurvivor, pos, remaining, gaps)` — recursive walk that tracks `currentValue` as `seq.apply(pos+1)`, filters multiples of `seq.head`, collects gaps between survivors
- `nextGapsWalkV2(seq)` — entry point: `steps = seq.head * seq.gapCycle.size`, starts walk from `pos=1` with `lastSurvivor = newHead`
- `nextGapCycleV2` now uses `nextGapsWalkV2` with no old residue pipeline assertions (cleaned up)

### What was removed (last session)

- `assert(assertNextGapsNonEmptyV2(seq))` — called old residue pipeline
- `assert(SieveUtils.assertRotateAtPreservesNonEmpty(...))` — called old pipeline

### Verification result (after fix)

**4302 valid, 0 invalid, 0 unknown** — done in 15.39s.

The fix uses `CycleIntegralProperties.assertCycleIntegralPositive(seq.integral, pos)` which proves `seq.integral(pos) > 0` using GapCycle's `allGreaterThan` invariant. The lemma is in `CycleIntegralProperties` (proved in `articles/integral-cycle.md`), and its preconditions are all satisfied by `CycleSieveSequence`'s invariants.

### Tests

**26/26 pass** — all V1 and V2 sieve tests pass.

---

## Attempts Made

### Attempt 1: Add `assertMemCyclePositive(gc, k)` lemma in GapCycle companion
- **What:** Proves `gc.memCycle(k) > 0` using private `values.list` access from companion
- **Result:** Timeout — inlining through `MemCycle.apply` → `ModCycle.apply` → `values(k % size)` too deep for Z3

### Attempt 2: Add `assertGapPositive(k)` as instance method on GapCycle
- **What:** Same as above but via instance method instead of companion
- **Result:** Timeout — same inlining depth issue

### Attempt 3: Remove old pipeline assertions, keep walk-based functions
- **What:** Removed `assert(assertNextGapsNonEmptyV2)` and `assert(SieveUtils.assertRotateAtPreservesNonEmpty(...))` from `nextGapCycleV2`
- **Result:** Verification cancelled at 2004/4296 — `current > 0` unprovable in `collectGapsV2`

### ✅ Attempt 4 (Success): Use `CycleIntegralProperties.assertCycleIntegralPositive` lemma
- **What:** Replaced bare `assert(current > 0)` with `assert(CycleIntegralProperties.assertCycleIntegralPositive(seq.integral, pos))`
- **Result:** **4302 valid, 0 invalid, all 26 tests pass** — the lemma links GapCycle's `allGreaterThan` invariant to CycleIntegral positivity

---

## Root Cause Analysis

### Why verification fails

The actual failing VC is **`current > 0`** in `collectGapsV2` at line 170. The recursive call passes `current` (from `seq.apply(pos+1)`) as the new `lastSurvivor`, but Stainless can't prove it's positive.

This is a **precondition gap** — the function requires `lastSurvivor > 0` but doesn't require that the integral values being walked are also positive. The fix is to add `require(current > 0)` inside the function body before the recursive call.

### Why earlier analysis was wrong

The earlier analysis assumed a deep CycleIntegral inlining timeout. The actual error is simpler:
1. `collectGapsV2` requires `lastSurvivor > 0` (line 160)
2. In the recursive case where `current` survives filtering, it's passed as the new `lastSurvivor` (line 170)
3. But Stainless doesn't know `current > 0` — it only knows `current = seq.apply(pos+1)`
4. The `seq.apply` returns a `BigInt` — no positivity guarantee
5. **Fix**: add `require(current > 0)` before the recursive call

---

## What We Know

| Fact | Evidence |
|------|----------|
| V1 works (V1 `next()` uses same structure) | V1 verified, all tests pass |
| V2 skeleton was green before walk additions | 4285 valid, 0 invalid |
| Old pipeline functions (`nextResiduesV2`, etc.) still compile | No compile errors |
| `collectGapsV2` + `nextGapsWalkV2` compile | Added and saved |
| `nextGapCycleV2` now uses walk-based gaps | Confirmed in file |
| **Verification times out with walk-based functions** | 10+ min no result |

---

## Fix Applied

**Added `assert(CycleIntegralProperties.assertCycleIntegralPositive(seq.integral, pos))`** in `collectGapsV2` else branch, replacing bare `assert(current > 0)`.

This works because:
1. `seq.integral = CycleIntegral(primes.head, gapCycle.memCycle)` 
2. `gapCycle` has `allGreaterThan(values.list, 0)` invariant
3. `assertCycleIntegralPositive` requires this `allGreaterThan` and proves `integral(pos) > 0`
4. `current = seq.apply(pos+1) = integral(pos)`, so `current > 0` is proved

## Remaining: `@extern` on `next()`

`next()` is still `@extern`. The GapCycle constructor requires `allGreaterThan(gaps, 0)`, and `nextGapCycleV2` has `require(ListBoundUtils.allGreaterThan(gaps, BigInt(0)))`. This VC is discharged by `@extern`.

**To remove `@extern`**, we would need to prove `allGreaterThan(gaps, 0)` for walk-generated gaps — which requires proving that all gaps (positive differences between survivors) are positive. This is a future task.

---

## Files Modified in This Session

| File | Change |
|------|--------|
| `SieveSequenceNextLevel.scala` | Removed 2 old residue pipeline assertions from `nextGapCycleV2` |
| `SieveSequenceNextLevel.scala` | Added `import v1.cycle.integral.recursive.properties.CycleIntegralProperties` |
| `SieveSequenceNextLevel.scala` | Replaced `assert(current > 0)` with `assert(CycleIntegralProperties.assertCycleIntegralPositive(seq.integral, pos))` |
| `OBJECTS.md` | Created — comprehensive reference of objects, properties, and article links |
| `tickets/walk-based-pipeline.md` | Updated with results |

## Files NOT Modified

| File | Content |
|------|---------|
| `SieveSequenceNextLevel.scala` | `collectGapsV2`, `nextGapsWalkV2` (walk-based functions), `nextGapCycleV2` uses walk-based gaps |
| `GapCycle.scala` | Unchanged (no new lemmas added, they timed out) |
| `CycleSieveSequence.scala` | `@extern` still on `next()` |

---

## Related Tickets

- `gap-cycle-integration.md` — V2 skeleton (Complete, was 4285 valid)
- `gap-cycle.md` — GapCycle construction
- `r3-r5-r12-gaps-nonempty-positive.md` — SUPERSEDED (old pipeline positivity attempt)

---

## Open Questions

1. Did the original 4285-valid state have `@extern` on `next()` too? (Yes, per session summary)
2. What specific VC(s) cause the timeout? (Unknown — need per-VC timeout to identify)
3. Can we run Stainless with per-VC timeout? (Unknown, needs build expertise)
