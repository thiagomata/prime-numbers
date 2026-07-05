# Lean ch6 — Trim to the A = B = C Proof Spine

**Created:** 2026-07-05
**Updated:** 2026-07-05
**Status:** **Complete.** SDSS trimmed from ~1800 to ~380 lines. 50 methods removed from SDSS. SDBS trimmed from 472 to 132 lines (17 methods removed). Both files verified green at 11426/11426.
**Next:** Update architecture.md and epic.

---

## Goal

Clean up chapter 6 by removing or consolidating methods that are not part of the A = B = C proof spine, and replacing duplicated or redundant lemmas with existing lower-chapter proofs. Target: remove unnecessary verification burden without breaking the top-level equivalence theorem.

## Background

The three representations (Spec, Canonical, Cycle) were proven equivalent for both current and next stages: `assertSpecCanonicalCycleNextMatch(nextPeriod)` (29/29 VCs, verified). The proof chain reaches through exactly **15 methods** across `SpecDerivedSieveSequence` and `SpecDerivedBySurvivors`. The remaining **64 methods** in these files are not needed by the spine — they support a different proof strategy (expansion bridge / survivor scan) that is not called from the top-level theorem.

## A = B = C Spine (15 methods — KEEP)

### SpecDerivedBySurvivors (SDBS) — 6 methods

| # | Method | Line | Proves |
|---|--------|------|--------|
| 1 | `assertSpecCanonicalCycleNextMatch(nP)` | 477 | Top: A = B = C for next stage |
| 2 | `assertCanonicalGapsEqSpecNextGapList(nP)` | 426 | A = B at gap level |
| 3 | `assertCycleNextEqSpecNext(nP)` | 450 | B = C |
| 4 | `assertSpecNextFilterEqCyclePrimes()` | 22 | Filter identity |
| 5 | `assertNextHeadResidueIsSpecNextHead()` | 304 | Rotation anchor |
| 6 | `assertHeadModulusEqualsSpecNextFilterModulus()` | 330 | Modulus identity |

### SpecDerivedSieveSequence (SDSS) — 9 methods

| # | Method | Line | Proves |
|---|--------|------|--------|
| 7 | `assertApplyMatches(k)` | 71 | core: cycle(k) == spec(k) |
| 8 | `assertNextHeadMatches()` | 91 | Head matching |
| 9 | `assertPrimesMatch()` | 104 | Prime list equality |
| 10 | `primorialMatchesProduct(primeList)` | 134 | Primorial-product bridge |
| 11 | `assertCycleModulusEqualsSpecFilterModulus()` | 145 | Modulus equality |
| 12 | `assertNextHeadLessThanNewModulus()` | 1783 | Bound for rotation anchor |
| 13 | `assertNextCycleGapsMatchSpecNext(nP)` | 1287 | Canonical gaps = gapList |
| 14 | `assertNextGapCycleValuesEqualSpecNextGapList(nP)` | 1232 | Gap values equality |
| 15 | `assertNextCycleApplyMatchesSpecNext(nP, k)` | 1247 | Apply match |

## Candidates for Removal (64 methods NOT in spine)

### SDBS — 17 methods

All are part of the expansion bridge / survivor scan. Not called from the spine.

| Method | Line | Status |
|--------|------|--------|
| `assertCycleSurvivorCoprimeToCyclePrimes(pos)` | 13 | Unused by spine |
| `assertCycleSurvivorCoprimeToSpecNextFilter(pos)` | 28 | Unused |
| `assertCycleSurvivorPassesSpecNextFilter(pos)` | 37 | Unused |
| `assertFirstSurvivorEqualsSpecNextHead()` | 45 | Unused |
| `assertAllSurvivorsPassSpecNextFilter(count)` | 50 | Unused |
| `assertAllSurvivorsPassSpecNextFilterFrom(from, count)` | 65 | Unused |
| `assertIntegralIncreasingForCount(count)` | 80 | Unused |
| `assertIntegralGeIntegral0(pos)` | 94 | Unused |
| `assertSurvivorAcceptedBySpecNext(pos)` | 109 | Unused |
| `assertNextHeadLessThanNewModulus()` | 119 | **Duplicate** of SDSS:1783 — not called from spine |
| `assertMinimalCycleSurvivorPassSpecNextFilter(pos)` | 131 | **Stub** — duplicates 37 |
| `assertCycleModulusEqualsProductTail()` | 154 | Unused |
| `assertCycleSurvivorModModulusCoprimeToTail(pos)` | 169 | Unused |
| `assertHeadModulusEqualsProductAllPrimes()` | 198 | Unused |
| `assertCycleSurvivorAppearsInNextFiltered(pos)` | 229 | Unused |
| `assertCycleSurvivorAppearsInNextSorted(pos)` | 264 | Unused |
| `assertSpecNextReducedAppearsInNextSorted(nP, k)` | 355 | Unused |

### SDSS — 47 methods

| Method | Line | Status |
|--------|------|--------|
| `assertCycleHeadMatchesSpecHead()` | 113 | Unused |
| `assertCyclePrimesTailEqualsSpecFilterValues()` | 119 | Unused |
| `assertNextPipelineGapsIsNextRotatedGaps()` | 151 | Unused |
| `assertCycleGapCycleEqualsSpecGapCycle()` | 160 | Unused |
| `assertCycleSpecNextFilterDecisionMatches(k)` | 175 | Unused |
| `assertCycleApplyLowersToIntegral(k)` | 191 | Unused |
| `assertCycleGapListNonEmpty()` | 197 | Unused |
| `assertNextPrimesHeadMatchesCycleApplyOne()` | 202 | Unused |
| `assertCycleApplyUpperBound(k)` | 210 | Unused |
| `assertCycleIndexOf(value)` | 217 | Unused |
| `expandedCoprime(...)` (private) | 227 | Unused |
| `assertNewHeadPlusModulusCoprime()` | 258 | Unused |
| `assertHeadPlusFilterModulusNotFrontMultiple()` | 287 | Unused |
| `assertCycleValueCoprimeToTail(k)` | 311 | Unused |
| `assertNewHeadCoprimeToAllPrimes()` | 322 | Unused |
| `assertCyclePositionMatchesSpec(k)` | 339 | Unused |
| `assertFirstSurvivorEqualsSpecNext0()` | 351 | Unused |
| `assertCycleSurvivorValuesStartAtSpecNextHead(count)` | 374 | Unused |
| `assertCycleIntegralSkippedRangeAllMultiples(...)` | 419 | Unused |
| `assertCycleSurvivorValuesSplitAtNextAccepted(...)` | 494 | Unused |
| `assertCycleNextAcceptedSurvivorMatchesSpecNext(...)` | 557 | Unused |
| `assertSurvivorGapEqualsSpecNextGap(nP, k)` | 1170 | Unused |
| `assertSpecNextIsKthSurvivor(nP, k)` | 1189 | Unused |
| `assertFullEquivalence(nP, k)` | 1211 | Unused |
| `assertNextCycleHeadMatchesSpecNext(nP)` | 1268 | Unused |
| `assertNextCycleGapsPositive(nP)` | 1314 | Unused |
| `nextGapList(from, count)` | 1341 | Unused |
| `assertNextGapListMatchesSpecNext(from, count)` | 1362 | Unused |
| `assertNextCycleMatchesSpecNext(nP)` | 1385 | Unused |
| `assertCurrentAndCanonicalNextApplyMatches(nP, k)` | 1408 | Unused |
| `assertModulusPositive()` | 1430 | Unused |
| `assertPrimesTailValuesPositive()` | 1443 | Unused |
| `assertHeadPositive()` | 1451 | Unused |
| `assertModulusTimesHeadPositive()` | 1462 | Unused |
| `nextPipelineGaps()` | 1476 | Unused |
| `assertNextPipelineGapsPositiveFromSpec(nP)` | 1493 | Unused |
| `nextPipelineGapCycleIfMatchesSpec(nP)` | 1510 | Unused |
| `repeatedCycle(times)` | 1545 | Unused |
| `assertRepeatedGapListIndexMatches(times, index)` | 1580 | Unused |
| `assertRepeatedCycleGapMatches(times, position)` | 1620 | Unused |
| `assertRepeatedCycleIntegralMatches(times, position)` | 1666 | Unused |
| `assertRepeatedCycleApplyMatches(times, k)` | 1719 | Unused |
| `nextFromCycle()` | 1759 | Unused |
| `nextVerified(nP)` | 1775 | Unused |
| `assertNextHeadLessThanHeadSquared()` | 1794 | Unused |

## Duplicates to Consolidate

| SDBS method | Duplicates | Proposed action |
|-------------|-----------|----------------|
| `assertNextHeadLessThanNewModulus()` (line 119) | SDSS:1783 (identical proof) | Remove SDBS copy |
| `assertMinimalCycleSurvivorPassSpecNextFilter(pos)` (line 131) | `assertCycleSurvivorPassesSpecNextFilter(pos)` (SDBS:37) | Remove stub |

## Lower-Chapter Replacement Opportunities

| SDSS/SDBS method | Could be replaced by | Benefit |
|-----------------|---------------------|---------|
| `assertRepeatedCycleApplyMatches(times, k)` (SDSS) | `CycleIntegralFilterProperties.assertReplicatedCycleValueEqual` (ch4) | Removes redundant induction |
| `assertSurvivorGapEqualsSpecNextGap(nP, k)` (SDSS) | `CycleIntegralFilterProperties.assertGapsFromSurvivorsMatchCI` (ch4) | Same proof, reuses ch4 |
| Pipeline positivity batch (SDSS:1430-1462) | `ListBoundUtils.allGreaterThan` (ch3) | General positivity, not ch6-specific |

## Execution Plan

### Phase 1 — Safe removals (no downstream callers)

Remove methods that are never called from within the file or from any other ch6 file:

1. Remove the stub `assertMinimalCycleSurvivorPassSpecNextFilter(pos)` (SDBS:131)
2. Remove `assertNextHeadLessThanNewModulus()` (SDBS:119) — keep SDSS:1783
3. Remove all 17 unused SDBS methods
4. Remove all 47 unused SDSS methods

**Risk:** Low — these are verified independently but never called. Removal won't break the A=B=C spine.
**Verify:** After each small batch, `just verify` to ensure green.

### Phase 2 — Replacement (optional)

Replace SDSS/SDBS methods with existing lower-chapter equivalents:

1. Replace `assertRepeatedCycleApplyMatches` with `assertReplicatedCycleValueEqual` from ch4
2. Replace pipeline positivity batch with `ListBoundUtils` calls
3. Verify that A=B=C spine still passes

### Phase 3 — Docs update

1. Update OBJECTS.md with reduced lemma counts for ch6
2. Update architecture.md to reflect leaner class
3. Archive the removed methods documentation in case they need to be resurrected

---

## Related Tickets

- `active/spec-derived-by-survivors.md` — original M3 proof ticket
- `sieve-sequence-epic.md` — epic overview

---

## Progress Log

### 2026-07-05 — SDBS fully trimmed (dedup + unreached methods)

Removed 17 methods from `SpecDerivedBySurvivors`:
- 2 duplicates: `assertMinimalCycleSurvivorPassSpecNextFilter`, `assertNextHeadLessThanNewModulus()`
- 15 unreached expansion bridge methods: all survivor coprimality chain, integral monotonicity, expansion bridge membership (both directions), survivor-to-accepts bridge, modulus-product bridge

Cleaned up unused imports (`decreases`, `GapCycle`, `CycleIntegralProperties`).

**Result:** 12152 valid, 0 invalid, 0 unknown. File reduced from 475 lines to 175 lines. Spine at 29/29 VCs (all cached).
**Next:** SDSS Phase 1 (47 unreached methods) or lower-chapter replacements.
