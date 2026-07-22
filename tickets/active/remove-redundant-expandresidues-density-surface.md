# Remove Redundant expandResidues Density Proof Surface

**Created:** 2026-07-14
**Status:** In progress
**Depends on:** `spec-same-head-filter-density-proof-review.md` (the verified transpose-based size proof)

## Goal

Remove the `expandResidues`/`filterList` density proof surface from `SieveUtils` and `SieveSequenceNextLevel` that is now superseded by the `SpecSieveSequence` transpose-based same-head size proof (`assertSameHeadExtendedFilterCount`).

## Current State

Two parallel verified proof surfaces exist for the same property:

1. **`SpecSieveSequence` (transpose-based)** — proves `countAcceptedHeadNonMultiplesBetween(h, h + h*M) == p * (h-1)` via row-major/column-major transpose over generated indices. Verified at HEAD (`14463 valid`).

2. **`SieveUtils` + `SieveSequenceNextLevel` (expandResidues-based)** — proves `nextFiltered.size == residues.size * (h - 1)` via block-major expansion counting and `filterList`. Verified earlier but never consumed by the current spec-local proof.

Only surface (1) holds the codebase together going forward. Surface (2) is isolated and duplicates the proof.

## Functions to Keep (used by SpecSieveSequence size proof)

| Function | Location | Used by |
|----------|----------|---------|
| `countZeroOffsets` | SieveUtils:290 | `assertGeneratedHeadMultiplesStrideMatchesZeroOffsets` (SpecSieveSequence:1214) |
| `assertCountZeroOffsetsOne` | SieveUtils:407 | `assertGeneratedHeadMultiplesStrideOne` (SpecSieveSequence:1243) |
| `assertCountZeroOffsetsFromWitness` | SieveUtils:348 | Internal dependency of `assertCountZeroOffsetsOne` |

## Functions to Remove

### From SieveUtils.scala

| Function | Line |
|----------|------|
| `countMultiples` | 272 |
| `countOffsetHits` | 310 |
| `countExpandedOffsetHits` | 330 |
| `assertCountZeroOffsetsFromWitness` | KEPT |
| `assertCountZeroOffsetsOne` | KEPT |
| `assertCountMultiplesExpandSingleton` | 423 |
| `assertCountMultiplesExpandSingletonOne` | 454 |
| `assertCountMultiplesAddOffset` | 468 |
| `assertCountMultiplesExpandByOffsetHits` | 502 |
| `assertCountExpandedOffsetHitsCons` | 537 |
| `assertCountExpandedOffsetHitsOnePerResidue` | 586 |
| `assertCountMultiplesExpandOnePerResidue` | 616 |
| `assertFilterExpandSingleResidueSizeByDensity` | 635 |
| `assertFilterExpandResiduesSizeByDensity` | 658 |
| `assertFilterListSizeByCount` | 673 |
| `assertCountMultiplesAppend` | 700 |

### From SieveSequenceNextLevel.scala

| Function | Line |
|----------|------|
| `assertNextFilteredSizeByDensity` | 257 |
| `assertNextFilteredSizeGreaterThanResiduesByDensity` | 272 |

## Dependencies

- None of the removed functions are called by the kept functions (`countZeroOffsets` is standalone; `assertCountZeroOffsetsOne` only calls `assertCountZeroOffsetsFromWitness`)
- None of the removed functions are called by tests
- `BezoutUtils.coprimeStepZeroOffset` and `BezoutUtils.assertCoprimeStepAtMostOneZero` are called by kept functions — must NOT be removed

## Validation

1. Baseline verify: `grep "total:" logs/verify.log` — 14463 valid, 0 invalid, 0 unknown
2. Remove SieveUtils functions, re-verify
3. Remove SieveSequenceNextLevel functions, re-verify
4. Update OBJECTS.md
