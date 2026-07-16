# Chapter 60: Goal-Driven Lemma Audit & Assembly Layer Migration

**Created:** 2026-07-16
**Status:** Active

## START HERE

Three goals define the proof chain. Only copy what's needed to chapter60 —
leave chapter6 untouched. Architecture: stateless objects, one-direction.

## Goals

1. **Spec generates primes** — the linear sieve sequence is a valid prime generator
2. **Cycle reconstructs spec** — an integral cycle has the same gaps, period, and apply as each spec
3. **Next cycle matches next spec** — a new integral cycle has the same gaps, period, and apply as the next spec

## Goal 1: Spec generates primes — COMPLETE

| Lemma | File | Status |
|-------|------|--------|
| `apply(k)` emits values accepted by filters | SpecSieveSequence | Done |
| `applyStrictlyIncreases` (monotonicity) | SpecSieveSequence | Done |
| `indexOfAccepted` (completeness) | SpecSieveSequence | Done |
| `assertApplyOneEqualsNextPrime` | HeadIsPrime | Done |
| `assertApplyOneIsPrimeIfBelowHeadSq` | HeadIsPrime | Done |

No gaps.

## Goal 2: Cycle reconstructs spec — COMPLETE

| Lemma | File | Status |
|-------|------|--------|
| `period` + `assertBlockShift` | PeriodProperties | Done |
| `gapList` + `specGapCycle` | PeriodProperties | Done |
| `assertSpecGapCycleIntegralMatchesApply` | PeriodProperties | Done |
| `assertMemCycleGapMatch` | PeriodProperties | Done |
| `assertApplyMatches` (wrapper) | **chapter6 only** | Thin wrapper, not needed |
| `assertCyclePeriod` (wrapper) | **chapter6 only** | Thin wrapper, not needed |

The core proof `assertSpecGapCycleIntegralMatchesApply(seq, period, k)`
already proves `cycleIntegral(k) == spec(k)` for all k >= 0. The chapter6
`SpecDerivedSieveSequence` / `SpecDerivedCoreProperties` wrappers package
this same fact with a `CycleSieveSequence` object — they add no new proof
content. Goal 2 is COMPLETE at the spec level.

If a derived wrapper is ever needed, it should be written fresh:
- `SpecDerivedSieveSequence` = case class (data model only, no calls out)
- `SpecDerivedCoreProperties` = stateless object (all lemmas, `derived` as param)
- Architecture: one-direction, no circular dependency

## Goal 3: Next cycle matches next spec — ASSEMBLY WRITTEN, PERIOD BOUNDARY ASSUMED

| Lemma | File | Status |
|-------|------|--------|
| `assertNextValueAcceptedByThis` | NextProperties | Done |
| `assertSurvivorAcceptedByNext` | NextProperties | Done |
| `mergedGapPrefix` + `assertMergedGapPrefixMatchesNext` | NextProperties | Done |
| `nextAcceptedOldIndex` + skip characterization | NextProperties | Done |
| `sameHeadSurvivorCount` (T' = T*(h-1)) | SurvivorCountProperties | Done |
| `assertSkippedBeforeNextAcceptedOldIndexIsMultiple` | NextProperties | Done |
| `assertFilterPreservesNextGap` | NextProperties | Done |
| `assertConsecutiveAcceptedByNextPreservesGap` | NextProperties | Done |
| `assertNextCycleReconstructsNextSpec` | NextStageProperties | Done |
| `assertNextGapListHasCorrectSize` | NextStageProperties | Done |
| `assertNextCycleIntegralBase` | NextStageProperties | Done |
| `assertPipelineOutputMatchesNextGapList` | NextStageProperties | Done |
| Period boundary for spec.next | **Assumed** | **Open** |

The assembly is written and verified. The remaining open item is proving
`spec.next.apply(nextPeriod) == spec.next.head.value + spec.next.tailPrimorial`
from the current stage's facts alone — this is the "packaging boundary"
acknowledged in the article (§7). It is supplied as a precondition today.

## Noise in chapter60 (not needed for the 3 goals)

These lemmas exist in chapter60 but are NOT on the critical path.
Do NOT remove from chapter6 — just consider not bringing them if
chapter60 is ever restructured.

**PeriodProperties:**
- `assertApplyModIsCoprime`, `assertApplyResidueCycles`
- `assertGapPeriodic`, `assertGapSum`, `assertApplyEqualsHeadPlusGapSum`
- `assertSpecGapPeriodPositive`
- `assertGapListFirstEqualsGap`, `assertGapListApplyEqualsGapAtPosition`

**NextProperties:**
- `assertSingletonFilterDecision`
- `assertOldAcceptedHeadNonMultipleAcceptedByNext`
- `assertOldAcceptedRejectedByNextIsHeadMultiple`
- `assertOldGeneratedValueBetweenNextValuesIsHeadMultiple`

**SurvivorCountProperties:**
- Fine-grained stride/range matching helpers

**SpecSieveSequence:**
- `assertApplyMonotonic`, `assertApplyStrictlyIncreasesBetween`
- `valueBoundImpliesIndexBound`, `assertIndexOfAcceptedAtMost`
- `assertIndexOfAcceptedStrictlyIncreasesForAcceptedValues`

## Key insight: chapter4 has newer properties chapter6 wasn't using

`RepeatedGapIntegralProperties` (ch4) provides:
- `assertRepeatedPeriodIsMultiplied` — repeated period = original * times
- `assertRepeatedValuesIntegralMatches` — integral invariance
- `assertReplicatedCycleValueEqual` — cycle value equality

Chapter 6 hand-rolls assertions instead of using these. Fresh writes
should use the newer chapter4 properties.

## Learning Log

| Date | Progress | Notes |
|------|----------|-------|
| 2026-07-16 | Ticket created. | Goal 1 done. Goal 2-3 analysis. |
| 2026-07-16 | Goal 2 marked COMPLETE. | `assertSpecGapCycleIntegralMatchesApply` already proves cycle = spec. Wrapper in ch6 is thin packaging only. |
| 2026-07-16 | Goal 3 assembly written. | `SpecSieveSeqNextStageProperties` with 6 functions, all verified. Pipeline requires explicit nextSeq param to avoid Stainless unfolding seq.next. 4770 valid, 0 invalid, 0 unknown. |
| 2026-07-16 | Period boundary is the last open item. | `spec.next.apply(nextPeriod) == spec.next.head.value + spec.next.tailPrimorial` is assumed, not derived. Article §7 acknowledges this. |
