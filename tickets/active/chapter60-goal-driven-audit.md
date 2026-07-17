# Chapter 60: Goal-Driven Lemma Audit & Assembly Layer Migration

**Created:** 2026-07-16
**Status:** Active

## START HERE

Three goals define the proof chain. Only copy what's needed to chapter60 —
leave chapter6 untouched. Architecture: stateless objects, one-direction.

### HANDOFF (2026-07-17, Cowork session -> CLI session)

The Cowork session that made the edits below has **no access to the
verification toolchain** (`just`, sbt/sdkman Java, Z3 via
`/opt/homebrew/Cellar/...`) — its sandbox is a separate Linux VM with the
repo mounted read/write but no macOS-specific build tools installed. It could
edit files but could not run `just verify` on any of them. The user
redirected: continue this ticket from the CLI session, which does have local
toolchain access.

**Status as of 2026-07-17 (CLI session):** Steps 1–4 complete.

- `assertSpecGapCycleGapsMatchSpec`: verified (4 VCs, all valid via Z3).
- `assertSpecGapCyclePeriodMatchesSpec`: written and verified. Ch60 now 4787
  valid, 0 invalid, 0 unknown.

**Next action:** Goal 3 revision step 2 — build `repeated(cycle, head)` and
prove `spec == repeated(cycle, head)` using `RepeatedGapIntegralProperties`
(`assertRepeatedPeriodIsMultiplied`, `assertRepeatedValuesIntegralMatches`).
See the side-by-side chain plan in the Goal 3 revision section below.

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

## Goal 2: Cycle reconstructs spec — COMPLETE (all lemmas verified 2026-07-17)

| Lemma | File | Status |
|-------|------|--------|
| `period` + `assertBlockShift` | PeriodProperties | Done |
| `gapList` + `specGapCycle` | PeriodProperties | Done |
| `assertSpecGapCycleIntegralMatchesApply` | PeriodProperties | Done |
| `assertMemCycleGapMatch` | PeriodProperties | Done |
| `assertSpecGapCycleGapsMatchSpec` | PeriodProperties | Done (verified 2026-07-17, 4 VCs valid) |
| `assertSpecGapCyclePeriodMatchesSpec` | PeriodProperties | Done (verified 2026-07-17, ch60: 4787 valid, 0 invalid, 0 unknown) |
| `assertApplyMatches` (wrapper) | **chapter6 only** | Thin wrapper, not needed |
| `assertCyclePeriod` (wrapper) | **chapter6 only** | Thin wrapper, not needed |

Draft for `assertSpecGapCyclePeriodMatchesSpec` (add to
`SpecSieveSeqPeriodProperties.scala` only after
`assertSpecGapCycleGapsMatchSpec` verifies green; one change at a time):

```scala
/**
 * The gap cycle built from the spec has exactly the spec's own period.
 */
def assertSpecGapCyclePeriodMatchesSpec(seq: SpecSieveSequence, period: BigInt): Boolean = {
  require(period > BigInt(0))
  require(seq.apply(period) == seq.head.value + seq.tailPrimorial)

  val gapCycle = specGapCycle(seq, period)
  assert(assertGapListSize(seq, BigInt(0), period))
  gapCycle.period == period
}.holds
```

Reasoning: `GapCycle.period == values.size` (see
`v1/chapter4/cycle/gap/GapCycle.scala:31`), `specGapCycle` builds its
`GapCycle` from `gapList(seq, 0, period)`, and `assertGapListSize` already
proves `gapList(seq, from, count).size == count`. Chaining these should be a
single trivial VC — but this is untested reasoning, not a verified fact,
until `just verify` actually runs it.

The core proof `assertSpecGapCycleIntegralMatchesApply(seq, period, k)`
already proves `cycleIntegral(k) == spec(k)` for all k >= 0. User (2026-07-17):
this pointwise-value equivalence implies same gaps and same period, but those
two facts must ALSO be proven as their own callable lemmas — they will be
depended on directly by later work (the Goal 3 side-by-side chain below), not
just implied. `assertSpecGapCycleGapsMatchSpec` and
`assertSpecGapCyclePeriodMatchesSpec` were added to make this explicit; both
were trivial (the gaps fact was already the `.ensuring` clause on
`specGapCycle`, the period fact follows directly from `assertGapListSize` +
`GapCycle.period == values.size`).

The chapter6 `SpecDerivedSieveSequence` / `SpecDerivedCoreProperties`
wrappers package the apply fact with a `CycleSieveSequence` object — they add
no new proof content beyond what's above. Goal 2 remains COMPLETE at the spec
level; no wrapper case class is needed for the apply/gaps/period facts
themselves.

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

## Goal 3 revision (2026-07-17): side-by-side transformation chain

User correction: the current `SpecSieveSeqNextStageProperties` assembly
derives the next stage by calling `seq.next` (spec's own linear-scan `next`),
then re-proving facts about `spec.next` from scratch. That is NOT what Goal 3
is supposed to establish. The actual goal, restated by the user:

1. For every spec seq, generate an integral-cycle seq that returns the same
   results, gaps, and period. **(Goal 2, done above.)**
2. For every spec seq, generate the NEXT integral-cycle seq **from the
   current integral-cycle seq itself** (not by re-deriving through
   `spec.next`'s linear scan) that replicates `spec.next`'s behavior.
3. The known hard sub-problem inside (2): proving the filter removes exactly
   the right number of elements. Already solved in chapter60 —
   `SpecSieveSeqSurvivorCountProperties.sameHeadSurvivorCount` proves
   `T' = T*(h-1)` via a value-range counting argument
   (`countAcceptedHeadNonMultiplesBetween`), NOT via the walk. This is the
   "better lemma" referenced below.

**Required proof shape — side by side, one step at a time, re-proving
equality after each step (not one big induction):**

1. `spec == cycle` (by definition / Goal 2's `assertSpecGapCycleIntegralMatchesApply`)
2. `spec == repeated(cycle, head)` — repeated-cycle properties
   (`v1.chapter4...RepeatedGapIntegralProperties`:
   `assertRepeatedPeriodIsMultiplied`, `assertRepeatedValuesIntegralMatches`
   — both already generic over any `CycleIntegral`, reusable as-is)
3. `filter(spec) == filter(repeated(cycle, head))` — same filter applied to
   equal sequences gives equal results
4. `gaps(filter(spec)) == gaps(filter(repeated(cycle, head)))` — by the gap
   definition
5. ... continue step by step until the full next cycle is built on both
   sides simultaneously, each step re-verified before the next.

**Mistake NOT to repeat (chapter6, documented in
`tickets/sieve-sequence-epic.md` §3 and §6):** three prior attempts to prove
`nextGapsWalk(cycle) == spec.next.gapList(...)` by reasoning *inside* the
opaque walk function (`SieveSequenceNextLevel.nextGapsWalk`) timed out and
were abandoned — this is explicitly flagged "Avoid" as a proof idiom, and
Leg 5 of the chapter6 epic ("Cycle == Canonical, using only Cycle's own
rules") is still listed as **Future**, no ticket, unsolved. The chapter6 walk
method must not be ported or re-attempted the same way. The winning pattern
elsewhere in this codebase is always "transfer through equivalence" /
position-based counting (as `sameHeadSurvivorCount` already does) — each step
above should follow that same shape: prove the step as its own small lemma
against already-verified facts, never by unfolding a recursive walk.

**Status:** Steps 1–5b done. Step 5c (full bijection) is the next hard unit of work.

| Step | Lemma | File | Status |
|------|-------|------|--------|
| 1 | `spec == cycle` (`assertSpecGapCycleIntegralMatchesApply`) | PeriodProperties | Done |
| 2a | `specRepeatedCycleIntegral` (constructor) | SpecDerivedRepeatedCycleProperties | Done (verified 2026-07-17) |
| 2b | `assertSpecRepeatedCyclePeriodIsHeadTimesPeriod` | SpecDerivedRepeatedCycleProperties | Done (verified 2026-07-17, ch60: 4823 valid) |
| 2c | `assertSpecRepeatedCycleIntegralMatchesBase` | SpecDerivedRepeatedCycleProperties | Done (verified 2026-07-17) |
| 3 | `assertSpecBaseAndRepeatedSurvivorValuesMatch` (filter equality) | SpecDerivedRepeatedCycleProperties | Done (verified 2026-07-17) |
| 4 | `assertSpecBaseAndRepeatedGapListMatch` (gap list equality) | SpecDerivedRepeatedCycleProperties | Done (verified 2026-07-17, ch60: 4896 valid) |
| 5a | `assertBaseCIEqualsSeqApplyShifted` (baseCI(k) == seq.apply(k+1)) | SpecDerivedRepeatedCycleProperties | Done (verified 2026-07-17, ch60: 4955 valid) |
| 5b | `assertFirstSurvivorMatchesNextSeqHead` (survivors.head == nextSeq.apply(0)) | SpecDerivedRepeatedCycleProperties | Done (verified 2026-07-17) |
| 5c | `survivors(i) == nextSeq.apply(i)` (full bijection) | SpecDerivedRepeatedCycleProperties | **Open** — requires helpers below |
| 6 | `gapsFromValues(survivors) == nextSeq.gapList(0, nextPeriod)` | TBD | Not started |
| 7 | `newCI = CycleIntegral(survivors.head, MemCycle(gapsFromValues(survivors)))` matches `nextSeq` | TBD | Not started |

**Step 5c requires these helpers (in order):**
1. `assertAcceptedByNextGivenStructure(seq, nextSeq, v)`: `seq.accepts(v) ∧ v % head ≠ 0 ∧ v ≥ nextSeq.head.value → nextSeq.accepts(v)` — from structural requires alone (no `seq.next` needed)
2. `assertSurvivorIsSeqApply(seq, period, ciPos)`: `survivorValues(baseCI, head, 0, count)` values are exactly the seq.apply-shifted non-head-multiples, i.e., the intermediate CI positions between consecutive survivors all have head-multiple values
3. The double-inequality proof for the inductive step:
   - Lower bound: `survivors(i+1) ≤ nextSeq.apply(i+1)` — by minimality of survivors (scans in order)
   - Upper bound: `nextSeq.apply(i+1) ≤ survivors(i+1)` — by `assertNoAcceptedValueBetweenGeneratedValues` on nextSeq (if `nextSeq.apply(i+1) < survivors(i+1)` then nextSeq accepted a value between its own consecutive generated values, contradiction)

Key tool for helper 1: `CoprimeUtils.isCoprime(v, head :: filterValues) = v % head ≠ 0 ∧ isCoprime(v, filterValues)` — this decomposition should exist in chapter2/chapter5.

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
| 2026-07-17 | User corrected Goal 3 framing. | Current assembly re-derives through `seq.next` (linear scan) instead of building the next cycle from the current cycle's own data. Goal 2's apply-equivalence should also yield standalone gaps/period lemmas, not just be implied. Recorded the side-by-side transformation-chain plan (spec == cycle == repeated(cycle,head) == filter(...) == gaps(filter(...)) == ...) and the explicit instruction not to repeat chapter6's opaque-walk mistake (3 timeouts, `nextGapsWalk`, Leg 5 still Future/no ticket in `sieve-sequence-epic.md`). |
| 2026-07-17 | Cowork session: toolchain blocker. | Added `assertSpecGapCycleGapsMatchSpec` to `SpecSieveSeqPeriodProperties.scala` but could not verify — Cowork's Linux sandbox lacks `just`/sbt/sdkman-Java/Z3 (justfile is macOS/homebrew-specific: `/opt/homebrew/Cellar/z3/...`, `DYLD_LIBRARY_PATH`). User confirmed the CLI Claude session has toolchain access and should take over from here. See HANDOFF block at top of ticket for exact next steps. Do NOT trust the "Done" status on unverified lemmas above — verify first. |
| 2026-07-17 | CLI session: Goal 2 fully verified. | Ran `just verify` (all green, 20411 valid) confirming `assertSpecGapCycleGapsMatchSpec`. Added `assertSpecGapCyclePeriodMatchesSpec` using `assertSpecGapCycleGapsMatchSpec` + `GapCycle.assertMemCycleValuesPositive` + `assertGapListSize` to chain `gapCycle.memCycle.values == gapList(seq,0,period)` → `gapCycle.values.list.size == period` → `gapCycle.period == period`. Both lemmas verified. Ch60: 4787 valid, 0 invalid, 0 unknown (was 4770). Next: Goal 3 step 2 — `repeated(cycle, head)` via `RepeatedGapIntegralProperties`. |
| 2026-07-17 | Goal 3 step 2: repeated-cycle period lemma. | Created `SpecDerivedRepeatedCycleProperties` (no chapter6 imports, stateless, one-direction). `specRepeatedCycleIntegral` constructs `CycleIntegral(head, MemCycle(repeat(gapCycle.memCycle.values, head)))` and exports `cycle.values == repeat(...)` in ensuring clause. `assertSpecRepeatedCyclePeriodIsHeadTimesPeriod` proves `repeatedCI.period == period * head` using `assertGapListSize` + `assertRepeatSize` before any filter step — this anchors the filter-window size for `sameHeadSurvivorCount`. Ch60: 4823 valid, 0 invalid, 0 unknown (was 4787, +36 new VCs). |
| 2026-07-17 | Goal 3 steps 2c–5b complete. | Added to `SpecDerivedRepeatedCycleProperties`: (2c) `assertSpecRepeatedCycleIntegralMatchesBase` — repeated CI and base CI agree pointwise via `assertRepeatedValuesIntegralMatches`; (3) `assertSpecBaseAndRepeatedSurvivorValuesMatch` — inductive equality of survivor lists; (4) `assertSpecBaseAndRepeatedGapListMatch` — trivial corollary of step 3; (5a) `assertBaseCIEqualsSeqApplyShifted` — baseCI(k) = seq.apply(k+1), direct from `assertSpecGapCycleIntegralMatchesApply`; (5b) `assertFirstSurvivorMatchesNextSeqHead` — first survivor = nextSeq.head.value, using `assertApplyOneEqualsNextPrime` + `assertPrimeNotDivisibleByDistinctPrime` from ch5. Ch60: 4955 valid, 0 invalid, 0 unknown (was 4823). Step 5c (full bijection `survivors(i) == nextSeq.apply(i)`) is now the blocking hard step — requires `assertAcceptedByNextGivenStructure` + "minimality of survivors" helper + double-inequality argument via `assertNoAcceptedValueBetweenGeneratedValues`. |
