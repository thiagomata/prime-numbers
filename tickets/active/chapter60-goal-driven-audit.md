# Chapter 60: Goal-Driven Lemma Audit & Assembly Layer Migration

**Created:** 2026-07-16
**Status:** Active

## START HERE

Three goals define the proof chain. Only copy what's needed to chapter6 —
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
   the right number of elements. Already solved in chapter6 —
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

**Status:** Steps 1–8 done. Step 9 (survivor gaps bridge) is the next unit of work.

| Step | Lemma | File | Status |
|------|-------|------|--------|
| 1 | `spec == cycle` (`assertSpecGapCycleIntegralMatchesApply`) | PeriodProperties | Done |
| 2 | `specRepeatedCycleIntegral` (constructor) | SpecDerivedRepeatedCycleProperties | Done (verified 2026-07-17) |
| 3 | `assertSpecRepeatedCyclePeriodIsHeadTimesPeriod` | SpecDerivedRepeatedCycleProperties | Done (verified 2026-07-17, ch60: 4823 valid) |
| 4 | `assertSpecRepeatedCycleIntegralMatchesBase` | SpecDerivedRepeatedCycleProperties | Done (verified 2026-07-17) |
| 5 | `assertSpecBaseAndRepeatedSurvivorValuesMatch` (filter equality) | SpecDerivedRepeatedCycleProperties | Done (verified 2026-07-17) |
| 6 | `assertSpecBaseAndRepeatedGapListMatch` (gap list equality) | SpecDerivedRepeatedCycleProperties | Done (verified 2026-07-17, ch60: 4896 valid) |
| 7 | `assertBaseCIEqualsSeqApplyShifted` (baseCI(k) == seq.apply(k+1)) | SpecDerivedRepeatedCycleProperties | Done (verified 2026-07-17, ch60: 4955 valid) |
| 8 | `assertFirstSurvivorMatchesNextSeqHead` (survivors.head == nextSeq.apply(0)) | SpecDerivedRepeatedCycleProperties | Done (verified 2026-07-17) |
| 9 | `assertSurvivorGapsEqualsMergedGapPrefix` | SpecDerivedRepeatedCycleProperties | **Open — to write** |
| 10 | `gapsFromValues(survivors) == nextSeq.gapList(0, nextPeriod)` | SpecDerivedRepeatedCycleProperties | Not started (follows from Step 9 + existing pipeline) |
| 11 | `newCI = CycleIntegral(survivors.head, MemCycle(gapsFromValues(survivors)))` matches `nextSeq` | SpecDerivedRepeatedCycleProperties | Not started (follows from Steps 8 + 10 + Goal 2) |

**Abandoned approach for Step 9 — indexed bijection via mutual induction:**
A direct proof of `survivors(i) == nextSeq.apply(i)` was attempted (2026-07-18) but always times out.
The helpers it would have needed:
1. `assertAcceptedByNextGivenStructure(seq, nextSeq, v)`: `seq.accepts(v) ∧ v % head ≠ 0 ∧ v ≥ nextSeq.head.value → nextSeq.accepts(v)`
2. `assertSurvivorIsSeqApply(seq, period, ciPos)`: the intermediate CI positions between consecutive survivors all have head-multiple values
3. A double-inequality inductive step (lower bound from minimality; upper bound from `assertNoAcceptedValueBetweenGeneratedValues`)

Do NOT attempt this approach. The EUF mismatch causes the postcondition VC to time out at 300s regardless of how the helpers are structured. Use Step 9's gap-equality bridge instead.

## Goal 3 revision (2026-07-19): Chapter 6 bridge approach — PREFERRED PLAN

**Context:** The indexed bijection approach via backward mutual induction (written 2026-07-18) times out at the
postcondition VC for `assertSurvivorAtIndexMatchesNextSeqApply` (line 940, class-level run:
847/856 valid, 9 unknown — 1 new at :940, 8 pre-existing borderline VCs). The user's question
"what's the problem with copying chapter 6's strategy?" revealed a better path.

**Key discovery:** Chapter 60 already has the chapter 6 pipeline in `SpecSieveSeqNextProperties`:
- `mergedGapPrefix(seq, nextSeq, k, remaining, period)` — walks seq's apply values, merges
  consecutive gaps where intermediate values are rejected by nextSeq (= head-multiples)
- `assertMergedGapPrefixMatchesNext(...)` — proves `mergedGapPrefix == gapList(nextSeq, seqIndex, remaining)`
- `assertPipelineOutputMatchesNextGapList(...)` — wraps the above: merged gap prefix from
  walking seq equals `nextSeq.gapList(0, nextPeriod)` (DONE, verified 2026-07-16)

**What chapter 6 actually does vs. what the abandoned indexed bijection was doing:**
- Chapter 6 proves `nextCycle.apply(k) == spec.next(k)` by CONSTRUCTION: nextCycle IS built from
  `spec.next.gapList`, so they trivially share the same CycleIntegral. No indexed bijection needed.
- The abandoned approach was trying to prove `survivors(i) == nextSeq.apply(i)` by mutual induction —
  harder because survivors come from CI filtering, not from construction.
- Chapter 6's REAL contribution for this step is `mergedGapPrefix` + `assertMergedGapPrefixMatchesNext`,
  which proves gap equality without any indexed bijection.

**Current step table (Steps 1–8 done, Steps 9–11 open):**

See the step table above. Steps 1–8 are all verified. Step 9 is the key new lemma:

**Step 9 — `assertSurvivorGapsEqualsMergedGapPrefix`:**

```scala
def assertSurvivorGapsEqualsMergedGapPrefix(
  seq: SpecSieveSequence,
  nextSeq: SpecSieveSequence,
  period: BigInt,
  nextPeriod: BigInt
): Boolean = {
  // requires: standard preconditions
  val gapCycle  = specGapCycle(seq, period)
  val baseCI    = CycleIntegral(seq.head.value, gapCycle.memCycle)
  val count     = period * seq.head.value
  val survivors = survivorValues(baseCI, seq.head.value, BigInt(0), count)
  gapsFromValues(survivors) == mergedGapPrefix(seq, nextSeq, BigInt(1), nextPeriod, period)
}.holds
```

NOTE: walk starts at `k=1` not `k=0`. `seq.apply(0) = seq.head.value` is rejected by `nextSeq`
because `nextSeq.filterValues.head == seq.head.value` — it is a multiple of itself.
`seq.apply(1) = nextSeq.head.value = nextSeq.apply(0)` is the correct starting point.

**SIZE NOTE:** `gapsFromValues(n-element list)` has `n-1` elements. `survivors` has `nextPeriod`
elements, so `gapsFromValues(survivors)` has `nextPeriod - 1` elements. But `gapList(nextSeq, 0,
nextPeriod)` has `nextPeriod` elements. Therefore the bridge uses `remaining = nextPeriod - 1`:
```
gapsFromValues(survivors) == mergedGapPrefix(seq, nextSeq, BigInt(1), nextPeriod - BigInt(1), period)
```
The final gap (from `survivors.last` to `nextSeq(nextPeriod)`) is the "wraparound" gap proved
separately as `nextSeq(nextPeriod) - nextSeq(nextPeriod - 1)`.

**Proof shape:** induction on `nextPeriod - 1` (number of survivor gaps):
- Each survivor `survivors(i)` = `baseCI(pos_i)` = `seq.apply(pos_i + 1)` (Step 7, 0-indexed base CI).
- The old-seq index for survivor i is `pos_i + 1` (1-indexed in seq, since baseCI(k) = seq.apply(k+1)).
- `mergedGapPrefix` walks from old index `pos_i + 1` to the next nextSeq-accepted old index.
- `gapsFromValues(survivors)(i)` = `survivors(i+1) - survivors(i)` = sum of seq gaps between consecutive survivors.
- The two computations are equal by Step 7 + definition of `sumGap`.

**Step 10:** Once `assertSurvivorGapsEqualsMergedGapPrefix` (Step 9) is proved:
```
gapsFromValues(survivors)
  == mergedGapPrefix(seq, nextSeq, 1, nextPeriod - 1, period)      [Step 9]
  == gapList(nextSeq, 0, nextPeriod - 1)                           [assertMergedGapPrefixMatchesNext]
```
Combined with the final wraparound gap lemma → full `gapList(nextSeq, 0, nextPeriod)` equality.

**Step 11:** Build `newCI = CycleIntegral(survivors.head, MemCycle(nextSeq.specGapCycle(nextPeriod).memCycle))`:
- `newCI.initialValue == nextSeq.head.value` — from Step 8.
- `newCI.memCycle.values == nextSeq.specGapCycle(nextPeriod).memCycle.values` — from Step 10 +
  `assertSpecGapCycleGapsMatchSpec(nextSeq, nextPeriod)` (Goal 2, already done for current seq;
  apply the SAME lemma to nextSeq).
- `newCI.apply(k) == nextSeq.apply(k+1)` — from `assertSpecGapCycleIntegralMatchesApply(nextSeq, nextPeriod, k+1)`.

**Indexed bijection code deleted (2026-07-20):** All mutual-induction code permanently removed
from `SpecDerivedRepeatedCycleProperties.scala`. File now contains only Steps 1–8 (verified).
Do NOT re-add any indexed bijection mutual-induction code — it always times out and distracts from the
Step 9 bridge approach.

**Precondition fix (2026-07-20):** `mergedGapPrefix` and its 20+ helpers previously required
`nextSeq.head.value == seq.head.value` — IMPOSSIBLE for `seq.next`. Fixed globally to
`seq.head.value <= nextSeq.head.value`. `assertPipelineOutputMatchesNextGapList` now starts
walk at `k=1`, passes `nextSeq(0) == seq.apply(1)` as explicit precondition.

## Noise in chapter6 (not needed for the 3 goals)

These lemmas exist in chapter6 but are NOT on the critical path.
Do NOT remove from chapter6 — just consider not bringing them if
chapter6 is ever restructured.

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
| 2026-07-17 | Goal 3 Steps 4–8 complete. | Added to `SpecDerivedRepeatedCycleProperties`: Step 4 `assertSpecRepeatedCycleIntegralMatchesBase` — repeated CI and base CI agree pointwise via `assertRepeatedValuesIntegralMatches`; Step 5 `assertSpecBaseAndRepeatedSurvivorValuesMatch` — inductive equality of survivor lists; Step 6 `assertSpecBaseAndRepeatedGapListMatch` — trivial corollary of Step 5; Step 7 `assertBaseCIEqualsSeqApplyShifted` — baseCI(k) = seq.apply(k+1), direct from `assertSpecGapCycleIntegralMatchesApply`; Step 8 `assertFirstSurvivorMatchesNextSeqHead` — first survivor = nextSeq.head.value, using `assertApplyOneEqualsNextPrime` + `assertPrimeNotDivisibleByDistinctPrime` from ch5. Ch60: 4955 valid, 0 invalid, 0 unknown (was 4823). Step 9 (survivor gaps bridge) is now the blocking unit of work. |
| 2026-07-18 | Abandoned: indexed bijection via backward mutual induction. | Attempted `survivors(i) == nextSeq.apply(i)` as Step 9 via mutual induction: wrote `assertSurvivorMatchesNextSeqApply_Base_LT/GEQ/Base/Step` + `assertSurvivorAtIndexMatchesNextSeqApply` (lines 707–952). Base ✓ (51/51, 39s). Step+TopLevel → class-level run 847/856 valid, 9 unknown. Root cause: EUF mismatch — both ensuring blocks re-compute 4-val chain `specGapCycle→CycleIntegral→survivorValues` independently; Z3 can't unify in 300s. Also: `decreases(nextPeriod - i)` required on both functions to avoid TypeChecker FatalError (mutual recursion). This approach is permanently abandoned. Added `verify-bg` + `verify-debug-bg` to justfile. |
| 2026-07-19 | Switched to chapter 6 bridge approach for Step 9. | Chapter 6 NEVER proves `survivors(i) == spec.next(i)` directly — it proves gap equality via `mergedGapPrefix` + `assertMergedGapPrefixMatchesNext`. Chapter 60 already has this pipeline in `SpecSieveSeqNextProperties` (`assertPipelineOutputMatchesNextGapList` DONE). New plan: Step 9 = `assertSurvivorGapsEqualsMergedGapPrefix` (bridge between CI filtering and spec walking, using Step 7 as key ingredient). Step 10 = transitivity. Step 11 = `assertSpecGapCycleIntegralMatchesApply` applied to nextSeq. See "Goal 3 revision (2026-07-19)" section above. |
| 2026-07-20 | Dead code removed. | 34 dead functions removed from 5 files (503 lines). `just compile` + `just verify-ch 60` both pass: 4393 valid, 0 invalid, 0 unknown. Count drop from 4893 to 4393 = exactly the VCs belonging to deleted functions. |
| 2026-07-20 | Rename chapter6→chapter6 (old removed, chapter60 becomes chapter6). | See "Rename tracking" section at bottom of this ticket. |
| 2026-07-20 | Abandoned bijection code deleted; mergedGapPrefix precondition fixed. | Recurring pattern: abandoned indexed bijection code acts as temptation bait causing every session to re-attempt mutual induction (always times out). Decision: permanently delete ALL such code from `SpecDerivedRepeatedCycleProperties.scala`. File now contains only Steps 1–8 (verified). Also discovered: `assertPipelineOutputMatchesNextGapList` required `nextSeq.head.value == seq.head.value` — IMPOSSIBLE for `seq.next` (next head is strictly larger). Root cause: `mergedGapPrefix` and all its helpers had equality precondition instead of `<=`. Fixed: replaced `require(nextSeq.head.value == seq.head.value)` with `require(seq.head.value <= nextSeq.head.value)` throughout (22 occurrences), added bridge assertions for lower bounds, updated `assertPipelineOutputMatchesNextGapList` to start walk at k=1 (where `seq.apply(1) = nextSeq.head.value`). Also changed `accepts` from partial function (with `require(value >= head.value)`) to total predicate (`value >= head.value && passesFilter(value)`) — eliminating 21 timeout-inducing VC obligations; all bridges now derive lower bounds by unfolding `accepts`. Ch60: **4893 valid, 0 invalid, 0 unknown** (58.9s). |

---

## Rename tracking: chapter60 → chapter6 (old chapter6 removed)

**Action:** user deletes `src/main/scala/v1/chapter6/` and renames `src/main/scala/v1/chapter6/` to `src/main/scala/v1/chapter6/`
(i.e. `rm -rf .../chapter6 && mv .../chapter60 .../chapter6`)

### Already done (2026-07-20, before code rename)
`chapter60` → `chapter6` replaced in these md files (simple sed pass):
- `LEARNINGS.md` (2 occurrences — path in §8.4, ticket reference in §21)
- `chapter60-review-questions-2026-07-17.md` (9 occurrences)
- `tickets/active/chapter60-stateless-properties.md` (1 occurrence)
- `tickets/active/chapter60-goal-driven-audit.md` (this file, 5 occurrences in body)
- `tickets/active/spark-sieve-data-generator.md` (1 occurrence)
- `articles/chapter6/gap-dynamics-v2.md` (8 path references: `../../src/main/scala/v1/chapter6/...`)

### Still needed after code rename

**1. `articles/chapter6/gap-dynamics-v2.md` — remove deleted function reference**
Line ~1287 links to `assertConsecutiveAcceptedByNextPreservesGap` which was deleted in the dead-code removal pass. Remove or replace that bullet.

**2. Files where "chapter6" = the OLD removed implementation**
These files use `chapter6` to mean the OLD code, not the new one. They need a note or reword so the phrase now refers to "old implementation (removed)" to avoid confusion:
- `tickets/active/chapter60-goal-driven-audit.md` (this file): lines 8–9 ("Only copy what's needed to chapter6 — leave chapter6 untouched"), learning log entries 2026-07-17 ("not to repeat chapter6's opaque-walk mistake"), 2026-07-19 ("Chapter 6 NEVER proves..."), 2026-07-18 ("no chapter6 imports")
- `tickets/active/chapter6b-curated-proof-spine.md`: 11 occurrences all refer to old ch6 vs chapter6b design — entire ticket is historical, consider moving to `tickets/archived/`
- `tickets/active/sieve-sequence-proof.md`: 21 occurrences — references to old ch6 proofs
- `tickets/active/split-spec-sieve-sequence-assertions.md`: 6 occurrences
- `src/main/scala/v1/chapter6/README.md` (will move here from chapter60/README.md): 23 occurrences of `chapter6` and extensive `chapter6b` historical notes — consider simplifying header

**3. `tickets/active/spark-sieve-data-generator.md`**
Line 28: "Verified sieve sequence code exists in `src/main/scala/v1/chapter6/` and `src/main/scala/v1/chapter6/`" — now only one directory, update to single path.

**4. `LEARNINGS.md` §8.4**
Text says "file paths in the output point to `chapter6/` not `chapter6/`" — after rename both refer to the same thing; update the note to say the cache hit issue is resolved by the rename.

**5. Files that are purely historical (no action needed, just FYI)**
These mention old chapter6 as historical context and are accurate as-is:
- `tickets/done/*` — all reference old ch6 proof work, fine to leave
- `tickets/trash/*` — archived, leave as-is
- `articles/chapter6/sieve-sequence.md` — documents old ch6, may want `[ARCHIVED]` header
- `articles/deprecated/deprecated-sieve-sequence.md` — already marked deprecated

### Green light checklist
- [x] `just compile` passes after dead-code removal
- [x] `just verify-ch 60` passes: 4393 valid, 0 invalid, 0 unknown
- [x] `chapter60` → `chapter6` replaced in all md files
- [x] User runs: `rm -rf src/main/scala/v1/chapter6 && mv src/main/scala/v1/chapter60 src/main/scala/v1/chapter6`
- [x] Package declarations updated: `package v1.chapter6` inside all moved files
- [x] `just compile` re-run after rename
- [x] Items 1–4 above applied to md files
