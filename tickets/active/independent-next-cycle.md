# Independent Next-Cycle Computation (B.nextFromCycle)

**Created:** 2026-07-01
**Updated:** 2026-07-02
**Status:** Phases A-D complete, Phase E in progress

## Current Verification Status (2026-07-02)

| Chapter | Valid | Invalid | Unknown | Notes |
|----------|-------|---------|---------|-------|
| ch1 | 16 | 0 | 0 | Green |
| ch2 | 1346 | 0 | 0 | Green |
| ch3 | **1582** | 0 | 0 | Green (+108 from Phase B/C/D) |
| ch4 | **2675** | 0 | 0 | Green (+282 from GapProperties) |
| ch5 | 981 | 0 | 0 | Green |
| ch6 | **4647** | 0 | 0 | Green (+18 from Phase D) |
| ch4 | 2393 | 0 | 0 | Green |
| ch5 | 981 | 0 | 0 | Green |
| ch6 | 4629 | 0 | 0 | Green |
| `just test` | — | — | — | **133/133 passed** |

### Phase B complete (2026-07-02)

The `ShiftedList` type is now fully verified. Root cause: `shift` was creating
`ShiftedList(origHead + gaps.head, gaps)` with **unchanged gaps**, which meant
`shifted.apply(i) == orig.apply(i+1)` was false for `i >= 1` (counts `gaps(0)`
twice and never reaches `gaps(i)`).

**Fix:** changed `shift` to use rotated gaps:
```scala
ShiftedList(origHead + gaps.head, ListUtils.rotateAt(gaps, BigInt(1)))
```

This makes the positional-shift law and gap-translation law mathematically true.

**New foundation lemmas added to ch3:**

| Lemma | File | Statement | VCs |
|-------|------|-----------|-----|
| `assertAppendApplyLeft` | `ListUtilsProperties` | `(left ++ right).apply(k) == left.apply(k)` for `k < left.size` | 12/12 |
| `assertAppendApplyRight` | `ListUtilsProperties` | `(left ++ right).apply(k) == right.apply(k - left.size)` for `k >= left.size` | 12/12 |
| `assertSplitAtOne` | `ListUtilsProperties` | `splitAt(list, 1)._1 == List(list.head) && splitAt(list, 1)._2 == list.tail` | 4/4 |
| `assertRotatedAtIndexPlusOne` | `RotationProperties` | `rotateAt(list, 1).apply(k) == list.apply(k+1)` for `k+1 < size` | 30/30 |
| `assertShiftedApplyIsOriginalPlusOne` | `ShiftedList` | `shifted.apply(i) == orig.apply(i+1)` | 42/42 |
| `assertGapTranslation` | `ShiftedList` | `shifted.apply(i+1)-shifted.apply(i) == orig.apply(i+2)-orig.apply(i+1)` | 30/30 |

## Goal

Prove the three sequence representations agree on both current-stage `apply`
and next-stage construction:

- A: `SpecSieveSequence`
- B: `SpecDerivedSieveSequence`
- C: `CycleSieveSequence`

The target theorem is not merely that gaps are positive. Gap positivity is a
constructor invariant required by `GapCycle`, and it follows from strict
increase of the relevant `apply` sequence. The final goal is equality of
observable sequence behavior:

1. A.apply == B.apply == C.apply for the current stage.
2. A.next.apply == B.next.apply == C.next.apply for the next stage.
3. The independently computed next gap cycle is the same cycle that realizes
   A.next/B.next apply behavior.

Operationally, give B (`SpecDerivedSieveSequence`) a `nextFromCycle()` method that:
1. Computes the next stage's gap cycle **independently** by running the standard sieve pipeline (`SieveSequenceNextLevel` functions) on B's own cycle data.
2. After computation, **proves** the output matches A.next's properties (head equality, gap equality, apply equality).

This replaces the current `nextVerified`, which constructs B.next from A.next's data directly (delegation, not computation).

## Motivation

B should generate its next by performing the sieve process itself — residues, expand, filter, sort, gaps, rotate — just as the spec does conceptually, but on the cycle representation. This validates that the sieve algorithm, not just the spec's bookkeeping, produces correct next stages.

Once proven for B, C (`CycleSieveSequence`) can use the **same** `nextFromCycle()` and inherit correctness without needing a spec link.

## Current State

| Component | Status |
|-----------|--------|
| Pipeline functions (residues → expand → filter → sort → gaps → rotate) | Exist in `SieveSequenceNextLevel`, preconditions now discharged by M1 |
| B.nextVerified | Exists — reads A.next directly (delegation) |
| B.nextFromCycle | Does NOT exist |
| Pipeline precondition lemmas for B.cycle | **DONE** (M1, 4 lemmas verified) |
| Pipeline output = A.next gap cycle lemma | Does NOT exist |
| Lemma 4a (survivors = A.next) | Proven in bridge |
| C.next() (walk-based) | Exists, unproven against spec |
| Phase A (rotation theory) | **DONE** |
| Phase A7 (ch6→ch3 delegation) | **DONE** |
| Phase B (ShiftedList) | **DONE** |
| Phase C (gap-positivity) | **DONE** — `assertSumPositive`, `assertIntegralStrictlyIncreasing`, `assertGapsPositive` at ch3 level. GapProperties provides 13 ch4 wrappers. |
| Phase D (`assertNextSortedStrictlyAscending`) | **DONE** — `isAscending` changed to strict `<`; `assertIsAscendingAtIndex` bridge lemma. |
| Phase E (`allGreaterThan(nextRotatedGaps(cycle), 0)`) | **NEXT** |
| `just test` | **GREEN** — 133/133 |

## Milestones

### M1: Pipeline precondition lemmas for B.cycle

The pipeline `SieveSequenceNextLevel` functions require:
- `seq.modulus > 0`
- `ListUtils.checkAllPositive(seq.primesTailValues)`
- `seq.head > 0`
- `seq.modulus * seq.head > 0`

Add lemmas on `SpecDerivedSieveSequence` proving these. All follow from `PrimeUtils.primorial > 0` for non-empty primes.

### M2: B.nextFromCycle()

Method on `SpecDerivedSieveSequence`:

```scala
def nextFromCycle(nextPeriod: BigInt): SpecDerivedSieveSequence = {
    // 1. Compute next gap cycle from the pipeline
    val newGaps = SieveSequenceNextLevel.nextRotatedGaps(cycle)
    val newGapCycle = GapCycle(newGaps)

    // 2. Next primes from B's own primes (precondition satisfied by constructor)
    val nextPrimes = primes.next

    // 3. Build the next cycle
    val nextCycle = CycleSieveSequence(nextPrimes, newGapCycle)

    // 4. Build a new bridge wrapping A.next
    // (A.next is used ONLY for the final match verification, not for gap computation)
    SpecDerivedSieveSequence(spec.next, nextPeriod)
}
```

The bridge returned is `SpecDerivedSieveSequence(spec.next, nextPeriod)` — this is the same as `nextVerified`. The point is that the gap cycle was computed from the pipeline, not read from A.next.

**Discharging CycleSieveSequence's own preconditions:**
- `!primes.next.isEmpty` — guaranteed since primes grow
- Coprimality of next head to tail primes — follows from Lemma 4a survivors

### M3: Prove pipeline output = A.next gap cycle

The core theorem. Two sub-steps:

**M3a:** Prove the pipeline's survivors = cycle's survivors (the set of values not divisible by `head` within one period of `head * cycle.size`). The pipeline generates all candidates via residues-expand-filter; the survivors are exactly the values `cycle(k)` where `Calc.mod(cycle(k), head) != 0`.

**M3b:** Prove the pipeline's rotated gaps = A.next's gap cycle values. Use Lemma 4a (`assertSurvivorGapEqualsSpecNextGap`) as the bridge — if pipeline survivors match survivors in Lemma 4a, and Lemma 4a proves survivor gaps = A.next gaps, then pipeline gaps = A.next gaps by transitivity.

### M4: C uses the same nextFromCycle

Replace `C.next()`'s walk with the pipeline-based computation (same `SieveSequenceNextLevel` functions). Since the pipeline is pure `(CycleSieveSequence) => GapCycle`, C can call it directly with no spec dependency.

## Validation

- M1: `just verify` — green, no new unknown VCs
- M2: `just compile` — B has `nextFromCycle()` and it compiles
- M3: `just verify-ch 6` — new lemma proves pipeline gaps = A.next gaps
- M4: `just verify` — full green, C.next() uses pipeline

## Risks

1. **Pipeline precondition discharge might require new lemmas** from PrimeUtils or CycleIntegral that don't exist yet. Mitigation: add them.
2. **Pipeline output = A.next gap cycle proof might hit the same list-equality wall** as the walk (6 timeouts). Mitigation: Lemma 4a uses position-based arithmetic, not list construction — the pipeline outputs a concrete list that can be compared element-by-element to `specGapCycle`'s memCycle values. The key difference from the walk: the walk builds a list from `collectGaps` (different recursion shape from `specGapCycle`), while the pipeline sorts from residues (different again). If this also blocks, fall back to: prove that the pipeline's rotated gaps produce the same `apply(k)` values as A.next (per-position verification, not list equality).
3. **Primes.next precondition** depends on Bertrand bound, which B cannot discharge independently — it's guaranteed by B's constructor linking to A.

## Related Tickets

- `tickets/active/sieve-sequence-proof.md` — broader SieveSequence proof effort, Leg 4 (survival walk) attempted 6 times and deferred. This ticket replaces Leg 4's walk approach with pipeline-based computation for both B and C, which makes Leg 5 (C independent) trivially solvable
- `tickets/active/verify-timeout-root-cause.md` — circular dependency cleanup (already fixed)

## 2026-07-01 Audit: Deleted `SpecDerivedCycleSieve` Lemmas

`SpecDerivedCycleSieve.scala` was deleted in commit `9f99e029` when
`SpecDerivedSieveSequence` was introduced. The previous bridge had several
verified lemmas that were not fully migrated.

Important distinction:

- **Portable canonical lemmas:** these prove that a canonical cycle built from
  `spec.next` matches `spec.next` by construction. They are valuable and should
  be re-ported to `SpecDerivedSieveSequence`.
- **Not independent pipeline lemmas:** these do **not** prove that
  `SieveSequenceNextLevel.nextRotatedGaps(cycle)` computes the same gaps.
  They prove that `spec.next.specGapCycle(nextPeriod)` stores
  `spec.next.gapList(0, nextPeriod)`.
- **Walk/pipeline attempts:** several old walk correctness attempts were
  explicitly commented as timeouts. Do not resurrect those blindly.

Portable lemmas found in the old bridge:

| Old lemma | Meaning | Porting status |
|---|---|---|
| `assertNextGapCycleValuesEqualSpecNextGapList(nextPeriod)` | `spec.next.specGapCycle(nextPeriod).memCycle.values == spec.next.gapList(0, nextPeriod)` | Ported and focused verified: 11/11 valid |
| `assertNextCycleApplyMatchesSpecNext(nextPeriod, k)` | `SpecDerivedSieveSequence(spec.next, nextPeriod).cycle(k) == spec.next(k)` | Ported and focused verified: 20/20 valid |
| `assertNextCycleGapsMatchSpecNext(nextPeriod)` | canonical next-cycle gaps equal `spec.next.gapList(0,nextPeriod)` | Ported and focused verified: 25/25 valid |
| `assertNextCycleHeadMatchesSpecNext(nextPeriod)` | canonical next-cycle head equals `spec.next.head.value` | Ported and focused verified: 16/16 valid |
| `assertNextCycleMatchesSpecNext(nextPeriod)` | packages canonical head + gaps; apply via indexed lemma | Ported and focused verified: 25/25 valid |
| `SpecSieveSequence.assertSpecGapPeriodPositive(period)` | `gapList(0,period)` is strictly positive via existing apply/gap invariant | Added and focused verified: 7/7 valid |
| `assertNextCycleGapsPositive(nextPeriod)` | canonical next-cycle stored gaps are strictly positive | Added and focused verified: 25/25 valid |
| `nextGapList(from,count)` + `assertNextGapListMatchesSpecNext(from,count)` | direct adjacent-difference target equals `spec.next.gapList` in forward order | Re-ported and focused verified: 21/21 valid |
| `assertModulusPositive()` | B.cycle tail modulus is positive | Added and focused verified: 3/3 valid |
| `assertPrimesTailValuesPositive()` | B.cycle tail prime values are all positive | Added and focused verified: 3/3 valid |
| `assertHeadPositive()` | B.cycle head is positive | Added and focused verified: 1/1 valid |
| `assertModulusTimesHeadPositive()` | B.cycle expanded modulus `modulus * head` is positive | Added and focused verified: 3/3 valid |
| `nextPipelineGaps()` | computes `SieveSequenceNextLevel.nextRotatedGaps(cycle)` after discharging all pipeline preconditions | Added and focused verified: 8/8 valid |
| `assertNextPipelineGapsPositiveFromSpec(nextPeriod)` | conditional positivity: if pipeline gaps equal canonical spec gaps, then pipeline gaps are positive | Added and focused verified: 12/12 valid |
| `nextPipelineGapCycleIfMatchesSpec(nextPeriod)` | conditional `GapCycle` builder behind the future producer-equality precondition | Added and focused verified: 25/25 valid |
| `assertSurvivorPositionMatchesSpecNext(m)` | survivor bridge through `indexOfAccepted` | Partially replaced by `assertSpecNextIsKthSurvivor`; compare before porting |
| `assertCycleDiffEqualsGap(pos)` | adjacent `cycle` difference equals gap-cycle element | Needs careful review; old code may have off-by-one risk in doc/code |

Non-port-directly findings:

- `assertNextGapCycleValuesEqualSpecNextGapList` is **not** a pipeline theorem.
  It is a canonical/spec theorem.
- Old comments document that direct `nextGapsWalk(cycle) == spec.next.gapList`
  timed out because `collectGaps` is opaque from outside.
- The current `nextFromCycle` attempt timed out at `GapCycle(newGaps)` because
  Stainless cannot prove `allGreaterThan(nextRotatedGaps(cycle), 0)` at that
  call site. A reusable rotation-positivity lemma was started in `SieveUtils`
  to isolate part of that obligation.

Verified reusable helper work from this pass:

| Helper | Statement | Validation |
|---|---|---|
| `SieveUtils.assertSplitAtPreservesAllGreaterThan(list,index,value)` | splitting a positive-bounded list preserves the bound on both pieces | Focused verified: 23/23 valid |
| `SieveUtils.assertRotateAtPreservesAllGreaterThan(list,index,value)` | rotating a positive-bounded list preserves the bound | Focused verified: 20/20 valid |
| `ListBoundUtils.assertLessThanAtIndex(list,bound,pos)` | `allLessThan(list,bound)` exposes the pointwise fact `list(pos) < bound` | Focused verified: 13/13 valid |
| `SieveUtils.assertPairwiseGapsAllPositive(list)` | strict ascending input gives positive adjacent gaps | Focused verified: 36/36 valid |
| `SieveUtils.assertWrapGapPositive(sorted,modulus)` | `sorted.last < modulus` and `sorted.head >= 0` give positive wrap gap | Focused verified: 21/21 valid |
| `SieveUtils.assertCalculateGapsAllPositive(sorted,modulus)` | sorted bounded residues give positive calculated gaps | Focused verified: 23/23 valid |
| `SortedList.insertSorted(x,list)` | postcondition exposes `isAscending(list) => isAscending(result)` at recursive call sites | Focused verified: 21/21 valid |
| `SortedList.sortFiltered(list)` | postcondition exposes `isAscending(result)` directly from the recursive sorting producer | Focused verified: 14/14 valid |
| `SieveSequenceNextLevel.assertNextGapsAllPositiveGivenSortedBounds(seq)` | `sortFiltered` sortedness plus nonempty/range/head bounds imply `nextGaps(seq)` is positive | Focused verified: 24/24 valid |
| `SieveSequenceNextLevel.assertNextRotatedGapsAllPositiveGivenSortedBounds(seq)` | positive `nextGaps(seq)` implies `nextRotatedGaps(seq)` is positive by rotation preservation | Focused verified: 36/36 valid |

Verifier-shape lesson from Phase E:

- The low-level gap arithmetic is now proved independently. The first two
  attempts at the next-level wrapper timed out only when Stainless had to expose
  `SortedList.isAscending(nextSorted(seq).list)` from the `SortedList` wrapper
  inside the larger VC.
- Attaching strict sortedness to the recursive sorting producers with
  `.ensuring` turned the wrapper green without requiring strict sortedness as a
  local precondition. This confirms the next missing stepping stone is **not**
  gap positivity; it is a small upstream bridge that exposes the remaining
  sorted-output facts (`nonEmpty`, `allLessThan`, `head >= 0`) from the
  expand/filter/sort pipeline in a verifier-friendly shape.
- `just verify-debug assertNextGapsAllPositiveGivenSortedBounds` confirmed the
  mechanism: the generated VCs repeatedly instantiate matchers for
  `isAscending(nextSorted(seq).list)` and then unroll through
  `nextSorted(seq)`, `SortedList.fromUnsorted(nextFiltered(seq))`,
  `nextFiltered(seq)`, prime-tail invariants, and recursive tails of
  `isAscending`. In other words, Stainless is not simply reusing the previously
  verified `SortedList.fromUnsorted`/constructor fact at the compositor site; it
  tries to unwrap the pipeline again. The debug log stopped after `25 / 27`
  while solving the body assertion, so use it as mechanism evidence rather than
  as a final verification result. After adding the producer `.ensuring`
  postconditions, the clean validation source is the focused non-debug run
  (`24/24 valid`).

Remaining independent-pipeline proof obligation:

- Primary obligation: prove the independent pipeline's rotated gap list equals
  the canonical next gap list:
  `SieveSequenceNextLevel.nextRotatedGaps(cycle) == spec.next.gapList(0,nextPeriod)`.
- Once that equality exists, positivity should come from the already verified
  canonical facts (`assertSpecGapPeriodPositive`, `assertNextCycleGapsPositive`)
  instead of a separate sorted-list positivity proof.
- Secondary fallback obligation: discharge the remaining sorted-output bounds
  and call `assertNextRotatedGapsAllPositiveGivenSortedBounds(seq)` to prove
  `ListBoundUtils.allGreaterThan(SieveSequenceNextLevel.nextRotatedGaps(seq), 0)`
  for the standard pipeline. The sorting, gap arithmetic, and rotation parts are
  now focused-verified; only the remaining range/head bridge remains.

## 2026-07-01 Refinement: Positivity is Supporting Evidence, Apply Equality is the Goal

The observation "gaps are required to be non-null/positive, therefore apply is
required to be always increasing" is correct and already represented in the
code:

- `SpecSieveSequence.assertGapPositive(k)` proves each adjacent apply
  difference is positive.
- `SpecSieveSequence.assertGapListPositive(from,count)` lifts that to lists.
- `SpecSieveSequence.assertSpecGapPeriodPositive(period)` now exposes the full
  period positivity fact directly.
- `SpecDerivedSieveSequence.assertNextCycleGapsPositive(nextPeriod)` now exposes
  the same fact through the canonical next-cycle bridge.

This is not a replacement for the main theorem. It is a way to avoid proving
positivity in the wrong representation. The main proof should still target
three-way equality of `apply` and `next`; positivity then follows from equality
with the canonical gap/apply representation.

## 2026-07-01 Progress: Canonical Target Re-Established in Current Class

Re-ported `nextGapList(from,count)` and
`assertNextGapListMatchesSpecNext(from,count)` from the deleted bridge into
`SpecDerivedSieveSequence`.

Validation:

- `just verify assertNextGapListMatchesSpecNext`
- Result: 21/21 valid, 0 invalid, 0 unknown

## 2026-07-01 Progress: Bottom-Up Repeated-Cycle Ladder

The repeated-cycle proof is now built from the lower representations upward,
instead of proving the Chapter 6 sequence fact directly:

1. Repeated list indexing.
2. Repeated `MemCycle` lookup.
3. Repeated `CycleIntegral` lookup.
4. Repeated `CycleSieveSequence.apply`.

This matters because `CycleSieveSequence.apply(k)` delegates to
`integral(k - 1)` when `k > 0`. The top-level apply proof therefore lowers the
sequence index `k` to the strictly smaller integral index `k - 1`; the Javadoc
on `assertRepeatedCycleApplyMatches` now states this at the method top to make
the induction shape harder to miss.

Validated helper ladder:

| Helper | Statement | Validation |
|---|---|---|
| `ListRepeatProperties.assertRepeatAllGreaterThan` | repeating a positive-bounded list preserves the bound | Focused verified: 14/14 valid |
| `ModOperations.modByPositiveMultipleThenBase(a,base,times)` | `mod(mod(a, base * times), base) == mod(a, base)` for positive `base,times` | Focused verified: 22/22 valid |
| `MemCycleProperties.assertRepeatedValuesCycleMatches(cycle,repeatedCycle,times,position)` | a `MemCycle` backed by repeated values has the same lookup as the original cycle | Focused verified: 39/39 valid |
| `CycleIntegralProperties.assertRepeatedValuesIntegralMatches(cycleIntegral,repeatedCycleIntegral,times,position)` | repeated physical cycle values preserve the recursive integral with the same initial value | Focused verified: 51/51 valid |
| `SpecDerivedSieveSequence.repeatedCycle(times)` | constructs the repeated physical gap storage for B | Focused verified: 14/14 valid |
| `SpecDerivedSieveSequence.assertRepeatedGapListIndexMatches(times,index)` | repeated gap list indexing agrees with the original periodic gap lookup | Focused verified: 13/13 valid |
| `SpecDerivedSieveSequence.assertRepeatedCycleGapMatches(times,position)` | repeated B gap-cycle lookup equals original B gap-cycle lookup | Focused verified: 18/18 valid |
| `SpecDerivedSieveSequence.assertRepeatedCycleIntegralMatches(times,position)` | repeated B integral lookup equals original B integral lookup | Focused verified: 17/17 valid |
| `SpecDerivedSieveSequence.assertRepeatedCycleApplyMatches(times,k)` | repeated B sequence apply equals original B sequence apply | Focused verified: 31/31 valid |

Lessons:

- Local Chapter 6 recursive versions of the integral/apply proofs initially
  timed out on final postconditions. Branch-local return expressions and stable
  aliases helped, but the better permanent fix was moving the repeated-cycle
  facts down into Chapter 4 where `MemCycle` and `CycleIntegral` can prove their
  own representation invariance directly.
- The generic `MemCycle` lemma intentionally takes an already-built repeated
  `MemCycle` plus a `values == repeat(...)` precondition. That keeps constructor
  obligations out of the generic proof and lets Chapter 6 discharge them at the
  concrete call site.
- The repeated-cycle result is a support lemma for the final target: equality
  of the three sequence representations' `apply` and `next` behavior. It does
  not itself prove the independent next pipeline equals the spec pipeline.
- `OBJECTS.md` has been updated with the newly proved repeated-list,
  repeated-`MemCycle`, repeated-`CycleIntegral`, and Chapter 6 repeated-cycle
  properties so future proof work can find these lemmas from the project
  catalog.

Meaning:

- This proves the direct adjacent-difference list built from `spec.next.apply`
  equals `spec.next.gapList`.
- It is still a canonical target, not an independent pipeline theorem.
- Producer proofs can now target either `nextGapList(0,nextPeriod)` or
  `spec.next.gapList(0,nextPeriod)` without reintroducing the deleted class.

## 2026-07-01 Progress: M1 Pipeline Preconditions Discharged

Added the four named precondition lemmas used by the commented `nextFromCycle`
sketch:

- `assertModulusPositive()` -> 3/3 valid
- `assertPrimesTailValuesPositive()` -> 3/3 valid
- `assertHeadPositive()` -> 1/1 valid
- `assertModulusTimesHeadPositive()` -> 3/3 valid

Meaning:

- B can now locally satisfy the `SieveSequenceNextLevel` requires for
  `nextResidues`, `nextExpanded`, `nextFiltered`, `nextSorted`, `nextGaps`, and
  `nextRotatedGaps`.
- This does not yet solve the `GapCycle(newGaps)` constructor requirement.
  The remaining positivity/equality theorem is still needed before wrapping the
  independent pipeline output as a cycle.

## 2026-07-01 Progress: Independent Pipeline List Exposed

Added `nextPipelineGaps()`, which computes
`SieveSequenceNextLevel.nextRotatedGaps(cycle)` after asserting the four M1
preconditions.

Validation:

- `just verify nextPipelineGaps`
- Result: 8/8 valid, 0 invalid, 0 unknown

Meaning:

- The independent producer can now run far enough to return a plain rotated gap
  list.
- The next proof target is no longer "can B call the pipeline?" It can.
- The remaining blocker is exactly the producer theorem:
  `nextPipelineGaps() == spec.next.gapList(0,nextPeriod)` (or the equivalent
  direct target `nextGapList(0,nextPeriod)`).

## 2026-07-01 Progress: Constructor Barrier Isolated Behind Equality

Added two conditional bridge methods:

- `assertNextPipelineGapsPositiveFromSpec(nextPeriod)`
- `nextPipelineGapCycleIfMatchesSpec(nextPeriod)`

Validation:

- `just verify assertNextPipelineGapsPositiveFromSpec` -> 12/12 valid
- `just verify nextPipelineGapCycleIfMatchesSpec` -> 25/25 valid

Meaning:

- If the future producer theorem proves
  `nextPipelineGaps() == spec.next.gapList(0,nextPeriod)`, then the pipeline
  output is known positive by the existing spec apply/gap invariant.
- Under the same equality precondition, `GapCycle(nextPipelineGaps())` now
  verifies. The old constructor timeout is therefore not an independent mystery;
  it reduces to the producer equality theorem.
- Remaining hard theorem:
  `nextPipelineGaps() == spec.next.gapList(0,nextPeriod)`.

## 2026-07-01 Plan: Verifier Stepping Stones Before M3 (WORK IN PROGRESS)

**Starting with S1: Representation Alias Lemmas.** Adding them one by one,
each change followed by `just verify`.

### S1 Progress

| # | Lemma | Statement | Validation |
|---|-------|-----------|------------|
| 1 | `assertCycleHeadMatchesSpecHead` | `cycle.head == spec.head.value` via `assertApplyMatches(0)` | 3/3 valid, 0 invalid |

## 2026-07-01 Plan: Verifier Stepping Stones Before M3

The repeated-cycle timeout showed the main Stainless limitation for this ticket:
facts that are obvious by representation are often invisible unless named as
small lemmas. Before attempting the full producer theorem, prove the following
classes of bridge facts upfront and verify them in isolation.

### S1: Representation Alias Lemmas

Goal: avoid reopening constructors and field definitions inside M3.

- Name every equality between spec, derived, and cycle representations that M3
  will need.
- Examples already useful: `cycle.integral` construction alias, prime-value
  aliases, canonical `spec.next.gapList` aliases.
- Missing likely aliases: any direct alias between `nextPipelineGaps()`,
  `SieveSequenceNextLevel.nextRotatedGaps(cycle)`, `nextGapList(0,nextPeriod)`,
  and `spec.next.gapList(0,nextPeriod)` once the right intermediate target is
  chosen.

### S2: Period and Modulo Normalization Lemmas

Goal: make cycle-period arithmetic explicit instead of expecting Stainless to
discover it.

- Proven example: `modByPositiveMultipleThenBase`.
- Reuse/prove small lemmas for:
  - reducing through repeated periods,
  - shifting by whole periods,
  - converting `cycle(k)` to `cycle(mod(k,size))`,
  - comparing old period, expanded period, and rotated next period indices.

Progress:

- `GapProperties.assertModIsPeriodic(ci,m,pos)` is now proved and focused
  verified: if `ci.sum mod m == 0` and one full cycle advances by `ci.sum`,
  then `ci(pos) mod m == ci(pos mod ci.size) mod m`. The proof avoids the
  previous timeout-prone global div/mod decomposition by recursively subtracting
  one full cycle from `pos`.

### S3: List Construction Shape Lemmas

Goal: bridge lists that contain the same values but are built by different
recursion shapes.

- Proven examples: repeated-list indexing and `nextGapList == spec.next.gapList`.
- Missing likely shape bridges:
  - pipeline survivor list equals the cycle survivor list,
  - sorted/filtered pipeline output preserves exactly the expected survivor
    values,
  - filtering preserves sorting, so if an expanded/candidate list is already
    sorted then the filtered survivor list remains sorted,
  - filtered-gap merge property: the gap between two consecutive filtered
    survivors equals the sum of the original consecutive gaps across the
    removed interval,
  - rotated pipeline gaps align index-by-index with the canonical next gap list.

### S4: Positivity and Non-Empty Transfer Lemmas

Goal: keep constructor VCs separate from producer equality.

- Proven examples: repeat preserves positivity, rotate/split preserve positivity,
  canonical spec next gaps are positive, and `nextPipelineGapCycleIfMatchesSpec`
  conditionally constructs the `GapCycle`.
- Remaining use: once producer equality is proven, positivity should be
  transferred from `spec.next.gapList` rather than reproved from the pipeline.

### S5: Sortedness Preservation Lemmas

Goal: keep ordering facts available through the pipeline instead of relying on
Stainless to infer them after filtering.

- Add/prove a focused lemma that filtering a sorted list preserves sortedness.
- This matters for the survivor pipeline because `nextFiltered` removes values
  but should not disturb the order needed by `nextSorted`, `nextGaps`, and the
  eventual index-by-index comparison with `spec.next.gapList`.
- Prefer a reusable list-level lemma first, then a narrow pipeline wrapper if
  the call site still needs representation aliases.

### S6: Filter Merge/Sum Lemmas

Goal: connect filtered survivor gaps to sums over the original unfiltered gap
sequence.

- Prove the merge property explicitly: if two consecutive values in the
  filtered survivor list come from original indices `i < j`, then the filtered
  gap between them equals the sum of original adjacent gaps from `i` through
  `j - 1`.
- In sequence notation, for original values `V` and filtered survivor values
  `F`, if `F(m) = V(i)` and `F(m + 1) = V(j)`, then:

  ```math
  F(m + 1) - F(m) =
    V(j) - V(i) =
    \sum_{r=i}^{j-1} (V(r + 1) - V(r))
  ```

- This is the precise bridge between "filter removes multiples" and "next
  gaps are merged old gaps." It should be proven before the full rotated-gap
  equality, otherwise Stainless will see the filtered list values and original
  gap list as unrelated constructions.
- Check existing `CycleIntegralFilterProperties` helpers first:
  `assertMergedGapIsCITelescope`, `mergedGaps`, `survivorValues`,
  `gapsFromValues`, `allGapsMatch`, and `assertNewCIGeneratesFiltered` may
  already contain reusable pieces of this theorem.

### S7: Apply-vs-Integral Lowering Lemmas

Goal: avoid hiding the `k > 0 => integral(k - 1)` branch inside large proofs.

- Proven example: repeated-cycle apply equality lowers positive sequence index
  `k` to integral index `k - 1`.
- M3/M4 should use this pattern whenever comparing `CycleSieveSequence.apply`
  values through gap/integral facts.

### S8: Directional Transfer Lemmas

Goal: transfer facts from the representation where they are cheap to the
representation where they are needed.

- Proven examples: Chapter 5 `contains` alias lesson, spec/cycle apply transfer,
  and conditional pipeline-gaps positivity from spec equality.
- Missing likely transfers:
  - survivor acceptance/rejection from `spec.next` to pipeline-filter facts,
  - sorted membership to filtered membership and back in the exact shape needed
    by M3,
  - gap equality from survivor positions to rotated pipeline gap positions.

### S9: Conditional Builders

Goal: isolate hard theorems from constructor noise.

- Proven example: `nextPipelineGapCycleIfMatchesSpec(nextPeriod)`.
- Continue this pattern for `nextFromCycle()`: build conditional methods first,
  then remove or discharge their equality preconditions only after the producer
  theorem is proven.

## Questions

1. Should `nextFromCycle()` accept `nextPeriod` as a parameter (like `nextVerified`), or compute it from the cycle size?
   - Current cycle's period = `head * gapCycle.size`
   - Next cycle's period = `newHead * newGapCycle.size`
   - But newGapCycle isn't known until after the pipeline runs
   - Propose: `nextPeriod` stays as parameter, same as `nextVerified`
