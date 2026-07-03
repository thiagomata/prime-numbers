# Independent Next-Cycle Computation (B.nextFromCycle)

**Created:** 2026-07-01
**Updated:** 2026-07-04
**Status:** Green baseline at HEAD; M3 (pipeline = spec.next) is the open theorem.

---

## ⤴ START HERE — current plan (read this first, before any code)

This section is the active plan. Everything below `## Reference & History` is
context. If you cannot state the micro-goal and the method in one sentence each,
your first job is to re-read this section — not to edit code.

### Where we actually are
- **Green baseline:** HEAD verifies clean (`just verify-ch 6` → 0 invalid,
  0 unknown). A+B Scala files are at the `5145c1e5` shape.
- **What's proven and active:** current-stage equality (`cycle(k) == spec(k)`),
  the M1 pipeline preconditions, the repeated-cycle ladder, the canonical
  next-cycle lemmas, and the migration-independent leaf
  `assertHeadPlusFilterModulusNotFrontMultiple`.
- **What's NOT proven:** M3 — `nextRotatedGaps(cycle) == spec.next.gapList(0,nextPeriod)`.
  This is the only theorem that matters. Everything else is supporting work.

### The micro-goal (one lemma at a time)
The next concrete step is **not** "do M3." It is one falsifiable lemma, chosen
because it's the cheapest unproven rung that unblocks the next. Define it
*before* coding, in this shape:

> **Lemma:** <name> — <one-line statement>
> **Preconditions it needs:** <explicit list — every fact the body relies on>
> **Why it's the next step:** <which rung it clears, what it unblocks>

State the precondition list by reading the proof you intend to write, not by
guessing. If you can't enumerate the preconditions, you don't yet understand the
lemma — keep reading reference material until you can.

### The method: debug-first precondition audit (do this on EVERY timeout)
Most timeouts here are **not** deep math — they are Stainless re-deriving facts
the proof never handed it. Evidence: LEARNINGS 18.4/18.5, the `accepts`/`>=`
precondition-of-a-precondition gap found 2026-07-03, and the debug note that
Stainless "tries to unwrap the pipeline again" instead of reusing verified facts.

**On any timeout, before considering a new approach:**
1. Run `just verify-debug <fn>` and read what Stainless is actually unfolding.
2. List every fact it is trying to rediscover (cross-instance calls, recursive
   unwinds, monotonicity it won't reuse).
3. Assert each one explicitly — as a local `assert(...)`, a `.ensuring` on the
   producer, or a directed equality lemma (LEARNINGS 18.3).
4. Re-verify. Repeat with the next unfolding.
5. **Only after a thorough audit yields nothing** is the wall "real" — and even
   then, the fallback is per-position apply equality (Risk §2), not a brand-new
   representation.

This replaces the old habit of "hit wall → invent new approach → add a section."
A new approach is a last resort, not a first response.

### Stopping rules (do NOT drift)
- **One lemma per working tree.** Define it, prove it green, commit. Then pick
  the next. Never carry two in-flight lemmas.
- **3 failed attempts on one lemma → STOP and surface the debug output**, do not
  try a variation, do not pivot approach. Report the failing VC verbatim.
- **Never commit red.** Mid-migration states are red by construction (see
  Recovery Log). If green isn't reachable in one working tree, revert and
  redefine the micro-goal smaller.
- **If the session can't state the micro-goal, the session stops** — it does not
  edit code. Re-read this section or ask.

### Documentation rule: no verify counts
**Do not record VC counts, `X/X valid` tallies, or "focused-verified" status
claims in this ticket or in OBJECTS.md.** They go stale the moment anything
changes (they already survived a red HEAD once, which made them actively
misleading). The durable facts are: the lemma *name*, *what it proves*, and the
*commit* that introduced it. For current status, re-run `just verify-ch 6`; the
only durable criterion is `invalid: 0 unknown: 0`. Record the green signal
(0/0), never the count.

### Two known approaches (decide once, don't relitigate)
The reference section documents both; the **Approach Comparison** subsection
gives the full analysis. Short version: **hedge, contract-migration first.**
The migration is mechanical (recipe in `## The Correct Track`) and unblocks 12
already-written lemmas (their focused-verify claims predate the red HEAD, so
treat them as drafts until re-verified); the value-level `SieveCycleAfterProof`
path is insurance but has proven less of the ladder. Pivot only on the failure signals
listed in the comparison. Do not start a third approach without exhausting the
debug-first audit on the existing two.

---

## Current Verification Status

**Authoritative as of 2026-07-04 recovery:** `just verify-ch 6` is green
(0 invalid, 0 unknown), full chapter, after restoring the `5145c1e5` baseline
and re-activating the leaf lemma. `just test` → 133/133.

> The per-chapter table that used to live here had duplicate/contradictory rows
> from stale baselines and was removed. Do not record verify counts in this
> ticket — they go stale immediately. To check current status, re-run
> `just verify-ch 6`; the durable criterion is `invalid: 0 unknown: 0`.

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

| Lemma | Statement |
|-------|-----------|
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

#### M3 Proof Ladder ("Santa Claus List")

The final target is:

```scala
SieveSequenceNextLevel.nextRotatedGaps(cycle) ==
  spec.next.gapList(0, nextPeriod)
```

The proof should move through the following small lemmas in order. Each lemma
states one mathematically true fact in the representation where it is cheapest
to prove, then exports it in the shape needed by the next layer.

Placement rule: put every reusable fact in the lowest chapter/representation
that can state it without mentioning chapter 6 sequence objects. Chapter 6
should mostly contain transfer lemmas and composition lemmas. In practice:

- Pure list order/membership/sort facts belong in chapter 3 list modules.
- Pure cycle/integral/gap/survivor facts belong in chapter 4, preferably
  `GapProperties` when they consume `CycleIntegralFilterProperties`.
- Prime/coprime/filter-value facts belong in chapter 5 unless they require a
  chapter 6 sequence object.
- Chapter 6 should connect `SpecSieveSequence`, `SpecDerivedSieveSequence`,
  `CycleSieveSequence`, and `SieveSequenceNextLevel` after lower-level facts
  already expose the needed math.

1. **Current apply equality**

   Status: already proved by `assertApplyMatches(k)`.

   ```math
   cycle(k) = spec(k)
   ```

   Purpose: every current-stage value used by the cycle pipeline is the same
   current-stage value used by the spec sequence.

2. **Current filter-head equality**

   Status: mostly already proved by `assertCycleHeadMatchesSpecHead()` and the
   definition of `spec.next.filterValues`.

   ```math
   cycle.head = spec.head.value = spec.next.filterValues.head
   ```

   Purpose: both sides test divisibility by the same newly added filter value
   when constructing the next stage.

3. **Keep/drop predicate transfer**

   Status: proved by `assertCycleSpecNextFilterDecisionMatches(k)`.
   Home: chapter 6 (`SpecDerivedSieveSequence`) because it relates `cycle(k)`,
   `spec(k)`, and `spec.next.filterValues`.

   ```math
   cycle(k) = spec(k)
   \land cycle.head = spec.next.filterValues.head
   \Rightarrow
   \bigl(\operatorname{mod}(cycle(k), cycle.head) \ne 0\bigr)
   =
   \bigl(\operatorname{mod}(spec(k), spec.next.filterValues.head) \ne 0\bigr)
   ```

   Candidate name:
   `assertCycleSpecNextFilterDecisionMatches(k)`.

   Purpose: this is the small "same value, same divisor, same decision" bridge.
   It prevents downstream survivor proofs from repeatedly reconstructing the
   equality through `assertApplyMatches`, head aliases, and `Calc.mod`.

4. **Cycle survivor exactness**

   Status: value-level pieces plus the first ordered survivor head are now
   proved in `GapProperties`:
   `assertSurvivorValuesContainsNonMultipleAtPosition`,
   `assertSurvivorValuesContainsOnlyNonMultiples`, and
   `assertSurvivorValuesExcludesMultipleAtPosition`; plus
   `allMultiplesInRange`, `assertAllMultiplesInRangeTail`, and
   `assertFirstSurvivorAtPosition` /
   `assertSurvivorValuesSplitAtFirstPosition`.
   Home: chapter 4 (`GapProperties`) because it is a pure
   `CycleIntegral`/survivor scan fact.

   ```math
   start \le k < start + count
   \Rightarrow
   cycle(k) \in survivorValues(cycle.integral, cycle.head, start, count)
   \iff
   \operatorname{mod}(cycle(k), cycle.head) \ne 0
   ```

   Purpose: the cycle-side survivor scan removes multiples of `cycle.head` and
   only those. The value-level lemmas are enough for membership/exclusion; the
   first-survivor-position lemma is the first ordered refinement:

   ```math
   allMultiplesInRange(ci, f, start, pos)
   \land \operatorname{mod}(ci(pos), f) \ne 0
   \Rightarrow
   survivorValues(ci, f, start, count).head = ci(pos)
   ```

   The stronger structural split is also proved:

   ```math
   survivorValues(ci, f, start, count)
   =
   ci(pos) :: survivorValues(ci, f, pos + 1, start + count - pos - 1)
   ```

   Remaining refinement: expose the same idea for the next/`i`-th survivor,
   not only the head of the current scan.

5. **Spec survivor exactness**

   Status: mostly already proved on the spec side through
   `assertNextValueAcceptedByThis`, `assertSpecNextIsKthSurvivor`,
   `assertSurvivorGapEqualsSpecNextGap`, and the private merge/copy lemmas in
   `SpecSieveSequence`. New public hooks now expose the needed filter-step
   shape: `nextAcceptedOldIndex(nextSeq,k,period)` returns the old-stream index
   used for the next emitted `nextSeq` value, and
   `assertSkippedBeforeNextAcceptedOldIndexIsMultiple(nextSeq,k,idx,period)`
   proves every skipped old index before it is a multiple of the new front
   filter.

   ```math
   spec.next(i) = spec(j)
   \quad\text{where } j \text{ is the } i\text{-th current value accepted by}
   \quad spec.next.filterValues
   ```

   Purpose: the spec sequence already knows that its next values are exactly the
   old accepted values under the added front filter.

6. **Ordered survivor equality**

   Status: missing, but advanced by the new chapter 4 ordered split lemma:
   `assertSurvivorValuesSplitAtFirstPosition` proves the first survivor of a
   scan and the remaining tail when the skipped prefix is known to be
   multiples. The chapter 6 base bridge
   `assertCycleSurvivorValuesStartAtSpecNextHead(count)` now applies that split
   at position 0 and proves the cycle-side survivor scan starts at
   `spec.next.head.value`.
   Home: split it. The survivor index/position mapping should be chapter 4
   if it can be stated over `CycleIntegral` and `survivorValues`; the final
   equality to `spec.next(i)` belongs in chapter 6.

   ```math
   cycleSurvivor(i) = spec.next(i)
   ```

   More explicit form:

   ```scala
   survivorValues(cycle.integral, cycle.head, start, count)(i) == spec.next(i)
   ```

   Purpose: membership is not enough; gaps depend on consecutive order. This
   lemma should combine current apply equality, filter-decision equality, and
   first-survivor/next-survivor facts.

7. **Expanded pipeline enumerates the same ordered survivor candidates**

   Status: missing/partially covered by `assertExpandedResiduesRepresentPeriod`
   and `assertNextFilteredContainsCoprime`.
   Progress: bounds for the expanded/filtered pipeline are now proved via
   `assertNextExpandedAllLessThan(seq)`,
   `assertNextFilteredAllLessThan(seq)`, and
   `nextFilteredWithBound(seq)`. These are range facts, not yet
   ordered survivor equality.
   Home: chapter 6, because this talks about `SieveSequenceNextLevel` pipeline
   stages. Any reusable list-level filter membership/order helper discovered
   while proving it should move down to chapter 3.

   ```math
   nextFiltered(cycle)
   =
   \{ cycle(k) \mid 0 \le cycle(k) < cycle.modulus \cdot cycle.head
      \land \operatorname{mod}(cycle(k), cycle.head) \ne 0 \}
   ```

   Purpose: connect the residue/expand/filter pipeline representation to the
   survivor scan/spec representation.

8. **Sort/order bridge**

   Status: missing.
   Home: chapter 3 for generic "filter preserves sorting" or "sort preserves
   ordered values" facts; chapter 6 only for the pipeline wrapper that applies
   those facts to `nextFiltered`/`nextSorted`.

   ```math
   nextSorted(cycle).list(i) = spec.next(i)
   ```

   Purpose: `nextFiltered` is a list built by residue expansion and filtering;
   `spec.next` is an increasing sequence. Either prove the filtered pipeline is
   already ordered, or prove sorting reorders it into the same increasing
   survivor sequence.

9. **Gap calculation equality**

   Status: missing, but should become straightforward after ordered survivor
   equality.
   Home: chapter 4 for generic "equal ordered survivor values imply equal
   gaps/telescoped gaps"; chapter 6 for the wrapper tying
   `calculateGaps(nextSorted(...))` to `spec.next.gapList`.

   ```math
   calculateGaps(nextSorted(cycle).list, cycle.modulus \cdot cycle.head)(i)
   =
   spec.next.gapList(0, nextPeriod)(i)
   ```

   Purpose: consecutive equal survivor values have equal adjacent differences.
   The wrap gap needs the period endpoint equality:

   ```math
   spec.next(nextPeriod) = spec.next.head.value + spec.next.filterModulus
   ```

10. **Rotation anchor equality**

    Status: missing.
    Home: chapter 3/4 for generic rotation/index facts; chapter 6 for the
    concrete equality involving `nextHeadResidueIndex(cycle)` and
    `spec.next.head.value`.

    ```math
    nextHeadResidueIndex(cycle)
    =
    \text{index of } spec.next.head.value \text{ in } nextSorted(cycle).list
    ```

    Purpose: the pipeline computes unrotated gaps from sorted residues, then
    rotates to begin at the next head. We must prove that this rotation is the
    same canonical start used by `spec.next.gapList`.

11. **Rotated gap equality**

    Status: final M3 theorem.

    ```math
    nextRotatedGaps(cycle) = spec.next.gapList(0, nextPeriod)
    ```

    Purpose: this unlocks `nextPipelineGapCycleIfMatchesSpec(nextPeriod)` and
    then `nextFromCycle()`.

Recommended implementation order:

1. Add the tiny filter-decision transfer lemma in `SpecDerivedSieveSequence`.
2. Add position/index survivor exactness for `survivorValues` in
   `GapProperties`, building on the value-level exactness lemmas.
3. Bridge cycle survivors to `spec.next` survivors.
4. Bridge `nextFiltered`/`nextSorted` to that same ordered survivor list.
5. Prove gap equality, then rotation equality.

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

## Companion article

`articles/sieve-sequence.md` is the published write-up of these results. Its
**§8a "Properties by Proof Status"** is the canonical map of which sequence
properties are verified vs. mathematically-true-but-pending vs. genuinely
blocked — the same taxonomy tracked operationally by this ticket's Failure log
(F1–F7) and START HERE section. When a lemma changes status (verified, deferred,
or blocked), update §8a and the relevant Failure-log entry together so the
article and the ticket stay in sync. The article's §8a.1 also names the
migration-independent leaf (`assertHeadPlusFilterModulusNotFrontMultiple`) that
stays green regardless of the contract-shape debate.

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
| `assertNextGapCycleValuesEqualSpecNextGapList(nextPeriod)` | `spec.next.specGapCycle(nextPeriod).memCycle.values == spec.next.gapList(0, nextPeriod)` |
| `assertNextCycleApplyMatchesSpecNext(nextPeriod, k)` | `SpecDerivedSieveSequence(spec.next, nextPeriod).cycle(k) == spec.next(k)` |
| `assertNextCycleGapsMatchSpecNext(nextPeriod)` | canonical next-cycle gaps equal `spec.next.gapList(0,nextPeriod)` |
| `assertNextCycleHeadMatchesSpecNext(nextPeriod)` | canonical next-cycle head equals `spec.next.head.value` |
| `assertNextCycleMatchesSpecNext(nextPeriod)` | packages canonical head + gaps; apply via indexed lemma |
| `SpecSieveSequence.assertSpecGapPeriodPositive(period)` | `gapList(0,period)` is strictly positive via existing apply/gap invariant |
| `assertNextCycleGapsPositive(nextPeriod)` | canonical next-cycle stored gaps are strictly positive |
| `nextGapList(from,count)` + `assertNextGapListMatchesSpecNext(from,count)` | direct adjacent-difference target equals `spec.next.gapList` in forward order |
| `assertModulusPositive()` | B.cycle tail modulus is positive |
| `assertPrimesTailValuesPositive()` | B.cycle tail prime values are all positive |
| `assertHeadPositive()` | B.cycle head is positive |
| `assertModulusTimesHeadPositive()` | B.cycle expanded modulus `modulus * head` is positive |
| `nextPipelineGaps()` | computes `SieveSequenceNextLevel.nextRotatedGaps(cycle)` after discharging all pipeline preconditions |
| `assertNextPipelineGapsPositiveFromSpec(nextPeriod)` | conditional positivity: if pipeline gaps equal canonical spec gaps, then pipeline gaps are positive |
| `nextPipelineGapCycleIfMatchesSpec(nextPeriod)` | conditional `GapCycle` builder behind the future producer-equality precondition |
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
| `SieveUtils.assertSplitAtPreservesAllGreaterThan(list,index,value)` | splitting a positive-bounded list preserves the bound on both pieces |
| `SieveUtils.assertRotateAtPreservesAllGreaterThan(list,index,value)` | rotating a positive-bounded list preserves the bound |
| `ListBoundUtils.assertLessThanAtIndex(list,bound,pos)` | `allLessThan(list,bound)` exposes the pointwise fact `list(pos) < bound` |
| `SieveUtils.assertPairwiseGapsAllPositive(list)` | strict ascending input gives positive adjacent gaps |
| `SieveUtils.assertWrapGapPositive(sorted,modulus)` | `sorted.last < modulus` and `sorted.head >= 0` give positive wrap gap |
| `SieveUtils.assertCalculateGapsAllPositive(sorted,modulus)` | sorted bounded residues give positive calculated gaps |
| `SortedList.insertSorted(x,list)` | postcondition exposes `isAscending(list) => isAscending(result)` at recursive call sites |
| `SortedList.sortFiltered(list)` | postcondition exposes `isAscending(result)` directly from the recursive sorting producer |
| `SieveSequenceNextLevel.assertNextGapsAllPositiveGivenSortedBounds(seq)` | `sortFiltered` sortedness plus nonempty/range/head bounds imply `nextGaps(seq)` is positive |
| `SieveSequenceNextLevel.assertNextRotatedGapsAllPositiveGivenSortedBounds(seq)` | positive `nextGaps(seq)` implies `nextRotatedGaps(seq)` is positive by rotation preservation |
| `GapProperties.assertSurvivorValuesContainsNonMultipleAtPosition(ci,fv,start,count,pos)` | scanned non-multiple CI value is kept in `survivorValues` |
| `GapProperties.assertSurvivorValuesContainsOnlyNonMultiples(ci,fv,start,count,value)` | every value kept in `survivorValues` is a non-multiple |
| `GapProperties.assertSurvivorValuesExcludesMultipleAtPosition(ci,fv,start,count,pos)` | scanned multiple CI value is excluded from `survivorValues` |
| `GapProperties.assertAllMultiplesInRangeTail(ci,fv,from,until)` | tail of an all-multiple prefix remains all-multiple |
| `GapProperties.assertFirstSurvivorAtPosition(ci,fv,start,count,pos)` | if `[start,pos)` are multiples and `pos` survives, survivor head is `ci(pos)` |
| `GapProperties.assertSurvivorValuesSplitAtFirstPosition(ci,fv,start,count,pos)` | if `[start,pos)` are multiples and `pos` survives, survivors split at `ci(pos)` |
| `SpecDerivedSieveSequence.assertCycleSurvivorValuesStartAtSpecNextHead(count)` | cycle survivor scan starts with `spec.next.head.value` and splits at integral position 0 |
| `SpecDerivedSieveSequence.assertCycleSurvivorHeadMatchesSpecNext0(count)` | initial cycle survivor scan head equals `spec.next(0)` |
| `SpecSieveSequence.nextAcceptedOldIndex(nextSeq,k,period)` | exposes the next emitted `nextSeq` value as an old-stream index |
| `SpecSieveSequence.assertSkippedBeforeNextAcceptedOldIndexIsMultiple(nextSeq,k,idx,period)` | every old index skipped before `nextAcceptedOldIndex` is a multiple of the new front filter |
| `SpecDerivedSieveSequence.assertCycleIntegralSkippedRangeAllMultiples(currentOldIndex,fromPos,untilPos)` | translates spec skipped old indices into a cycle-integral all-multiple prefix |
| `SpecDerivedSieveSequence.assertCycleSurvivorValuesSplitAtNextAccepted(currentOldIndex,count)` | peels the next `spec.next` survivor from the cycle-integral survivor scan |
| `SpecDerivedSieveSequence.assertCycleNextAcceptedSurvivorMatchesSpecNext(currentOldIndex)` | value peeled by the cycle survivor scan equals the next value in `spec.next` |
| `SpecDerivedSieveSequence.assertCycleSurvivorTailHeadMatchesSpecNext(currentOldIndex,count)` | head of the remaining cycle survivor scan equals the following `spec.next` value |
| `SpecDerivedSieveSequence.assertCycleSurvivorWindowHeadMatchesSpecNext(specIndex,currentOldIndex,count)` | aligned survivor window head equals `spec.next(specIndex + 1)` |
| `SpecDerivedSieveSequence.survivorWindowCovers(specIndex,currentOldIndex,count,offset)` | raw old-window coverage predicate threaded by recursive ordered survivor equality |
| `SpecDerivedSieveSequence.assertCycleSurvivorWindowAtMatchesSpecNext(specIndex,offset,currentOldIndex,count)` | aligned survivor window at `offset` equals `spec.next(specIndex + offset + 1)` |
| `SpecDerivedSieveSequence.assertHeadPlusFilterModulusNotFrontMultiple()` | exposes that the period endpoint is not divisible by the next front filter |
| `SpecDerivedSieveSequence.initialSurvivorWindowCovers(count,offset)` | raw initial-window coverage predicate for direct survivor equality |
| `SpecDerivedSieveSequence.assertCycleSurvivorAtMatchesSpecNext(offset,count)` | initial survivor scan at `offset` equals `spec.next(offset)` |
| `SpecDerivedSieveSequence.assertInitialSurvivorGapMatchesSpecNextGap(k,count)` | adjacent initial survivor gap equals adjacent `spec.next` gap |
| `SpecDerivedSieveSequence.assertInitialSurvivorGapsFromValuesAtMatchesSpecNextGap(k,count)` | `gapsFromValues(initialSurvivors)(k)` equals adjacent `spec.next` gap |
| `SpecDerivedSieveSequence.assertInitialSurvivorGapListAtMatchesSpecNextGapList(k,count,nextPeriod)` | pointwise initial survivor gap list equals `spec.next.gapList` |
| `SpecDerivedSieveSequence.initialSurvivorGapListCovers(scanCount,from,gapCount)` | recursive adjacent-pair coverage predicate for survivor gap prefixes |
| `SpecDerivedSieveSequence.initialSurvivorGapList(from,gapCount,scanCount)` | forward gap prefix built from adjacent initial survivor values |
| `SpecDerivedSieveSequence.assertInitialSurvivorGapListMatchesNextGapList(from,gapCount,scanCount)` | survivor-gap prefix equals canonical adjacent next-gap prefix |
| `SpecDerivedSieveSequence.assertInitialSurvivorGapListMatchesSpecNextGapList(from,gapCount,scanCount)` | survivor-gap prefix equals `spec.next.gapList` |

Verifier-shape lesson from Phase E:

- The low-level gap arithmetic is now proved independently. The first two
  attempts at the next-level wrapper timed out only when Stainless had to expose
  `SortedList.isAscending(nextSorted(seq).list)` from the `SortedList` wrapper
  inside the larger VC.
- When a public wrapper around a recursive/private search is used in a
  postcondition, carry the recursive result as an explicit local invariant.
  Here, returning `skippedIsMultiple` from the branch that calls
  `assertSkippedIndexBeforeFirstIsMultiple` avoided a 300s postcondition
  timeout caused by Stainless trying to rediscover the branch fact through
  `nextAcceptedOldIndex`.
- Attaching strict sortedness to the recursive sorting producers with
  `.ensuring` turned the wrapper green without requiring strict sortedness as a
  local precondition. This confirms the next missing stepping stone is **not**
  gap positivity; it is a small upstream bridge that exposes the remaining
  sorted-output facts (`nonEmpty`, `allLessThan`, `head >= 0`) from the
  expand/filter/sort pipeline in a verifier-friendly shape.
- For the spec-to-cycle survivor bridge, the successful shape was to make the
  `spec.next` precondition bundle explicit before calling `nextAcceptedOldIndex`:
  lower bound for `next.accepts`, non-empty filter values, tail equality with
  `spec.filterValues`, head equality with `spec.head`, and the period
  non-multiple fact. Without those facts as local invariants, Stainless unfolded
  the search wrapper and timed out instead of reusing the already-verified
  skipped-index lemma.
- The next recursive ordered-survivor lemma must carry a raw old-window endpoint,
  not only a survivor offset. A condition such as `count > offset` is too weak:
  the cycle scan count measures old integral positions, while the survivor
  offset counts only retained values. The induction should thread an invariant
  of the form "the old index for the target `spec.next` value is inside
  `[currentOldIndex, currentOldIndex + count]`" so each recursive tail call can
  prove its own `nextAcceptedOldIndex(...)-1 < start + count` precondition.
- Do not equate `nextSeq.head.value` with `nextSeq.filterValues.head`. In a
  next-stage sequence, `nextSeq.head.value` is the next emitted prime/head,
  while `nextSeq.filterValues.head` is the old head/front filter. The verified
  contract shape is `nextSeq.filterValues.head == spec.head.value`, plus a
  separate lower bound `apply(k) >= nextSeq.head.value` before calling
  `nextSeq.accepts(apply(k))`. Expose the period-endpoint non-multiple fact
  with `assertHeadPlusFilterModulusNotFrontMultiple()` instead of rediscovering
  it at every recursive-search call.
- For recursive list lifts over survivor gaps, make the coverage invariant
  first. `initialSurvivorGapListCovers(scanCount,from,gapCount)` records the
  adjacent-pair coverage needed by every gap in the prefix; with that predicate
  available, `initialSurvivorGapList` and the list equality
  `assertInitialSurvivorGapListMatchesSpecNextGapList` verify as simple
  same-shape recursions rather than a generic list extensionality problem.
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
  postconditions, re-run the focused non-debug verify for a clean result.

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
  for the standard pipeline. The sorting, gap arithmetic, and rotation parts have
  supporting lemmas written; only the remaining range/head bridge is open.
  (Re-verify each before relying on it — status claims here have gone stale before.)

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
-

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
| `ListRepeatProperties.assertRepeatAllGreaterThan` | repeating a positive-bounded list preserves the bound |
| `ModOperations.modByPositiveMultipleThenBase(a,base,times)` | `mod(mod(a, base * times), base) == mod(a, base)` for positive `base,times` |
| `MemCycleProperties.assertRepeatedValuesCycleMatches(cycle,repeatedCycle,times,position)` | a `MemCycle` backed by repeated values has the same lookup as the original cycle |
| `CycleIntegralProperties.assertRepeatedValuesIntegralMatches(cycleIntegral,repeatedCycleIntegral,times,position)` | repeated physical cycle values preserve the recursive integral with the same initial value |
| `SpecDerivedSieveSequence.repeatedCycle(times)` | constructs the repeated physical gap storage for B |
| `SpecDerivedSieveSequence.assertRepeatedGapListIndexMatches(times,index)` | repeated gap list indexing agrees with the original periodic gap lookup |
| `SpecDerivedSieveSequence.assertRepeatedCycleGapMatches(times,position)` | repeated B gap-cycle lookup equals original B gap-cycle lookup |
| `SpecDerivedSieveSequence.assertRepeatedCycleIntegralMatches(times,position)` | repeated B integral lookup equals original B integral lookup |
| `SpecDerivedSieveSequence.assertRepeatedCycleApplyMatches(times,k)` | repeated B sequence apply equals original B sequence apply |

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

- `assertModulusPositive()`
- `assertPrimesTailValuesPositive()`
- `assertHeadPositive()`
- `assertModulusTimesHeadPositive()`

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
-

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

- `just verify assertNextPipelineGapsPositiveFromSpec`
- `just verify nextPipelineGapCycleIfMatchesSpec`

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

`assertCycleHeadMatchesSpecHead` — `cycle.head == spec.head.value` via `assertApplyMatches(0)`.

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
- Progress: `GapProperties` now has the value-level exactness pair for
  `survivorValues`: scanned non-multiples are kept, kept values are
  non-multiples, and scanned multiples are excluded. This avoids a dependency
  cycle because `GapProperties` can consume `CycleIntegralFilterProperties`
  without the lower filter module depending back on gap wrappers.
- Remaining bridge: position/index exactness for consecutive survivors. The
  current exactness lemmas prove membership/exclusion by value; the merge-sum
  theorem still needs the original positions `i < j` for adjacent survivors.
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

---

## ⬇ Reference & History (context only — the active plan is at the top)

Everything below is background. **Do not start a session here.** It is preserved
because the proven-fact tables and dependency analysis have lasting value, but
it accreted over many attempts and contains stale framing. The three sections
worth jumping to from here:

- **`## The Correct Track`** — the full contract-migration recipe (Group 1/2/3
  function lists, require-diff tables, validation gate).
- **`## NEW APPROACH: SieveCycleAfterProof`** — the value-level alternative and
  its remaining bridge.
- **`## Approach Comparison & Recommendation`** — the decision frame and the
  failure signals for when to pivot between the two.

When in doubt, trust the START HERE section at the top over anything below.

## Questions

1. Should `nextFromCycle()` accept `nextPeriod` as a parameter (like `nextVerified`), or compute it from the cycle size?
   - Current cycle's period = `head * gapCycle.size`
   - Next cycle's period = `newHead * newGapCycle.size`
   - But newGapCycle isn't known until after the pipeline runs
   - Propose: `nextPeriod` stays as parameter, same as `nextVerified`

## Recovery Log (2026-07-03): Contract-Shape Migration Broke HEAD

### What happened
HEAD (`d97bffcb`) was **red**. A previous editor began a contract-shape
migration of five functions in `SpecSieveSequence` (A) and left it half-finished
across two commits, then abandoned the work mid-migration in the working tree.

**OLD (green) shape** — uniform in `5145c1e5`:
- `require(nextSeq.head.value == head.value)`

**NEW (in-progress) shape** — in `nextAcceptedOldIndex` and 4 siblings:
- `require(nextSeq.filterValues.head == head.value)`
- `require(apply(k) >= nextSeq.head.value)`

### Root cause: the migration was coupled across A and B
Commit `cb49ccf2` did TWO things at once:
1. Started migrating the **callee** `nextAcceptedOldIndex` (+4 siblings) in A to
   the NEW shape, but did NOT migrate the A-side **callers** (`mergedGapPrefix`,
   `assertMergedGapPrefixAllPositive`, etc.).
2. Simultaneously **added** B's survivor-window lemmas (`survivorWindowCovers`,
   `initialSurvivorWindowCovers`, `assertCycleSurvivorWindow*`), which were
   *written against the NEW shape* (e.g. `survivorWindowCovers` line 730:
   `require(spec.next.filterValues.head == spec.head.value)`).

Result: A-side callers with the OLD (weak) shape could not discharge the NEW
(strong) callee precondition → TIMEOUT at `SpecSieveSequence.scala:2755`
(`assertMergedGapPrefixAllPositive` calling `nextMergedGapOldIndex`,
precondition 5/9). The working-tree changes were an unfinished attempt to finish
the same migration.

### Why a surgical A-only revert was insufficient
Reverting only A's 5 functions to the OLD shape (verified: the one A-side
timeout cleared) immediately surfaced a **second** timeout in B:
`SpecDerivedSieveSequence.scala:869` (`initialSurvivorWindowCovers` calling
`survivorWindowCovers`, which calls the now-OLD-shape `nextAcceptedOldIndex`).
B's lemmas genuinely depend on the NEW shape — they cannot be re-activated
against the OLD shape.

### Recovery actions taken
1. Tagged the broken HEAD: `git tag pre-recovery-snapshot d97bffcb` (all new
   code preserved, recoverable).
2. Stashed the uncommitted working-tree changes (named stash `{0}`).
3. Discovered `cb49ccf2` + `d97bffcb` touched **only** A, B, and 3 markdown
   files. Since B's changes were additive (new survivor lemmas) + the same
   migration, restoring **both** A and B to the last green commit `5145c1e5`
   was the clean fix (no commented-out code needed).
   - `git restore --source=5145c1e5 --worktree <file>` for B (A already reverted
     by editing the 5 require blocks). `git restore` is NOT in the opencode.json
     deny list (only `checkout`/`revert`/`push --force`/`rm` are).
4. Verified green via `just verify-ch 6` (0 invalid, 0 unknown). Committed as
   `bd444a35`.
5. Re-activated the ONE migration-independent leaf lemma from `cb49ccf2`:
   `assertHeadPlusFilterModulusNotFrontMultiple` (self-contained, no
   migration-shape require). Verified green; committed as `49c79b58`.

### Current state
- **HEAD = `49c79b58`** — green (5199/5199). Contains the green baseline plus
  the one safe leaf lemma.
- `pre-recovery-snapshot` tag → `d97bffcb` (broken HEAD, all new code).
- Stash `{0}` → the editor's uncommitted working-tree changes.
- Commits `cb49ccf2`, `d97bffcb` → the 12 remaining survivor lemmas (in history).

### Deferred work (needs a properly-scoped change)
The **12 remaining survivor lemmas** (~635 lines) are coupled to the contract
migration. They are stored in commits `cb49ccf2`/`d97bffcb` and tag
`pre-recovery-snapshot`, and are NOT in the current code. To bring them back,
follow **The Correct Track** below — do NOT improvise, do NOT migrate one
function at a time, do NOT commit a red state.

---

## The Correct Track — read this before touching the migration

This is the step-by-step recipe to redo the contract migration so it stays
green end-to-end. The previous editor got lost by migrating the callee alone
and committing red. **Every step ends green or you revert.**

> **Why this matters (the dependency on the Santa Claus List).** The 12 deferred
> Group-3 lemmas are the bridge from per-position survivor matching to list-level
> gap equality. The final one, `assertInitialSurvivorGapListMatchesSpecNextGapList`,
> is what lets the pipeline output be compared list-by-list to
> `spec.next.gapList`. Without these, the M3 pipeline-output theorem can only be
> attacked value-by-value, which is the fragile cross-instance path that times
> out. So the migration is not cosmetic — it unblocks the cheapest known route
> through M3 ladder step 6.

### Background: what the migration is
Two `require` shapes for the next-stage bridge functions in
`SpecSieveSequence` (A):

- **OLD shape (current, green):** `require(nextSeq.head.value == head.value)`
- **NEW shape (target):**
  `require(nextSeq.filterValues.head == head.value)` +
  `require(apply(k) >= nextSeq.head.value)` (the latter only where the body
  calls `nextSeq.accepts(apply(k))`)

The OLD shape is *mathematically weaker* (`head.value != filterValues.head` in
general — see LEARNINGS 18.6). The NEW shape is the correct one but is
backwards-incompatible: every caller must be upgraded to supply the stronger
facts. That is why this must be done as one atomic change.

### The four groups that must move together (all or nothing)
Before writing any code, confirm these lists with `grep`. They are the complete
dependency closure of the migration.

**Group 1 — A-side callees to migrate to NEW shape (5 functions):**
- `SpecSieveSequence.assertAcceptedByNextWhenOldAcceptedAndNewHeadNonMultiple`
- `SpecSieveSequence.assertNextAcceptedImpliesOldAcceptedAndNewHeadNonMultiple`
- `SpecSieveSequence.nextMergedGapOldIndex` (private)
- `SpecSieveSequence.nextAcceptedOldIndex`
- `SpecSieveSequence.assertSkippedBeforeNextAcceptedOldIndexIsMultiple`

Per-function require diff (line numbers verified at green HEAD):

| # | Function (line) | OLD require | NEW require | Add lower bound? |
|---|---|---|---|---|
| 1 | `assertAcceptedByNextWhenOldAcceptedAndNewHeadNonMultiple` (L1133) | `nextSeq.head.value == head.value` | `nextSeq.filterValues.head == head.value` | No — takes `value: BigInt`, not `apply(k)` |
| 2 | `assertNextAcceptedImpliesOldAcceptedAndNewHeadNonMultiple` (L1166) | `nextSeq.head.value == head.value` | `nextSeq.filterValues.head == head.value` | No — takes `value: BigInt`, not `apply(k)` |
| 3 | `nextMergedGapOldIndex` (L2539) | `nextSeq.head.value == head.value` | `nextSeq.filterValues.head == head.value` | **Yes** — body calls `nextSeq.accepts(apply(k))` |
| 4 | `nextAcceptedOldIndex` (L2599) | `nextSeq.head.value == head.value` | `nextSeq.filterValues.head == head.value` | **Yes** — delegates to `nextMergedGapOldIndex` |
| 5 | `assertSkippedBeforeNextAcceptedOldIndexIsMultiple` (L2640) | `nextSeq.head.value == head.value` | `nextSeq.filterValues.head == head.value` | **Yes** — calls `nextAcceptedOldIndex` |

**Group 2 — A-side direct callers that must be upgraded in lockstep:**
These call a Group-1 callee and were the actual timeout site last time:
- `SpecSieveSequence.mergedGapPrefix` (calls `nextMergedGapOldIndex`)
- `SpecSieveSequence.assertMergedGapPrefixAllPositive` (calls `nextMergedGapOldIndex`)
- `SpecSieveSequence.assertMergedGapPrefixHeadMatchesNext` (calls `nextMergedGapOldIndex`)
- `SpecSieveSequence.assertMergedGapPrefixMatchesNext` (calls `nextMergedGapOldIndex`)

Per-function require diff (line numbers verified at green HEAD). All four get
BOTH the filterValues-head swap AND the lower bound:

| # | Function (line) | OLD require | NEW require | Add lower bound? |
|---|---|---|---|---|
| 6 | `mergedGapPrefix` (L2697) | `nextSeq.head.value == head.value` | `nextSeq.filterValues.head == head.value` | **Yes** — calls `nextMergedGapOldIndex` |
| 7 | `assertMergedGapPrefixAllPositive` (L2742) | `nextSeq.head.value == head.value` | `nextSeq.filterValues.head == head.value` | **Yes** — calls `mergedGapPrefix` |
| 8 | `assertMergedGapPrefixHeadMatchesNext` (L2786) | `nextSeq.head.value == head.value` | `nextSeq.filterValues.head == head.value` | **Yes** — calls `mergedGapPrefix` |
| 9 | `assertMergedGapPrefixMatchesNext` (L2826) | `nextSeq.head.value == head.value` | `nextSeq.filterValues.head == head.value` | **Yes** — calls `mergedGapPrefix` |

> **Lower-bound caveat (corrects a common misconception).** The four Group-2
> callers already carry `require(nextSeq.accepts(apply(k)))`. It is tempting to
> think that `accepts` *implies* `apply(k) >= nextSeq.head.value`, so the new
> lower-bound require comes for free. **It does not.** `accepts(value)` itself
> has `require(value >= head.value)` (SpecSieveSequence L163-164) — i.e. the
> lower bound is a *precondition of* `accepts`, not a consequence of it. So each
> Group-2 caller must derive `apply(k) >= nextSeq.head.value` independently
> (e.g. from an existing monotonicity lemma, or a local `assert(...)`) and add
> it as an explicit require. Do not assume the solver connects these on its own.

(Other A-side callers of the Group-1 acceptance bridges —
`assertNextValueAtOrBeforeFirstSurvivor`,
`assertNextSuccessorOldIndexAfterAnchor`,
`assertFirstSurvivorAtOrBeforeNextValue`,
`assertPeriodBoundIsNonNonMultiple`,
`assertSkipUntilNonMultiple` — were green in both shapes last time; re-check them
with `just verify` but they likely need no change.)

**Group 3 — B-side lemmas written against the NEW shape (12 functions):**
Restored verbatim from `pre-recovery-snapshot` (lines ~716-1190 in
`SpecDerivedSieveSequence.scala`). They call `spec.nextAcceptedOldIndex` and
internally `require(spec.next.filterValues.head == spec.head.value)`, so they
ONLY compile-and-prove once Group 1 is NEW-shape.
- `survivorWindowCovers`, `initialSurvivorWindowCovers`,
  `assertCycleSurvivorWindowHeadMatchesSpecNext`,
  `assertCycleSurvivorWindowAtMatchesSpecNext`,
  `assertCycleSurvivorAtMatchesSpecNext`
- `assertInitialSurvivorGapMatchesSpecNextGap`,
  `assertInitialSurvivorGapsFromValuesAtMatchesSpecNextGap`,
  `assertInitialSurvivorGapListAtMatchesSpecNextGapList`,
  `initialSurvivorGapListCovers`, `initialSurvivorGapList`,
  `assertInitialSurvivorGapListMatchesNextGapList`,
  `assertInitialSurvivorGapListMatchesSpecNextGapList`

**Group 4 — already re-activated, leave alone:**
- `SpecDerivedSieveSequence.assertHeadPlusFilterModulusNotFrontMultiple`
  (leaf, migration-independent, green at HEAD `49c79b58`).

### The recipe (do ALL of 1-4 in one working tree before verifying)
1. **Branch off the current green HEAD** (`49c79b58` or later). Tag it:
   `git tag migration-attempt-<date> HEAD`.
2. **Migrate Group 1 + Group 2 in A together** — edit all 9 functions' require
   blocks (5 callees to NEW shape, 4 callers upgraded to supply the NEW facts).
   Do this in one editing pass; do not verify until Step 3.
3. **Restore Group 3 into B** from the snapshot:
   `git show pre-recovery-snapshot:src/main/scala/v1/chapter6/seq/sieve/SpecDerivedSieveSequence.scala`
   and copy out the 12 functions (lines ~716-1190) into the current B, placing
   them after `assertHeadPlusFilterModulusNotFrontMultiple` / the survivor-scan
   lemmas as in the snapshot. Do NOT re-add the deleted OLD-shape
   `require(spec.next.head.value == spec.head.value)` lines — those were the
   point of the migration.
4. **`just verify-ch 6`** (full chapter, NOT focused). Expected: green
   (`invalid: 0 unknown: 0`), with all 12 Group-3 functions present and valid.

### If it goes red
- **Do NOT commit. Do NOT "finish it later."** That is exactly what broke HEAD.
- `git restore --source=49c79b58 --worktree <both files>` to return to green.
- Read the SPECIFIC timeout VC. If it's a Group-2 caller failing a Group-1
  callee precondition, that caller needs an additional fact (likely derivable
  from `assertHeadPlusFilterModulusNotFrontMultiple()` or the existing
  acceptance-bridge lemmas) — add it as a local `assert(...)`, not a new
  `require`.
- If after 3 attempts it's still red, STOP and ask for help (project rule
  `stop-and-ask`). Report the failing VC verbatim.

### Validation gate (what "done" means)
- `just verify-ch 6` → `invalid: 0 unknown: 0`.
- The 12 Group-3 functions each appear with `valid` status in the log.
- `OBJECTS.md`: un-strike the 12 DEFERRED rows (revert the 2026-07-03 edit).
- Commit as ONE commit with a message listing all migrated functions.

### Lessons
- **A contract migration must move callee + ALL callers + dependent lemmas in
  one green-to-green change.** Doing the callee alone leaves callers unable to
  discharge the stronger precondition. (Now LEARNINGS 18.8.)
- **When two files are touched by the same commit, suspect coupling.** The
  migration was not independent of B's new lemmas.
- The leaf lemma `assertHeadPlusFilterModulusNotFrontMultiple` is the *correct*
  fact that replaces the false assumption `nextSeq.head.value ==
  nextSeq.filterValues.head` (LEARNINGS 18.6) — keep it independent of the
  migration so it stays green regardless of shape.
- **Mid-migration states are red by construction.** Never commit one. Verify the
  whole chapter, not just the touched function (focused runs hide cross-file
  breakage).

---

## NEW APPROACH: `SieveCycleAfterProof` (2026-07-03)

**Status:** 5 lemmas verified, 0 contract migration needed. See `SieveCycleAfterProof.scala`.

### Motivation

The contract migration (Groups 1-3 above) was **abandoned after it broke HEAD**.
Note: HEAD broke because the migration was left *half-finished* (callee migrated,
callers and B-side lemmas not — see the Recovery Log above), **not** because the
survivor math timed out. The 12 deferred lemmas *did* focused-verify (94/94,
128/128, etc.); only the wiring was broken. That framing matters: the math is
not disproven, the engineering procedure was. The Correct Track recipe above
documents the fix.

Separately, two genuine mathematical obstacles exist in the *index-based* proof
style — recursive integral monotonicity (`assertCycleIntegralIncreasing`) times
out for symbolic positions, and cross-instance `accepts` calls unfold and time
out (LEARNINGS §18.1). The new value-level approach below is an attempt to route
around those obstacles rather than pay the migration cost. Whether it clears the
harder rungs (ordered equality, gap equality, rotation) is **not yet known** —
see the Approach Comparison section at the end of this ticket.

### Core idea

Replace the index-based `nextAcceptedOldIndex` with a direct **value-level scan** through the cycle integral, filtering by the new filter head. The scan is bounded by the repeated-gap cycle (`head.value` repetitions) — proven finite by existing arithmetic lemmas (`assertHeadPlusFilterModulusNotFrontMultiple`, distinct-prime coprimality).

### Verified lemmas (value-level, no contract migration)

| Function | What it proves | Techniques |
|----------|----------------|------------|
| `assertCycleSurvivorCoprimeToCyclePrimes` | Every cycle-integral survivor (not divisible by head) is coprime with all primes | `assertCycleValueCoprimeToTail` + `mod(survivor, head) != 0` |
| `assertSpecNextFilterEqCyclePrimes` | `spec.next.filterValues == cyclePrimes` | `assertPrimesMatch`, prime list chain through spec |
| `assertCycleSurvivorCoprimeToSpecNextFilter` | Every survivor is coprime with `spec.next.filterValues` | Combines the two lemmas above |
| `assertCycleSurvivorPassesSpecNextFilter` | Every survivor passes `spec.next.passesFilter` | Coprimality lemma + `passesFilter` delegation (avoids `accepts` >= precondition) |
| `assertFirstSurvivorEqualsSpecNextHead` | `cycle.integral(0) == spec.next.head.value` | `assertNextHeadMatches`, `assertApplyMatches(1)` |

### Timeout obstacles found

1. **`CycleIntegralProperties.assertCycleIntegralIncreasing`** — recursive induction on integral positions times out for symbolic `pos`. This blocks the `>=` precondition in `spec.next.accepts(survivor)`.
2. **`SpecCycleSieveEquivalence.assertNextAcceptsMatchesCyclePrimesCoprime`** — cross-instance call timeout (LEARNINGS §18.1 pattern). Calls `spec.next.accepts(value)` inside SpecCycleSieveEquivalence, which triggers full unfold.
3. **Workaround**: Use `spec.next.passesFilter` directly (no `>=` precondition), proving filter-passing through coprimality + filter-equality chains.

### Remaining bridge to full theorem

`nextRotatedGaps(cycle) == spec.next.gapList(0, nextPeriod)` needs:

1. Prove `nextSorted.list` survivors are the same values as `spec.next(i) - head` after rotation alignment
2. Prove gap lists match (inner + wrap gaps)

Key risks: rotation-index proof (may trigger recursion timeout), sorted-list survivor ordering vs spec.next ordering.

### Updated phase plan

| Phase | What | Status |
|-------|------|--------|
| 1 | `SieveCycleAfterProof` coprimality + filter lemmas | **5/5 verified** |
| 2 | Prove `nextSorted.list` survivors = `spec.next` values (ordered) | NOT STARTED |
| 3 | Prove gap equality from value equality | NOT STARTED |
| 4 | M4: C uses pipeline | NOT STARTED |
| (alt path) | Contract migration (Groups 1-3) | **PAUSED, not disproven** — broke HEAD from a wiring bug; 12 lemmas written (need re-verification). See Approach Comparison below. |

Which path is *active* is a decision, not settled — see **Approach Comparison &
Recommendation** below. Do not assume value-level has won just because it is the
most recent commit; it has proven less of the ladder so far.

---

## Approach Comparison & Recommendation (2026-07-03)

This section is the decision frame for the two paths. Read it before choosing.

### They are not two ways to prove the same lemma

The two approaches target **different rungs of the M3 ladder** (see the Santa
Claus List above):

- **Old (contract migration)** is a *refactor of the spec-side bridge* so that
  12 already-written survivor-window lemmas can be re-activated. Those lemmas
  prove `cycleSurvivor(i) == spec.next(i)` — **ladder step 6 (ordered survivor
  equality)** — via index/old-stream machinery. The migration is plumbing; it
  does not itself prove the pipeline equality, it unblocks the existing step-6
  proof.
- **New (`SieveCycleAfterProof`)** is a *fresh value-level proof* that bypasses
  the index machinery. Its 5 verified lemmas establish survivor ⟹ coprime ⟹
  passes `spec.next.passesFilter` — **ladder steps 3-5 (filter-decision +
  membership)**, done a different way. It has **not yet reached step 6, nor
  steps 7-11** (ordered equality, sort bridge, gap equality, rotation).

So the "94/94, 128/128" focused-verify numbers (old) and the "5/5 verified"
numbers (new) measure **different things**. Both can be true without
contradiction. Comparing them as if they were head-to-head is the first trap.

### What each is actually blocked on

| | Old (contract migration) | New (SieveCycleAfterProof) |
|---|---|---|
| Done | 12 lemmas written (red globally only due to migration; need re-verification) | 5 lemmas written, globally green |
| The wall | **Mechanical**: 9 coupled `require` changes across 2 files; one misstep breaks HEAD. **Known fix** (Correct Track recipe). | **Mathematical**: rotation-index proof + sorted-survivor ordering vs `spec.next` ordering. **Unknown if provable.** |
| Risk shape | High *engineering* risk, low *mathematical* risk. Math is already proven; only wiring is broken. | Low *engineering* risk, high *mathematical* risk. Hard part still ahead and looks like known-timeout territory. |
| Reaches final theorem? | Yes — once green, step 6 is done; steps 7-11 remain (always needed). | Unknown — steps 6-11 all ahead; step 6 must be re-derived in value-level style. |

### The decisive fact

**The new approach has proven less of the ladder than the old one, not more.**
`SieveCycleAfterProof`'s filter-passing result is a *prerequisite* of ordered
survivor equality — the old approach's 12 lemmas assume that territory and go
further. The new approach is currently at "survivors pass the filter," which is
necessary but not sufficient. It still has to clear the *same ordering/gap/
rotation wall* the old approach was trying to short-circuit — and the ticket
itself flags that wall as the likely timeout region (Risk §2: "might hit the
same list-equality wall as the walk"; the walk timed out 6 times).

The `passesFilter`-instead-of-`accepts` workaround (avoiding the `>=`
precondition) is genuinely clever and removes **one** obstacle. But it removes
an obstacle on the **easy part** (filter membership). The hard part (ordered
equality, gap equality, rotation) is still entirely unproven in the new style.

### Recommendation: hedge, old first

The new approach is the right **insurance policy**, but it should not yet
replace the old approach as the active path.

1. **Don't abandon written math.** The old approach's 12 lemmas are real,
       written progress on step 6. The new approach would have to
   re-derive that from scratch in a style whose hard cases are untested.
2. **The old approach's blocker is mechanical and now has a checklist.** The
   Correct Track recipe turns "9 coupled changes" into an ordered procedure
   with a validation gate. The risk was *procedural* (a dev got lost), not
   *mathematical*. With the procedure written down, that risk is far lower.
3. **The new approach's blocker is mathematical and unknown.** "5/5 verified"
   is evidence the approach-to-the-wall is clean, not that the wall is
   scalable.
4. **Run them as a hedge, old first.** Try the migration (now well-specified;
   unblocks the most proven work). If green, the 12 lemmas are back and step 6
   is done. If the migration *or* the re-activated lemmas reveal a deeper
   timeout, pivot to value-level — and the 5 green `SieveCycleAfterProof`
   lemmas are a reusable foundation either way.

### Concrete failure signals (when to pivot)

- **Old approach → pivot to new if:** after a Correct-Track migration,
  `assertCycleSurvivorWindowAtMatchesSpecNext` or
  `assertInitialSurvivorGapListMatchesSpecNextGapList` times out *even with the
  correct preconditions*. That means the index-based step-6 proof itself does
  not scale, and the value-level style is worth the re-derivation cost.
- **New approach → do not keep hammering if:** the rotation-index lemma or the
  sorted-survivor-ordering lemma times out. That is the known wall. It means
  *neither* approach clears step 7+ cheaply, and the real decision becomes
  whether a third representation is needed (e.g. per-position apply equality
  rather than list equality — the Risk §2 fallback).

### Reusable regardless of path

`assertHeadPlusFilterModulusNotFrontMultiple` (already re-activated, green) and
the 5 `SieveCycleAfterProof` lemmas are **path-independent** — neither depends
on the contract-shape debate. Keep them regardless of which path is chosen.

---

## Failure log — what was tried and why it didn't work

Purpose: **break the circles.** Before re-attempting something, check it isn't
already on this list. Each entry names the dead end, the mechanism, the lesson,
and — where known — the fix that eventually worked. Newest last. (No verify
counts — see the documentation rule in START HERE.)

### F1. Survival-walk list equality (Leg 4) — list extensionality wall
- **Tried:** prove `nextGapsWalk(cycle) == spec.next.gapList(0, nextPeriod)`
  directly, in `SieveSequenceNextLevel` / `SpecCycleSieveEquivalence`.
  Attempted ~6 times across `sieve-sequence-proof.md` (Leg 4).
- **Mechanism:** the walk's `collectGaps` is opaque from outside its recursion,
  so Stainless cannot relate the constructed list to the spec gap list. List
  extensionality over differently-shaped recursions is a genuine SMT weak spot.
- **Lesson:** do not compare *completed constructed lists* of different
  recursion shapes. Either (a) prove correspondence *inside* the recursion via
  an invariant-carrying walk, or (b) avoid list equality entirely and prove
  per-position apply equality.
- **Current status:** deferred. The pipeline approach (this ticket) replaced
  the walk, but M3 risks the same wall — see Risk §2 and the fallback there.

### F2. `GapCycle(newGaps)` constructor positivity — call-site positivity wall
- **Tried:** `nextFromCycle` builds `GapCycle(nextRotatedGaps(cycle))`; the
  `GapCycle` constructor requires `allGreaterThan(gaps, 0)`.
- **Mechanism:** Stainless cannot prove the rotated gaps are positive *at the
  constructor call site*, even though positivity is provable from sortedness +
  bounds in isolation. The constructor obligation forces re-unfolding the whole
  pipeline instead of reusing the sortedness fact.
- **Fix that worked (partial):** isolate the equality from the constructor —
  `nextPipelineGapCycleIfMatchesSpec(nextPeriod)` takes the producer-equality
  as a precondition, so the hard theorem and the constructor obligation are
  separated. Also: `.ensuring` sortedness on the recursive sort *producers*
  (`sortFiltered`, `insertSorted`) lets the wrapper reuse the fact instead of
  re-deriving it (LEARNINGS 18.4). Remaining gap: the range/head bridge
  (`nonEmpty`, `allLessThan`, `head >= 0`) from the filter pipeline.

### F3. Repeated-cycle global postconditions — chapter-6 unwinding wall
- **Tried:** prove repeated-`CycleSieveSequence.apply` equality directly in
  chapter 6. Timed out on final postconditions.
- **Mechanism:** the chapter-6 apply proof lowers `apply(k)` to
  `integral(k - 1)`; doing the repeated-cycle invariance at the sequence level
  forces Stainless to unwind through the integral recursion it can't see inside.
- **Fix that worked:** push the representation-invariance facts *down* into
  chapter 4 (`MemCycle`, `CycleIntegral`) where each representation proves its
  own repeated-cycle invariance directly; chapter 6 only composes. Pattern:
  representation facts belong in the lowest chapter that can state them.

### F4. Contract migration committed mid-flight — broke HEAD red
- **Tried (2026-07-03):** migrate `nextAcceptedOldIndex` + 4 siblings to a
  stronger `require` shape across two commits, leaving callers and B-side
  dependent lemmas un-migrated.
- **Mechanism:** a stronger precondition is backwards-incompatible. Callers
  with the old (weak) shape cannot discharge the new (strong) callee
  precondition → timeout at `assertMergedGapPrefixAllPositive`. Committing the
  callee migration without the callers = red by construction.
- **Lesson:** a precondition migration must move callee + ALL callers +
  cross-file dependent lemmas in **one** green-to-green change. Never commit a
  mid-migration state. (Now LEARNINGS 18.8 + the Correct Track recipe above.)
- **Outcome:** recovered by restoring both files to the last green commit
  (`5145c1e5`); tag `pre-recovery-snapshot` preserves the broken state.

### F5. Symbolic-position integral monotonicity — induction wall
- **Tried:** `CycleIntegralProperties.assertCycleIntegralIncreasing` to supply
  the `survivor >= head` lower bound needed by `spec.next.accepts(survivor)`.
- **Mechanism:** recursive induction on `CycleIntegral` positions times out for
  symbolic `pos`. The monotonicity is true but the induction doesn't scale.
- **Workaround (new approach):** route around `accepts` entirely — use
  `spec.next.passesFilter` (no `>=` precondition) and prove filter-passing via
  coprimality. This removes the obstacle but only on the *easy* part (filter
  membership); the hard parts (ordered/gap/rotation equality) still face the
  same family of induction walls. Untested whether the new style clears them.

### F6. Cross-instance `accepts` call — LEARNINGS 18.1 wall
- **Tried:** `SpecCycleSieveEquivalence.assertNextAcceptsMatchesCyclePrimesCoprime`
  calls `spec.next.accepts(value)` from a different object → full unfold, timeout.
- **Mechanism:** cross-instance calls trigger Stainless to unfold the callee
  instead of reusing its contract, even for simple lemmas (LEARNINGS 18.1-18.3).
- **Workaround:** directed equality lemmas, explicit `require` for component
  equalities, avoid `val` aliases, and (per F5) prefer `passesFilter` over
  `accepts` to dodge the `>=` precondition that triggers the unfold.

### F7. Wrapper postcondition sortedness — producer-reuse wall
- **Tried:** wrappers around `nextSorted`/`SortedList` needed
  `isAscending(nextSorted(seq).list)` in their postconditions; timed out.
- **Mechanism:** Stainless re-instantiates the matcher and unwraps the pipeline
  (`nextSorted` → `SortedList.fromUnsorted` → `nextFiltered` → prime tails →
  recursive `isAscending`) instead of reusing the verified sortedness fact.
  Confirmed via `just verify-debug`.
- **Fix that worked:** attach strict sortedness to the recursive *producers*
  via `.ensuring` (`sortFiltered`, `insertSorted`), so the fact is in scope at
  the compositor site without unwinding (LEARNINGS 18.4). Also carry branch
  invariants explicitly out of recursive searches (LEARNINGS 18.5).
- **General lesson:** this is the canonical example of the debug-first method
  in START HERE — a "wall" that dissolved entirely once the missing producer
  postcondition was named. Most timeouts here look like this.

### Recurring theme
F2, F3, F6, F7 are all the *same* failure mode: **Stainless re-derives a fact
the proof never handed it.** F1 and F5 are closer to genuine SMT limits
(list extensionality, symbolic induction) — but even those should be audited
with `just verify-debug` before being accepted as real walls. **Default
assumption: a timeout is a missing named fact, not a math wall, until the
debug-first audit proves otherwise.**

### How to add to this log
When an attempt fails (3 strikes per the stopping rule), append an entry:
- **Tried:** the lemma/approach and where.
- **Mechanism:** what Stainless was doing when it timed out (cite the debug).
- **Lesson / fix:** what to do instead, or the lemma that unblocked it.
Do NOT record VC counts. Do NOT delete an entry when it's later solved —
mark it **Resolved (by ...)** so the dead-end knowledge persists.
