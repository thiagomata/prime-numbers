# Independent Next-Cycle Computation (B.nextFromCycle)

**Created:** 2026-07-01
**Updated:** 2026-07-01
**Status:** Plan phase

## Goal

Give B (`SpecDerivedSieveSequence`) a `nextFromCycle()` method that:
1. Computes the next stage's gap cycle **independently** by running the standard sieve pipeline (`SieveSequenceNextLevel` functions) on B's own cycle data.
2. After computation, **proves** the output matches A.next's properties (head equality, gap equality, apply equality).

This replaces the current `nextVerified`, which constructs B.next from A.next's data directly (delegation, not computation).

## Motivation

B should generate its next by performing the sieve process itself — residues, expand, filter, sort, gaps, rotate — just as the spec does conceptually, but on the cycle representation. This validates that the sieve algorithm, not just the spec's bookkeeping, produces correct next stages.

Once proven for B, C (`CycleSieveSequence`) can use the **same** `nextFromCycle()` and inherit correctness without needing a spec link.

## Current State

| Component | Status |
|-----------|--------|
| Pipeline functions (residues → expand → filter → sort → gaps → rotate) | Exist in `SieveSequenceNextLevel`, but preconditions undischarged |
| B.nextVerified | Exists — reads A.next directly (delegation) |
| B.nextFromCycle | Does NOT exist |
| Pipeline precondition lemmas for B.cycle | Do NOT exist |
| Pipeline output = A.next gap cycle lemma | Does NOT exist |
| Lemma 4a (survivors = A.next) | Proven in bridge |
| C.next() (walk-based) | Exists, unproven against spec |

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

Remaining independent-pipeline proof obligation:

- Prove or expose `ListBoundUtils.allGreaterThan(SieveSequenceNextLevel.nextGaps(seq), 0)`
  for the standard `nextGaps`/`calculateGaps` pipeline. Once that exists,
  `assertRotateAtPreservesAllGreaterThan(nextGaps(seq), nextHeadResidueIndex(seq), 0)`
  should bridge the `nextRotatedGaps` positivity part of the `GapCycle(newGaps)`
  timeout.

## Questions

1. Should `nextFromCycle()` accept `nextPeriod` as a parameter (like `nextVerified`), or compute it from the cycle size?
   - Current cycle's period = `head * gapCycle.size`
   - Next cycle's period = `newHead * newGapCycle.size`
   - But newGapCycle isn't known until after the pipeline runs
   - Propose: `nextPeriod` stays as parameter, same as `nextVerified`
