# Sieve Sequence Proof — Survival Walk Correctness

**Status:** Active
**Created:** 2026-06-24
**Updated:** 2026-06-28
**Owner:** `SpecDerivedCycleSieve` (`src/main/scala/v1/chapter6/seq/sieve/SpecDerivedCycleSieve.scala`)
**Umbrella design doc:** [`../sieve-sequence-epic.md`](../sieve-sequence-epic.md)

## EPIC Context (do not duplicate per-ticket)

A three-way connection between three sieve representations:

| Leg | Statement | Status |
|---|---|---|
| 1 | Spec is correct | ✅ Done (`SpecSieveSequence` linear scan) |
| 2 | Spec-derived Cycle ≡ Spec, current stage | ✅ Done (`SpecDerivedCycleSieve.assertApplyMatches(k)`: `cycle(k) == spec(k)`) |
| 3 | Canonical next cycle built from `spec.next` matches `spec.next` | ✅ Done (`assertNextCycleMatchesSpecNext`) |
| **4** | **Survival walk producer theorem: `nextGapsWalk(cycle)` emits `spec.next` gaps and `cycle.next()(k) == spec.next(k)`** | ❌ **This ticket** |
| 5 | `CycleSieveSequence` ≡ Canonical, using ONLY Cycle's structural rules (no Spec link) | Future |

**Key architectural fact (confirmed with user, 2026-06-24; renumbered 2026-06-28):** Canonical is *built around Spec by definition* and is allowed to use Spec freely. The "walks with its own legs" / "no Spec link" constraint applies to the future raw **`CycleSieveSequence`** refinement (Leg 5), not to Canonical (Leg 3) or the survival-walk bridge (Leg 4).

## Goal

Keep the Spec/Canonical/Cycle sieve-sequence proof organized around one
canonical active ticket.

The current verified result is:

```
SpecDerivedCycleSieve(spec.next, nextPeriod).cycle(k) == spec.next(k)
```

with matching head and gap list, under the existing next-stage preconditions.

The remaining unverified result is the **survival-to-gaps producer theorem**:
the concrete survival walk used by `CycleSieveSequence.next()` must be shown to
emit the same ordered gaps as `spec.next.gapList(0, nextPeriod)`.

Equivalently, prove that the **cycle strategy** — computing the next head and
next gaps from the cycle's own arithmetic — produces results that match what
`spec.next` produces:

```
next head:  cycle(1) == spec.next.head.value                          [already proven: assertNextHeadMatches]
next gaps:  <cycle strategy output> == spec.next.gapList(0, nextPeriod)   [open]
```

The "cycle strategy" is whichever verified idiom produces the next gap list from Canonical's own data and matches `spec.next.gapList`. Multiple idioms are admissible (per user guidance 2026-06-24, citing `RecursiveCycleMatchesModCycle`, `assertSimplifiedDiffValuesMatchCycle`, `ModIdempotence`).

## Current State

- **Next head:** Verified. `SpecDerivedCycleSieve.assertNextHeadMatches()` gives
  `cycle(1) == spec.next.head.value`. The pure cycle-arithmetic form
  `cycle(1) = cycle.head + cycle.gapCycle.memCycle(0)` is exposed by
  `CycleSieveSequence.assertNextHeadGreaterThanHead`.
- **Canonical next stage:** Verified. `assertNextCycleApplyMatchesSpecNext`,
  `assertNextCycleGapsMatchSpecNext`, `assertNextCycleHeadMatchesSpecNext`,
  and `assertNextCycleMatchesSpecNext` prove that the next canonical cycle
  built from `spec.next` matches `spec.next`.
- **Per-survivor bridges:** Verified. `assertSurvivorPositionMatchesSpecNext`
  and `assertSurvivorGapEqualsSpecNextGap` show that `spec.next` values occur
  at survivor positions of the current cycle and that adjacent survivor
  differences match adjacent `spec.next` gaps.
- **Survival-walk producer:** Open. No verified lemma currently proves
  `SieveSequenceNextLevel.nextGapsWalk(cycle) == spec.next.gapList(0, nextPeriod)`.
  No verified lemma currently proves `cycle.next()(k) == spec.next(k)`.

## Expected State

A verified Leg-4 bridge from the concrete survival walk to the canonical
`spec.next` stage.

The final theorem can be split in two layers.

### Layer A — Survival Walk Emits Spec Gaps

First prove that the concrete walk-backed gap producer emits the same ordered
gap list as the Spec next stage:

```
assertNextGapsWalkMatchesSpecNextGapList(nextPeriod)
  : SieveSequenceNextLevel.nextGapsWalk(cycle)
      == spec.next.gapList(0, nextPeriod)
```

under the period anchors:
```
period > 0
spec(period) == spec.head.value + spec.filterModulus
nextPeriod > 0
spec.next(nextPeriod) == spec.next.head.value + spec.next.filterModulus
spec.primes.nextPrime.value < spec.head.value * spec.head.value
```

### Layer B — Concrete `next()` Matches Spec Next

Then use Layer A to discharge the facts needed by `cycle.next()` and prove:

```
assertCycleNextApplyMatchesSpecNext(nextPeriod, k)
  : cycle.next()(k) == spec.next(k)
```

This should follow from:

1. `cycle.next().head == cycle(1) == spec.next.head.value`
2. `cycle.next().gapCycle.memCycle.values == spec.next.gapList(0, nextPeriod)`
3. the already verified reconstruction lemma for cycles built from Spec gaps
   (`assertNextCycleApplyMatchesSpecNext`)

## Leg 4 Math Plan — Survival Walk Prefix Invariant

The failed attempts compared the **completed** walked list against
`spec.next.gapList(...)` from outside:

```text
nextGapsWalk(cycle) == spec.next.gapList(0, nextPeriod)
```

That shape is too opaque because `collectGaps` hides the relationship between
its accumulator, its last survivor, and the number of emitted survivor gaps.
The next attempt should prove the correspondence **inside the recursion**.

Define an invariant-carrying walk with an explicit emitted survivor count:

```text
walkPrefix(lastSurvivor, lastPos, pos, remaining, emitted, gaps)
```

where:

- `gaps.reverse == spec.next.gapList(0, emitted)` after emitting `emitted`
  next-stage gaps;
- `lastSurvivor == spec.next(emitted)` when `emitted < nextPeriod`;
- `lastSurvivor == cycle(lastPos)` and `cycle(lastPos) == spec(lastPos)`;
- every scanned value between `lastPos` and `pos` that was not emitted is
  rejected by `spec.next`;
- when `cycle(pos + 1)` survives the new-head filter, it equals
  `spec.next(emitted + 1)` and the emitted gap is:

```text
cycle(pos + 1) - lastSurvivor
  == spec.next(emitted + 1) - spec.next(emitted)
  == spec.next.gapList(emitted, 1).head
```

The two branch obligations are:

### Skip Branch

If the current walked value is a multiple of the current head:

```text
Calc.mod(cycle(pos + 1), cycle.head) == 0
```

then `assertCurrentMultipleRejectedByNext(pos + 1)` proves it is rejected by
`spec.next`, so the emitted prefix does not change:

```text
emitted' = emitted
gaps' = gaps
lastSurvivor' = lastSurvivor
```

### Emit Branch

If the current walked value is not a multiple of the current head:

```text
Calc.mod(cycle(pos + 1), cycle.head) != 0
```

then `assertCurrentNonMultipleAcceptedByNext(pos + 1)` proves it is accepted by
`spec.next`. The missing local proof is that it is the **next** accepted value
after `lastSurvivor`, not merely some later accepted value. The likely bridge is
to combine:

- the recursive invariant that all skipped interior values were rejected;
- `SpecSieveSequence.indexOfAccepted` for `lastSurvivor`;
- `assertConsecutiveAcceptedByNextPreservesGap` or the existing merge/copy
  lemmas when the old-index relationship is visible.

When that bridge is established:

```text
cycle(pos + 1) == spec.next(emitted + 1)
gap = cycle(pos + 1) - lastSurvivor
    == spec.next(emitted + 1) - spec.next(emitted)
```

and the prefix advances:

```text
emitted' = emitted + 1
gaps' = gap :: gaps
lastSurvivor' = cycle(pos + 1)
```

## Draft Code Shape

This is a proof scaffold, not code to paste all at once. Add one helper or
postcondition at a time and verify between changes.

```scala
def collectGapsWithSpecPrefix(
  lastSurvivor: BigInt,
  lastPos: BigInt,
  pos: BigInt,
  remaining: BigInt,
  emitted: BigInt,
  gaps: List[BigInt],
  nextPeriod: BigInt
): List[BigInt] = {
  require(nextPeriod > BigInt(1))
  require(spec.next(nextPeriod) == spec.next.head.value + spec.next.filterModulus)
  require(remaining >= BigInt(0))
  require(pos >= BigInt(1))
  require(lastPos >= BigInt(0))
  require(lastPos < pos)
  require(emitted >= BigInt(0))
  require(emitted < nextPeriod)
  require(lastSurvivor == spec.next(emitted))
  require(cycle(lastPos) == lastSurvivor)
  require(gaps.reverse == spec.next.gapList(BigInt(0), emitted))
  require(ListBoundUtils.allGreaterThan(gaps, BigInt(0)))
  decreases(remaining)

  if (remaining == BigInt(0)) {
    gaps.reverse
  } else {
    val current = cycle(pos + BigInt(1))
    if (Calc.mod(current, cycle.head) == BigInt(0)) {
      assert(assertCurrentMultipleRejectedByNext(pos + BigInt(1)))
      collectGapsWithSpecPrefix(
        lastSurvivor,
        lastPos,
        pos + BigInt(1),
        remaining - BigInt(1),
        emitted,
        gaps,
        nextPeriod
      )
    } else {
      assert(assertCurrentNonMultipleAcceptedByNext(pos + BigInt(1)))

      // Missing bridge lemma:
      // current == spec.next(emitted + 1)
      assert(assertWalkSurvivorIsNextSpecValue(
        lastPos,
        pos + BigInt(1),
        emitted,
        nextPeriod
      ))

      val gap = current - lastSurvivor
      assert(gap == spec.next(emitted + BigInt(1)) - spec.next(emitted))
      assert(spec.next.assertGapListFirstEqualsGap(emitted, BigInt(1)))

      collectGapsWithSpecPrefix(
        current,
        pos + BigInt(1),
        pos + BigInt(1),
        remaining - BigInt(1),
        emitted + BigInt(1),
        gap :: gaps,
        nextPeriod
      )
    }
  }
}.ensuring(res =>
  ListBoundUtils.allGreaterThan(res, BigInt(0)) &&
  (emitted == nextPeriod ==> res == spec.next.gapList(BigInt(0), nextPeriod))
)
```

Expected supporting lemmas, in likely order:

1. `assertWalkInitialPrefix(nextPeriod)`
   - Shows the walk starts with `lastSurvivor == spec.next(0)` and an empty
     emitted prefix.
2. `assertWalkSkippedValueRejected(pos)`
   - Alias over `assertCurrentMultipleRejectedByNext(pos)` using the exact
     walk indexing convention.
3. `assertWalkSurvivorAccepted(pos)`
   - Alias over `assertCurrentNonMultipleAcceptedByNext(pos)`.
4. `assertWalkSurvivorIsNextSpecValue(lastPos, pos, emitted, nextPeriod)`
   - The key missing bridge: if all values between `lastPos` and `pos` were
     rejected and `cycle(pos)` is accepted, then `cycle(pos)` is
     `spec.next(emitted + 1)`.
5. `assertCollectGapsPrefixMatchesSpec(nextPeriod, emitted)`
   - Recursive invariant proof for the prefix-producing helper.
6. `assertNextGapsWalkMatchesSpecNextGapList(nextPeriod)`
   - Thin top-level wrapper, preferably after either replacing `nextGapsWalk`
     with the invariant-carrying helper or proving the helper has the same
     recursion/output shape as `nextGapsWalk`.

**Do not start with item 6.** The old attempts already showed that comparing
the completed walked list from outside times out. The next proof must expose
the prefix invariant inside the walk recursion first.

## Known Proof Idioms

| Idiom | Source | Shape | Trade-off |
|---|---|---|---|
| **Internal walk prefix invariant** | New Leg-4 helper around `SieveSequenceNextLevel.collectGaps` | Carries `emitted`, `lastSurvivor == spec.next(emitted)`, and `gaps.reverse == spec.next.gapList(0, emitted)` through the recursion | **Primary candidate for the next EPIC step.** The old outside comparison timed out; proving the prefix while the recursion is visible is the best next move. |
| **Diff-based induction** | `ClassicCycleIntegralProperties.assertDiffEqualsCycleValue` + `assertSameDiffAfterCycle` | `integral(k+1) - integral(k) == cycle(k+1)`; diffs repeat per period via `MemCycleProperties.valueMatchAfterManyLoopsInBoth` | Useful supporting arithmetic, but not enough by itself to certify `nextGapsWalk`, because the walk's `lastSurvivor` accumulator still needs an emitted-prefix invariant. |
| Merge via `indexOfAccepted` | `SpecSieveSequence.mergedGapPrefix` + `assertMergedGapPrefixMatchesNext` | Walks current stage's accepted indices, no positional scan over naturals | Verified on Spec; reusable as fallback. |
| Outside comparison of walk output | `SieveSequenceNextLevel.nextGapsWalk` after it returns | `val walked = nextGapsWalk(cycle); walked == spec.next.gapList(...)` | **Avoid.** Timed out repeatedly. The walk must expose correspondence through its own recursion or a same-shape verified helper. |

**Decision:** Pursue the **internal walk prefix invariant** first. Use
diff-based and `indexOfAccepted` lemmas only as supporting facts inside the
emit branch.

## Placement

- New proof lemmas live on **`SpecDerivedCycleSieve`** or a focused sibling/helper around `SieveSequenceNextLevel.collectGaps` if the walk needs an internal invariant. Avoid changing `CycleSieveSequence` itself until the walk producer facts are isolated.

## Alternatives Considered

1. Reuse `SpecSieveSequence.mergedGapPrefix` directly. Rejected as primary: it walks Spec's `apply`, which is fine for Canonical (Leg 3 may use Spec) but doesn't surface the cycle-arithmetic structure that the later raw Cycle refinement (Leg 5) will need. Keep as fallback.
2. Write a `CanonicalNextLevel` sibling object. Deferred — start with methods on `SpecDerivedCycleSieve`; refactor if it grows.
3. The residue pipeline (`nextRotatedGaps`). Rejected: `v0-v2-apply-equivalence.md` 2026-06-23 log shows the project deliberately de-prioritized residue-pipeline proofs.

## Risks and Assumptions

1. **Diff idiom applicability.** `assertSameDiffAfterCycle` proves `integral(pos+1)-integral(pos) == integral(pos+size+1)-integral(pos+size)`. This is a *single-period* shift. The next gap list spans `head` periods (one per value filtered by the new head). Need to confirm the diff idiom lifts cleanly across `head` periods, not just one.
2. **Cross-instance calls are expensive (LEARNINGS 18).** Canonical calling `spec.next.gapList` and `spec.next.indexOfAccepted` is a cross-instance call. Keep the number of such calls per lemma small; isolate them.
3. **Period anchor for the next stage.** `nextPeriod` must satisfy `spec.next(nextPeriod) == spec.next.head.value + spec.next.filterModulus`. This is the same shape as the current-stage anchor; carry it as a precondition.
4. **The product-not-divisible caveat** (`Calc.mod(SieveUtils.product(filterValues), head.value) != 0`) is still an open constructor obligation on `CycleSieveSequence`. Out of scope here; it is tracked in `../blocked/primorial-not-divisible-by-new-prime.md`.

## Validation

- `green-to-green`: check `verify.log` (do not re-run on clean state) before each code change; run full `just verify` after each non-markdown change.
- `small-changes`: ONE lemma/assertion per verify cycle.
- `stop-and-ask`: 3 failed attempts on a lemma → stop, paste the error, ask.
- Mirror the structure of existing verified cycle lemmas (`ClassicCycleIntegralProperties`, `SpecSieveSequence.assertMergedGapPrefixMatchesNext`) per PROOF_GUIDE.

## Related Tickets

- `../done/canonical-spec-to-cycle-alignment.md` — Leg 2 (canonical construction + current-stage equivalence). Its Lemma 5 (gap-walk equality) is superseded in scope by this ticket's diff-based approach, but the proof log remains useful.
- `../superseded/v0-v2-apply-equivalence.md` — older overall Spec/Cycle equivalence plan; documents the residue-vs-walk decision and the conditional next bridge.
- `../superseded/remove-extern-from-next.md` — old `CycleSieveSequence.next()` removal framing. The surviving issue is the walk producer theorem listed here.
- `../superseded/walk-based-pipeline.md` — failed walk approach to avoid.
- `../blocked/prove-apply1-is-prime.md` — hard "prime before p squared" wall. Keep separate from equivalence unless a future proof actually needs primality.
- `../blocked/primorial-not-divisible-by-new-prime.md` — hard Euclid-lemma/product wall.

## Update Log

### 2026-06-29 — Canonical bridge renamed to SpecDerivedCycleSieve

Renamed the bridge class/file from `CanonicalCycleSieve` to
`SpecDerivedCycleSieve`.

**Reason:** the old name encouraged treating this bridge as a generic
"canonical" proof object, while the actual strategy is more precise: the cycle
is derived from a `SpecSieveSequence`, and the future proof should expose
Spec-derived repeated windows and survivor gaps instead of accumulating more
local lemmas around an opaque walk.

**Validation:** full `just verify` passed after the Scala rename:

```text
total: 10546 valid: 10546 (10525 from cache, 21 trivial) invalid: 0 unknown: 0 time: 33.23
```

### 2026-06-28 — Walk prefix base case verified

Added `SpecDerivedCycleSieve.assertWalkInitialPrefix()`.

**Statement:**

```scala
cycle(1) == spec.next(0) &&
  List.empty[BigInt] == spec.next.gapList(0, 0)
```

This verifies item 1 from the expected supporting lemmas:
`assertWalkInitialPrefix`. It packages the base case for the future
survival-walk prefix invariant:

- before any gap is emitted, the emitted gap prefix is empty;
- the empty prefix is definitionally `spec.next.gapList(0, 0)`;
- the walk's initial survivor `cycle(1)` is exactly `spec.next(0)`, via the
  existing next-head bridge and `assertFirstSurvivorEqualsSpecNext0`.

**Why this matters:** the full walk theorem needs an induction over emitted
survivor gaps. This lemma gives the verified base state of that induction
without unfolding `nextGapsWalk` or comparing the completed walk output from
outside, which previously timed out.

**Validation:** full `just verify` passed:

```text
total: 10514 valid: 10514 (10476 from cache, 21 trivial) invalid: 0 unknown: 0 time: 36.15
```

### 2026-06-28 — Walk skip branch verified

Added `SpecDerivedCycleSieve.assertWalkSkippedValueRejected(pos)`.

**Statement:**

```scala
pos >= 1 &&
  Calc.mod(cycle(pos), cycle.head) == 0
  ==> !spec.next.accepts(cycle(pos))
```

This verifies item 2 from the expected supporting lemmas:
`assertWalkSkippedValueRejected`. It packages the local skip branch for the
future survival-walk prefix invariant: if the walked current-stage value is a
multiple of the old head, then the next Spec stage rejects that value because
the old head is now part of the next filter.

**Why this matters:** in the recursive walk proof, skipped positions must leave
the emitted gap prefix unchanged. This lemma supplies the branch condition
bridge needed to justify that the skipped value is not a missing `spec.next`
element.

**Validation:** full `just verify` passed:

```text
total: 10530 valid: 10530 (10495 from cache, 21 trivial) invalid: 0 unknown: 0 time: 37.01
```

### 2026-06-28 — Walk emit branch verified

Added `SpecDerivedCycleSieve.assertWalkSurvivorAccepted(pos)`.

**Statement:**

```scala
pos >= 1 &&
  Calc.mod(cycle(pos), cycle.head) != 0
  ==> spec.next.accepts(cycle(pos))
```

This verifies item 3 from the expected supporting lemmas:
`assertWalkSurvivorAccepted`. It packages the local emit branch for the future
survival-walk prefix invariant: if the walked current-stage value is not a
multiple of the old head, then the next Spec stage accepts that value.

**Why this matters:** together with `assertWalkSkippedValueRejected`, the proof
now has verified branch facts for both outcomes of the walk decision. The next
missing step is no longer "does this branch match Spec acceptance?"; it is the
stronger recursive invariant that connects each emitted survivor to the correct
`spec.next` index and gap prefix.

**Validation:** full `just verify` passed:

```text
total: 10546 valid: 10546 (10511 from cache, 21 trivial) invalid: 0 unknown: 0 time: 34.62
```

**Bookkeeping:** added the lemma to `OBJECTS.md` and the supporting verifier
table in `articles/sieve-sequence.md`.

### 2026-06-24 — Ticket created
Scoped Leg 3. Confirmed with user: Canonical may use Spec freely; the "no Spec link" constraint applied to the raw `CycleSieveSequence` refinement (then called Leg 4, now Leg 5 after the 2026-06-28 survival-walk split). Selected diff-based induction (`ClassicCycleIntegralProperties` pattern) as the primary proof idiom, with `mergedGapPrefix`/`indexOfAccepted` as fallback. Walk approach explicitly excluded (3 prior timeouts).

### 2026-06-24 — First single-gap lemma verified
Added `SpecDerivedCycleSieve.assertNextFirstGapMatchesSpecNext(nextPeriod)`.

**Statement:** `spec.next(1) - spec.next(0) == spec.next.gapList(0, nextPeriod).head`, proved without scanning positions.

**Why this approach (not the diff idiom yet):** For the *first* gap, the cleanest statement is just `spec.next(1) - spec.next(0)`, which by `apply`'s base case reduces to `spec.next(1) - spec.next.head.value`. The `gapList` head is definitionally `apply(from+1) - apply(from)`, so the proof is pure arithmetic substitution plus `assertApplyMonotonic`. No `indexOfAccepted` and no diff induction needed at this smallest step.

**Validation:** `just verify` passed with `9001 valid: 9001 (8961 from cache, 20 trivial) invalid: 0 unknown: 0`. +30 VCs over the previous green state (8971).

**Lesson:** The single-gap case is trivial because both sides are direct `apply` differences. The hard part (matching the *whole* gap list) is where the strategy choice matters; the diff idiom will enter there. This confirms the "smallest meaningful step first" approach from `small-changes` is paying off: we have a green foundation before tackling the list-level induction.

**Next:** Either (a) lift to the full list via diff induction, or (b) first add a positional single-gap lemma `assertNextGapAtMatchesSpecNext(i)` generalizing this to arbitrary `i`, mirroring `assertNextGapEqualsCurrentGapSum`. Leaning (b) as the next atomic step, since it's the natural generalization and consumes the same pattern.

### 2026-06-24 — Positional single-gap lemma verified (with one fixed timeout)
Added `SpecDerivedCycleSieve.assertNextGapAtMatchesSpecNext(nextPeriod, index)`.

**Statement:** For any `0 <= index < nextPeriod`,
`spec.next(index + 1) - spec.next(index) == spec.next.gapList(0, nextPeriod).apply(index)`.

This generalizes `assertNextFirstGapMatchesSpecNext` from `index = 0` to any valid index, and is the per-position input to the list-level equality.

**Attempt 1 — timeout (VC at SpecDerivedCycleSieve.scala:549):** the precondition `index < gapList.size` for `gapList(0, nextPeriod).apply(index)` timed out at 120s. The solver could not connect `index < nextPeriod` to `gapList(0, nextPeriod).size == nextPeriod` on its own.

**Attempt 2 — fix and verify:** added one `assert(spec.next.assertGapListSize(0, nextPeriod))` to discharge the size precondition before the `.apply(index)` call. Verified:
`total: 9033 valid: 9033 (8993 from cache, 20 trivial) invalid: 0 unknown: 0`.
+32 VCs over the previous clean green (9001).

**Supporting change:** `SpecSieveSequence.assertGapListApplyEqualsGapAtPosition` was `private`; promoted to public so the Canonical lemma can consume it. Visibility-only change, no logic change.

**Lesson (candidate for LEARNINGS.md):** When a lemma calls `list.apply(index)` with `index` bounded by an *external* parameter (here `nextPeriod`) rather than by `list.size` directly, Stainless cannot synthesize the size precondition even when `index < externalBound` is required. Always precede such an `.apply` with an explicit `assertGapListSize` (or equivalent) so the bound is locally available. This is the same family of issues as LEARNINGS 1.2 (facts must be locally visible to the solver, not just globally true).

**Next:** Lift from per-position equality to full list equality. Two candidate idioms: (a) induction on `nextPeriod` using `assertNextGapAtMatchesSpecNext` for the head + recursive IH for the tail (mirrors `SpecSieveSequence.assertMergedGapPrefixMatchesNext`); (b) diff-based induction via `ClassicCycleIntegralProperties.assertSameDiffAfterCycle`. Leaning (a) since the per-position lemma is already verified and the list-equality induction is a direct structural lift.

### 2026-06-24 — List-equality lemma verified (after fixing a real bug in attempt 1)
Added `SpecDerivedCycleSieve.nextGapList(from, count)` (builder) and
`SpecDerivedCycleSieve.assertNextGapListMatchesSpecNext(from, count)` (lemma).

**Statement:** `nextGapList(from, count) == spec.next.gapList(from, count)` for all `from, count >= 0`.

This is the list-level lift: the Canonical-computed next gap list (built directly from `spec.next` adjacent differences, forward order) equals Spec's own `gapList`, element-for-element.

**Attempt 1 — FAILED (2 timeouts, `unknown: 2`):** Two real problems, not just solver weakness:
1. **Builder-order bug (my error):** the first builder `(spec.next(count) - spec.next(count-1)) :: nextGapList(count-1)` produced the list in REVERSED order — `[gap(count-1), ..., gap(0)]` — while `spec.next.gapList` is forward-ordered. The equality being proved was simply false. The solver timed out choking on an unprovable goal.
2. **Recursion-precondition timeout (LEARNINGS 2.1 family):** the recursive call `assertNextGapListMatchesSpecNext(nextPeriod - 1)` needs the period anchor `spec.next(nextPeriod - 1) == head + modulus`, which does NOT follow from the outer anchor on `nextPeriod`.

**Attempt 2 — FIX and verify:** Rewrote the builder to forward order with a sliding `from` parameter, mirroring `SpecSieveSequence.gapList`'s own recursion shape exactly:
```scala
(spec.next(from + 1) - spec.next(from)) :: nextGapList(from + 1, count - 1)
```
and restructured the induction to recurse on `count` with `from + 1`, mirroring the verified `assertGapListPositive`/`assertGapListApplyEqualsGapAtPosition` pattern. This keeps the induction self-contained — no period-anchor precondition needs to be re-derived at recursive calls. Verified:
`total: 9062 valid: 9062 (9019 from cache, 20 trivial) invalid: 0 unknown: 0`.
+29 VCs over the previous clean green (9033).

**Supporting changes:** `SpecSieveSequence.assertGapListFirstEqualsGap` promoted `private → public` (visibility-only), so the lemma can consume it for the head case.

**Lessons (candidates for LEARNINGS.md):**
- **Builder/list-equality bugs are easy to miss.** When proving `myBuilder == specBuilder` by induction, FIRST sanity-check the builder produces the same order as the spec builder on paper. A reversed builder makes the goal unprovable, and the solver expresses this as a timeout rather than a counterexample — which looks like solver weakness but is actually a logic bug.
- **Sliding-window induction over `from` beats fixed-`from` induction over `count`** when the list builder recurses on `from + 1`. The period anchor / other preconditions stay local; no re-derivation needed at recursive calls. This is the same shape used by every verified list lemma in `SpecSieveSequence` (`assertGapListPositive`, `assertGapListSize`, `assertGapListApplyEqualsGapAtPosition`).

**Status of Leg 3:** The direct-difference next gap list now has a verified equality to `spec.next.gapList`. What remains is connecting the *cycle strategy* (the walk/rotate pipeline, or an equivalent cycle-arithmetic computation) to this list — i.e., proving the cycle strategy's output equals `nextGapList` (and therefore `spec.next.gapList`). That is the genuinely hard producer theorem.

### 2026-06-24 — STRATEGY CORRECTION: transfer Spec's gap facts through assertApplyMatches
User feedback (2026-06-24): the perceived "complexity" of Leg 3 was self-inflicted. Spec has already proven gap periodicity (`assertGapPeriodic`) and gap merging (`assertMergeGapEqualsOldGapSum`, `mergedGapPrefix`). And Leg 2 has already proven the canonical cycle replicates Spec at every index (`assertApplyMatches`: `cycle(k) == spec(k)` for all `k >= 0`).

Therefore every Spec gap fact transfers to the canonical cycle by rewriting each `spec.apply(i)` to `cycle(i)` through the verified equivalence — **no new pipeline, no walk, no residue computation**. The previous framing ("connect the cycle strategy to nextGapList") was chasing a hard theorem that isn't required.

**Revised Leg 3 plan:** add transfer lemmas, one per Spec gap fact:
1. `assertGapPeriodicMatchesSpec(k, period)` — periodicity transfer. **DONE.**
2. `assertMergeGapEqualsOldGapSumMatchesSpec(...)` — merge transfer (next).
3. (possibly) `assertGapSumMatchesSpec(period)` — period-sum transfer.

Each is a pure transfer: call the Spec lemma, rewrite through `assertApplyMatches`, conclude. No timeouts expected.

### 2026-06-24 — Periodicity transfer verified (first attempt)
Added `SpecDerivedCycleSieve.assertGapPeriodicMatchesSpec(k, period)`.

**Statement:** `cycle(period + k + 1) - cycle(period + k) == cycle(k + 1) - cycle(k)`.

**Proof:** pure transfer — `spec.assertGapPeriodic(k, period)` gives the Spec-side equality; four calls to `assertApplyMatches` rewrite `spec(...)` → `cycle(...)` at the four positions `k, k+1, k+period, k+period+1`.

**Validation:** `just verify` passed first attempt with `9087 valid: 9087 (9043 from cache, 20 trivial) invalid: 0 unknown: 0`. +25 VCs over the previous green (9062).

**Lesson:** This confirms the user's point — when a property is already proven on Spec and Canonical is proven equivalent to Spec index-by-index, the transfer is mechanical (call + rewrite) and verifies trivially. Do NOT re-derive the property from scratch on the cycle side.

### 2026-06-24 — Scoping principle for the cycle rule list
User guidance (2026-06-24): the rules stated over `canonical.cycle` should carry **only what the equivalence check requires**, not everything that is true. For example, the next head is in fact prime (proven on the Spec side), but the cycle does not need to know that for the gap/apply equivalence. Adding "head is prime" as a cycle rule would add complexity without load-bearing value.

**Decision rule for what becomes a cycle fact:**
- INCLUDE if a downstream equivalence lemma (or the eventual Leg-4 `CycleSieveSequence` proof) consumes it.
- EXCLUDE if it's merely true but not required by any consumer.

So far the load-bearing cycle facts are: gap positivity, gap periodicity, the copy rule, the merge rule, and the period sum. "Head is prime" is excluded.

### 2026-06-24 — Gap positivity transfer verified
Added `SpecDerivedCycleSieve.assertGapPositiveMatchesSpec(k)`.

**Statement:** `cycle(k + 1) - cycle(k) > 0` for all `k >= 0`.

**Proof:** pure transfer — `spec.assertGapPositive(k)` gives the Spec-side positivity; two calls to `assertApplyMatches` rewrite `spec(k), spec(k+1)` → `cycle(k), cycle(k+1)`.

**Validation:** `just verify` passed first attempt with `9100 valid: 9100 (9068 from cache, 20 trivial) invalid: 0 unknown: 0`. +13 VCs over the previous green (9087).

**Next:** The gap copy rule — if `cycle(k)` and `cycle(k+1)` are both not multiples of the new head `cycle(1)`, the next gap is `cycle(k+1) - cycle(k)`. Transfers from `SpecSieveSequence.assertFilterPreservesNextGap`.

### 2026-06-24 — Copy rule attempt 1 TIMED OUT (logical gap, not solver weakness)
Attempted `assertCopyGapMatchesSpec(k)` with preconditions
`Calc.mod(cycle(k), cycle(1)) != 0` and `Calc.mod(cycle(k+1), cycle(1)) != 0`.

**Timeout:** `unknown: 2` at precondition 4/6 of `spec.assertFilterPreservesNextGap`,
which is `spec.next.accepts(spec(k))`.

**Root cause (genuine logical gap, NOT solver weakness):** the cycle-side
hypothesis "not a multiple of `cycle(1)`" only gives coprimality against the
new head. But `spec.next.accepts(v)` requires coprimality against the **whole**
`cycle.primes` list (new head + tail). `assertNextAcceptsMatches` bridges
`spec.next.accepts(v) == SieveUtils.isCoprime(v, cycle.primes)` — so the
hypothesis is too weak by exactly the tail-coprimality part.

**The catch:** for a *current* generated value `cycle(k)`, tail-coprimality
(`isCoprime(cycle(k), cycle.primes.tail)`) IS true (it's why `cycle(k)` was
generated in the first place). So the right statement is:
> if `cycle(k)` survives the tail filter (always true for generated values)
> AND `cycle(k)`, `cycle(k+1)` are not multiples of the new head,
> then the gap is copied.

The fix is to either (a) strengthen the precondition to full coprimality
against `cycle.primes`, or (b) prove a cycle-side lemma that generated values
are tail-coprime and layer the copy rule on top.

**Action taken:** commented out the lemma (per `never-destroy`), restored green
at `9100 valid`. Promoted `spec.assertFilterPreservesNextGap` to public
(benign; no caller now, but keeps it available for the retry).

**Status:** STOPPED per `stop-and-ask` (1 of 3 attempts; this is a logical gap
worth user input, not a retry-the-same-thing situation). Awaiting direction
between options (a) and (b) above.

### 2026-06-24 — Copy rule correction approved

The previous `assertFilterPreservesNextGap` is not reusable for the actual
`spec.next` stage because it also requires:

```text
nextSeq.head.value == head.value
```

That is false for a real next stage, whose head is `spec(1) > spec.head`.
Tail-coprimality alone therefore cannot repair the old lemma.

The corrected pure-Spec lemma will use the actual load-bearing contract:

```text
nextSeq.filterValues.tail == filterValues
nextSeq.head.value >= head.value
nextSeq.accepts(apply(k))
nextSeq.accepts(apply(k + 1))
```

From those assumptions:

1. `apply(k)` and `apply(k+1)` both occur in `nextSeq`.
2. They are consecutive in the old stream.
3. Any `nextSeq` value between them is accepted by the old tail filter because
   `nextSeq.filterValues.tail == filterValues`.
4. Therefore no third accepted value can lie strictly between them in either
   stream.

The conclusion is the copied-gap equality:

```text
nextSeq(nextSeq.indexOfAccepted(apply(k)) + 1)
  - nextSeq(nextSeq.indexOfAccepted(apply(k)))
==
apply(k + 1) - apply(k)
```

Canonical will then use `assertWalkDecisionMatchesNextAccept` at `k` and
`k + 1` to establish the two next-acceptance assumptions, and transfer the old
values through `assertApplyMatches`.

### 2026-06-24 — Corrected Spec copy lemma attempt 1 timed out

Attempted
`SpecSieveSequence.assertConsecutiveAcceptedByNextPreservesGap(nextSeq, k)`
with the corrected no-equal-head contract described above.

The mathematical body mostly verified, including:

- projecting a `nextSeq` value through `nextSeq.filterValues.tail` into old
  acceptance;
- proving the old successor is at or below the next-sequence successor;
- proving the next-sequence successor is at or below the accepted old
  successor;
- concluding the copied-gap equality.

However, focused verification timed out on three precondition VCs before or at
the beginning of the body:

```text
nextSeq.accepts(apply(k))
nextSeq.accepts(apply(k + 1))
nextSeq.indexOfAccepted(apply(k)) requires apply(k) >= nextSeq.head.value
```

Stainless did not retain the lower-bound component hidden inside the
cross-instance `accepts` requirements. Result:

```text
47 total, 44 valid, 3 unknown, 3 timeouts at 120 seconds each
```

This matches `LEARNINGS.md` section 18: cross-instance calls can lose simple
arithmetic facts when several unfoldings share one VC.

The attempted lemma was commented out, not deleted. Full verification was
restored:

```text
9100 valid, 0 invalid, 0 unknown
```

Do not retry the same shape. The next viable approach is to isolate the lower
bound as its own tiny lemma or change the copy lemma contract to carry explicit
facts:

```text
apply(k) >= nextSeq.head.value
apply(k + 1) >= nextSeq.head.value
```

Only one of those changes should be tried in the next verification cycle.

### 2026-06-24 — Corrected Spec copy lemma attempt 2 verified

Retried the same mathematical sandwich proof with the two domain facts exposed
as explicit preconditions:

```text
apply(k) >= nextSeq.head.value
apply(k + 1) >= nextSeq.head.value
```

This separates two logically distinct obligations:

- `nextSeq.accepts(value)` says that the value passes the next filter;
- `value >= nextSeq.head.value` says that the value belongs to the searchable
  domain of `nextSeq.indexOfAccepted`.

With those facts available directly, Stainless verifies
`assertConsecutiveAcceptedByNextPreservesGap`. The lemma proves that when two
consecutive old-sequence values are both accepted by the next sequence, they
remain consecutive there, so their gap is copied unchanged. It does not assume
equal sequence heads.

Focused verification:

```text
49 valid, 0 invalid, 0 unknown
```

Full verification:

```text
9149 valid, 0 invalid, 0 unknown
```

**Next:** transfer this pure-Spec fact through `SpecDerivedCycleSieve`. The
canonical lemma must use the old head `cycle.head` as the newly added filter,
not `cycle(1)`: `cycle(1)` is the next sequence's starting value, while
`cycle.head` is the prime newly included in `spec.next.filterValues`.

### 2026-06-24 — Canonical copy transfer attempt 1 timed out

Attempted `SpecDerivedCycleSieve.assertCopyGapMatchesSpec(k)` with the corrected
filter condition:

```text
Calc.mod(cycle(k), cycle.head) != 0
Calc.mod(cycle(k + 1), cycle.head) != 0
```

and the corrected next-stage index:

```text
nextIndex = spec.next.indexOfAccepted(spec(k))
```

The proof body was layered through `assertApplyMatches`,
`assertWalkDecisionMatchesNextAccept`, and the newly verified
`assertConsecutiveAcceptedByNextPreservesGap`.

**Timeout:** `nextIndex` was declared before those assertions. Stainless checks
method-call preconditions at the declaration site, so it timed out before
entering the useful proof body on both requirements of `indexOfAccepted`:

```text
spec(k) >= spec.next.head.value
spec.next.accepts(spec(k))
```

This is an ordering problem in the attempted implementation, not a new
mathematical gap. The attempted method is commented out. Full verification was
restored:

```text
9149 valid, 0 invalid, 0 unknown
```

**Next planned attempt:** establish acceptance and lower bounds first, invoke
`assertConsecutiveAcceptedByNextPreservesGap`, and only then evaluate
`indexOfAccepted(spec(k))`. Do not place any `indexOfAccepted` call, including a
`val` initializer, before those facts.

### 2026-06-24 — Canonical copy transfer attempt 2 timed out

Moved `indexOfAccepted(spec(k))` below all acceptance and lower-bound
assertions, exactly as planned. This removed both index precondition timeouts
from attempt 1.

The next isolated failure was:

```text
nextSeq.accepts(spec(k))
```

even after calling:

```text
assertWalkDecisionMatchesNextAccept(k)
```

Focused verification reached 10 of 59 obligations before the acceptance
assertion timed out at 120 seconds. The diagnostic context retained the walk
lemma call and the lower bound, but did not cheaply rewrite its equality result
through both representation equality and the local `nextSeq = spec.next` alias.

The method remains commented out. Full verification was restored:

```text
9149 valid, 0 invalid, 0 unknown
```

**Current conclusion:** the pure-Spec copy theorem is verified. The canonical
wrapper is not yet verified. Index ordering is fixed; the remaining blocker is
the cross-representation acceptance transfer.

**Next planned unit:** create one small canonical lemma whose postcondition is
directly:

```text
Calc.mod(cycle(k), cycle.head) != 0
  ==> spec.next.accepts(spec(k))
```

for `k >= 1`. Its body should call `assertApplyMatches(k)` and
`assertWalkDecisionMatchesNextAccept(k)`, then expose only this implication.
The copy lemma can consume that direct endpoint without asking Stainless to
reconstruct the equality inside its larger VC.

### 2026-06-24 — Acceptance transfer attempt 3 timed out

Created the planned isolated lemma
`assertWalkNonMultipleAcceptedByNext(k)`. It had only the two essential
requirements:

```text
k >= 1
Calc.mod(cycle(k), cycle.head) != 0
```

Its body called `assertWalkDecisionMatchesNextAccept(k)`, selected the positive
acceptance branch for `cycle(k)`, and then used `assertApplyMatches(k)` to
rewrite the endpoint to `spec(k)`.

Focused verification generated only 17 obligations, but timed out on:

```text
spec.next.accepts(cycle(k))
```

The final `spec.next.accepts(spec(k))` obligation was also unknown. Result:

```text
17 total, 15 valid, 0 invalid, 2 unknown
```

This establishes that the problem is not caused by the size of the copy-gap
lemma or by the local `nextSeq` alias. Stainless is not exporting the positive
branch of the boolean equivalence from
`assertWalkDecisionMatchesNextAccept` cheaply enough for a caller.

The attempted lemma is commented out. Full verification is restored:

```text
9149 valid, 0 invalid, 0 unknown
```

This is the third failed canonical acceptance-transfer attempt. Per
`AGENTS.md`, stop before trying another variation.

**Decision required before continuing:**

1. Strengthen or reshape `assertWalkDecisionMatchesNextAccept` so the needed
   positive acceptance fact is part of a direct implication/postcondition,
   then reverify that existing lemma.
2. Avoid consuming the equivalence and prove next acceptance directly inside a
   new small lemma from tail coprimality plus non-divisibility by `cycle.head`.

Option 2 duplicates part of the existing bridge proof but gives Stainless a
straight-line positive theorem. Option 1 is less duplication but changes a
currently verified load-bearing lemma and may reproduce the same timeout.

### 2026-06-24 — Direct constructive acceptance test

Tested option 2 as `assertCurrentNonMultipleAcceptedByNext(k)`. The proof
constructs next acceptance directly:

1. `assertApplyMatches(k)` transfers the current value to `spec(k)`.
2. `spec.accepts(spec(k))` provides coprimality with the old tail filter.
3. The nonzero remainder against `cycle.head` supplies the newly added filter.
4. Structural unfolding proves coprimality with all of `cycle.primes`.
5. Direct list equalities prove `spec.next.filterValues == cycle.primes`.
6. The final expression proves `spec.next.accepts(spec(k))`.

Focused result:

```text
46 total, 45 valid, 0 invalid, 1 unknown
```

The single timeout was:

```text
assert(value >= nextSpec.head.value)
```

This assertion is redundant. Stainless subsequently verified the same
lower-bound precondition at the final `nextSpec.accepts(spec(k))` call in
0.1 seconds, and it verified the final acceptance postcondition in 0.4 seconds.
All coprimality and filter-list construction obligations passed.

The attempted lemma is commented out and full verification is restored:

```text
9149 valid, 0 invalid, 0 unknown
```

**Recommended next iteration:** re-enable the exact constructive lemma and
remove only the redundant standalone lower-bound assertion. Do not otherwise
change the proof. This is materially different from the earlier equivalence
approach: the desired final theorem already verified in this test.

### 2026-06-24 — Direct constructive acceptance attempt 2 timed out

Applied exactly the recommended change: re-enabled the constructive lemma and
removed only:

```text
assert(value >= nextSpec.head.value)
```

Focused verification then timed out on the lower-bound precondition of the
final call:

```text
nextSpec.accepts(spec(k))
```

Result:

```text
45 total, 44 valid, 0 invalid, 1 unknown
```

The acceptance postcondition itself remained valid, and every coprimality and
filter-list equality obligation remained valid. Removing the standalone
assertion did not eliminate the expensive lower-bound VC; it moved that VC to
the final consumer. The earlier interpretation that the final call had already
proved the bound cheaply was cache/run-order dependent and was too optimistic.

The method is commented out again. Full verification is restored:

```text
9149 valid, 0 invalid, 0 unknown
```

**Current precise blocker:** prove or carry
`spec(k) >= spec.next.head.value` without combining it in one VC with the full
constructive coprimality context. A future plan should isolate this ordering
fact in a separate lemma or add it as an explicit requirement to the
acceptance-transfer lemma. Do not retry another assertion-order variation.

### 2026-06-24 — Isolated next-head ordering lemma verified

Added `SpecDerivedCycleSieve.assertCurrentValueAtOrAboveNextHead(k)`:

```text
k >= 1 ==> spec(k) >= spec.next.head.value
```

The proof follows an already verified local pattern:

```text
spec(1) <= spec(k)                  [current Spec monotonicity]
spec(1) == cycle(1)                 [canonical apply equality]
cycle(1) == spec.next.head.value    [next-head correspondence]
```

Focused verification:

```text
21 valid, 0 invalid, 0 unknown
```

Full verification:

```text
9170 valid, 0 invalid, 0 unknown
```

This confirms the ordering fact is independently cheap and stable. The next
small change should make the constructive acceptance lemma consume this public
ordering lemma before its final `accepts` call. No coprimality proof needs to be
changed.

### 2026-06-24 — Constructive next acceptance verified

Re-enabled `assertCurrentNonMultipleAcceptedByNext(k)` and replaced its local
ordering reconstruction with:

```text
assertCurrentValueAtOrAboveNextHead(k)
```

No coprimality or filter-list reasoning changed. The lemma now verifies:

```text
k >= 1
Calc.mod(cycle(k), cycle.head) != 0
------------------------------------------
spec.next.accepts(spec(k))
```

Focused verification:

```text
43 valid, 0 invalid, 0 unknown
```

The final `accepts` lower-bound precondition, which previously timed out at
120 seconds, verified in 0.1 seconds.

Full verification:

```text
9213 valid, 0 invalid, 0 unknown
```

**Lesson:** the timeout was caused by combining the ordering derivation with
the full constructive coprimality context in one VC. Exporting the ordering
fact through a small verified lemma made the final consumer cheap and stable.

**Next:** re-enable the corrected `assertCopyGapMatchesSpec(k)`, call
`assertCurrentNonMultipleAcceptedByNext` at `k` and `k + 1`, and then consume
the already verified pure-Spec
`assertConsecutiveAcceptedByNextPreservesGap`.

### 2026-06-24 — Copy gap transfer verified (3rd attempt, new approach)

Uncommented and verified `SpecDerivedCycleSieve.assertCopyGapMatchesSpec(k)`.

The earlier attempts (2 from this ticket + 1 retry) all timed out on
cross-instance acceptance transfer. The successful approach differs in three ways. An isolation test
(`assertNextAcceptsViaAlias`, 9 VCs, 8 valid, 1 timeout) confirmed that
the alias alone reproduces the timeout — the other two factors may also
help but are not the root cause:

1. **No `nextSeq` alias.** CONFIRMED as root cause. `val nextSeq = spec.next`
   blocks the solver from connecting cached lemma results to `nextSeq.foo(...)`.
   Use `spec.next` directly.
2. **Lemma return values captured and asserted.** Each call to
   `assertCurrentNonMultipleAcceptedByNext` and
   `assertCurrentValueAtOrAboveNextHead` captures its return value, then
   `assert`s it.
3. **Redundant assertions removed.** Removed the redundant
   `spec.assertApplyMonotonic` and standalone `spec(k) >= ...` lines.
   Reduced VCs from 61 to 53.

**Statement:** For `k >= 1`, if both `cycle(k)` and `cycle(k+1)` are not
multiples of `cycle.head`:
```
spec.next(nextIndex + 1) - spec.next(nextIndex) == cycle(k + 1) - cycle(k)
```
where `nextIndex = spec.next.indexOfAccepted(spec(k))`.

**Validation:** Focused verification: 53 VCs in 9.70s. Full `just verify`:
`9266 valid, 0 invalid, 0 unknown`. +53 VCs over previous green (9213).

**Lesson (see LEARNINGS.md 18.3):** Confirmed via isolation test
(`assertNextAcceptsViaAlias`). The `val nextSeq = spec.next` alias alone,
in a 9-VC lemma, causes `nextSeq.accepts(spec(k))` to time out. The alias
blocks the solver from connecting cached `.holds` results to the local
variable. Fix: use `spec.next` directly + capture/assert return values.

### 2026-06-24 — Status summary and next targets

**Verified (Leg 3):**
1. `assertNextFirstGapMatchesSpecNext` — first gap equality
2. `assertNextGapAtMatchesSpecNext` — per-position gap equality
3. `nextGapList` + `assertNextGapListMatchesSpecNext` — full gap list builder + equality
4. `assertGapPeriodicMatchesSpec` — gap periodicity transfer
5. `assertGapPositiveMatchesSpec` — gap positivity transfer
6. `assertConsecutiveAcceptedByNextPreservesGap` (Spec-side) — pure-Spec copy lemma
7. `assertCurrentValueAtOrAboveNextHead` — ordering lemma
8. `assertCurrentNonMultipleAcceptedByNext` — constructive next acceptance
 9. `assertCopyGapMatchesSpec` — canonical copy rule

### 2026-06-24 — Merge rule and period sum verified

**Merge rule — rejection side:**
Added `SpecDerivedCycleSieve.assertCurrentMultipleRejectedByNext(k)`. Mirror of
`assertCurrentNonMultipleAcceptedByNext`. When `Calc.mod(cycle(k), cycle.head) == 0`,
the value is not coprime with `cycle.primes` and is rejected by `spec.next`.
28 VCs, full verify 9354 valid.

**Merge rule — acceptance side:** Already covered by
`assertCurrentNonMultipleAcceptedByNext` + `assertNextGapEqualsCurrentGapSum`.
The merged gap equals the sum of current gaps via `indexOfAccepted` on the Spec
side — no additional cycle lemma needed.

**Period sum:**
Added `SpecDerivedCycleSieve.assertNextFilterModulusRelation()`. Proves
`spec.next.filterModulus == cycle.head * spec.filterModulus`. When the old head
becomes a filter prime, the filter modulus grows by that factor.
16 VCs, full verify 9370 valid.

**Isolated assertions restored:**
- `assertCycleGapEqualsSpecGap(k)` — cycle-side gap equals Spec-side gap (9 VCs)
- `assertNextAcceptsViaAlias(k)` — acceptance through `val` alias via bridge lemma (18 VCs)
- `assertSpecApplyMonotonic(from, until)` — Spec apply monotonicity (3 VCs)
- `assertCurrentMultipleRejectedByNext(k)` — rejection side of merge rule (28 VCs)
- `assertNextFilterModulusRelation()` — period sum relation (16 VCs)

Full verify: **9373 valid, 0 invalid, 0 unknown**.

**Status: Leg 3 complete.** All items from the ticket's goal are verified:
- Next head ✅ (`assertNextHeadMatches`)
- Next acceptance ✅ (`assertCurrentNonMultipleAcceptedByNext` + `assertCurrentMultipleRejectedByNext`)
- Copy rule ✅ (`assertCopyGapMatchesSpec`)
- Merge rule ✅ (`assertNextGapEqualsCurrentGapSum` + rejection lemma)
- Period sum ✅ (`assertNextFilterModulusRelation`)
- Gap list equality ✅ (`assertNextGapListMatchesSpecNext`)
- Gap periodicity/positivity transfers ✅ (`assertGapPeriodicMatchesSpec`, `assertGapPositiveMatchesSpec`)

**Next:** Leg 4 — survival-walk correctness: prove the concrete
`nextGapsWalk` output matches `spec.next` gaps, then use that to prove
`cycle.next()(k) == spec.next(k)`. See `../sieve-sequence-epic.md` for the
epic roadmap.

## Next-Stage Equivalence (P1 / P2)

**Goal:** prove the structural-identity equalities (head + gaps + apply) hold
one stage later — i.e. for `spec.next` as the current stage. Two planned
approaches (per `tickets/sieve-sequence-epic.md` §1):

- **P1 (math side):** `SpecDerivedCycleSieve(spec.next, nextPeriod).cycle(k) == spec.next(k)` ∀k.
  Proves a *correct* next cycle exists, built from `spec.next`'s own data, by
  the same construction as Leg 2. Does NOT prove the implementation's `cycle.next()`
  computes it.
- **P2 (computational):** `cycle.next()(k) == spec.next(k)` ∀k. Proves the
  optimized `CycleSieveSequence.next()` (via `nextGapsWalk`) matches `spec.next`.

**Clarification on `stop-and-ask` (user, 2026-06-25):** when a ticket pursues
multiple planned approaches, the 3-attempt counter applies *per approach*.
Failure of one approach is expected process — comment it out and try the next.
Stop-and-ask only when all ticketed approaches are exhausted.

### 2026-06-25 — P1 verified (after fixing an off-by-one-stage bug)
Added `SpecDerivedCycleSieve.assertNextCycleApplyMatchesSpecNext(nextPeriod, k)`.

**Statement:** `SpecDerivedCycleSieve(spec.next, nextPeriod).cycle(k) == spec.next(k)` for all `k >= 0`.

This is Leg 2's `assertApplyMatches` instantiated one stage later. The proof
constructs `nextCanonical = SpecDerivedCycleSieve(spec.next, nextPeriod)` and
calls `nextCanonical.assertApplyMatches(k)` (Leg 2's current-stage lemma, which
applies because `nextCanonical.spec == spec.next`).

**Bug in attempt 1 (caught via focused verify):** the first version called
`nextCanonical.assertNextApplyMatches(nextPeriod, k)` — but that lemma proves
apply-matches for `nextCanonical.spec.next` = `spec.next.next` (TWO stages
ahead), demanding a precondition I don't have. Fix: call
`nextCanonical.assertApplyMatches(k)` instead, which proves
`nextCanonical.cycle(k) == nextCanonical.spec(k) == spec.next(k)`.

**Validation:** focused verify `just verify assertNextCycleApplyMatchesSpecNext`
passed in 3.13s (29 VCs) — confirming the user's point that focused verify is
faster for single-lemma iteration. Full `just verify`:
`9402 valid: 9402 (9382 from cache, 20 trivial) invalid: 0 unknown: 0`.
+29 VCs over previous green (9373).

**Lesson:** when a method `m` is on a wrapper `W(spec)`, calling `w.m` operates
on `w.spec`, not on the *original* `spec`. `nextCanonical.assertNextApplyMatches`
is about `spec.next.next`, not `spec.next`. The right call for "next stage" is
`nextCanonical.assertApplyMatches` (the current-stage lemma, on the
next-stage wrapper). Off-by-one-stage bugs are easy to miss on paper — focused
verify caught it fast.

**Status:** P1 complete. P2 (the computational `cycle.next()` equivalence)
remains open — that is the deferred Lemma 5 / open hole, and the next planned
approach.

### P2 exploration contract (user, 2026-06-25)

P2 is a hard theorem (3 prior timeouts before Leg 3 existed). The exploration
process for P2:

- **Try multiple ideas.** Timeouts are expected and are NOT failure — they are
  exploration. Each idea gets its own verify cycle.
- **After each attempt (success or timeout): record what was learned** in this
  ticket. The learning is the deliverable even when the proof doesn't land.
  Specifically record: the idea, the statement attempted, where it timed out
  (which VC / precondition), and why.
- **Honest self-check after each attempt:** "Do I genuinely have a new idea, or
  am I stuck retrying variations of the same shape?" If stuck (no new idea) →
  STOP, summarize all learnings, ask for direction. This is the spirit of
  `stop-and-ask` applied to multi-approach exploration.
- **Keep state green:** every failed attempt is commented out (per
  `never-destroy`), tree restored to green before the next idea.

### 2026-06-25 — P2 idea exploration (no verify cycles spent — analysis only)

Before writing any P2 code, sketched three ideas and self-checked each against
the documented root cause of the 3 prior timeouts (the walk's opacity).

**Idea A — structural equality of two cycle objects.** Prove
`cycle.next().gapCycle == SpecDerivedCycleSieve(spec.next, nextPeriod).cycle.gapCycle`.
The primes side is easy; the gapCycle side reduces to
`nextGapsWalk(cycle) == spec.next.gapList(0, nextPeriod)` — i.e. the exact
comparison that timed out 3×. **Rejected: reduces to the known-hard problem.**

**Idea B — a `canonicalNext()` builder on `SpecDerivedCycleSieve` that uses
`nextGapList` (the verified direct list) instead of the walk.** This sidesteps
the walk but, on reflection, just restates what P1 already proves (P1 builds
the next cycle from `spec.next`'s own data). It does not prove the
implementation's `cycle.next()` is correct. **Rejected: not a new result;
already covered by P1.**

**Idea C — `nextGapsWalk(cycle) == nextGapList(0, nextPeriod)`.** Compare the
walk against a Canonical-local list (not `spec.next.gapList` directly), then
use the already-proven `nextGapList == spec.next.gapList` by transitivity.
**Self-check:** the left side is still `collectGaps`/`nextGapsWalk`, which
recurses `head × period` positions and is opaque to the solver from outside
`.holds`. Changing the right side from `spec.next.gapList` to `nextGapList`
does not change that the left side must be unwound. **Rejected: same opacity
shape as the prior failures.**

**Conclusion (honest self-check):** all three ideas bottom out at "the solver
must see inside `collectGaps`/`nextGapsWalk`," which is the documented root
cause. I do NOT currently have a genuinely new idea that avoids this. Per the
P2 contract, this is the "stuck, not exploring" trigger — STOP and surface to
the user rather than burn verify cycles on known-shape attempts.

**What would constitute a genuinely new idea (for discussion):**
1. **Strengthen `collectGaps`'s postcondition** (`.ensuring`) to export the
   element values or the list contents, so external lemmas get structural
   information without unwinding the recursion. This changes the walk itself,
   not just the comparison.
2. **Prove the walk via an accumulator parameter** — add a recursive invariant
   inside `collectGaps` that carries the "values emitted so far correspond to
   spec.next's first N gaps" fact, proved step-by-step inside the recursion
   where the structure IS visible.
3. **Avoid the walk entirely** — accept that `cycle.next()` stays a separate
   optimization whose correctness is not formally certified, and document P1
   as the verified construction path (the design doc's guardrail already
   anticipates this).

Awaiting user direction on which (if any) of these to pursue, or a different
angle entirely.

### 2026-06-25 — CORRECTION: the above "STUCK" conclusion was premature

User pointed out (2026-06-25) that Spec has already proven the merge fact:
`SpecSieveSequence.assertMergedGapPrefixMatchesNext` (public, verified) proves

```
mergedGapPrefix(nextSeq, k, remaining, period) == nextSeq.gapList(seqIndex, remaining)
```

— i.e. the next stage's gaps ARE the current stage's gaps, merged according to
the new-head filter. This is a **Spec-side, non-walk** proof (uses
`indexOfAccepted`, not positional scanning), so it does NOT have the opacity
problem that killed ideas A/B/C above.

**The genuinely new idea I missed:** transfer the merge fact to the canonical
cycle, exactly like Leg 3 transferred periodicity/positivity. Since
`cycle0.gaps == spec0.gaps` and `cycle0.head == spec0.head` (Leg 2), running
the *same merge process* on the cycle's identical inputs produces the same
output: `cycle1.gaps == spec1.gaps`. Same inputs + same process ⇒ same output.

This subsumes P2's goal: once `cycleMergedGapPrefix` (a cycle-side mirror of
Spec's `mergedGapPrefix`) is proven to equal `spec.next.gapList`, the canonical
next cycle built from it has the same gaps as `spec1` — and combined with P1,
the same apply.

**Retracted:** the "STUCK, no new idea" conclusion. The new idea (transfer the
Spec-proven merge to the cycle) was always available; I missed it by fixating
on `nextGapsWalk`. Lesson: when stuck on a cycle-side proof, ALWAYS first ask
"what has Spec already proven about this, and can it transfer?" before
declaring no path exists.

### 2026-06-25 — P2 via merge transfer: plan

Mirror Spec's merge machinery on the canonical cycle, bottom-up:

1. `cycleNextMergedGapOldIndex` — mirror of `Spec.nextMergedGapOldIndex`
   (one-step old-index transformer; decides copy vs. merge by divisibility
   against the new head). Operates on `cycle.apply`, bridged via
   `assertApplyMatches`.
2. `cycleMergedGapPrefix` — mirror of `Spec.mergedGapPrefix` (builds the gap
   list by repeatedly calling the one-step transformer).
3. `assertCycleMergedGapPrefixMatchesSpecNext` — transfer of
   `assertMergedGapPrefixMatchesNext`: proves
   `cycleMergedGapPrefix(...) == spec.next.gapList(...)`.
4. Conclude `cycle1.gaps == spec1.gaps` (the canonical next cycle's gaps
   equal spec.next's gaps).

Each step mirrors a verified Spec lemma and transfers through
`assertApplyMatches`. This is the Leg-3 transfer pattern, applied to the
merge.

## P2 ranked approaches (user directive 2026-06-25: try in order, save learnings, stop only when all exhausted)

**Target:** prove `SpecDerivedCycleSieve(spec.next, nextPeriod).cycle` matches
`spec.next` in head, gaps, AND apply (the P1 next-cycle, not the walk).

### Ranked approaches

1. **Congruence packaging (cheapest).** All three equalities follow from
   congruence: `nextCanonical.cycle` is built by calling the *same* Spec
   functions (`specGapCycle`, `PrimeUtils.primeValues`) that build `spec.next`'s
   own certified data. Same function symbol + equal inputs ⇒ equal output,
   without unfolding. head via `assertNextHeadMatches`; apply via P1
   (`assertNextCycleApplyMatchesSpecNext`); gaps via packaging
   `assertNextGapCycleValuesEqualSpecNextGapList` + construction.
   **Why first:** no new mathematics; pure packaging of verified facts.

2. **Corrected-contract merge transfer.** Define a Spec-side merge lemma under
   `nextSeq.head.value >= head.value` (the contract that fits `spec.next`),
   mirroring `assertConsecutiveAcceptedByNextPreservesGap` (the copy case,
   verified). Transfer the conclusion to the cycle. **Why second:** real new
   Spec proof, moderate cost, but required only if (1) doesn't deliver the
   gaps equality in the form needed.

3. **Walk connection (`cycle.next()` ≡ spec.next).** Prove
   `nextGapsWalk(cycle) == spec.next.gapList(0, nextPeriod)`. **Why third:** the
   documented hard open hole; 3 prior timeouts. Try only if (1)+(2) are
   insufficient AND a genuinely new angle on the walk appears.

4. **`createNextGaps` pure function.** Define a pure function of `(head, gaps)`
   and prove both sides against it. **Why last:** requires re-proving the
   merge's soundness/completeness (the hard work Spec already did internally);
   user flagged this as non-trivial.

### Per-approach contract
- Each approach may have several lemma variations attempted.
- After each attempt (success or timeout): record idea, statement, where it
  timed out, and why. Comment out failures, restore green.
- Self-check after each: "new idea, or stuck on the same shape?" Stop only
  when no new idea remains across all approaches.

### 2026-06-25 — Approach 1 (congruence packaging) SUCCEEDED

Added three packaging lemmas + one top-level conjunction, all verified:

- `assertNextCycleGapsMatchSpecNext(nextPeriod)`: `nextCanonical.cycle.gapCycle.memCycle.values == spec.next.gapList(0, nextPeriod)`.
- `assertNextCycleHeadMatchesSpecNext(nextPeriod)`: `nextCanonical.cycle.head == spec.next.head.value`.
- `assertNextCycleMatchesSpecNext(nextPeriod)`: conjunction of head + gaps + apply (apply via P1).

**How:** pure congruence. `nextCanonical = SpecDerivedCycleSieve(spec.next, nextPeriod)`
builds its cycle by calling the *same* Spec functions (`specGapCycle`,
`PrimeUtils.primeValues`) that certify `spec.next`'s own data. Same function
symbol + equal inputs ⇒ equal output, with no unfolding of merge or walk.
The gaps chain composes `assertNextGapCycleValuesEqualSpecNextGapList` (verified)
with the constructor equality; head composes `assertHeadMatches` (transferred).

**Validation:** focused verify on each (gaps 24 VCs / 4.13s, head 16 VCs / 2.17s,
conjunction 30 VCs / 2.81s); full verify `9472 valid: 9472 invalid: 0 unknown: 0`
(+70 over the 9402 P1 baseline). All first-attempt, no timeouts.

**What this delivers:** the next-stage structural identity (head + gaps + apply)
is proven for the canonical cycle built from `spec.next`. This is exactly the
goal: "a new cycle that also ensures same apply, gaps, and head."

**What this does NOT deliver:** it proves a *correct* next cycle exists. It does
NOT prove the implementation's `CycleSieveSequence.next()` (the walk via
`nextGapsWalk`) produces this cycle. That remains the P2 walk open hole.

**Approaches 2 and 4 are now UNNECESSARY** for the stated target — congruence
delivered it without the merge transfer (2) or a pure `createNextGaps`
function (4). Approach 3 (walk connection) is a *different, harder* goal
(certifying the implementation, not just existence); it remains open and is
documented as such in the design doc's guardrail.

**Lesson:** When the target object is *constructed from* the source of truth by
calling the same certified functions, congruence closes the equality without
any transfer or unfolding. Always check "is the target built by the same
function the source uses?" before reaching for transfer lemmas. This mirrors
Leg 2's `assertApplyMatches`, which is itself derived from head + gaps
construction equality.

### 2026-06-25 — `nextVerified` constructor: .ensuring postcondition timed out

Added `SpecDerivedCycleSieve.nextVerified(nextPeriod)` — a conditional
next-stage constructor returning `SpecDerivedCycleSieve(spec.next, nextPeriod)`.
Conditional (not universal) per user guidance: it carries the next-stage
preconditions as hypotheses, avoiding the Bertrand/Euclid walls that would be
required to prove `spec.next` always exists.

**Attempt 1 — `.ensuring` postcondition TIMED OUT.** The postcondition called
`result.assertNextCycleHeadMatchesSpecNext(nextPeriod)`, whose own preconditions
include the period anchor for `spec.next.next` (two stages ahead). The VC for
that bubbled-up precondition timed out, and even after adding it as an explicit
`require` (the `assertAcceptsEqualWhenTrue` bubbling pattern), the full
focused verify ran past 10 minutes without completing — chaining `.next.next`
in the postcondition compounds verification cost catastrophically.

**Attempt 2 — plain constructor (no `.ensuring`) PASSED (13 VCs / 1.53s).**
`nextVerified` is now a thin conditional constructor with no postcondition VC.
Callers who want the correctness proof call the standalone lemma
`assertNextCycleMatchesSpecNext(nextPeriod)` explicitly (already verified).

**Lesson (candidate for LEARNINGS.md):** `.ensuring` postconditions that call
other `.holds`/`.ensuring` lemmas whose preconditions reference `.next.next`
(sibling-of-sibling stages) blow up verification cost. The bubbling-up trick
(bubbling the callee's preconditions into the caller's `require`s) works for
*one* level of `.next`, but each additional level compounds. Prefer **plain
constructors + standalone correctness lemmas** over `.ensuring` when the
correctness lemma reaches across more than one stage.

**Validation:** focused verify `nextVerified` 13 VCs / 1.53s; full verify
`9485 valid: 9485 invalid: 0 unknown: 0` (+13 over the 9472 baseline).

**Status:** `nextVerified` delivers the verified conditional next-stage
constructor. Combined with `assertNextCycleMatchesSpecNext`, the next-stage
equivalence is conditionally proven (head + gaps + apply all match `spec.next`
under the stated hypotheses).

## Approach 3 — walk correctness (in progress, 2026-06-25)

Goal: prove `nextGapsWalk(cycle0) == spec.next.gapList(0, nextPeriod)`, closing
the implementation-certification half. Strategy: prove the correspondence
*from inside the walk's recursion* via an invariant, where the structure IS
visible — rather than comparing the walk's output to `spec.next.gapList` from
outside (the shape that timed out 3×).

**Guiding principle (user, 2026-06-25): "Keep things stupid simple for the
verifier even if computing slower."** Dumb code the solver can follow beats
clever code it can't. Implications:
- The reverse in `collectGaps` is a perf optimization that costs proof effort.
  For proof purposes, prefer forward-appending (`gaps ++ List(gap)`) over
  prepend+reverse, even though it's O(n²) at runtime. Stainless doesn't care
  about runtime.
- Avoid clever compositions; spell out each step.

### Approach 3 plan
1. **Position-to-index bridge (base case)** — the cycle position holding
   `spec.next(1)` is a survivor of the new-head filter. ✅ DONE
   (`assertFirstSurvivorPositionMatchesSpecNextOne`, 9500 valid).
2. **Position-to-index bridge (inductive step)** — generalize to the m-th
   survivor: `cycle(spec.indexOfAccepted(spec.next(m))) == spec.next(m)` and
   that position survives the filter.
3. **Invariant-carrying companion** to `collectGaps` — a forward-appending
   variant whose invariant is `gaps == spec.next.gapList(0, m)` after processing
   the first `m` survivors.
4. **Top-level wrap** — `nextGapsWalk == spec.next.gapList`.

### 2026-06-25 — Red-state incident + KISS principle applied
While inserting the bridge lemma, the Edit matched the wrong
`spec.next(k) == cycle(pos)` site and split `assertNextFirstGapMatchesSpecNext`'s
doc block, breaking compilation (red state). Per green-to-green, fixed by
removing the broken insertion and re-inserting at the correct location with a
unique anchor. Lesson: when an `old_string` appears multiple times in a file,
use a longer/unique anchor — never a common pattern.

Bridge base case then verified first attempt (15 VCs / 4.32s). Full verify
`9500 valid: 9500 invalid: 0 unknown: 0` (+15 over 9485).

### 2026-06-25 — Walk step 2 (generalized bridge) verified
Added `assertSurvivorPositionMatchesSpecNext(m)` — for any `m >= 0`, the cycle
position holding `spec.next(m)` survives the new-head filter. Verified first
attempt: 15 VCs / 3.84s focused; full `9515 valid` (+15 over 9500).

This is the per-survivor fact the walk-correctness invariant will consume.

### 2026-06-25 — Walk step 3 attempt 1 (direct equality) TIMED OUT
Attempted `assertNextGapsWalkMatchesSpecNextGapList(nextPeriod)`:
`nextGapsWalk(cycle) == spec.next.gapList(0, nextPeriod)`, with the bridge
lemmas and `assertNextGapListMatchesSpecNext` as hints.

**Timeout (122s)** at the postcondition VC `walkGaps == specGaps`. As
predicted: the hint establishes the *target* (`nextGapList == spec.next.gapList`),
but the solver cannot relate the walk's opaque `collectGaps` output to that
target from outside `.holds`. This is the documented root cause.

Commented out, green restored (9515). Per the contract, this is expected
exploration, not a failure — it confirms the walk must be proven *from inside*
via an invariant.

### Walk step 3 — attempt 2 plan (invariant-carrying companion)
Build a companion to `collectGaps` driven by **next-index `m`** (KISS) rather
than by position:
- For each `m`, look up `spec.next(m)`'s cycle position via `indexOfAccepted`
  (already verified via `assertSurvivorPositionMatchesSpecNext`).
- Emit the gap `spec.next(m+1) - spec.next(m)`.
- Invariant: `gaps == spec.next.gapList(0, m)` by construction.

This sidesteps the position-counting problem entirely. The companion's output
is *definitionally* `spec.next.gapList`. What remains (step 3b) is proving
the companion's output equals `collectGaps`'s output — but that may be
unnecessary if `nextGapsWalk` can be redefined to use the companion.

**A third option (γ, noted by user):** prove the survivor sets are equal
(cycle's survivors == spec.next's filtered values, since `cycle ≡ spec`), so
the gap lists are equal. The bridge lemmas are the per-survivor facts γ needs;
this may subsume the companion approach.

### 2026-06-25 — Walk step 3 attempts 2 & 3 TIMED OUT. STOP per stop-and-ask.

Three timeouts on the walk connection, all with the same root cause:

| Attempt | Statement | Timeout |
|---|---|---|
| 1 | `nextGapsWalk(cycle) == spec.next.gapList(0, nextPeriod)` | 122s, postcondition VC |
| 2 | `nextGapsWalk(cycle) == nextGapList(0, nextPeriod)` (cycle-local RHS) | 121s, same VC |
| 3 | `invariantGapList(0, count, Nil) == spec.next.gapList(0, count)` (fresh KISS companion, no walk involved) | 121s, postcondition VC |

**Critical finding from attempt 3:** even the *fresh* companion (no `collectGaps`, no walk, just a clean forward-appending recursion emitting `spec.next(m+1) - spec.next(m)`) times out when asked to prove equality to `spec.next.gapList`. This means **the opacity is NOT specific to the walk** — it's a general difficulty proving list-equality between two different recursive list-builders (one `++`-appending, one `::`-consing).

**This reframes the problem.** The walk itself may not be the obstacle; the obstacle is list-builder-vs-list-builder equality. Yet `assertNextGapListMatchesSpecNext` (which proves `nextGapList == spec.next.gapList`) DID verify — because it mirrors `gapList`'s exact cons-based recursion. So the lesson:

> To prove a recursive list-builder L == `gapList`, L must use the SAME recursion
> shape as `gapList` (cons-based, `head :: tail`), not a different shape
> (`++`-append). The KISS principle of "slow but simple" must be applied to the
> *recursion shape*, not just the algorithm — match the target's shape, even at
> runtime cost.

**Implication:** attempt 4 (if pursued) should rewrite the companion with
cons-based recursion (mirroring `nextGapList`'s verified shape), NOT
`++`-append. But `nextGapList` ALREADY is that shape and is verified == `spec.next.gapList`.
So attempt 4 reduces to attempt 2 (`nextGapsWalk == nextGapList`), which timed out.

**Status:** All three attempts on the walk connection have timed out. The
verified state stands at: a correct next cycle EXISTS (Approach 1, `nextVerified`)
and the gap-list correspondence is provable for cons-shaped builders, but
connecting the position-driven walk (`collectGaps`) to the index-driven
`nextGapList` remains open. Per stop-and-ask (3 timeouts, no new idea that
differs in *recursion shape*), STOP and report.

---

## SESSION SNAPSHOT — 2026-06-25 (consolidated for next agent/session)

### Verified this session (all green, state at `9515 valid`)

| Lemma | What it proves | Where |
|---|---|---|
| `assertNextCycleApplyMatchesSpecNext` (P1) | `SpecDerivedCycleSieve(spec.next, nextPeriod).cycle(k) == spec.next(k)` ∀k | Approach 1 |
| `assertNextCycleGapsMatchSpecNext` | next canonical cycle's `.gapCycle.memCycle.values == spec.next.gapList(0, nextPeriod)` | Approach 1 |
| `assertNextCycleHeadMatchesSpecNext` | next canonical cycle's `.head == spec.next.head.value` | Approach 1 |
| `assertNextCycleMatchesSpecNext` | conjunction of head + gaps + apply | Approach 1 |
| `nextVerified(nextPeriod)` | conditional next-stage constructor; correctness via standalone lemma | packaging |
| `assertFirstSurvivorPositionMatchesSpecNextOne` | cycle position of `spec.next(1)` survives new-head filter | walk bridge base |
| `assertSurvivorPositionMatchesSpecNext(m)` | cycle position of `spec.next(m)` survives, for any `m >= 0` | walk bridge general |

**Net result:** a *correct* next cycle is conditionally proven to exist
(head + gaps + apply all match `spec.next`). The implementation's
`CycleSieveSequence.next()` walk is NOT yet certified to produce it.

### The open hole, precisely

> Prove `nextGapsWalk(cycle) == spec.next.gapList(0, nextPeriod)` (or equivalently `== nextGapList(0, nextPeriod)`).

### Key insight (LEARNINGS candidate)

**The opacity is not specific to the walk.** Attempt 3 built a fresh KISS
companion with NO walk involvement — just `++`-appending `spec.next` diffs —
and it STILL timed out proving equality to `spec.next.gapList`. Meanwhile
`assertNextGapListMatchesSpecNext` (which proves `nextGapList == spec.next.gapList`)
verified fine because it mirrors `gapList`'s cons-based shape.

> **Lesson:** To prove a recursive list-builder `L == gapList`, `L` must use
> the SAME recursion shape as `gapList` (`head :: tail`), not a different
> shape (`++`-append). KISS must be applied to the **recursion shape**, not
> just the algorithm — match the target's shape, even at runtime cost.

### Untried ideas (ranked, for the next session)

1. **Rewrite `collectGaps` with cons-based recursion** matching `nextGapList`'s
   shape. Per the insight above, this is the one variation not yet tried that
   differs in *recursion shape*. Caution: modifies a load-bearing verified
   function (`never-destroy` rule — comment out the old, don't delete).

2. **γ — survivor-sets-equal route (user-suggested).** Prove the cycle's
   survivor set equals `spec.next`'s filtered values (via the verified bridge
   lemmas `assertSurvivorPositionMatchesSpecNext`), then derive gap-list
   equality as a consequence. Genuinely different *mathematical* route, not a
   recursion-shape tweak. Most promising untried angle.

3. **Strengthen `collectGaps`'s `.ensuring` postcondition** to export the
   element correspondence, so external lemmas get structural info without
   unwinding. Changes the walk's contract.

4. **Accept the walk as uncertified.** `nextVerified` is the verified path;
   `cycle.next()` stays a tested optimization. The design doc's guardrail
   already documents this as acceptable.

### Artifacts left in the code (commented out, per never-destroy)

- `assertNextGapsWalkMatchesSpecNextGapList` (attempt 1, timed out)
- `assertNextGapsWalkMatchesNextGapList` (attempt 2, timed out)
- `invariantGapList` + `assertInvariantGapListMatchesSpecNextGapList` (attempt 3, timed out)

All three carry full doc comments recording the statement, the timeout, and
the analysis, so the next agent inherits the findings without re-deriving.

### Rule-compliance note

This session followed: `green-to-green` (state green throughout, restored
after each timeout), `small-changes` (one lemma per verify cycle), `never-destroy`
(failed attempts commented out, not deleted), `ticket-first` (this record),
`stop-and-ask` (stopped at 3 timeouts with the same root cause), and the
multi-approach exploration contract (timeouts treated as expected process,
learnings saved after each).

---

## IDEA δ — apply-equivalence, not gap-list equivalence (user, 2026-06-25)

### The reframe

All three timed-out attempts (1, 2, 3) targeted **gap-list equality**:
`nextGapsWalk(cycle) == spec.next.gapList`. That's hard because it requires
proving two recursive list-builders produce element-equal lists — and the
walk's recursion is opaque from outside `.holds`.

**The turnover (user insight):** we don't actually need gap-list equality.
What we need is that the `CycleSieveSequence` built from the walk's gaps
(`cycle.next()`) **generates the same stream** as `spec.next`:

```
cycle.next()(k) == spec.next(k)   for all k >= 0
```

This is **apply-equivalence**, a different and weaker-in-the-right-way
statement. It does NOT require the walk's gap *list* to be element-equal to
`spec.next.gapList` — only that the walk's gaps, when used as a cycle,
reconstruct `spec.next`'s stream.

### Why this is genuinely new

- None of attempts 1–3 targeted apply-equivalence; all targeted gap-list
  equality.
- The existing `assertNextCycleApplyMatchesSpecNext` (P1) proves
  apply-equivalence for the *canonical* next cycle (built from `spec.next`),
  NOT for `cycle.next()` (the walk). So this specific statement — "the
  walk-built cycle's apply matches `spec.next`'s apply" — is unattempted.
- It sidesteps the list-equality opacity entirely: instead of relating two
  list-builders, it relates two `apply` functions, which are recursive but
  structurally simpler (each is `head + sum of first k gaps`).

### Why it might be tractable

1. **Same head:** `cycle.next().head == cycle(1) == spec.next.head.value`
   (proven via `assertNextHeadMatches`). Both sides start from the same value.
2. **Same survivors (per-value, proven):** the walk keeps exactly the
   non-multiples of `cycle.head`; `spec.next` generates exactly the values
   accepted by the new filter. `assertCurrentNonMultipleAcceptedByNext` and
   `assertCurrentMultipleRejectedByNext` prove these coincide per-value.
3. **Bridge lemmas available:** `assertSurvivorPositionMatchesSpecNext(m)`
   proves the cycle position of `spec.next(m)` is a survivor — the per-index
   fact that could drive an apply-equality induction.

### Honest caveat

"Same gap multiset ⇒ same stream" is NOT automatically true — two gap lists
generate the same stream iff they are **cyclic rotations** of each other
(same gaps, possibly different starting point), not merely multiset-equal.
So the proof can't rest on multiset-equality alone. Two cleaner options:

- **(δ-a)** Prove the walk's gaps are a *rotation* of `spec.next`'s gaps.
- **(δ-b)** Prove apply-equality directly: `cycle.next()(k) == spec.next(k)`
  by showing both equal `spec`'s k-th survivor of the head-filter, using the
  bridge lemmas. This avoids gap-list reasoning entirely.

(δ-b) is preferred — it never touches the gap list as an ordered structure.

### Probe plan (KISS)

Test the idea with the smallest possible lemmas before committing:
1. `cycle.next()(0) == spec.next(0)` — heads match (both `cycle(1)`). Should
   be trivial.
2. `cycle.next()(1) == spec.next(1)` — first post-head value matches, using
   bridge lemmas.

If both verify, the apply-equality route is viable and we build up
inductively. If they time out, the idea is killed with a recorded reason —
the thinking is preserved either way.

### Outcome

**Probe step 1 TIMED OUT (4 VCs, 483s) — but with a deeper discovery than expected.**

The timeouts were NOT on the lemma's conclusion (`cycle.next()(0) == spec.next(0)`).
They were on `cycle.next()`'s OWN runtime `require` clauses:

```
nonEmpty(nextGapsWalk(cycle))          // walk produces non-empty list
allGreaterThan(newGaps, 0)             // all gaps positive
isCoprime(newHead + ..., primes)       // head coprimality
```

These are the runtime preconditions inside `CycleSieveSequence.next()` (lines
99–104), which assert the walk's output is well-formed. Stainless cannot
discharge them because the walk is opaque. Therefore:

> **`cycle.next()` CANNOT BE CALLED from any verified context** — not because
> its output is wrong, but because its own preconditions depend on the walk's
> output, which is unprovable from outside.

Any lemma that writes `val x = cycle.next()` will hit these preconditions and
time out, regardless of what the lemma is trying to prove about `x`.

**This is a stronger result than the gap-list timeouts.** It means:
- Idea δ (apply-equivalence) is blocked at the *call site*, not at the
  conclusion. The apply-equality is unreachable without first proving the
  walk's output satisfies `next()`'s preconditions.
- The same blocker would affect ANY approach that invokes `cycle.next()`.
- The ONLY way to certify `cycle.next()` is to first prove the walk's output
  is valid (non-empty, positive, coprime) — which is itself a walk-correctness
  problem.

**Idea δ status:** Killed — not because apply-equivalence is wrong, but
because it requires calling `cycle.next()`, which is uncallable in proof
context. The reasoning is preserved (this section) so a future approach that
first proves the walk's output validity could then revisit apply-equivalence.

**Revised understanding of the open hole:** the fundamental obstacle is
`nextGapsWalk`'s opacity, which blocks BOTH (a) gap-list equality and
(b) `cycle.next()`'s own preconditions. Until the walk's output is proven
valid, `cycle.next()` is unusable in proofs, and the cycle's next-stage
correctness rests entirely on `nextVerified` (the construction path, not the
walk path).

**Implication for next steps:** any viable approach must either
  1. prove the walk's output validity directly (still the core open problem), or
  2. bypass `cycle.next()` entirely and use `nextVerified` as the certified
     next-stage constructor (the current state — acceptable per the design
     doc's guardrail).

---

## IDEA ε — recurrence-based apply induction (user, 2026-06-25)

### The characterization

A filtered stream's `apply` follows a deterministic recurrence:

```
apply(0)     = head
apply(n+1)   = apply(n) + 1                          if apply(n)+1 survives the filter
             = first survivor after apply(n)         otherwise
```

("survives the filter" = not a multiple of any prime in the filter list.)

This recurrence UNIQUELY determines the stream from `(head, filter-primes)`.
Any two streams with the same head and the same filter behavior have the same
apply — by induction on `n`, because each `apply(n+1)` is determined solely by
`apply(n)` and the filter.

### The proof structure (simple as pie)

1. **Base:** `spec.next.apply(0) == cycle.apply(0)` — both are the head. Done
   via Approach 1 / `assertNextCycleHeadMatchesSpecNext`.
2. **Inductive step:** assume `spec.next.apply(n) == cycle.apply(n)`. Then
   `spec.next.apply(n+1) == cycle.apply(n+1)` because BOTH compute the next
   value by the same recurrence rule from the same `apply(n)`.

No gap-list comparison. No calling `cycle.next()`. No list-equality. Just:
same base + same recurrence ⟹ same apply, by induction.

### Why this is different from all prior attempts

| Prior attempt | What it proved | Why it failed |
|---|---|---|
| 1, 2 | gap-list equality | list-builder vs list-builder, opaque |
| 3 | companion list equality | same list-equality opacity |
| δ probe | apply via `cycle.next()` | `cycle.next()`'s preconditions opaque |

Idea ε: proves apply equality via **per-position recurrence**, not list
equality and not `cycle.next()`. Each step is local (one position), not
collective (whole list). The induction doesn't open any walk recursion.

### Connection to `CycleIntegralOnesProperties`

The `[1]`-cycle (all naturals, gap 1 everywhere) is the base case of this
characterization: before any filtering, `apply(n+1) - apply(n) == 1` always.
Each filter step replaces some `1`s with larger gaps in a way determined by
the filter prime. So the recurrence is the *filtered* version of the
`[1]`-cycle's trivial `+1` recurrence.

### Probe plan

Step 1: prove `spec.next.apply` follows the recurrence (standalone lemma on
Spec — should be near-trivial since it's how `searchNext` works by definition).

Step 2: prove `nextVerified`'s cycle follows the same recurrence (via Approach
1's construction — the cycle is built from `spec.next`'s own data).

Step 3: conclude apply equality by induction.

If step 1+2 verify, the characterization is proven and the induction closes.
If they target `cycle.next()` instead and time out, we learn the recurrence
approach also hits the walk opacity — but for `nextVerified`, it should be clean.

---

## ARCHITECTURAL SYNTHESIS — the integral-cycle arsenal (user, 2026-06-25)

### The key realization

**A `CycleSieveSequence` IS a `CycleIntegral(head, gapCycle)` plus structural
conditions.** It is not a black box with a walk inside — the "sieve" part is
just the conditions (positive gaps, coprime head, periodicity, etc.); the
"sequence" part is pure integral-cycle arithmetic.

Every "does `CycleSieveSequence` match `spec.next`" question decomposes into:
1. **Integral-cycle half** — characterized by the purpose-built arsenal:
   - `assertDiffEqualsCycleValue`: `CI_{i+1} - CI_i == Cycle_{i+1}` (gaps ARE cycle values)
   - `assertSimplifiedDiffValuesMatchCycle`: `apply(pos+1) - apply(pos) == cycle.values(mod(pos+1, size))` (mod closed form of the diff)
   - `assertCycleIntegralMatchModCycleDef`: `apply(pos) == div(pos,size)*sum + integralValues(mod(pos,size)) + init` (full closed form)
   - `assertSameDiffAfterCycle`: diffs repeat per period
   All non-recursive, all per-position, all verified. NONE unfold a recursion.
2. **Conditions half** — the Leg-3 cycle rules (positivity, periodicity, copy,
   merge), proven as transfers from Spec.

**Both halves are done.** The arsenal was built so half 1 never unfolds
recursion; Leg 3 was built so half 2 is transferred. Together: a
`CycleSieveSequence` whose conditions hold IS a verified reconstruction of
the spec stream, characterized per-position via the closed form.

### Why this is the designed path (not a workaround)

The integral-cycle properties (`CycleIntegralOnesProperties`,
`ClassicCycleIntegralProperties`, `ModCycleIntegralProperties`,
`CycleIntegralProperties`) were **created for this moment** — they exist to
let us reason about cycle-integral streams (which is what sieve sequences are)
without unfolding recursion. The `[1]`-cycle base case (`CycleIntegralOnesProperties`)
is the zeroth sieve stage; each filter step produces a new cycle integral
whose closed form is characterized by the arsenal.

### Corrected proof structure for the walk

Reframe: instead of "does the walk produce a list equal to `spec.next.gapList`"
(list-equality, opaque), ask "**does `CycleIntegral(cycle(1), G)`, via the
closed form, reconstruct `spec.next` per-position?**" where `G` is the walk's
output. By `assertDiffEqualsCycleValue`, this reduces to per-position gap
facts (`G(i mod |G|) == spec.next(i+1) - spec.next(i)`), NOT list-equality.

```
For each position i:
  CI.apply(i+1) - CI.apply(i) == G(i mod |G|)              [diff property]
  G(i mod |G|) == spec.next(i+1) - spec.next(i)            [per-position, via bridge lemmas]
Base:
  CI.apply(0) == cycle(1) == spec.next(0)                  [head match]
∴ by induction, CI.apply(i) == spec.next(i) for all i
```

No list-equality. No walk-unfolding. No calling `cycle.next()`. Just:
diff property + per-position gap facts + induction.

### Remaining empirical question

The per-position gap fact still references `G`'s elements. Whether Stainless
can verify `G(i mod |G|) == spec.next(i+1) - spec.next(i)` without unfolding
`G` is the open empirical question — but the *structure* is now right, and
it uses the arsenal as designed. This is fundamentally different from all
prior attempts (which compared lists or called `cycle.next()`).

### 2026-06-25 — ARSENAL BRIDGE VERIFIED (breakthrough)

Added `SpecDerivedCycleSieve.assertCycleDiffEqualsGap(pos)`:

> `cycle.apply(pos + 1) - cycle.apply(pos) == cycle.gapCycle.memCycle(pos + 1)`

**This is the keystone.** It proves the integral-cycle arsenal's diff property
(`assertDiffEqualsCycleValue`) applies directly to `CycleSieveSequence`,
confirming the synthesis: a sieve cycle sequence's adjacent differences ARE
its gap-cycle elements, per-position, no recursion unfolding.

Verified: focused 7 VCs / 12.66s; full `9522 valid: 9522 invalid: 0 unknown: 0`
(+7 over 9515). First attempt, no timeouts.

**Why this is a breakthrough (not just another lemma):** every prior attempt
(attempts 1–3, δ) tried to relate the walk's output to `spec.next` by
*list-equality* or by *calling `cycle.next()`* — both opaque. This lemma gives
a **per-position** characterization of the cycle's stream via its gaps, which
is exactly the shape the arsenal was designed to support. The next step is to
chain: diff property (this) + Leg-2 gap equality (`cycle.gapCycle ==
spec.gapCycle`) ⟹ `cycle.apply(pos+1) - cycle.apply(pos) == spec.apply(pos+1) -
spec.apply(pos)`, and with the head match, induction gives `cycle.apply ==
spec.apply` per-position.

**Supporting change:** added `import v1.chapter4.cycle.integral.recursive.CycleIntegral`
to `SpecDerivedCycleSieve.scala` (was missing; needed for the `cycle.integral`
type assertion in the proof).

### 2026-06-25 — Construction foundation attempt 1 (repeat-list) TIMED OUT

Attempted the alignment primitive: a `repeatList` helper + lemma that
repeating a cycle's gap list `times` times produces a `CycleIntegral`
generating the same stream.

**Timeout (2 VCs, 241s)** on constructing `MemCycle(repeatList(...))` and on
the equality `stretched(pos) == ci(pos)`. The repeated list's structure is
opaque to the solver — same list-builder opacity that killed the walk.

**Lesson:** the list-construction route (build a new list, wrap in MemCycle,
prove equality) recapitulates the walk's opacity. The repeat step should NOT
be done by literally building a list. The arsenal's design intent is to
characterize via the **closed form** (`div(pos,size)*sum +
integralValues(mod(pos,size)) + init`), which is pure arithmetic and needs no
list-building.

**Revised plan:** skip the literal repeat-list. Characterize the filtered
stream's m-th value directly via the closed form + divisibility structure.
The alignment (period divides x) is a bookkeeping condition on the closed
form's `div`/`mod`, not a list to construct.

**Open uncertainty:** the m-th non-multiple of x still requires knowing
*which* positions are non-multiples (survivor counting). Whether the closed
form makes this tractable is the next empirical question — but it's a
genuinely different angle from list-building.

### 2026-06-25 — CORRECTED UNDERSTANDING: the arsenal's method (user, 2026-06-25)

User pointed (again) at the diff property:
```
ModCycleIntegral(pos+1) - ModCycleIntegral(pos) == Cycle.values(mod(pos+1, size))
```

**The insight I kept missing:** this is a **closed-form lookup, not a list
access.** The gap at any position is computable from `(pos, size)` via `mod`
+ a single cycle lookup. No list needs to be built or compared.

This kills the repeat-list approach. "Repeat the cycle k times" is an
**arithmetic identity on the lookup index**, not a list construction:

```
stretchedCycle.values(mod(pos+1, k*size)) == originalCycle.values(mod(pos+1, size))
```

Same values, because the repeated pattern wraps. No `MemCycle(repeatList(...))`,
no opacity.

**Alignment condition:** once `sum` (per-period total) is a multiple of `x`
(achieved by repeating enough times), divisibility-by-`x` of `apply(pos)`
becomes periodic:
```
apply(pos) mod x == (integralValues(mod(pos,size)) + init) mod x   [when sum ≡ 0 mod x]
```
depends only on `mod(pos, size)`. So the survivor structure is periodic, and
the filtered cycle is well-defined and periodic — **all via closed forms.**

**Why all 5 prior attempts failed:** every one built or compared a *list*.
The arsenal's point is that you NEVER do that — you reason per-position via
`mod`-lookups and the closed form. I was using the arsenal's statements but
not its method.

**Corrected path:** state the filtered-cycle construction purely via closed
forms — gap lookups, divisibility via closed form, periodic survivor
structure. No list construction anywhere.

### 2026-06-25 — DEEP READ: ModCycleIntegralProperties closed form (user-directed)

Read `ModCycleIntegralProperties.scala` and the integral-cycle article in
full. The closed form is the **definition** of `ModCycleIntegral.apply`:

```
apply(pos) = div(pos, size) * integralValues.last        // periods elapsed × per-period increment
           + integralValues(mod(pos, size))              // position within current period
           + initialValue                                 // starting offset
```

And `assertCycleIntegralMatchModCycleDef` proves the recursive `CycleIntegral.apply`
equals this closed form. So EVERY `CycleIntegral` — including sieve cycles —
has its `apply` characterized by pure-arithmetic closed form. No recursion
unfolding. No list comparison.

**The key for the filtered-cycle construction:** divisibility-by-x of apply:

```
apply(pos) mod x  =  [ div(pos,size)*sum + integralValues(mod(pos,size)) + init ] mod x
```

If `sum` (= `integralValues.last`) is a multiple of `x`, then `div(pos,size)*sum mod x == 0`:

```
apply(pos) mod x  ==  [ integralValues(mod(pos,size)) + init ] mod x     [when sum ≡ 0 mod x]
```

…depends ONLY on `mod(pos, size)`. So the survivor structure is periodic with
period `size`, characterizable entirely via the closed form.

**Alignment** (making sum a multiple of x): `valueMatchAfterManyLoopsInBoth`
proves repeating cycle values doesn't change them — just changes period
counting. No list built.

**Corrected construction path (NO lists, anywhere):**
1. Characterize `apply(pos) mod x` via closed form → periodic in `mod(pos, size)`.
2. Survivors within one period form a fixed sub-pattern, indexed by intra-period positions.
3. Filtered cycle's gaps = closed-form diffs between consecutive survivors
   (each a sum of original gaps, via `integralValues` lookups).
4. Filtered cycle's `apply` reconstructs non-multiples via closed form on the
   new gap cycle.

**Every step is closed-form arithmetic + list-LOOKUP (not list-BUILDING).**
This is what the arsenal was built for. The repeat-list attempt was the wrong
approach — build a list when I should have used the lookup identity.

**Status:** Corrected understanding complete. Ready to write the first real
lemma (divisibility-periodicity via closed form) next. State green at 9522.

### 2026-06-25 — ARTICLE ALREADY DESCRIBES THE NEEDED PROPERTIES (§5 drafts)

Read `articles/integral-cycle.md` in full. **Section 5 "Extended Properties
[Draft]" already contains the exact properties needed for the filtered-cycle
construction, mathematically proven and described — just pending Stainless
verification.** I was reinventing what's already written.

| § | Property | Statement | Article status |
|---|---|---|---|
| **5.1** | Modulo Invariance | If `S mod v == 0`, then `CI_i mod v == (I_{(i mod n)} + init) mod v` — divisibility depends only on intra-period position | Math proven, Stainless pending |
| **5.2** | x-fold Concatenation Invariance | `CycleIntegral(L^(x), init)_i == CycleIntegral(L, init)_i` — repeating the cycle reproduces the same stream | Math proven, Stainless pending |
| 5.3 | Right Index Shift | rotation invariance | Math proven, pending |
| 5.4 | Left Index Shift | rotation invariance | Math proven, pending |

**§5.1 IS the divisibility-periodicity characterization** I worked out last
message — `CI_i mod v == (I_{(i mod n)} + init) mod v` when `S mod v == 0`.
Already proven mathematically in the article.

**§5.2 IS the alignment primitive** — `CI(L^(x)) == CI(L)`. My `repeatList`
attempt was the wrong implementation (list-building); the article's
characterization is via closed forms (the div/mod arithmetic matches, so no
list is needed).

Both are marked "Stainless verification pending."

### Corrected plan (translate §5.1/§5.2 drafts into verified Scala)

1. **Verify §5.2 (x-fold Concatenation)** via closed forms: prove
   `CI(L^(x), init)_i == CI(L, init)_i` by showing both sides have the same
   closed form (via `assertCycleIntegralMatchModCycleDef`). Alignment primitive,
   done right (closed-form arithmetic, no list-building).

2. **Verify §5.1 (Modulo Invariance)** via the closed form: prove the
   reduction `CI_i mod v == (I_{(i mod n)} + init) mod v` when `S mod v == 0`,
   using the closed form.

3. **Then** the filtered-cycle construction follows: alignment (5.2) +
   divisibility periodicity (5.1) ⟹ survivor structure periodic ⟹ filtered
   cycle well-defined ⟹ reconstructs non-multiples.

The math is done in the article. The work is translating §5.1/§5.2 from draft
math into verified Scala, building on the arsenal's existing verified lemmas
(`assertCycleIntegralMatchModCycleDef`, `assertSimplifiedDiffValuesMatchCycle`,
`valueMatchAfterManyLoopsInBoth`).

**Lesson:** Read the existing articles in full before inventing new lemmas.
The integral-cycle article's §5 drafts are exactly the filtered-cycle
construction tools, already mathematically proven. My 5 timeouts came from
not recognizing this and building list-based variants instead of translating
the closed-form drafts.

### 2026-06-25 — THE FILTER PROPERTY (new work, user-directed)

§5.1 and §5.2 are foundation tools (drafts to verify), but the **filter
property itself is new** — a lemma that, given a `CycleIntegral C` and divisor
`x` (with ≥1 non-multiple of `x` in C's values), establishes a cycle integral
`C'` enumerating exactly C's non-multiples of `x`. Built from DivMod + Cycle +
List properties, via closed forms.

**Construction plan (no list materialization):**
1. **Alignment (§5.2):** force `size | x` by treating the cycle as repeated.
   Characterized via closed form, NOT by building `L^(x)`.
2. **Divisibility periodicity (§5.1):** `CI_i mod x == (I_{(i mod n)} + init) mod x`
   when `sum mod x == 0`. Survivor structure periodic in `mod(i, n)`.
3. **Filter property (new):** the non-multiples within one period form a fixed
   survivor sub-pattern; the gaps between consecutive survivors define `C'`;
   `C'.apply` reconstructs the non-multiples via the closed form on `C'`'s gaps.

**Critical method constraint (the lesson from 5 failures):** every step is
closed-form arithmetic + list-LOOKUP. NEVER build a list (`repeatList`,
`++`, `collectGaps`) and prove equality — that's the opacity trap. The
arsenal's method is per-position closed forms throughout.

### 2026-06-25 — §5.2 Approach 2 TIMED OUT (6th list-building failure)

Attempted `assertXFoldConcatenationInvariance` with a smarter proof
(`valueMatchAfterManyLoopsInBoth` + induction) — but still via
`MemCycle(repeatList(...))`. **3 VCs timed out (362s), all on constructing
`MemCycle(repeatList(...))` or accessing it.** Commented out, green restored.

**Architectural wall identified (honest pattern, 6 failures):**

| # | Approach | List built | Outcome |
|---|---|---|---|
| 1 | walk == spec.next.gapList | `collectGaps` output | timeout |
| 2 | walk == nextGapList | `collectGaps` output | timeout |
| 3 | invariantGapList == spec.next.gapList | `++`-appended | timeout |
| 4 | cycle.next() == spec.next | (calls walk) | timeout |
| 5 | MemCycle(repeatList) == original | `repeatList` | timeout |
| 6 | §5.2 with IH + valueMatch | `repeatList` | timeout |

**Every timeout traces to constructing `MemCycle(someBuiltList)`.** The solver
cannot see (a) the built list is non-empty, (b) its elements relate to the
original's, or (c) through `++`/`::` recursion. `MemCycle` is built around a
`List[BigInt]`, and list-construction is opaque from outside `.holds`.

**Implication:** the filter property CANNOT be proven by constructing the
filtered cycle's gap list — not via walk, companion, repeatList, or append.
The list-construction wall is absolute in the current setup.

**Genuinely new ideas (NOT same-shape retries):**
1. **Strengthen `MemCycle`'s `.ensuring` postcondition** to export structural
   info (size, element-at-index) so external lemmas get it without unfolding.
   Changes `MemCycle` itself — caution per never-destroy, but the only path
   that addresses the root cause.
2. **State the filter as pure existence via ModCycleIntegral arithmetic**
   (no list) — "there exist size'/sum'/integralValues' such that the closed
   form reconstructs non-multiples." Still needs a MemCycle to instantiate,
   so may not escape the wall.
3. **Accept the wall** — `nextVerified` (construction path, no list) is the
   verified route; the walk/filter remains a documented open hole.

**Status:** STOPPED. 6 failures, no genuinely new idea that avoids list
materialization. The architectural wall is real and well-characterized.
Awaiting user direction — strengthening MemCycle's postcondition (idea 1) is
the most promising untried angle, but it touches a load-bearing type.

### 2026-06-28 — Ticket cleanup and article-proof audit

Audited `articles/sieve-sequence.md` against the current code and ticket state.
The article's strongest "three-sequence equivalence" wording is too broad if
read as certifying the concrete survival walk.

**What is source-backed today:**

- `SpecDerivedCycleSieve(spec.next, nextPeriod).cycle` matches `spec.next` in
  head, stored gaps, and apply behavior.
- Current-stage Canonical matches Spec by construction (`assertApplyMatches`).
- Per-survivor bridge lemmas show that `spec.next` values occur at survivor
  positions of the current cycle, and adjacent survivor differences match
  adjacent `spec.next` gaps.

**What remains missing:**

1. Prove the concrete survival walk emits the spec gaps in order:

   ```text
   SieveSequenceNextLevel.nextGapsWalk(cycle)
     == spec.next.gapList(0, nextPeriod)
   ```

2. Or bypass list equality and prove apply equivalence for the concrete
   `next()` result:

   ```text
   cycle.next()(k) == spec.next(k)
   ```

   This is currently blocked even before the conclusion because calling
   `cycle.next()` requires proving properties of `nextGapsWalk(cycle)`
   (`nonEmpty`, positivity, and first next-cycle filter facts).

3. If returning to the walk route, add proof strength inside or around
   `collectGaps`: either stronger `.ensuring` postconditions with element/order
   correspondence, or an accumulator invariant that exposes the emitted gap
   prefix while the recursion is still visible.

4. Keep primality and product-number-theory walls separate unless a future
   proof truly needs them. The equivalence proof should not drag in
   "prime before p squared" or Euclid's lemma by default.

**Ticket lifecycle cleanup:**

- Kept this file as the one active sieve-sequence proof ticket.
- Moved completed alignment/background tickets out of `active/`:
  `canonical-spec-to-cycle-alignment.md`, `cycle-integral-filter-merge.md`,
  `assert-no-divisor-by-factor-list.md`, `euclid-full-formalization.md`, and
  `euclid-h4-strategy.md`.
- Moved replaced sieve proof plans out of `active/`:
  `v0-v2-apply-equivalence.md`, `remove-extern-from-next.md`, and
  `draft-nextprime-v0.md`.
- Moved hard, real but currently non-actionable mathematical walls into
  `tickets/blocked/`: `prove-apply1-is-prime.md` and
  `primorial-not-divisible-by-new-prime.md`.

**Validation:** Markdown-only cleanup. Checked the existing `verify.log` first:
`10495 valid`, `0 invalid`, `0 unknown`. Per AGENTS.md, no Stainless rerun was
needed because no non-markdown files were changed.
