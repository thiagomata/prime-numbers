# V0 Skip Multiples Until Non-Multiple (Gap Merge)

**Created:** 2026-06-19
**Status:** Blocked on full merge assembly — full lemma times out without more decomposition
**Depends on:** `v0-filter-preserves-next-position.md` (completed, 6379 valid)

## Related Tickets

- `v0-filter-preserves-next-position.md` — Proves `Calc.mod(W, p) != 0 ⇒ nextSeq(vIdx+1) == W`. The complement of this lemma (covers the non-multiple case).
- `v0-gap-properties.md` — P3 `assertGapSum` proves `sumGap(from, until) == apply(until) - apply(from)`, which gives the merged gap sum.
- `v0-residue-cycle-proof.md` — P3 `assertApplyResidueCycles` establishes `apply(p) = head + M`.

## Goal

Add lemma `assertSkipUntilNonMultiple(nextSeq, k)` to `SieveSequenceV0` that proves:

Given V = seq_n(k) = seq_{n+1}(px) and Calc.mod(seq_n(k+1), p) == 0:
- There exists a first index m > k where Calc.mod(seq_n(m), p) != 0
- seq_{n+1}(px + 1) == seq_n(m)
- The merged gap = sum_{i=k}^{m-1} gap_n(i) = seq_n(m) - V

This is the "gap merge" case: when a value is removed by the new filter, its gap merges with subsequent gaps until a surviving value is found.

## Current State

- Last green state before full assembly attempt: 6510 valid, 0 invalid, 0 unknown after adding acceptance bridge helpers, cumulative index-to-value ordering, and value-bound-to-index-bound ordering
- Full `assertSkipUntilNonMultiple` assembly attempt is currently too heavy: `6639 total, 6637 valid, 0 invalid, 2 unknown`
- `assertFilterPreservesNextPosition(nextSeq, k)` — handles the `Calc.mod(W, p) != 0` case
- `nextDoesNotPassAcceptedValue(k, value)` — gives `apply(k+1) <= value` when `apply(k) < value` and `accepts(value)`
- `indexOfAccepted(value)` — completeness: every accepted value appears in apply
- `assertGapSum(p)` — `sumGap(0, p) == M` (for merged gap calculation)
- `assertBlockShift(0, p)` — `apply(p) == head + M` where `p = indexOfAccepted(head + M)`
- `assertAcceptedByNextWhenOldAcceptedAndNewHeadNonMultiple(nextSeq, value)` — proves the acceptance bridge from the old tail filter to the extended next filter when `value` is not a multiple of the new head filter
- `assertNextAcceptedImpliesOldAcceptedAndNewHeadNonMultiple(nextSeq, value)` — proves the reverse bridge from extended next-filter acceptance back to old-filter acceptance plus the non-multiple fact for the new head filter
- `applyIndexOrderPreservesValues(from, until)` — proves `from <= until ==> apply(from) <= apply(until)` by induction over the already verified local strict-growth lemma
- `valueBoundImpliesIndexBound(index, bound)` — proves `apply(index) <= apply(bound) ==> index <= bound` by contradiction using strict growth and `applyIndexOrderPreservesValues`

## Termination Witness

`head + M` is always in both sequences:
- `head + M = apply(p)` where `p = indexOfAccepted(head + M)` (proved by P3)
- `Calc.mod(head + M, p) = Calc.mod(head, p) != 0` since `Calc.mod(M, p) == 0` (M is product of filterValues, p is new prime)
- Therefore `head + M` is also accepted by `nextSeq` (coprime to filterValues and to p)

This provides the termination bound: `indexOfAccepted(head + M) - k` is a valid decreasing measure for the search.

## Proof Design

### Helper: `findFirstNonMultipleAfter(k, p)`

```scala
private def findFirstNonMultipleAfter(k: BigInt, p: BigInt): BigInt = {
  require(k >= BigInt(0))
  require(p > BigInt(0))
  require(Calc.mod(head.value + filterModulus, p) != BigInt(0))
  decreases(indexOfAccepted(head.value + filterModulus) - k)
  if (Calc.mod(apply(k + BigInt(1)), p) != BigInt(0)) k + BigInt(1)
  else findFirstNonMultipleAfter(k + BigInt(1), p)
}.ensuring(res => {
  res >= k + BigInt(1) &&
  Calc.mod(apply(res), p) != BigInt(0)
})
```

### Lemma: `assertFirstNonMultipleIsAtOrBefore(k, zIdx, p)`

Proves: if `Calc.mod(apply(zIdx), p) != 0` and `zIdx > k`, then `findFirstNonMultipleAfter(k, p) <= zIdx`.

Proof by induction on `zIdx - k`:
- Base: `zIdx = k+1`. If `Calc.mod(apply(k+1), p) != 0`, then `findFirstNonMultipleAfter(k, p) = k+1 = zIdx`.
- Inductive: `zIdx > k+1`. If `Calc.mod(apply(k+1), p) != 0`, then `findFirstNonMultipleAfter(k, p) = k+1 < zIdx`. If `Calc.mod(apply(k+1), p) == 0`, then `findFirstNonMultipleAfter(k, p) = findFirstNonMultipleAfter(k+1, p) <= zIdx` by IH.

### Main Lemma: `assertSkipUntilNonMultiple(nextSeq, k)`

1. `m = findFirstNonMultipleAfter(k, p)`
2. `apply(m)` is not a multiple of p → `nextSeq.accepts(apply(m))`
3. `nextSeq.nextDoesNotPassAcceptedValue(vIdx, apply(m))` → `nextSeq(vIdx+1) <= apply(m)`
4. `nextSeq(vIdx+1)` is accepted by this seq → exists `zIdx = indexOfAccepted(nextSeq(vIdx+1))`
5. `Calc.mod(apply(zIdx), p) != 0` (since `nextSeq(vIdx+1)` is in nextSeq)
6. By `assertFirstNonMultipleIsAtOrBefore`: `m <= zIdx`
7. Strict monotonicity: `apply(m) <= apply(zIdx) = nextSeq(vIdx+1)`
8. From 3 and 7: `nextSeq(vIdx+1) == apply(m)`

### Gap Merge (Corollary)

The merged gap `apply(m) - V = sumGap(k, m)` by `assertSumGapTelescopes` from P3.

## Implementation Plan

1. Add `findFirstNonMultipleAfter(k, p)` — recursive helper with `decreases(indexOfAccepted(head+M) - k)`
2. Add `assertFirstNonMultipleIsAtOrBefore(k, zIdx, p)` — prove helper returns the FIRST non-multiple
3. Add `assertSkipUntilNonMultiple(nextSeq, k)` — main lemma (one `.holds` or `.ensuring`)
4. (Optional) Add gap merge corollary using `assertGapSum`

## Risks

1. **`indexOfAccepted` in decreases**: The decreasing measure uses `indexOfAccepted(head + M)`, which is itself a recursive function. Stainless may not accept it as a valid measure. Alternative: use `M` directly (filterModulus) as a bound on the number of allowed recursions.

2. **`assertFirstNonMultipleIsAtOrBefore` induction**: Proving `findFirstNonMultipleAfter(k, p) <= zIdx` requires induction aligned with the helper's recursion. The solver may need explicit `assert` calls at each step.

3. **Completeness connection**: Step 4 (`nextSeq(vIdx+1) = apply(zIdx)`) requires `indexOfAccepted` on this seq, which needs `accepts(nextSeq(vIdx+1))` and `nextSeq(vIdx+1) >= head.value`. Both should hold.

4. **Timeout risk**: The proof chain has multiple recursive lemmas. If timeout occurs, try inlining or simplifying.

## Fallback

If the full lemma times out, prove a simpler version: given `m = findFirstNonMultipleAfter(k, p)`, prove `nextSeq(vIdx+1) == apply(m)` without the full `forall` property about intermediate values being multiples. The `findFirstNonMultipleAfter` function's recursion already encodes this property structurally.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-06-19 | Ticket created. Termination bound is `indexOfAccepted(head+M)` using the head+M witness (exists in both sequences). Three-step plan: helper function, "first-index" lemma, main lemma. | Start with `findFirstNonMultipleAfter`. |
| 2026-06-20 | The skip proof needs an explicit bridge from old acceptance plus non-multiple-of-new-head to next-sequence acceptance. Stainless verifies this as `assertAcceptedByNextWhenOldAcceptedAndNewHeadNonMultiple`; verification is green at 6452 valid, 0 invalid, 0 unknown. | Use the bridge at the `apply(m)` step of `assertSkipUntilNonMultiple`. Next expected hard point is proving the old-stream index for `nextSeq(vIdx + 1)` is within the finite `bound`, or replacing that need with a monotone/index-order lemma. |
| 2026-06-20 | The reverse acceptance bridge is also needed for `z = nextSeq(vIdx + 1)`. Stainless verifies `assertNextAcceptedImpliesOldAcceptedAndNewHeadNonMultiple`, giving old-sequence acceptance and `Calc.mod(z, p) != 0` from next-sequence acceptance. Verification is green at 6472 valid, 0 invalid, 0 unknown. | Use the reverse bridge before calling `indexOfAccepted(z)` and before proving the first-non-multiple ordering. |
| 2026-06-20 | The cumulative index-to-value ordering lemma verifies cleanly: `applyIndexOrderPreservesValues(from, until)` lifts local strict monotonicity to `from <= until ==> apply(from) <= apply(until)`. Verification is green at 6490 valid, 0 invalid, 0 unknown. | Add the reverse-order contradiction helper next: from `apply(index) <= apply(bound)`, prove `index <= bound`. This should discharge the commented `assert(zIdx <= bound)` once `z <= apply(bound)` is known. |
| 2026-06-20 | The reverse-order contradiction helper also verifies: `valueBoundImpliesIndexBound(index, bound)` proves `apply(index) <= apply(bound) ==> index <= bound`. Verification is green at 6510 valid, 0 invalid, 0 unknown. | In the main skip proof, prove `z = nextSeq(vIdx + 1) <= apply(bound)` using `nextSeq.nextDoesNotPassAcceptedValue(vIdx, apply(bound))`, then call `valueBoundImpliesIndexBound(zIdx, bound)` to replace the brittle raw `assert(zIdx <= bound)`. |
| 2026-06-20 | Re-enabling the full `assertSkipUntilNonMultiple` lemma in one piece is too heavy for Stainless. The first timeout is at `assert(nextSeq(vIdx) < apply(m))`, even after `nextSeq(vIdx) == V` and `m >= k + 1`; a later interrupted VC also points at `assert(zIdx > k)`. Verification result: 6639 total, 6637 valid, 0 invalid, 2 unknown. | Do not keep pushing the full assembly inline. Next green-to-green path should split two tiny helpers: one proving the anchor comparison `nextSeq.indexOfAccepted(V)` gives `nextSeq(vIdx) == V < apply(m)` from `m > k`; another proving `zIdx > k` from `apply(zIdx) = z`, `z = nextSeq(vIdx + 1)`, `z > V`, and `apply(k) = V`. |
| 2026-06-20 | After backing the full lemma out to comments, `just verify` is green again: 6510 total, 6510 valid, 0 invalid, 0 unknown, time 22.39s. The attempted proof body is intentionally preserved as commented code so the next iteration can lift only one missing fact at a time. | Next concrete helper should be an index-strict ordering lemma: `from < until ==> apply(from) < apply(until)`. That should discharge the first timeout by deriving `apply(k) < apply(m)` from `m >= k + 1`, then substituting `nextSeq(vIdx) == apply(k)`. |
| 2026-06-20 | The strict index-order helper verifies: `applyIndexStrictlyPreservesValues(from, until)` proves `from < until ==> apply(from) < apply(until)` by induction over local strict growth. Verification is green at 6529 valid, 0 invalid, 0 unknown. | Use this helper to replace the timeout-prone inline proof of `nextSeq(vIdx) < apply(m)` with a small anchor lemma. |
| 2026-06-20 | The bounded search now also exposes `res <= bound`, and the recursive skip invariant verifies: `assertSkippedIndexBeforeFirstIsMultiple(k, idx, p, bound)` proves every old index between `k` and the first non-multiple returned by `findFirstNonMultipleAfter` is a multiple of `p`. Verification is green at 6571 valid, 0 invalid, 0 unknown. | This supports the recursive gap-merging framing: copied gaps correspond to immediate non-multiples, while skipped old gaps are accounted for one by one as multiples of the new filter. Next step is to connect this invariant to `nextSeq(vIdx + 1) == apply(m)`. |
| 2026-06-20 | The anchor comparison now verifies as `assertNextAnchorBeforeFirstSurvivor(nextSeq, k, p, bound)`: from the aligned value `nextSeq(indexOfAccepted(apply(k))) == apply(k)` and strict old-stream ordering, Stainless proves the next-sequence anchor is before `apply(m)`, where `m` is the first old-stream non-multiple after `k`. Verification is green at 6596 valid, 0 invalid, 0 unknown. | Use this helper before `nextSeq.nextDoesNotPassAcceptedValue(vIdx, apply(m))`. The next small bridge should prove that old skipped values are rejected by the extended next filter because they are multiples of its new head filter. |
| 2026-06-20 | The negative filter bridge now verifies as `assertRejectedByNextWhenNewHeadMultiple(nextSeq, value, p)`: if `p` is the new head of `nextSeq.filterValues` and `Calc.mod(value, p) == 0`, then `nextSeq.accepts(value)` is false. Verification is green at 6606 valid, 0 invalid, 0 unknown. | Compose this with `assertSkippedIndexBeforeFirstIsMultiple` so every old index skipped before the first survivor is explicitly rejected by `nextSeq`. |
| 2026-06-20 | The composed skipped-value lemma verifies as `assertSkippedOldValueRejectedByNext(nextSeq, k, idx, p, bound)`: every old index strictly between the aligned index `k` and the first old non-multiple is rejected by `nextSeq`. Verification is green at 6636 valid, 0 invalid, 0 unknown. | This proves the negative side of the gap merge. The remaining main step is the positive equality: use the anchor comparison plus `nextDoesNotPassAcceptedValue` to show `nextSeq(vIdx + 1) <= apply(m)`, then use first-non-multiple ordering to show the reverse inequality. |
| 2026-06-20 | The upper inequality helper now verifies as `assertNextValueAtOrBeforeFirstSurvivor(nextSeq, k, p, bound)`: once `apply(m)` is accepted by `nextSeq` and the aligned next-sequence value is strictly before it, `nextSeq.nextDoesNotPassAcceptedValue` proves `nextSeq(vIdx + 1) <= apply(m)`. Verification is green at 6688 valid, 0 invalid, 0 unknown. | This completes the easy half of the equality. The next step is the reverse inequality: map `z = nextSeq(vIdx + 1)` back to an old index `zIdx`, prove `zIdx > k`, then use `assertFirstNonMultipleIsAtOrBefore` plus old-stream monotonicity to show `apply(m) <= z`. |
| 2026-06-20 | The reverse-index helper now verifies as `assertNextSuccessorOldIndexAfterAnchor(nextSeq, k)`: for `z = nextSeq(indexOfAccepted(apply(k)) + 1)`, the old witness `indexOfAccepted(z)` is strictly after `k`. Verification is green at 6729 valid, 0 invalid, 0 unknown. | This discharges the previously timed-out `zIdx > k` fact. The next small helper should combine this with `assertNextValueAtOrBeforeFirstSurvivor`, `valueBoundImpliesIndexBound`, `assertFirstNonMultipleIsAtOrBefore`, and old-stream monotonicity to prove the reverse inequality `apply(m) <= nextSeq(vIdx + 1)`. |
| 2026-06-20 | The bounded reverse-index helper now verifies as `assertNextSuccessorOldIndexWithinBound(nextSeq, k, p, bound)`: for `z = nextSeq(indexOfAccepted(apply(k)) + 1)`, the old witness `indexOfAccepted(z)` is at most `bound`. Verification is green at 6774 valid, 0 invalid, 0 unknown. | This isolates the suspicious value-to-index bound. The next helper can now safely call `assertFirstNonMultipleIsAtOrBefore(k, zIdx, p, bound)` using the pair `zIdx > k` and `zIdx <= bound`, then finish the reverse inequality `apply(m) <= z`. |
| 2026-06-20 | The lower inequality now verifies as `assertFirstSurvivorAtOrBeforeNextValue(nextSeq, k, p, bound)`: for `m = findFirstNonMultipleAfter(k, p, bound)`, Stainless proves `apply(m) <= nextSeq(indexOfAccepted(apply(k)) + 1)`. Verification is green at 6839 valid, 0 invalid, 0 unknown. | This completes the reverse half of the equality by using the successor's old index, first-non-multiple minimality, and old-stream monotonicity. |
| 2026-06-20 | The bounded equality now verifies as `assertNextSuccessorIsFirstSurvivor(nextSeq, k, p, bound)`: `nextSeq(indexOfAccepted(apply(k)) + 1) == apply(findFirstNonMultipleAfter(k, p, bound))`. Verification is green at 6881 valid, 0 invalid, 0 unknown. | The gap-merge dots are connected for any caller-provided finite bound whose endpoint is not a multiple of `p`. The remaining work is to wrap this in the period/block-shift setup used by `assertSkipUntilNonMultiple(nextSeq, k, period)`. |
