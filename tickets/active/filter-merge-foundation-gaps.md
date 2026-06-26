# Filter-Merge Foundation — Cross-Layer Property Gaps

**Created:** 2026-06-26
**Updated:** 2026-06-26
**Status:** Plan phase
**Depends on:** `cycle-integral-filter-merge.md` (complete, 9948 valid)

## Related Tickets

- `cycle-integral-filter-merge.md` — Filter-merge lemmas at CI level (complete). Delivered `assertReplicatedCycleValueEqual`, `assertSameCIWithSameCycle`, `assertShiftAtMerge`, `assertSameBeforeMerge`, `assertShiftAfterMerge`, `findFirstMultiple`, `assertConsecutiveGapSumEqualsDiff`.
- `canonical-next-strategy.md` — Canonical transfer of Spec merge facts (complete, Leg 3 at 9472). Demonstrates the transfer pattern but skips the CI-native construction.
- `remove-extern-from-next.md` — Walk-based `collectGaps` has opacity issues. The filter-merge at CycleIntegral level provides a structural alternative.
- `sieve-foundation-cycle-integral-ones-and-filter-preserves-primes.md` — Done ticket about CI ones and filter preserves primes.

## Goal

Identify and fill **all foundational property gaps** across the dependency chain (div/mod → list → cycle → integral cycle) before attempting the full filter-merge composition proof. The sieve filter-merge theorem is a finite induction applying single-gap merges at every multiple position within one period. Each step of that induction calls for specific properties at each abstraction layer. Missing any one blocks the whole proof.

**Short term:** Close the three genuinely missing lemmas (list `repeat` properties, CI merge sum invariance, post-merge non-multiple guarantee).

**Long term:** Complete the full filter-merge composition proof: given CI with `sum mod f == 0` and `CI(0) mod f != 0`, there exists a filtered CI with no multiples of f.

## Current State

- **Verification:** 9948 valid, 0 invalid, 0 unknown (green)
- **Single-merge atom:** Verified (before/at/after, all three cases)
- **Replication invariance:** Verified (`assertReplicatedCycleValueEqual` + `assertSameCIWithSameCycle`)
- **Periodicity:** Verified (`assertCIShiftEqualsSum`, `assertModPeriodicWithMultipleSum`)
- **Survivor scan:** Verified (`findFirstMultiple` + `assertFindFirstMultipleCorrect`)

## Gap Analysis by Layer

### DIV/MOD — essentially complete

| Need | Lemma | Status |
|------|-------|--------|
| `(f * s) mod f == 0` | `assertMultipleModZero` (SieveUtils:49) | ✅ |
| `mod(a + b, b) == mod(a, b)` | `APlusBSameModPlusDiv` (AdditionAndMultiplication:24) | ✅ |
| `mod(mod(a, f*n), n) == mod(a, n)` | Via `ATimesBSameMod` (AdditionAndMultiplication:173) — used inline in `assertReplicatedCycleValueEqual` | ✅ usable, no standalone |
| `a + b*m` doesn't change mod | `ATimesBSameMod(a, b, m)` (any m) | ✅ |

**Remaining:** `modNesting` standalone wrapper. 1-line compose from `ATimesBSameMod`. Trivial.

### LIST — missing the `repeat` function entirely

| Need | Status |
|------|--------|
| `repeat(L, f): List[BigInt]` function | ❌ Doesn't exist (commented-out `repeatList` was removed from CycleIntegralProperties) |
| `sum(repeat(L, f)) == f * sum(L)` | ❌ Needs `repeat` defined, then induction on `f` using `listCombine` |
| `repeat(L, f)(k) == L(k mod |L|)` for `k < f*|L|` | ❌ Needed as the list premise for `assertReplicatedCycleValueEqual` |

**Why needed:** The replication strategy (step 1 of the filter proof) requires replicating a gap list f times. Without `repeat` and its properties, we cannot construct or reason about the replicated cycle's values list. The `assertReplicatedCycleValueEqual` lemma takes the list-access premise as a `require` — proving that premise for a concrete replicated list demands `repeat(L,f)(k) == L(k mod n)`.

### CYCLE (MemCycle) — done

| Need | Lemma | Status |
|------|-------|--------|
| `cycle(pos) == values(pos mod size)` | `findValueInCycle` | ✅ |
| `cycle.values(k) == cycle(k)` for `k < size` | `smallValueInCycle` | ✅ |
| Replicated cycle values match original | `assertReplicatedCycleValueEqual` | ✅ |

### CYCLE INTEGRAL — 3 genuine gaps

| Need | Lemma | Status |
|------|-------|--------|
| Period shift: `CI(pos+size) == CI(pos) + sum` | `assertCIShiftEqualsSum` | ✅ |
| Single merge (before/at/after) | 3 lemmas | ✅ |
| Merged gap = sum of old gaps | `assertConsecutiveGapSumEqualsDiff` | ✅ |
| `CI_replicated(pos) == CI_original(pos)` | Compose `assertReplicatedCycleValueEqual` + `assertSameCIWithSameCycle` | ✅ composable |
| **CI.sum unchanged after single merge** | ❌ **GAP 2** |
| **`CI_new(mergeIndex) mod f != 0` after merge at a multiple** | ❌ **GAP 3** |
| **`gapsFromValues(survivorValues(ci, f, pos, size))` connects to new CI's cycle.values** | ❌ composable but needs stitching (uses list `repeat` properties from GAP 1) |

### GAP 1: List `repeat` function + properties

**What:** Define `repeat(list: List[BigInt], times: BigInt): List[BigInt]` and prove:
```
sum(repeat(L, f)) == f * sum(L)
repeat(L, f)(k) == L(Calc.mod(k, L.size))  for k < f * L.size
```

**Why needed:** The replication strategy requires knowing that the replicated gap list has sum `f * old_sum` (so CI.sum mod f == 0) and that accessing the replicated list at position `k` gives the same value as the original at `k mod n`. Without these, `assertReplicatedCycleValueEqual`'s list premise cannot be discharged.

**File:** New file `src/main/scala/v1/chapter3/list/properties/ListRepeatProperties.scala` or add to `ListUtilsProperties.scala`.

**Approach:** Induction on `times` using `listCombine` for the sum property. Induction on index using list access + slice for the access property.

**Risk:** List-level induction should be fast (no CI or MemCycle). Low timeout risk.

### GAP 2: CI sum invariant under single gap merge

**What:** When two consecutive cycle values at positions `mergeIndex` and `mergeIndex+1` in CI_old are merged into one value `sum = g_k + g_{k+1}` in CI_new, prove `CI_new.sum == CI_old.sum`.

**Why needed:** After one merge (removing one multiple), the new CI still needs `sum mod f == 0` for periodicity to hold on the next scan. This invariant ensures the replication trick works for every intermediate CI.

**Math:** CI_old.sum = Σ cycle_old(i) = sum of all gaps. CI_new.sum = Σ cycle_new(i) = same sum, because the only change is merging two values into their sum. Total sum is preserved.

**File:** `CycleIntegralFilterProperties.scala`.

**Approach:** The merged cycle has size n-1, and its cycle values are: [g1, ..., g_{k-1}, gk+gk+1, g_{k+2}, ..., gn]. Sum is the same as original. Proof uses the cycle values premise (`allGapsMatchBeforeMerge` / `allGapsMatchAfterMerge`) which specify each cycle value explicitly.

**Risk:** Requires expressing "sum of all cycle values" which is `CI.sum = ListUtils.sum(cycle.values)`. The sum of the new list = sum of old list because the new list is the old list with two elements merged. Needs a list-level sum-preservation lemma.

### GAP 3: Post-merge non-multiple guarantee

**What:** If `CI_old(mergePosition) mod f == 0` (a multiple), and `CI_old(mergePosition + 1) mod f != 0` (the NEXT position is NOT a multiple), then after merging at `mergePosition`, `CI_new(mergePosition) == CI_old(mergePosition + 1)` and therefore `CI_new(mergePosition) mod f != 0`.

**Why needed:** Validates that one merge step actually REMOVES one multiple. Without this, we can't guarantee progress — the next position might also be a multiple, requiring another merge at the same position.

**Math:** `assertShiftAtMerge` proves `CI_new(mergeIndex) == CI_old(mergeIndex + 1)`. If `CI_old(mergeIndex + 1) mod f != 0`, then `CI_new(mergeIndex) mod f != 0`. The multiple at position `mergeIndex` is gone.

**File:** `CycleIntegralFilterProperties.scala`.

**Approach:** Compose `assertShiftAtMerge` with the modulo premise. The lemma is: `require(CI_old(mergeIndex) mod f == 0)`, `require(CI_old(mergeIndex + 1) mod f != 0)`, `require(single-merge premises about CI_new)`, prove `CI_new(mergeIndex) mod f != 0`.

**Risk:** Handling the edge case where `CI_old(mergeIndex + 1)` is ALSO a multiple. In that case, the merge needs to be repeated at the same position. This is handled by the composition (outer loop rescans from the same position).

**Concern:** In the sieve with replicated gaps, multiple consecutive multiples are possible. The lemma should handle the general case: after merge at position p, if CI_old(p+1) mod f == 0 (another multiple), the new CI_new(p) is still a multiple. Then the composition rescans from p. The lemma should state the conditional: `CI_new(p) mod f == CI_old(p+1) mod f`.

## Approaches Considered

### Approach: Fill gaps bottom-up (RECOMMENDED)

Fill each gap in dependency order: list `repeat` → CI sum invariance → post-merge modulo guarantee → composition.

**Dependency order:**
1. **GAP 1:** List `repeat` function + sum + access properties
2. **GAP 2:** CI sum invariant under single merge
3. **GAP 3:** Post-merge non-multiple guarantee
4. **Composition:** Stitch `gapsFromValues` + `survivorValues` chain into `allGapsMatch` premise
5. **Full theorem:** Combine all into the complete filter-merge composition

**Strengths:** Each gap is small (1-2 assertions) and can be verified independently. The list `repeat` property is the foundation — everything else builds on it.

**Risks:** GAP 2 (CI sum invariant) requires reasoning about the sum of cycle values list which involves `ListUtils.sum`. The list-level operations should verify quickly since there's no CI recursion.

## Assumptions

1. `ATimesBSameMod` handles arbitrary signed `m` for modulo shift proofs
2. `listCombine` (`sum(A ++ B) == sum(A) + sum(B)`) is adequate for the replication sum proof
3. `assertConsecutiveGapSumEqualsDiff` is the arithmetic foundation for GAP 2
4. The existing single-merge lemmas (`assertSameBeforeMerge`, `assertShiftAtMerge`, `assertShiftAfterMerge`) are correct and complete
5. MemCycle construction from filtered gaps is done EXTERNALLY (not inside `.holds` lemmas)
6. The composition proof uses `decreases(ci.size)` for termination (one merge reduces size by 1)

## Risks

1. **List `repeat` access property:** Proving `repeat(L,f)(k) == L(k mod n)` requires modulo arithmetic on list indices. The `Calc.mod` wrapper + list access might be heavy. Mitigation: use `findValueInCycle` on the MemCycle wrapping the list instead.
2. **CI sum invariant:** `CI.sum` is `ListUtils.sum(cycle.values)`. Proving two lists have the same sum requires a list equivalence lemma. If the solver can't see through the list structure, this may timeout. Mitigation: use explicit list construction with `listCombine` on the concatenation of sublists.
3. **Composition proof:** The full filter-merge composition requires induction on `ci.size` with MemCycle construction at each step. This is the same wall as the walk-based `collectGaps`. The approach is to prove RELATIONSHIPS (not constructions) — each step takes two CIs as parameters and proves a relationship. The caller constructs the intermediate CIs externally.
4. **Edge cases:** Empty cycle (size 0), cycle where all values are multiples (no survivors), cycle where only one position is non-multiple. Need to handle or exclude these cases explicitly.

## Validation

- `green-to-green`: verify before and after each change
- `small-changes`: ONE lemma per verify cycle
- Target verification count: maintain 9948+ valid
- Target files:
  - `src/main/scala/v1/chapter3/list/properties/ListRepeatProperties.scala` — GAP 1
  - `src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralFilterProperties.scala` — GAP 2, GAP 3

## Implementation Plan

### Phase 1: List foundation (GAP 1)
1. Define `repeat(list: List[BigInt], times: BigInt): List[BigInt]` — `ListRepeatProperties.scala`
2. Prove `assertRepeatSumMultiplier(L, f): sum(repeat(L,f)) == f * sum(L)` — uses `listCombine` + induction on `f`
3. Prove `assertRepeatAccess(L, f, k): repeat(L,f)(k) == L(Calc.mod(k, L.size))` for `k < f * L.size`

### Phase 2: CI merge invariants (GAP 2, GAP 3)
4. Prove `assertMergedSumPreserved(oldCI, newCI, mergeIndex): newCI.sum == oldCI.sum` — `CycleIntegralFilterProperties.scala`
5. Prove `assertMergedPositionNotMultiple(oldCI, newCI, mergeIndex, f): CI_new(mergeIndex) mod f == CI_old(mergeIndex + 1) mod f` — extends `assertShiftAtMerge`

### Phase 3: Composition stitching
6. Prove `gapsFromValues(survivorValues(ci, f, 0, ci.size))` satisfies `allGapsMatch` for a new CI constructed externally
7. Full filter-merge composition theorem

## Related Articles

- `integral-cycle.md` — §5.2 "Invariance by x-fold concatenation" (draft, now achievable)
- `sieve-sequence.md` — §3-7 verified sieve properties
- `integral.md` — discrete integral definition
- `cycle.md` — cycle equivalence

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-06-26 | Ticket created. Gap analysis complete: 3 genuine gaps (list repeat, CI sum invariance, post-merge non-multiple) + 1 composable (mod nesting). Related tickets reviewed. Single-merge atom and replication invariance already verified at 9948 valid. | Start Phase 1: list `repeat` function. |
