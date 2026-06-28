# Filter-Merge Foundation — Cross-Layer Property Gaps

**Created:** 2026-06-26
**Updated:** 2026-06-26
**Status:** Plan phase
**Depends on:** `../done/cycle-integral-filter-merge.md` (complete, 9948 valid)

## Related Tickets

- `../done/cycle-integral-filter-merge.md` — Filter-merge lemmas at CI level (complete). Delivered `assertReplicatedCycleValueEqual`, `assertSameCIWithSameCycle`, `assertShiftAtMerge`, `assertSameBeforeMerge`, `assertShiftAfterMerge`, `findFirstMultiple`, `assertConsecutiveGapSumEqualsDiff`.
- `canonical-next-strategy.md` — Canonical transfer of Spec merge facts and the current survival-walk open hole. Demonstrates the transfer pattern but skips the CI-native construction.
- `../superseded/remove-extern-from-next.md` — Old walk-based `collectGaps` framing. The filter-merge at CycleIntegral level remains a structural alternative.
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

### Phase 1: List foundation (GAP 1) ✅ DONE
1. Define `repeat(list: List[BigInt], times: BigInt): List[BigInt]` — `ListRepeatProperties.scala` ✅
2. Prove `assertRepeatSumMultiplier(L, f): sum(repeat(L,f)) == f * sum(L)` — uses `listCombine` + induction on `f` ✅
3. Prove `assertRepeatedIndex`: `repeat(L, f)(k) == L(Calc.mod(k, L.size))` ✅
4. Prove `assertConcatAccessLeft/Right`: `++` access properties ✅
5. Create `RepeatedList` class with `apply`/`toValues`/`size`/`sum` + ensurings ✅
6. Prove `assertSumMultiplier` for `RepeatedList` ✅
7. Prove `assertElementNotMultiple` for `RepeatedList` ✅

### Phase 2: CI merge invariants (GAP 2, GAP 3) ⚠️ PARTIAL
4. ~~Prove `assertMergedSumPreserved(oldCI, newCI, mergeIndex): newCI.sum == oldCI.sum`~~ — timed out (CI level), commented out
5. Prove `assertRemoveMultipleModNotZero`: `CI_new(m) mod f != 0` if `CI_old(m+1) mod f != 0` ✅
6. Prove `assertCycleAtSizeMatch`: cycle values at period boundary match ✅
7. Prove `assertNewCIAtSizeEqualsOld`: `CI_new(newSize) == CI_old(oldSize)` ✅
8. Prove `assertMergeSumBase` (list-level, base case) ✅
9. Prove `assertMergeSumStep` (list-level, inductive step) ✅
10. ~~Prove `assertMergeSumPreserved` (list-level, full induction)~~ — 3+ failed attempts, commented out ⚠️

### Phase 3: Composition stitching ✅ DONE
11. Prove `gapsFromValues(survivorValues(ci, f, 0, ci.size))` satisfies `allGapsMatch` for a new CI ✅
12a. Prove survivors contain no multiples of f ✅
12b. Full filter-merge composition theorem ✅

## What `assertFilterMergeComposition` proves

Given:
- `originalCI` with `CI(0) mod f != 0`
- `survivors = survivorValues(originalCI, f, 0, originalCI.size)`
- `newCI` built from survivors: `initialValue = survivors.head`, `cycle.values = gapsFromValues(survivors)`

Proves: `newCI(k) mod f != 0` for all `k in [0, maxIndex]` by induction.

**Composes:** `assertNewCIMatchesSurvivors` (maps newCI to survivors) + `assertSurvivorAtNotMultiple` (survivors have no multiples).

## Related Articles

- `integral-cycle.md` — §5.2 "Invariance by x-fold concatenation" (draft, now achievable)
- `sieve-sequence.md` — §3-7 verified sieve properties
- `integral.md` — discrete integral definition
- `cycle.md` — cycle equivalence

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-06-26 | Ticket created. Gap analysis complete: 3 genuine gaps (list repeat, CI sum invariance, post-merge non-multiple) + 1 composable (mod nesting). Related tickets reviewed. Single-merge atom and replication invariance already verified at 9948 valid. | Start Phase 1: list `repeat` function. |
| 2026-06-26 | GAP 1 (list foundation) complete. `repeat`, `assertRepeatSumMultiplier`, `assertRepeatedIndex`, `assertRepeatSize`, `assertConcatAccessLeft`, `assertConcatAccessRight` all verified. `RepeatedList` class created with `apply`/`toValues`/`size`/`sum` ensurings. `RepeatedListProperties` with `assertSumMultiplier` (9/9, base + step induction), `assertElementNotMultiple` (8/8). 10135 valid. | Move to GAP 2 and GAP 3. |
| 2026-06-26 | GAP 3 (post-merge non-multiple) complete. `assertRemoveMultipleModNotZero` (16/16) — after merge at multiple, new value not a multiple provided next old value isn't. 10102 valid. | Move to GAP 2. |
| 2026-06-26 | GAP 2 atom `assertCycleAtSizeMatch` (13/13): `new.cycle(newSize) == old.cycle(oldSize)` given `new.cycle(0) == old.cycle(0)`. | Next step. |
| 2026-06-26 | GAP 2 atom `assertNewCIAtSizeEqualsOld` (33/33): `CI_new(newSize) == CI_old(oldSize)` using `assertCycleAtSizeMatch` + `assertDiffEqualsCycleValue` + merge lemmas. Two branches (after merge vs at merge). | Next step. |
| 2026-06-26 | GAP 2 composition `assertMergedSumPreserved` at CI level: timed out. Composes `assertCIShiftEqualsSum` ×2 + `assertNewCIAtSizeEqualsOld`. VC explosion. Commented out. | Move to list-level approach. |
| 2026-06-26 | GAP 2 list-level `assertMergeSumBase` (8/8): sum equality when mergeIndex==0, heads merge, tail sums match. `assertMergeSumStep` (5/5): sum equality when heads match and tail sums match. | Next step. |
| 2026-06-26 | GAP 2 list-level induction `assertMergeSumPreserved`: 3+ failed attempts. The solver can't propagate tail premises (`oldValues.head == newValues.head`, tail sum equality) through the recursion. Each variant: conditional requires (`||`) in top-level require + explicit assertions for size/element equality, recursive call preconditions still fail. Commented out. 10193 green. **ASKING FOR HELP** on this induction. The atoms are verified; the composition is the wall. | Await guidance. |
| 2026-06-26 | **GAP 2 CLOSED via Approach 1 (decompose via `sumAfterMerge`).** Added `newValuesAfterMerge` predicate (mirrors `sumAfterMerge`'s recursion shape) + `assertSumNewValuesAfterMerge` bridge lemma (`sum(newValues) == sumAfterMerge(oldValues, mergeIndex)`, 31/31, 4.72s) + `assertMergeSumPreserved` closure (composes bridge + verified `assertMergePreservesListSum`, 15/15, 4.30s). Full verify `10256 valid: 10256 invalid: 0 unknown: 0` (+63 over 10193). **Approach 2 (bubble premises into induction) unnecessary — Approach 1 succeeded.** | Proceed to Phase 3 (composition stitching) or revisit `assertMergedSumPreserved` at CI level with the list foundation now in place. |
| 2026-06-27 | List repeat foundation expanded: `assertRepeatConcat` (8/8), `assertRepeatSumDecomposition` (15/15), `assertRepeatSumTimes` (3/3), `assertModCycleEqualsMemCycle` bridge (3/3). 10285 valid (+29). Full "repeated cycle values equal" (MemCycle/ModCycle/CI) TIMEOUT: solver can't stitch `findValueInCycle` + `assertRepeatedIndex` in one VC. Bridge lemma `assertModCycleEqualsMemCycle` verified, serves as stepping stone. | Move to Phase 3: composition stitching (item 11). |
| 2026-06-27 | Phase 3 item 12a: `assertSurvivorAtNotMultiple` (24/24) — proves `Calc.mod(survivors(index), filterValue) != 0` for any index in `survivorValues(ci, f, start, count)`. Mirrors `survivorValues` recursion to prove by induction that every included value is not a multiple of `f`. Also added: `assertGapsFromValuesSize` (9/9), `assertFirstSurvivorHead` (8/8), `assertNewCIMatchesSurvivors` (20/20). 10352 valid (+17). | Proceed to full composition theorem. |
| 2026-06-27 | Phase 3 item 12b END: `assertFilterMergeComposition` (34/34) — full filter-merge composition theorem. Takes originalCI + newCI + survivors + filterValue, proves `newCI(k) mod f != 0` for all k up to maxIndex. Composes: `assertNewCIMatchesSurvivors` (maps newCI values to survivor sequence) + `assertSurvivorAtNotMultiple` (proves each survivor is not a multiple). 10386 valid (+34). **All Phase 3 items complete. Ticket done.** | Mark ticket as complete. |

### GAP 2 Resolution (2026-06-26)

**Root cause of the failed induction:** `assertMergeSumPreserved`'s recursion needed the *tail-merge-relation* (`newValues.tail(mergeIndex-1) == oldValues.tail(mergeIndex-1) + oldValues.tail(mergeIndex)`) at the recursive call, but the outer lemma only had the relation at the original `mergeIndex`. The solver couldn't derive the shifted relation from the outer `require`s.

**Why decomposition works:** `sumAfterMerge` is defined recursively with the *same structure* as the merged list. So relating `newValues` to `sumAfterMerge` is a *predicate match* (`newValuesAfterMerge`), not an arithmetic equality proof. The predicate mirrors the recursion exactly, so its induction propagates trivially. Then `assertMergePreservesListSum` (already verified) closes `sumAfterMerge == sum(oldValues)`.

**Lesson (LEARNINGS candidate):** when a list-equality induction stalls on tail-relation propagation, decompose into:
1. A *predicate* that mirrors a verified recursive helper's structure (structural match, easy to induct).
2. A *bridge* lemma proving the candidate list matches the helper's output (trivial IH).
3. The *helper*'s own correctness (already verified).

This converts an arithmetic-induction wall into a structural-match + two easy inductions. The key is choosing a helper whose recursion shape matches the candidate list's structure — `sumAfterMerge` matched because both walk the mergeIndex down identically.

### 2026-06-27: List repeat foundation expansion

**Goal:** Add `assertRepeatConcat` (repeat = concat), `assertRepeatSumDecomposition` (sum decomposes), and prove repeated-list values equal to original through all layers (list → ModCycle → MemCycle → CycleIntegral).

**Results:**
- `assertRepeatConcat`: `repeat(list,n) == list ++ repeat(list, n-1)` — verified (8/8)
- `assertRepeatSumDecomposition`: `sum(repeat(list,n)) = sum(list) + sum(repeat(list,n-1))` — verified (15/15)
- `assertRepeatSumTimes`: `sum(repeat(list,n)) = sum(list) * n` — verified (3/3)
- `assertModCycleEqualsMemCycle` (bridge: if values match, ModCycle(k) == MemCycle(k)) — verified (3/3)
- Total: 10285 valid (+29 from 10256)

**Failed/Timeout:**
- `assertRepeatedCycleValuesEqual` (MemCycle: prove cycle values match given repeat relationship): TIMEOUT on postcondition. Solver can't stitch `findValueInCycle` + implied `assertRepeatedIndex` relationship through the VC.
- ModCycle version (calls MemCycle version): TIMEOUT (inherits the MemCycle timeout)
- `assertReplicatedCIValuesEqual` (CycleIntegral level): TIMEOUT on `replicatedCI(position) == originalCI(position)`

**Root cause of timeout:** The postcondition `repeatedCycle(position) == originalCycle(position)` using only `findValueInCycle` is insufficient — the solver needs to connect `repeatedCycle.values(Calc.mod(p, repeated.size))` with `originalCycle.values(Calc.mod(p, original.size))` via `repeat(values, times)`. This requires `assertRepeatedIndex` to be called explicitly, but even that may not help if the solver can't unfold the `repeat` definition within the VC.

**Possible solutions (future):**
1. Decompose: prove `repeatedCycle(calc.mod(p, repeated.size)) == originalCycle(calc.mod(p, original.size))` as a separate lemma first
2. Use `assertRepeatedIndex` directly instead of `findValueInCycle` as the bridge
3. Revisit with a faster solver (native Z3 instead of smt-z3 fallback)

**Why decomposition works:** `sumAfterMerge` is defined recursively with the *same structure* as the merged list. So relating `newValues` to `sumAfterMerge` is a *predicate match* (`newValuesAfterMerge`), not an arithmetic equality proof. The predicate mirrors the recursion exactly, so its induction propagates trivially. Then `assertMergePreservesListSum` (already verified) closes `sumAfterMerge == sum(oldValues)`.

**Lesson (LEARNINGS candidate):** when a list-equality induction stalls on tail-relation propagation, decompose into:
1. A *predicate* that mirrors a verified recursive helper's structure (structural match, easy to induct).
2. A *bridge* lemma proving the candidate list matches the helper's output (trivial IH).
3. The *helper*'s own correctness (already verified).

This converts an arithmetic-induction wall into a structural-match + two easy inductions. The key is choosing a helper whose recursion shape matches the candidate list's structure — `sumAfterMerge` matched because both walk the mergeIndex down identically.
