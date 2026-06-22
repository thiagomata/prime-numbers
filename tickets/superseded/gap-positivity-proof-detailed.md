# Gap Positivity Proof — Detailed Explanation

**Goal:** Remove `@extern` from `CycleSieveSequence.next()` by proving the walk-based pipeline produces valid gaps (non-empty, all > 0).

---

## 1. What Are We Proving?

### The Problem

When `next()` computes the next sieve sequence, it needs to compute a new gap cycle:

```scala
def nextGapCycleV2(seq: CycleSieveSequence): GapCycle = {
  val gaps = nextGapsWalkV2(seq)   // Walk-based gap computation
  require(gaps.nonEmpty)          // VC #1: Must have at least one gap
  require(ListBoundUtils.allGreaterThan(gaps, BigInt(0)))  // VC #2: All gaps > 0
  GapCycle(gaps)
}
```

The `GapCycle` constructor has requires:
- `gaps.nonEmpty` — at least one gap in the list
- `allGreaterThan(gaps, 0)` — every gap is strictly positive

Currently, these requires are not verified, so `next()` is marked `@extern` (unverified).

### The Walk-Based Pipeline

The walk computes gaps by walking through the integral sequence and filtering multiples of the new head prime:

```scala
def collectGapsV2(seq, lastSurvivor, lastPos, pos, remaining, gaps):
  if remaining == 0:
    return gaps.reverse  // Done: reverse to correct order
  else:
    current = seq.apply(pos + 1)  // Next value in sequence
    if current % seq.head == 0:   // Multiple of head → filtered out
      recurse with same lastSurvivor
    else:
      gap = current - lastSurvivor  // Gap between survivors
      recurse with new lastSurvivor = current, gap :: gaps
```

We walk `head * gapCycle.size` positions (one full cycle of the new head through the existing gap cycle).

---

## 2. What Needs To Be Proved

### VC #1: `gaps.nonEmpty` — At Least One Survivor

**What it means:** After walking `head * gapCycle.size` values, at least one of them is NOT a multiple of `head`.

**Why it should be true:**
- After one complete gap cycle, cumulative sum = `gapCycle.sum = modulus = product(primes.tail)`
- Since `head` is a prime NOT in `primes.tail`, by Euclid's lemma: `head ∤ modulus`
- As we walk through cycles, residues modulo `head` cycle through all non-zero values
- Since `head ∤ modulus`, the shift between cycles is non-zero, so we eventually hit all residues
- There are exactly `(head-1) * gapCycle.size` survivors

**Current blocker:** We don't have Euclid's lemma (prime doesn't divide product of other primes) in the system.

**Difficulty:** HIGH

---

### VC #2: `allGreaterThan(gaps, 0)` — All Gaps Are Positive

**What it means:** Every gap computed is strictly positive (> 0).

**Why it should be true:** Each gap = `current - lastSurvivor`. Both are values from the integral sequence. If we can prove the integral is strictly increasing, then any later survivor is greater than any earlier survivor, so gaps are positive.

This has two sub-problems:

#### 2a: Non-Consecutive Gap > 0

**What it means:** For any positions `p < q`, the integral value at `q` is greater than at `p`:
```
ci(q) > ci(p) for any q > p
```

This is **transitivity** of the strictly increasing property.

**Already proven for consecutive positions:**
```scala
// From CycleIntegralProperties:
assertDiffEqualsCycleValue(ci, a): ci(a+1) - ci(a) == ci.cycle(a+1)
assertCycleValuePositive(ci, a+1): ci.cycle(a+1) > 0

// Therefore: ci(a+1) > ci(a) for consecutive positions
```

**What's missing:** The gap may span **non-consecutive** positions (intermediate values filtered out). Need to prove that if `ci(a+1) > ci(a)` and `ci(a+2) > ci(a+1)`, then `ci(a+2) > ci(a)`.

**Solution:** Induction over distance:
```scala
def assertCycleIntegralIncreasing(ci, a, b):  // PROVEN ✅
  // Base: ci(a+1) > ci(a) using assertDiffEqualsCycleValue + assertCycleValuePositive
  // Step: assume ci(b-1) > ci(a), prove ci(b) > ci(a)
  //   ci(b) - ci(b-1) > 0 (cycle value positive)
  //   ci(b) > ci(b-1) > ci(a)
```

**Status:** ✅ **Already added and verified!**

#### 2b: Output List `allGreaterThan` Property

**What it means:** If each gap added to the list is > 0, then the final list has all gaps > 0.

**Why it should be true:** The `allGreaterThan` property is defined as:
```scala
def allGreaterThan(list, v):
  list.isEmpty → true
  list.head > v && allGreaterThan(list.tail, v)
```

Each recursive step builds `gap :: gaps` where:
- `gap > 0` (from 2a)
- `allGreaterThan(gaps, 0)` (induction hypothesis)

By induction, `allGreaterThan(gap :: gaps, 0)` holds at every step.

**Solution:** A lemma mirroring `collectGapsV2`:
```scala
def assertCollectGapsV2AllPositive(...): // Need to add
  // Base case: if remaining == 0, gaps.reverse maintains positivity
  // Step: for each survivor found:
  //   - assert ci(lastPos) < ci(pos) using assertCycleIntegralIncreasing
  //   - gap = current - lastSurvivor > 0
  //   - recurse with gap :: gaps
```

**Status:** ❌ **Failing — solver can't verify**

---

## 3. Lemmas We Have

### Already Verified

| Lemma | File | What It Proves |
|-------|------|----------------|
| `assertDiffEqualsCycleValue(ci, pos)` | CycleIntegralProperties.scala | `ci(pos+1) - ci(pos) == ci.cycle(pos+1)` |
| `assertCycleValuePositive(ci, pos)` | CycleIntegralProperties.scala | `ci.cycle(pos) > 0` (uses GapCycle invariant) |
| `assertCycleIntegralPositive(ci, pos)` | CycleIntegralProperties.scala | `ci(pos) > 0` by induction |
| `assertCycleIntegralIncreasing(ci, a, b)` | CycleIntegralProperties.scala | `ci(b) > ci(a)` for any `b > a` ✅ **NEWLY ADDED** |

### The New Lemma We're Trying to Add

```scala
def assertCollectGapsV2AllPositive(
  seq: CycleSieveSequence, 
  lastSurvivor: BigInt, 
  lastPos: BigInt,
  pos: BigInt, 
  remaining: BigInt, 
  gaps: List[BigInt]
): Boolean = {
  require(remaining >= 0)
  require(pos >= 1)
  require(lastSurvivor > 0)
  require(lastPos >= 0)
  require(lastPos < pos)
  require(ListBoundUtils.allGreaterThan(gaps, BigInt(0)))
  decreases(remaining)
  if (remaining == BigInt(0)) {
    ListBoundUtils.allGreaterThan(gaps.reverse, BigInt(0))
  } else {
    val current = seq.apply(pos + 1)
    if (current % seq.head == BigInt(0)) {
      assertCollectGapsV2AllPositive(seq, lastSurvivor, lastPos, pos + 1, remaining - 1, gaps)
    } else {
      // KEY ASSERTION: ci(pos) > ci(lastPos)
      assert(CycleIntegralProperties.assertCycleIntegralIncreasing(seq.integral, lastPos, pos))
      val gap = current - lastSurvivor
      assert(gap > BigInt(0))
      assertCollectGapsV2AllPositive(seq, current, pos, pos + 1, remaining - 1, gap :: gaps)
    }
  }
}.holds
```

---

## 4. What's Missing / Not Working

### Current Failure

The solver returns **UNKNOWN** for the assertion `gap > BigInt(0)` in the lemma.

**Root cause:** Even though we assert `ci(lastPos) < ci(pos)` (via `assertCycleIntegralIncreasing`), the solver can't deduce that `current > lastSurvivor`, hence can't conclude `gap > 0`.

**Why:** The transitivity lemma (`assertCycleIntegralIncreasing`) proves that integral values increase, but there's a gap between:
- `ci(lastPos) < ci(pos)` — integral values at positions
- `lastSurvivor = ci(lastPos)` and `current = ci(pos)` — specific values at those positions

Wait, they ARE the same! `lastSurvivor = seq.apply(lastPos + 1)` and `current = seq.apply(pos + 1)` which are integral values.

The issue is likely the solver needs more explicit chaining or the requires aren't being propagated correctly through the recursion.

---

## 5. Example Trace

Let's trace through `S_1V2().next()` (head=3, gapCycle=[2]):

```
Initial: lastSurvivor = seq.apply(1) = 5, lastPos = 0, pos = 1, remaining = 3*1 = 3
Step 1: current = seq.apply(2) = 7
        7 % 3 = 1 ≠ 0 → survivor
        gap = 7 - 5 = 2 > 0 ✅
        recurse: lastSurvivor=7, lastPos=1, pos=2, remaining=2, gaps=[2]
Step 2: current = seq.apply(3) = 9
        9 % 3 = 0 → filtered
        recurse: lastSurvivor=7, lastPos=1, pos=3, remaining=1, gaps=[2]
Step 3: current = seq.apply(4) = 11
        11 % 3 = 2 ≠ 0 → survivor
        gap = 11 - 7 = 4 > 0 ✅
        recurse: lastSurvivor=11, lastPos=3, pos=4, remaining=0, gaps=[4,2]
Base: remaining == 0 → gaps.reverse = [2,4]
```

Result: `GapCycle([2, 4])` ✅

All gaps positive! The lemma should prove this works for any valid input.

---

## 6. Next Steps

1. **Fix the lemma** — The solver is struggling with `gap > BigInt(0)`. Try:
   - Adding explicit `current > lastSurvivor` assertion before computing gap
   - Or using a different approach: prove `allGreaterThan(gaps.reverse, 0)` in base case directly

2. **Deal with nonEmpty** — If gap positivity is proven but nonEmpty still fails:
   - Option A: Accept `@extern` stays (we made progress on gap > 0)
   - Option B: Add invariant to `CycleSieveSequence` requiring `primes.tail.product % primes.head != 0`

3. **Wire and remove @extern** — Once both VCs pass, remove `@extern` from `next()`

---

## Summary

| VC | What | Status | Blocker |
|----|------|--------|---------|
| 1 | `gaps.nonEmpty` | NOT STARTED | Needs Euclid's lemma (HIGH difficulty) |
| 2a | `ci(b) > ci(a)` for any b>a | ✅ DONE | None - transitivity lemma added |
| 2b | `allGreaterThan(result, 0)` | ❌ FAILING | Solver can't verify `gap > 0` |

**Priority:** Fix 2b first (LOW difficulty per ticket), then deal with 1.