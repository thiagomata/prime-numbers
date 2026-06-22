# Gap Positivity Proof — Remove @extern from next()

**Created:** 2026-06-08
**Status:** Planning
**Depends on:** `walk-based-pipeline.md` (Complete, 4309 valid, 0 invalid)

---

## Goal

Remove `@extern` from `CycleSieveSequence.next()` by proving that all gaps computed by the walk-based pipeline are strictly positive (`> 0`) and non-empty.

---

## Current State

- **Verification:** 4309 valid, 0 invalid ✅
- **Tests:** 26/26 pass ✅
- **`next()` status:** `@extern`

---

## The Three Things That Need Proof

When `next()` calls `nextGapCycleV2(this)`, three VCs block verification:

```
nextGapCycleV2(seq):
  gaps = nextGapsWalkV2(seq)            (walk produces list of gaps)
    └── collectGapsV2(seq, newHead, 1, steps, [])
          for each step:
            current = apply(pos+1)
            if current % head != 0:     (survivor)
              gap = current - lastSurvivor
              gaps = gap :: gaps


  require(gaps.nonEmpty)                → VC #1
  require(allGreaterThan(gaps, 0))      → VC #2
  GapCycle(gaps)                        → constructor require = VC #2
```

### VC #1: `gaps.nonEmpty`

**What it needs:** At least one of the `head * gapCycle.size` values walked survives filtering by `head`.

**Already known:** Each gap ≥ 1 (GapCycle invariant). After one full gapCycle, cumulative sum = `gapCycle.sum = modulus = product(primes.tail)`. Since `head` is a prime NOT in `primes.tail`: `modulus % head ≠ 0`.

After `head` cycles, the residues modulo `head` cycle through all non-zero values because the per-cycle shift `modulus % head ≠ 0`. So there are exactly `(head-1) * gapCycle.size > 0` survivors.

**Challenge:** Proving `head ∤ modulus` needs Euclid's lemma (prime doesn't divide product of other primes). Not currently available in the system.

**Difficulty:** HIGH unless we add a stronger invariant to CycleSieveSequence.

---

### VC #2: `allGreaterThan(gaps, 0)`

This has **two sub-problems**:

#### Sub-problem 2a: Each individual gap > 0

Each gap = `current - lastSurvivor`. Both are values from the integral.

**Already proved for consecutive positions:**
```
ci(k+1) - ci(k) = ci.cycle(k+1)    (assertDiffEqualsCycleValue)
ci.cycle(k+1) > 0                  (assertCycleValuePositive, from GapCycle invariant)
∴ ci(k+1) > ci(k)                  (consecutive strictly increasing)
```

**What's missing:** The gap may span **non-consecutive** positions (intermediate values filtered). Need:
```
ci(q) > ci(p) for any q > p
```
Proof: simple induction over `q-p` using the consecutive lemma at each step.

**Difficulty:** LOW. This is a textbook induction lemma.

#### Sub-problem 2b: The output list `allGreaterThan` property

Need: if each gap added to the list is > 0, then the final list has all gaps > 0.

This follows from:
- `allGreaterThan` defined as: `list.head > v && allGreaterThan(list.tail, v)`
- Each recursive step builds `gap :: gaps` where `gap > 0` and `allGreaterThan(gaps, 0)`
- By induction: `allGreaterThan(gap :: gaps, 0)` holds at every step

**Difficulty:** LOW. Induction mirroring the recursion of `collectGapsV2`.

---

## Summary Table

| # | What | Difficulty | Approach |
|---|------|------------|----------|
| 2a | gap > 0 (current > lastSurvivor) | LOW | Induction lemma `ci(q) > ci(p)` using existing lemmas |
| 2b | allGreaterThan(result, 0) | LOW | Mirror collectGapsV2 recursion, prove each step preserves invariant |
| 1 | `gaps.nonEmpty` | HIGH | Needs Euclid's lemma or a new invariant |

---

## Proposed Plan

### Cycle 1: Add transitivity lemma (fixes 2a)

```scala
def assertCycleIntegralIncreasing(ci: CycleIntegral, a: BigInt, b: BigInt): Boolean = {
  require(a >= 0)
  require(b > a)
  require(ci.initialValue >= BigInt(0))
  require(ListBoundUtils.allGreaterThan(ci.cycle.values, BigInt(0)))
  require(ci.cycle.values.nonEmpty)
  require(ci.cycle.size > 0)
  decreases(b - a)
  if (a + 1 == b) {
    assert(assertDiffEqualsCycleValue(ci, a))
    assert(assertCycleValuePositive(ci, a + 1))
    ci(b) > ci(a)
  } else {
    assert(assertCycleIntegralIncreasing(ci, a, b - 1))
    assert(assertDiffEqualsCycleValue(ci, b - 1))
    assert(assertCycleValuePositive(ci, b))
    ci(b) > ci(a)
  }
}.holds
```

Adds ~1 VC (induction base + step). Expected: green.

### Cycle 2: Add inductive walk lemma (fixes 2b)

```scala
def assertCollectGapsV2AllPositive(
  seq: CycleSieveSequence, lastSurvivor: BigInt,
  pos: BigInt, remaining: BigInt, gaps: List[BigInt]
): Boolean = {
  require(remaining >= 0)
  require(pos >= 1)
  require(lastSurvivor > 0)
  require(ListBoundUtils.allGreaterThan(gaps, BigInt(0)))
  decreases(remaining)
  if (remaining == BigInt(0)) {
    ListBoundUtils.allGreaterThan(gaps.reverse, BigInt(0))
  } else {
    val current = seq.apply(pos + 1)
    if (current % seq.head == BigInt(0)) {
      assertCollectGapsV2AllPositive(seq, lastSurvivor, pos + 1, remaining - 1, gaps)
    } else {
      assert(assertCycleIntegralIncreasing(seq.integral, specPos, pos))
      assert(current > lastSurvivor)
      assert(gap > 0)
      // allGreaterThan(gap :: gaps, 0) follows from gap > 0 && allGreaterThan(gaps, 0)
      assertCollectGapsV2AllPositive(seq, current, pos + 1, remaining - 1, gap :: gaps)
    }
  }
}.holds
```

Mirrors `collectGapsV2` structure exactly. Uses Cycle 1 lemma inside.
Expected: green.

### Cycle 3: Wire and remove @extern

- Add `assert(assertCollectGapsV2AllPositive(...))` in `nextGapsWalkV2`
- Remove `@extern` from `next()`

**Risk:** If VC #1 (nonEmpty) still blocks, we can:
- Accept @extern stays, OR
- Add `require(seq.gapCycle.sum % seq.head != 0)` to `nextGapCycleV2` and adjust the CycleSieveSequence invariant to guarantee this

---

## Open Question: nonEmpty

The cleanest option if nonEmpty proves hard:

**Option A:** Add invariant `primes.tail.product % primes.head != 0` to CycleSieveSequence
- This is always true (Euclid) but proving it in Stainless is the heavy part

**Option B:** Narrow the @extern boundary — keep @extern only on `nextGapCycleV2` or on the individual require
- Saves progress on 2a/2b (which are the main value)

**Option C:** `require(seq.head > gapCycle.size)`
- For any prime `p`, in `p` values there are at most `gapCycle.size / gapCycle.size = 1` per cycle... doesn't quite work

---

## Related

- `OBJECTS.md` lines 661, 669-670
- `articles/integral-cycle.md` — CycleIntegral properties
- `articles/sieve-sequence.md` — mathematical proof of strictly increasing (not in code)
- `src/main/scala/v1/cycle/integral/recursive/properties/CycleIntegralProperties.scala`
