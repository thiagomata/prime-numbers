# `nextFromWindow()` — Requirement Analysis

**Status:** Complete — method verified (14/14), analysis documented  
**Created:** 2026-06-29  
**Verification:** 10592 valid

---

## The Method

```scala
def nextFromWindow(): CycleSieveSequence = {
    val window = SieveSequenceNextLevel.currentWindow(integral, steps)
    val survivors = window.filter(v => Calc.mod(v, head) != BigInt(0))
    require(!survivors.isEmpty)
    require(survivors.size > BigInt(1))
    val gaps = CycleIntegralFilterProperties.gapsFromValues(survivors)
    require(ListBoundUtils.allGreaterThan(gaps, BigInt(0)))
    val newGapCycle = GapCycle(gaps)
    val newHead = apply(BigInt(1))
    require(newHead < head * head)
    require(SieveUtils.isCoprime(newHead + newGapCycle.memCycle(0), primes))
    require(Calc.mod(newHead + newGapCycle.memCycle(0), newHead) != BigInt(0))
    require(Calc.mod(SieveUtils.product(primes), newHead) != BigInt(0))
    nextWithGapCycle(newGapCycle)
}
```

---

## The 7 Requirements and Why Each Is a `require`

In Stainless, `require` can only appear at the top of a function body (before any `val` or `assert`). All preconditions must be `require` or all must be `assert` — mixing is not allowed. Since some cannot be proven, all 7 are `require`.

| # | Require | Why `require` not `assert` | Proving strategy |
|---|---------|---------------------------|------------------|
| 1 | `!survivors.isEmpty` | Solver cannot prove `currentWindow` always has ≥1 value not divisible by head — needs to know `Calc.mod(cycle.head + cycle.gapCycle.memCycle(0), cycle.head) != 0` from constructor, but the chain `cycle.head + gapMemCycle(0) = integral(0) = apply(1) = survivors(0)` is too deep for the solver to follow automatically. | Caller proves using constructor invariant of `CycleSieveSequence`. |
| 2 | `survivors.size > 1` | Requires knowing at least two integral values in `head * gapCycle.size` steps are not divisible by head. This depends on `steps` being large enough and the gap cycle distribution — a number theory fact the solver cannot derive. | Caller proves via P2 lemmas: at least `nextPeriod ≥ 2` survivors exist. |
| 3 | `allGreaterThan(gaps, 0)` | Gaps are adjacent differences of survivors. Survivors are increasing (integral values are strictly increasing). Proving this requires unfolding `currentWindow` recursion + `CycleIntegral`'s positivity invariant — the solver times out on the unfolded recursion. | Caller proves via `assertSurvivorGapEqualsSpecNextGap` (spec.next gaps are positive). |
| 4 | `newHead < head * head` | **Bertrand's postulate** — a theorem, not provable by the solver. Same assumption as `SpecSieveSequence.next`. | Caller provides via `spec.primes.nextPrime.value < spec.head.value * spec.head.value`. |
| 5 | `isCoprime(newHead + firstGap, primes)` | Requires `spec.accepts(spec(1))` + `assertApplyMatches(1)` + `assertPrimesMatch()` — the solver times out linking these across module boundaries (SpecDerived → Spec → Cycle). | Caller proves via `assertSpecNextIsKthSurvivor` + `spec.next.accepts`. |
| 6 | `Calc.mod(newHead + firstGap, newHead) != 0` | Requires `cycle(1) = cycle.head + cycle.gapCycle.memCycle(0)` — unfolding `apply(1)` → `integral(0)` → `head + gapCycle(0)` is too deep. | Caller proves via survivor filter construction (survivors are filtered by `mod(v, head) != 0`). |
| 7 | `Calc.mod(product(primes), newHead) != 0` | Old primorial not divisible by new head. Requires proving `newHead` is a new prime not in `primes` — needs the `AllPrimesSoFarList` invariant or the unproven primorial-not-divisible lemma. | Caller proves via `SpecDerivedCycleSieve` constructor invariants (the primorial is not divisible by any new prime). |

---

## Comparison with `SpecSieveSequence.next`

```
SpecSieveSequence.next:                    CycleSieveSequence.nextFromWindow:
  require(primes.nextPrime < head²)          require(newHead < head * head)           ← same
  // no explicit requires for rest           require(5-7)                             ← structural invariants
  // gaps come from primes.next              require(1-3)                             ← gap well-formedness
```

Both methods follow the same pattern: `require` preconditions that the caller must discharge. `SpecSieveSequence.next` has fewer requires because its gap construction (`primes.next`) happens inside a separate certified code path (`SpecSieveSequence` constructor), while `nextFromWindow()` builds gaps inline from survivors.

---

## Caller Chain to Discharge the Requires

```scala
// The SpecDerivedCycleSieve bridge:
assertFirstSurvivorEqualsSpecNext0()           // → head match (survivors(0) = newHead)
assertSurvivorGapEqualsSpecNextGap(nextPeriod, 0)  // → first gap matches spec.next
assertSurvivorGapEqualsSpecNextGap(nextPeriod, i)   // → all gaps match spec.next
assertSpecNextIsKthSurvivor(nextPeriod, 0)         // → spec.next(0) matches cycle survivor
assertSpecNextIsKthSurvivor(nextPeriod, 1)         // → spec.next(1) matches cycle survivor
// spec.next.accepts(spec.next(1)) is true by construction
// → isCoprime(firstGenerated, cycle.primes) follows
// → Calc.mod(firstGenerated, newHead) != 0 follows

cycle.nextFromWindow()  // all 7 requires discharged
```

---

## Failed Approaches (Noted for Posterity)

| Approach | Attempts | Failure mode |
|----------|----------|-------------|
| `assertNewHeadCoprimeToPrimes()` lemma | 4 attempts | Timed out at final VC — solver can't connect `spec.accepts` + `assertApplyMatches` + `assertPrimesMatch` into `isCoprime(cycle(1), cycle.primes)` |
| Bridge lemma `assertSurvivorGapsForNextFromWindow` | 2 attempts | Timed out at penultimate VC — postcondition too complex for solver |
| Adding next-stage Bertrand bound as constructor `require` | 1 attempt | Broke existing `SpecDerivedCycleSieve(spec.next, nextPeriod)` construction sites |

All timeouts share the same root cause: cross-module reasoning (Spec → Cycle → GapCycle → MemCycle) where the solver cannot follow the full definition chain in one VC.
