package v1.chapter6.seq.sieve

import stainless.collection.List
import stainless.lang.BooleanDecorations
import v1.chapter2.div.Calc
import v1.chapter3.list.ListBoundUtils
import v1.chapter3.list.properties.ListRepeatProperties
import v1.chapter4.cycle.gap.GapCycle
import v1.chapter4.cycle.integral.recursive.CycleIntegral
import v1.chapter5.prime.{AllPrimesSoFarList, PrimeUtils}

/**
 * Canonical bridge from the linear spec to the concrete cycle representation.
 *
 * Construct this only when a `SpecSieveSequence` has a certified positive
 * period: `spec(period) == spec.head.value + spec.tailPrimorial`. The class
 * derives the spec gap cycle for that period, packages it as a
 * `CycleSieveSequence`, and hosts the lemmas proving that the derived cycle
 * emits the same values as the spec.
 *
 * This is not another independent definition of a sieve sequence. It is the
 * "trusted cycle because it was built from the spec" object. It is allowed to
 * use spec facts freely, unlike a raw `CycleSieveSequence`, whose eventual goal
 * is to stand on cycle-side structural facts.
 *
 * `SpecDerivedBySurvivors` wraps this class for a value-level survivor proof
 * lane. `SpecDerivedEquivalence` exists only to transfer facts between that
 * survivor lane and this canonical bridge.
 */
case class SpecDerivedSieveSequence(
  spec: SpecSieveSequence,
  period: BigInt
) {
  require(period > BigInt(0))
  require(spec(period) == spec.head.value + spec.tailPrimorial)
  require(spec.primes.nextPrime.value < spec.head.value * spec.head.value)
  require(spec.primes.list.nonEmpty)
  require(
    Calc.mod(
      SieveUtils.product(spec.filterValues),
      spec.head.value
    ) != BigInt(0)
  )

  /** Gap cycle derived from the spec — same as SpecDerivedCycleSieve. */
  val gapCycle: GapCycle = spec.specGapCycle(period)

  /** Prime list as AllPrimesSoFarList — all lemmas from prime chapter available. */
  val primes: AllPrimesSoFarList = spec.primes

  /** Prime list as List[BigInt] for CycleSieveSequence construction. */
  val cyclePrimes: List[BigInt] = PrimeUtils.primeValues(primes.list.list)

  /** Standard CycleSieveSequence (for callers that need the concrete type). */
  val cycle: CycleSieveSequence = CycleSieveSequence(primes, gapCycle)

  /** Cycle integral — same as cycle.integral. */
  val integral: CycleIntegral = cycle.integral
  /**
   * Computes the number of survivors after applying the head filter
   * to the expanded residue interval, then proves the closed form.
   *
   * The body calls `spec.sameHeadSurvivorCount` which actually scans
   * the interval [head, head + head*tailPrimorial) and counts every
   * accepted value not divisible by the head. The ensuring proves
    * this count equals `period * (head - 1)`, the expected period of
    * the next stage's gap cycle.
   */
  def nextPeriod(): BigInt = {
    assert(v1.chapter6.seq.sieve.properties.SpecDerivedCoreProperties.primorialMatchesProduct(this, spec.primes.list.tail))
    spec.sameHeadSurvivorCount(period)
  }.ensuring(count => {
    count == period * (spec.head.value - BigInt(1))
  })

  /**
   * Builds the same B cycle with its gap period repeated `times` times.
   *
   * Math:
   *
   *   B      = cycle
   *   G      = B.gapCycle.memCycle.values
   *   times  > 0
   *   G exp times = repeat(G, times)
   *
   *   repeatedCycle(times) = CycleSieveSequence(primes, GapCycle(G exp times))
   *
   * Repeating the stored gap list does not change the semantic cycle: it only
   * changes the physical period length. This constructor is isolated so later
   * lemmas can compare the original and repeated cycles without reopening
   * `GapCycle` positivity/non-emptiness obligations.
   */
  def repeatedCycle(times: BigInt): CycleSieveSequence = {
    require(times > BigInt(0))

    val gaps = cycle.gapCycle.memCycle.values
    val repeatedGaps = ListRepeatProperties.repeat(gaps, times)

    assert(GapCycle.assertMemCycleValuesPositive(cycle.gapCycle))
    assert(ListRepeatProperties.assertRepeatAllGreaterThan(gaps, times, BigInt(0)))
    assert(ListRepeatProperties.assertRepeatSize(gaps, times))
    assert(repeatedGaps.size == gaps.size * times)
    assert(gaps.nonEmpty)
    assert(repeatedGaps.nonEmpty)
    assert(ListBoundUtils.allGreaterThan(repeatedGaps, BigInt(0)))

    CycleSieveSequence(primes, GapCycle(repeatedGaps))
  }
}
