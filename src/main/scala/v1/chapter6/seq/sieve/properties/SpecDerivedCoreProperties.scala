package v1.chapter6.seq.sieve.properties

import stainless.lang.{BigInt, BooleanDecorations, decreases}
import v1.chapter2.div.Calc
import v1.chapter2.div.properties.AdditionAndMultiplication
import v1.chapter5.prime.PrimeUtils
import v1.chapter6.seq.sieve.{SieveUtils, SpecDerivedSieveSequence}

object SpecDerivedCoreProperties {


  /**
   * Proves `cycle(k) == spec(k)` for every non-negative `k`.
   *
   * The derived cycle uses the gap cycle certified by the spec, so the cycle
   * integral and the spec-generated value agree at the same index.
   */
  def assertApplyMatches(derived: SpecDerivedSieveSequence, k: BigInt): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    require(k >= BigInt(0))
    if (k == BigInt(0)) {
      assert(cycle.head == spec.head.value)
      assert(spec(BigInt(0)) == spec.head.value)
      cycle(k) == spec(k)
    } else {
      assert(cycle.gapCycle.memCycle == gapCycle.memCycle)
      assert(cycle.integral ==
        v1.chapter4.cycle.integral.recursive.CycleIntegral(
          spec.head.value, gapCycle.memCycle))
      assert(spec.assertSpecGapCycleIntegralMatchesApply(period, k))
      cycle(k) == spec(k)
    }
  }.holds


  /**
   * Proves `cycle(1) == spec.next.head.value`.
   *
   * The first generated value after the current head is the next prime in the
   * spec, and the derived cycle is already known to match the spec at index `1`.
   */
  def assertNextHeadMatches(derived: SpecDerivedSieveSequence): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    assert(SpecDerivedCoreProperties.assertApplyMatches(derived, BigInt(1)))
    assert(spec.assertApplyOneEqualsNextPrime())
    assert(cycle(BigInt(1)) == spec(BigInt(1)))
    assert(spec(BigInt(1)) == spec.primes.nextPrime.value)
    assert(spec.next.head.value == spec.primes.nextPrime.value)
    cycle(BigInt(1)) == spec.next.head.value
  }.holds


  /**
   * Proves that the derived cycle stores the same prime values as the spec.
   *
   * This exposes the prime-list agreement needed by later filter and coprime
   * arguments while also checking that the cycle head matches the spec head.
   */
  def assertPrimesMatch(derived: SpecDerivedSieveSequence): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    assert(SpecDerivedCoreProperties.assertApplyMatches(derived, BigInt(0)))
    assert(cycle.head == spec.head.value)
    assert(cyclePrimes == PrimeUtils.primeValues(primes.list.list))
    assert(primes.list.list == spec.primes.list.list)
    true
  }.holds


  /**
   * Proves that `PrimeUtils.primorial(primeList.list)` equals
   * `SieveUtils.product(PrimeUtils.primeValues(primeList.list))`.
   *
   * The proof follows the sorted-prime list recursively, reducing the tail until
   * the singleton primorial/product case is reached.
   */
  def primorialMatchesProduct(derived: SpecDerivedSieveSequence, primeList: v1.chapter5.prime.SortedPrimeList): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    require(primeList.list.nonEmpty)
    decreases(primeList.list.size)
    if (primeList.list.tail.isEmpty) {
      PrimeUtils.primorial(primeList.list) == PrimeUtils.primeValues(primeList.list).last
    } else {
      assert(SpecDerivedCoreProperties.primorialMatchesProduct(derived, primeList.tail))
      PrimeUtils.primorial(primeList.list) == SieveUtils.product(PrimeUtils.primeValues(primeList.list))
    }
  }.holds


  /**
   * Proves that the derived cycle modulus equals `spec.tailPrimorial`.
   *
   * The cycle modulus is the product of the stored tail prime values, and the
   * spec tail primorial uses the same prime list.
   */
  def assertCycleModulusEqualsSpecTailPrimorial(derived: SpecDerivedSieveSequence): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    assert(SpecDerivedCoreProperties.primorialMatchesProduct(derived, spec.primes.list.tail))
    cycle.modulus == spec.tailPrimorial
  }.holds


  /**
   * Proves that `derived.nextPeriod()` has the expanded-filter count.
   *
   * The spec counts one full expanded block of `period * head` generated values
   * and removes exactly the head multiples, giving `period * (head - 1)`.
   */
  def assertNextPeriodMatchesExpandedFilterCount(derived: SpecDerivedSieveSequence): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    assert(SpecDerivedCoreProperties.primorialMatchesProduct(derived, spec.primes.list.tail))
    assert(Calc.mod(spec.tailPrimorial, spec.head.value) != BigInt(0))
    assert(spec.assertExpandedGeneratedHeadMultipleCount(period))

    val count = derived.nextPeriod()

    count == period * (spec.head.value - BigInt(1))
  }.holds


  /**
   * Proves that `derived.nextPeriod()` also matches the shifted scan window.
   *
   * The repeated-cycle integral scans `(head, head + head * tailPrimorial]`
   * instead of `[head, head + head * tailPrimorial)`, and the swapped endpoints
   * are both rejected head multiples.
   */
  def assertNextPeriodMatchesShiftedWindowCount(derived: SpecDerivedSieveSequence): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    assert(SpecDerivedCoreProperties.primorialMatchesProduct(derived, spec.primes.list.tail))
    assert(Calc.mod(spec.tailPrimorial, spec.head.value) != BigInt(0))
    assert(spec.assertSameHeadShiftedWindowCount(period))

    val count = derived.nextPeriod()

    count == period * (spec.head.value - BigInt(1))
  }.holds


  /**
   * The gap cycle stores exactly `period` gaps, matching the spec's
   * canonical period.
   */
  def assertCyclePeriod(derived: SpecDerivedSieveSequence): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    assert(spec.assertGapListSize(BigInt(0), period))
    cycle.gapCycle.period == period
  }.holds


  /**
   * Per-index survivor-to-spec-next gap equality.
   *
   * Proves that for consecutive cycle survivors `pos1`, `pos2` corresponding
   * to `spec.next(k)` and `spec.next(k+1)`, the gap between survivors equals
   * the gap between the corresponding spec.next values.
   */
  def assertSurvivorGapEqualsSpecNextGap(derived: SpecDerivedSieveSequence, nextPeriod: BigInt, k: BigInt): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    require(nextPeriod > BigInt(1))
    require(k >= BigInt(0))
    require(k + BigInt(1) < nextPeriod)
    require(spec.next(nextPeriod) == spec.next.head.value + spec.next.tailPrimorial)
    assert(spec.assertNextValueAcceptedByThis(k))
    assert(spec.assertNextValueAcceptedByThis(k + BigInt(1)))
    val pos1 = spec.indexOfAccepted(spec.next(k))
    val pos2 = spec.indexOfAccepted(spec.next(k + BigInt(1)))
    assert(SpecDerivedCoreProperties.assertApplyMatches(derived, pos1))
    assert(SpecDerivedCoreProperties.assertApplyMatches(derived, pos2))
    assert(spec(pos1) == spec.next(k))
    assert(spec(pos2) == spec.next(k + BigInt(1)))
    spec.next(k + BigInt(1)) - spec.next(k) == cycle(pos2) - cycle(pos1)
  }.holds


  /**
   * Canonical next-stage gap-cycle packaging.
   *
   * This lemma is intentionally about the Spec-certified next cycle, not about
   * the independent pipeline output. It records the construction fact that
   * `spec.next.specGapCycle(nextPeriod)` stores exactly
   * `spec.next.gapList(0, nextPeriod)` as its memory-cycle values. Keeping this
   * bridge explicit prevents future edits from mistaking the canonical
   * Spec-derived cycle proof for a proof about `nextRotatedGaps(cycle)`.
   */
  def assertNextGapCycleValuesEqualSpecNextGapList(derived: SpecDerivedSieveSequence, nextPeriod: BigInt): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    require(nextPeriod > BigInt(0))
    require(spec.next(nextPeriod) == spec.next.head.value + spec.next.tailPrimorial)

    spec.next.specGapCycle(nextPeriod).memCycle.values == spec.next.gapList(BigInt(0), nextPeriod)
  }.holds


  /**
   * Canonical next-stage gap equality.
   *
   * The canonical wrapper for `spec.next` stores `spec.next.specGapCycle` as
   * its gap cycle. The earlier packaging lemma exposes that this gap cycle's
   * memory values are exactly `spec.next.gapList(0, nextPeriod)`.
   */
  def assertNextCycleGapsMatchSpecNext(derived: SpecDerivedSieveSequence, nextPeriod: BigInt): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    require(nextPeriod > BigInt(0))
    require(spec.next(nextPeriod) == spec.next.head.value + spec.next.tailPrimorial)
    require(spec.next.primes.nextPrime.value < spec.next.head.value * spec.next.head.value)
    require(spec.next.primes.list.nonEmpty)
    require(Calc.mod(SieveUtils.product(spec.next.filterValues), spec.next.head.value) != BigInt(0))

    val nextCanonical = SpecDerivedSieveSequence(spec.next, nextPeriod)
    val nextSpecGapCycle = spec.next.specGapCycle(nextPeriod)

    assert(nextCanonical.cycle.gapCycle == nextSpecGapCycle)
    assert(SpecDerivedCoreProperties.assertNextGapCycleValuesEqualSpecNextGapList(derived, nextPeriod))

    nextCanonical.cycle.gapCycle.memCycle.values == spec.next.gapList(BigInt(0), nextPeriod)
  }.holds


  /**
   * Proves that the current head is rejected by the current head filter.
   *
   * This isolates the endpoint fact `mod(head, head) == 0`, used when comparing
   * the raw spec interval with the shifted repeated-integral interval.
   */
  def assertSpecHeadRejectedByHeadFilter(derived: SpecDerivedSieveSequence): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    assert(spec.head.value > BigInt(0))
    assert(AdditionAndMultiplication.ATimesBSameMod(BigInt(0), spec.head.value, BigInt(1)))
    assert(Calc.mod(spec.head.value, spec.head.value) == BigInt(0))

    Calc.mod(spec.head.value, spec.head.value) == BigInt(0)
  }.holds


  /**
   * Proves that the repeated first-expanded endpoint is rejected by `spec.next`.
   *
   * The endpoint value is `head + head * tailPrimorial`, equivalently
   * `head * (1 + tailPrimorial)`, so it is divisible by the current head and
   * cannot survive the next-stage head filter.
   */
  def assertRepeatedCycleFullFirstExpandedEndpointRejected(derived: SpecDerivedSieveSequence): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    val count = period * spec.head.value
    val index = count - BigInt(1)
    val repeated = derived.repeatedCycle(spec.head.value)
    val value = repeated.integral(index)

    assert(spec.head.value > BigInt(0))
    assert(count > BigInt(0))
    assert(index >= BigInt(0))
    assert(spec.assertBlockShiftMultiple(BigInt(0), spec.head.value, period))
    assert(spec(count) == spec.head.value + spec.head.value * spec.tailPrimorial)
    assert(SpecDerivedRepeatedCycleProperties.assertRepeatedCycleNextAcceptsMatchesHeadFilterFullFirstExpandedPeriod(derived))
    assert(SpecDerivedRepeatedCycleProperties.assertRepeatedCycleApplyMatches(derived, spec.head.value, count))
    assert(SpecDerivedCoreProperties.assertApplyMatches(derived, count))
    assert(repeated(count) == repeated.integral(index))
    assert(repeated(count) == cycle(count))
    assert(cycle(count) == spec(count))
    assert(value == spec.head.value + spec.head.value * spec.tailPrimorial)
    assert(AdditionAndMultiplication.ATimesBSameMod(BigInt(0), spec.head.value, BigInt(1) + spec.tailPrimorial))
    assert(Calc.mod(spec.head.value * (BigInt(1) + spec.tailPrimorial), spec.head.value) == BigInt(0))
    assert(value == spec.head.value * (BigInt(1) + spec.tailPrimorial))
    assert(Calc.mod(value, spec.head.value) == BigInt(0))
    assert(spec.next.accepts(value) == (Calc.mod(value, spec.head.value) != BigInt(0)))

    !spec.next.accepts(value)
  }.holds


  /**
   * Proves that the next head is smaller than the new cycle modulus.
   *
   * Under the lower bounds `head >= 3` and `tailPrimorial >= 2`, the first next
   * value remains below `cycle.head * cycle.modulus`.
   */
  def assertNextHeadLessThanNewModulus(derived: SpecDerivedSieveSequence): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    require(spec.head.value >= 3)
    require(spec.tailPrimorial >= 2)

    assert(SpecDerivedCoreProperties.assertApplyMatches(derived, BigInt(1)))
    assert(SpecDerivedCoreProperties.assertCycleModulusEqualsSpecTailPrimorial(derived))
    assert(spec(BigInt(1)) <= spec.searchBound(BigInt(1)))
    assert(spec.head.value * spec.tailPrimorial > spec.head.value + spec.tailPrimorial)
    cycle(BigInt(1)) < cycle.head * cycle.modulus
  }.holds
}
