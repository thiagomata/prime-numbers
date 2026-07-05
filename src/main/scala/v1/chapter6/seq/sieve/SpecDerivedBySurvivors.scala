package v1.chapter6.seq.sieve

import stainless.lang.BooleanDecorations
import v1.chapter2.div.Calc
import v1.chapter5.prime.PrimeUtils

case class SpecDerivedBySurvivors(
  derived: SpecDerivedSieveSequence
) {
  def assertSpecNextFilterEqCyclePrimes(): Boolean = {
    assert(derived.assertPrimesMatch())
    assert(derived.spec.next.filterPrimes == derived.spec.primes.list.list)
    derived.spec.next.filterValues == derived.cyclePrimes
  }.holds

  /**
   * Rotation anchor (ladder step 10, arithmetic prerequisite).
   *
   * Proves that the value `nextHeadResidueIndex` searches for in
   * `nextSorted(cycle).list` is exactly `spec.next.head.value`. This holds
   * because `cycle(1) == spec.next.head.value` (assertNextHeadMatches) and,
   * for stages with `head >= 3`, `cycle(1) < head * modulus`
   * (assertNextHeadLessThanNewModulus), so reducing `cycle(1)` modulo
   * `head * modulus` leaves it unchanged.
   *
   * The S_0 seed stage (head = 2, modulus = 1) is excluded: there
   * `cycle(1) = 3 > 2 = head*modulus`, so the reduction wraps. S_0 does not
   * need the pipeline equivalence (it is defined directly).
   */
  def assertNextHeadResidueIsSpecNextHead(): Boolean = {
    require(derived.spec.head.value >= 3)
    require(derived.spec.filterModulus >= 2)

    assert(derived.assertNextHeadMatches())
    assert(derived.assertNextHeadLessThanNewModulus())
    assert(derived.assertCycleModulusEqualsSpecFilterModulus())
    Calc.mod(derived.cycle(BigInt(1)),
             derived.cycle.head * derived.cycle.modulus) ==
      derived.spec.next.head.value
  }.holds

  /**
   * Load-bearing modulus identity for the expansion bridge.
   *
   * Proves `cycle.head * cycle.modulus == spec.next.filterModulus`. This is
   * the key arithmetic fact that connects the cycle's reduced range
   * `[0, head*modulus)` to the spec's next-stage filter modulus. It holds
   * because:
   *   cycle.modulus == spec.filterModulus                         (assertCycleModulusEqualsSpecFilterModulus)
   *   spec.next.filterPrimes == spec.primes.list.list             (definitional: primes.next.list.tail.list)
   *   spec.filterPrimes == spec.primes.list.tail.list             (definitional)
   *   primorial(head :: tail) == head * primorial(tail)           (primorialUnfold)
   *
   * Confirmed load-bearing by the S_2 hand-analysis: `5 * 6 = 30 = primorial([5,3,2])`.
   */
  def assertHeadModulusEqualsSpecNextFilterModulus(): Boolean = {
    assert(derived.assertCycleModulusEqualsSpecFilterModulus())
    assert(derived.spec.filterPrimes == derived.spec.primes.list.tail.list)
    assert(derived.spec.next.filterPrimes == derived.spec.primes.list.list)
    assert(PrimeUtils.primorialUnfold(derived.spec.primes.list.list))
    derived.cycle.head * derived.cycle.modulus == derived.spec.next.filterModulus
  }.holds

  def assertCanonicalCycleNextMatchSpecNext(nextPeriod: BigInt): Boolean = {
    require(nextPeriod > BigInt(0))
    require(derived.spec.next(nextPeriod) ==
      derived.spec.next.head.value + derived.spec.next.filterModulus)
    require(derived.spec.next.primes.nextPrime.value <
      derived.spec.next.head.value * derived.spec.next.head.value)
    require(derived.spec.next.primes.list.nonEmpty)
    require(Calc.mod(
      SieveUtils.product(derived.spec.next.filterValues),
      derived.spec.next.head.value) != BigInt(0))
    require(derived.spec.head.value >= 3)
    require(derived.spec.filterModulus >= 2)

    val nextCanonical = SpecDerivedSieveSequence(
      derived.spec.next, nextPeriod)

    assert(assertNextHeadResidueIsSpecNextHead())
    assert(assertHeadModulusEqualsSpecNextFilterModulus())
    assert(derived.assertNextCycleGapsMatchSpecNext(nextPeriod))
    assert(nextCanonical.cycle.gapCycle.memCycle.values ==
      derived.spec.next.gapList(BigInt(0), nextPeriod))

    assert(assertSpecNextFilterEqCyclePrimes())
    val cNext = CycleSieveSequence(
      derived.spec.primes.next,
      nextCanonical.cycle.gapCycle)
    assert(nextCanonical.cycle.gapCycle.memCycle.values == cNext.gapCycle.memCycle.values)
    assert(cNext.head == nextCanonical.cycle.head)
    cNext.apply(BigInt(0)) == nextCanonical.cycle.apply(BigInt(0))
  }.holds

  def assertSpecCanonicalCycleNextMatch(nextPeriod: BigInt): Boolean = {
    require(nextPeriod > BigInt(0))
    require(derived.spec.next(nextPeriod) ==
      derived.spec.next.head.value + derived.spec.next.filterModulus)
    require(derived.spec.next.primes.nextPrime.value <
      derived.spec.next.head.value * derived.spec.next.head.value)
    require(derived.spec.next.primes.list.nonEmpty)
    require(Calc.mod(
      SieveUtils.product(derived.spec.next.filterValues),
      derived.spec.next.head.value) != BigInt(0))
    require(derived.spec.head.value >= 3)
    require(derived.spec.filterModulus >= 2)

    assert(assertCanonicalCycleNextMatchSpecNext(nextPeriod))
    true
  }.holds

  def assertRepeatedCycleProof(nextPeriod: BigInt): Boolean = {
    require(nextPeriod > BigInt(1))
    require(derived.spec.next(nextPeriod) ==
      derived.spec.next.head.value + derived.spec.next.filterModulus)
    require(derived.spec.next.primes.nextPrime.value <
      derived.spec.next.head.value * derived.spec.next.head.value)
    require(derived.spec.next.primes.list.nonEmpty)
    require(Calc.mod(
      SieveUtils.product(derived.spec.next.filterValues),
      derived.spec.next.head.value) != BigInt(0))
    require(derived.spec.head.value >= 3)
    require(derived.spec.filterModulus >= 2)

    val h = derived.spec.head.value
    assert(derived.assertRepeatedCycleApplyMatches(h, BigInt(0)))
    assert(derived.assertSurvivorGapEqualsSpecNextGap(nextPeriod, BigInt(0)))
    assert(assertCanonicalCycleNextMatchSpecNext(nextPeriod))
    true
  }.holds
}
