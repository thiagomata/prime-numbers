package v1.chapter6.seq.sieve

import stainless.lang.BooleanDecorations
import stainless.lang.decreases
import v1.chapter2.div.Calc
import v1.chapter4.cycle.gap.GapCycle
import v1.chapter4.cycle.integral.recursive.properties.CycleIntegralProperties

case class SpecDerivedBySurvivors(
  derived: SpecDerivedSieveSequence
) {
  def assertCycleSurvivorCoprimeToCyclePrimes(pos: BigInt): Boolean = {
    require(pos >= BigInt(0))
    require(Calc.mod(derived.cycle.integral(pos), derived.spec.head.value) != BigInt(0))

    assert(derived.assertPrimesMatch())
    assert(derived.assertCycleValueCoprimeToTail(pos + BigInt(1)))
    SieveUtils.isCoprime(derived.cycle.integral(pos), derived.cyclePrimes)
  }.holds

  def assertSpecNextFilterEqCyclePrimes(): Boolean = {
    assert(derived.assertPrimesMatch())
    assert(derived.spec.next.filterPrimes == derived.spec.primes.list.list)
    derived.spec.next.filterValues == derived.cyclePrimes
  }.holds

  def assertCycleSurvivorCoprimeToSpecNextFilter(pos: BigInt): Boolean = {
    require(pos >= BigInt(0))
    require(Calc.mod(derived.cycle.integral(pos), derived.spec.head.value) != BigInt(0))

    assert(assertCycleSurvivorCoprimeToCyclePrimes(pos))
    assert(assertSpecNextFilterEqCyclePrimes())
    SieveUtils.isCoprime(derived.cycle.integral(pos), derived.spec.next.filterValues)
  }.holds

  def assertCycleSurvivorPassesSpecNextFilter(pos: BigInt): Boolean = {
    require(pos >= BigInt(0))
    require(Calc.mod(derived.cycle.integral(pos), derived.spec.head.value) != BigInt(0))

    assert(assertCycleSurvivorCoprimeToSpecNextFilter(pos))
    derived.spec.next.passesFilter(derived.cycle.integral(pos))
  }.holds

  def assertFirstSurvivorEqualsSpecNextHead(): Boolean = {
    assert(derived.assertFirstSurvivorEqualsSpecNext0())
    derived.cycle.integral(BigInt(0)) == derived.spec.next.head.value
  }.holds

  def assertAllSurvivorsPassSpecNextFilter(count: BigInt): Boolean = {
    require(count >= BigInt(0))
    decreases(count)

    if (count == BigInt(0)) true
    else {
      val rest = assertAllSurvivorsPassSpecNextFilter(count - BigInt(1))
      val pos = count - BigInt(1)
      if (Calc.mod(derived.cycle.integral(pos), derived.spec.head.value) != BigInt(0)) {
        assert(assertCycleSurvivorPassesSpecNextFilter(pos))
      }
      true
    }
  }.holds

  def assertAllSurvivorsPassSpecNextFilterFrom(from: BigInt, count: BigInt): Boolean = {
    require(from >= BigInt(0))
    require(count >= BigInt(0))
    decreases(count)

    if (count == BigInt(0)) true
    else {
      val rest = assertAllSurvivorsPassSpecNextFilterFrom(from + BigInt(1), count - BigInt(1))
      if (Calc.mod(derived.cycle.integral(from), derived.spec.head.value) != BigInt(0)) {
        assert(assertCycleSurvivorPassesSpecNextFilter(from))
      }
      true
    }
  }.holds

  def assertIntegralIncreasingForCount(count: BigInt): Boolean = {
    require(count >= BigInt(0))
    decreases(count)

    if (count <= BigInt(1)) true
    else {
      assert(GapCycle.assertMemCycleValuesPositive(derived.cycle.gapCycle))
      assert(CycleIntegralProperties.assertCycleValuePositive(
        derived.cycle.integral, count - BigInt(1)))
      assert(assertIntegralIncreasingForCount(count - BigInt(1)))
      derived.cycle.integral(count - BigInt(2)) < derived.cycle.integral(count - BigInt(1))
    }
  }.holds

  def assertIntegralGeIntegral0(pos: BigInt): Boolean = {
    require(pos >= BigInt(0))
    decreases(pos)

    if (pos == BigInt(0)) derived.cycle.integral(pos) >= derived.cycle.integral(BigInt(0))
    else {
      assert(GapCycle.assertMemCycleValuesPositive(derived.cycle.gapCycle))
      assert(CycleIntegralProperties.assertCycleValuePositive(derived.cycle.integral, pos))
      assert(derived.cycle.integral(pos) ==
        derived.cycle.integral(pos - BigInt(1)) + derived.cycle.integral.cycle(pos))
      assert(assertIntegralGeIntegral0(pos - BigInt(1)))
      derived.cycle.integral(pos) >= derived.cycle.integral(BigInt(0))
    }
  }.holds

  def assertSurvivorAcceptedBySpecNext(pos: BigInt): Boolean = {
    require(pos >= BigInt(0))
    require(Calc.mod(derived.cycle.integral(pos), derived.spec.head.value) != BigInt(0))

    assert(assertFirstSurvivorEqualsSpecNextHead())
    assert(assertIntegralGeIntegral0(pos))
    assert(assertCycleSurvivorPassesSpecNextFilter(pos))
    derived.spec.next.accepts(derived.cycle.integral(pos))
  }.holds

  def assertNextHeadLessThanNewModulus(): Boolean = {
    require(derived.spec.head.value >= 3)
    require(derived.spec.filterModulus >= 2)

    assert(derived.assertApplyMatches(BigInt(1)))
    assert(derived.assertCycleModulusEqualsSpecFilterModulus())
    assert(derived.spec(BigInt(1)) <= derived.spec.searchBound(BigInt(1)))
    assert(derived.spec.head.value * derived.spec.filterModulus >
           derived.spec.head.value + derived.spec.filterModulus)
    derived.cycle(BigInt(1)) < derived.cycle.head * derived.cycle.modulus
  }.holds

  def assertMinimalCycleSurvivorPassSpecNextFilter(pos: BigInt): Boolean = {
    require(pos >= BigInt(0))
    require(Calc.mod(derived.cycle.integral(pos), derived.spec.head.value) != BigInt(0))

    assert(assertCycleSurvivorPassesSpecNextFilter(pos))
    derived.spec.next.passesFilter(derived.cycle.integral(pos))
  }.holds
}
