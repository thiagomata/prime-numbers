package v1.chapter6.seq.sieve

import stainless.lang.BooleanDecorations
import stainless.lang.decreases
import v1.chapter2.div.Calc

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
}
