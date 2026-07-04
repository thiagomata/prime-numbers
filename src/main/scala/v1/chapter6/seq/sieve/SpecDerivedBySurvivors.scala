package v1.chapter6.seq.sieve

import stainless.lang.BooleanDecorations
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
}
