package v1.chapter6.seq.sieve

import stainless.lang.BooleanDecorations
import v1.chapter6.seq.sieve.properties.SpecDerivedCoreProperties

case class SpecDerivedEquivalence(
  derived: SpecDerivedSieveSequence
) {
  val bySurvivors = SpecDerivedBySurvivors(derived)

  def assertHeadMatches(): Boolean = {
    assert(derived.cycle.head == bySurvivors.derived.cycle.head)
    assert(derived.cycle.modulus == bySurvivors.derived.cycle.modulus)
    derived.cycle.head == bySurvivors.derived.cycle.head &&
    derived.cycle.modulus == bySurvivors.derived.cycle.modulus
  }.holds

  def assertApplyMatches(k: BigInt): Boolean = {
    require(k >= BigInt(0))
    assert(SpecDerivedCoreProperties.assertApplyMatches(derived, k))
    derived.cycle(k) == bySurvivors.derived.cycle(k)
  }.holds

  def assertGapCycleMatches(): Boolean = {
    assert(derived.cycle.gapCycle == bySurvivors.derived.cycle.gapCycle)
    derived.cycle.gapCycle.memCycle.values ==
      bySurvivors.derived.cycle.gapCycle.memCycle.values
  }.holds

  def assertNextHeadNewModulusMatch(): Boolean = {
    assert(SpecDerivedCoreProperties.assertNextHeadLessThanNewModulus(derived))
    assert(SpecDerivedCoreProperties.assertNextHeadLessThanNewModulus(derived))
    true
  }.holds
}
