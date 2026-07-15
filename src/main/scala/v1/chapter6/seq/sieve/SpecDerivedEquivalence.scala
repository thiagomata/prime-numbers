package v1.chapter6.seq.sieve

import stainless.lang.BooleanDecorations
import v1.chapter6.seq.sieve.properties.SpecDerivedCoreProperties

/**
 * Transfer wrapper between the canonical bridge and the survivor proof lane.
 *
 * `SpecDerivedSieveSequence` and `SpecDerivedBySurvivors` are not two competing
 * sequence definitions. The survivor lane simply wraps the canonical bridge so
 * it can prove value-level filtering facts in a separate namespace. This small
 * class packages both views and proves that they share the same head, modulus,
 * gap cycle, and generated values.
 *
 * Use this object when a lemma proved through the survivor route needs to be
 * consumed as a fact about the canonical spec-derived cycle, or vice versa.
 */
case class SpecDerivedEquivalence(
  derived: SpecDerivedSieveSequence
) {
  val bySurvivors = SpecDerivedBySurvivors(derived)
}

object SpecDerivedEquivalence {
  def assertHeadMatches(equivalence: SpecDerivedEquivalence): Boolean = {
    val derived = equivalence.derived
    val bySurvivors = equivalence.bySurvivors

    assert(derived.cycle.head == bySurvivors.derived.cycle.head)
    assert(derived.cycle.modulus == bySurvivors.derived.cycle.modulus)
    derived.cycle.head == bySurvivors.derived.cycle.head &&
    derived.cycle.modulus == bySurvivors.derived.cycle.modulus
  }.holds

  def assertApplyMatches(equivalence: SpecDerivedEquivalence, k: BigInt): Boolean = {
    require(k >= BigInt(0))

    val derived = equivalence.derived
    val bySurvivors = equivalence.bySurvivors

    assert(SpecDerivedCoreProperties.assertApplyMatches(derived, k))
    derived.cycle(k) == bySurvivors.derived.cycle(k)
  }.holds

  def assertGapCycleMatches(equivalence: SpecDerivedEquivalence): Boolean = {
    val derived = equivalence.derived
    val bySurvivors = equivalence.bySurvivors

    assert(derived.cycle.gapCycle == bySurvivors.derived.cycle.gapCycle)
    derived.cycle.gapCycle.memCycle.values ==
      bySurvivors.derived.cycle.gapCycle.memCycle.values
  }.holds

  def assertNextHeadNewModulusMatch(equivalence: SpecDerivedEquivalence): Boolean = {
    val derived = equivalence.derived

    assert(SpecDerivedCoreProperties.assertNextHeadLessThanNewModulus(derived))
    assert(SpecDerivedCoreProperties.assertNextHeadLessThanNewModulus(derived))
    true
  }.holds
}
