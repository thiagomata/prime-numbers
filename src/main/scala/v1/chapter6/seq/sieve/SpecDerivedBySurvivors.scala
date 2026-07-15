package v1.chapter6.seq.sieve

import stainless.lang.BooleanDecorations
import v1.chapter2.div.Calc
import v1.chapter5.prime.PrimeUtils
import v1.chapter6.seq.sieve.properties.{
  SpecDerivedCoreProperties,
  SpecDerivedRepeatedCycleProperties
}

/**
 * Value-level survivor proof lane over a canonical derived cycle.
 *
 * This class deliberately wraps `SpecDerivedSieveSequence` instead of defining
 * a new sieve sequence. Its purpose is to prove next-stage facts by following
 * survivor values through the head filter, using coprimality and modulus facts,
 * rather than by relying on the older index-heavy `nextAcceptedOldIndex` route.
 *
 * The wrapper exists because some next-stage obligations are clearer as
 * statements about values that survive filtering: a cycle survivor passes the
 * next spec filter, its reduced residue appears in the pipeline list, and the
 * rotation anchor is the next spec head. Those facts support the bridge between
 * the canonical spec-derived cycle and the concrete transition helpers.
 *
 * It is different from `SpecDerivedSieveSequence` only in proof strategy. The
 * underlying spec, cycle, head, modulus, and gap cycle are the same; that
 * sameness is recorded by `SpecDerivedEquivalence`.
 */
case class SpecDerivedBySurvivors(
  derived: SpecDerivedSieveSequence
)

object SpecDerivedBySurvivors {
  def assertSpecNextFilterEqCyclePrimes(bySurvivors: SpecDerivedBySurvivors): Boolean = {
    val derived = bySurvivors.derived

    assert(SpecDerivedCoreProperties.assertPrimesMatch(derived))
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
  def assertNextHeadResidueIsSpecNextHead(bySurvivors: SpecDerivedBySurvivors): Boolean = {
    require(bySurvivors.derived.spec.head.value >= 3)
    require(bySurvivors.derived.spec.tailPrimorial >= 2)

    val derived = bySurvivors.derived

    assert(SpecDerivedCoreProperties.assertNextHeadMatches(derived))
    assert(SpecDerivedCoreProperties.assertNextHeadLessThanNewModulus(derived))
    assert(SpecDerivedCoreProperties.assertCycleModulusEqualsSpecTailPrimorial(derived))
    Calc.mod(derived.cycle(BigInt(1)),
             derived.cycle.head * derived.cycle.modulus) ==
      derived.spec.next.head.value
  }.holds

  /**
   * Load-bearing modulus identity for the expansion bridge.
   *
   * Proves `cycle.head * cycle.modulus == spec.next.tailPrimes`. This is
   * the key arithmetic fact that connects the cycle's reduced range
   * `[0, head*modulus)` to the spec's next-stage filter modulus. It holds
   * because:
   *   cycle.modulus == spec.tailPrimes.                           (assertCycleModulusEqualsSpecTailPrimorial)
   *   spec.next.filterPrimes == spec.primes.list.list             (definitional: primes.next.list.tail.list)
   *   spec.filterPrimes == spec.primes.list.tail.list             (definitional)
   *   primorial(head :: tail) == head * primorial(tail)           (primorialUnfold)
   *
   * Confirmed load-bearing by the S_2 hand-analysis: `5 * 6 = 30 = primorial([5,3,2])`.
   */
  def assertHeadModulusEqualsSpecNextTailPrimorial(bySurvivors: SpecDerivedBySurvivors): Boolean = {
    val derived = bySurvivors.derived

    assert(SpecDerivedCoreProperties.assertCycleModulusEqualsSpecTailPrimorial(derived))
    assert(derived.spec.filterPrimes == derived.spec.primes.list.tail.list)
    assert(derived.spec.next.filterPrimes == derived.spec.primes.list.list)
    assert(PrimeUtils.primorialUnfold(derived.spec.primes.list.list))
    derived.cycle.head * derived.cycle.modulus == derived.spec.next.tailPrimorial
  }.holds

  def assertCanonicalCycleNextMatchSpecNext(bySurvivors: SpecDerivedBySurvivors, nextPeriod: BigInt): Boolean = {
    require(nextPeriod > BigInt(0))
    require(bySurvivors.derived.spec.next(nextPeriod) ==
      bySurvivors.derived.spec.next.head.value + bySurvivors.derived.spec.next.tailPrimorial)
    require(bySurvivors.derived.spec.next.primes.nextPrime.value <
      bySurvivors.derived.spec.next.head.value * bySurvivors.derived.spec.next.head.value)
    require(bySurvivors.derived.spec.next.primes.list.nonEmpty)
    require(Calc.mod(
      SieveUtils.product(bySurvivors.derived.spec.next.filterValues),
      bySurvivors.derived.spec.next.head.value) != BigInt(0))
    require(bySurvivors.derived.spec.head.value >= 3)
    require(bySurvivors.derived.spec.tailPrimorial >= 2)

    val derived = bySurvivors.derived

    val nextCanonical = SpecDerivedSieveSequence(
      derived.spec.next, nextPeriod)

    assert(assertNextHeadResidueIsSpecNextHead(bySurvivors))
    assert(assertHeadModulusEqualsSpecNextTailPrimorial(bySurvivors))
    assert(SpecDerivedCoreProperties.assertNextCycleGapsMatchSpecNext(derived, nextPeriod))
    assert(nextCanonical.cycle.gapCycle.memCycle.values ==
      derived.spec.next.gapList(BigInt(0), nextPeriod))

    assert(assertSpecNextFilterEqCyclePrimes(bySurvivors))
    val cNext = CycleSieveSequence(
      derived.spec.primes.next,
      nextCanonical.cycle.gapCycle)
    assert(nextCanonical.cycle.gapCycle.memCycle.values == cNext.gapCycle.memCycle.values)
    assert(cNext.head == nextCanonical.cycle.head)
    cNext.apply(BigInt(0)) == nextCanonical.cycle.apply(BigInt(0))
  }.holds

  /**
   * End-to-end: spec.next(k) == canonical.next(k) == cycle.next(k).
   *
   * The canonical next's apply matches spec.next by construct (assertApplyMatches
   * on the canonical instance). The pipeline-built cNext shares the same primes
   * and GapCycle as the canonical next, so their apply values are identical for
   * all k. This lemma pins the first two positions explicitly.
   */
  def assertSpecCanonicalCycleNextMatch(bySurvivors: SpecDerivedBySurvivors, nextPeriod: BigInt): Boolean = {
    require(nextPeriod > BigInt(0))
    require(bySurvivors.derived.spec.next(nextPeriod) ==
      bySurvivors.derived.spec.next.head.value + bySurvivors.derived.spec.next.tailPrimorial)
    require(bySurvivors.derived.spec.next.primes.nextPrime.value <
      bySurvivors.derived.spec.next.head.value * bySurvivors.derived.spec.next.head.value)
    require(bySurvivors.derived.spec.next.primes.list.nonEmpty)
    require(Calc.mod(
      SieveUtils.product(bySurvivors.derived.spec.next.filterValues),
      bySurvivors.derived.spec.next.head.value) != BigInt(0))
    require(bySurvivors.derived.spec.head.value >= 3)
    require(bySurvivors.derived.spec.tailPrimorial >= 2)

    val derived = bySurvivors.derived

    val nextCanonical = SpecDerivedSieveSequence(
      derived.spec.next, nextPeriod)
    val cNext = CycleSieveSequence(
      derived.spec.primes.next,
      nextCanonical.cycle.gapCycle)

    assert(assertCanonicalCycleNextMatchSpecNext(bySurvivors, nextPeriod))
    assert(SpecDerivedCoreProperties.assertApplyMatches(nextCanonical, BigInt(0)))
    assert(SpecDerivedCoreProperties.assertApplyMatches(nextCanonical, BigInt(1)))

    assert(cNext.apply(BigInt(0)) == derived.spec.next(BigInt(0)))
    assert(cNext.apply(BigInt(1)) == derived.spec.next(BigInt(1)))
    true
  }.holds

  /**
   * For any k, the pipeline-built cycle equals spec.next.
   *
   * Prerequisites (all called before the final equality):
   *   assertCanonicalCycleNextMatchSpecNext — rotation, modulus, gap equality
   *   SpecDerivedCoreProperties.assertApplyMatches(nextCanonical, k)   — canonical.cycle(k) == spec.next(k)
   *
   * Since cNext shares the same primes.next and same GapCycle as
   * nextCanonical.cycle, their .apply(k) is identical for all k.
   */
  def assertCycleNextApplyEqualsSpecNext(bySurvivors: SpecDerivedBySurvivors, nextPeriod: BigInt, k: BigInt): Boolean = {
    require(k >= BigInt(0))
    require(nextPeriod > BigInt(0))
    require(bySurvivors.derived.spec.next(nextPeriod) ==
      bySurvivors.derived.spec.next.head.value + bySurvivors.derived.spec.next.tailPrimorial)
    require(bySurvivors.derived.spec.next.primes.nextPrime.value <
      bySurvivors.derived.spec.next.head.value * bySurvivors.derived.spec.next.head.value)
    require(bySurvivors.derived.spec.next.primes.list.nonEmpty)
    require(Calc.mod(
      SieveUtils.product(bySurvivors.derived.spec.next.filterValues),
      bySurvivors.derived.spec.next.head.value) != BigInt(0))
    require(bySurvivors.derived.spec.head.value >= 3)
    require(bySurvivors.derived.spec.tailPrimorial >= 2)

    val derived = bySurvivors.derived

    val nextCanonical = SpecDerivedSieveSequence(
      derived.spec.next, nextPeriod)
    val cNext = CycleSieveSequence(
      derived.spec.primes.next,
      nextCanonical.cycle.gapCycle)

    assert(assertCanonicalCycleNextMatchSpecNext(bySurvivors, nextPeriod))
    assert(SpecDerivedCoreProperties.assertApplyMatches(nextCanonical, k))
    cNext.apply(k) == derived.spec.next(k)
  }.holds

  /**
   * Explicit Spec.next(k) == Canonical.next(k) == Cycle.next(k).
   *
   * From:
   *   assertCycleNextApplyEqualsSpecNext(nextPeriod, k)  — Cycle.next(k) == Spec.next(k)
   *   SpecDerivedCoreProperties.assertApplyMatches(nextCanonical, k)                 — Canonical.next(k) == Spec.next(k)
   * Therefore Canonical.next(k) == Cycle.next(k) by transitivity.
   */
  def assertBNextApplyEqualsCNextApply(bySurvivors: SpecDerivedBySurvivors, nextPeriod: BigInt, k: BigInt): Boolean = {
    require(k >= BigInt(0))
    require(nextPeriod > BigInt(0))
    require(bySurvivors.derived.spec.next(nextPeriod) ==
      bySurvivors.derived.spec.next.head.value + bySurvivors.derived.spec.next.tailPrimorial)
    require(bySurvivors.derived.spec.next.primes.nextPrime.value <
      bySurvivors.derived.spec.next.head.value * bySurvivors.derived.spec.next.head.value)
    require(bySurvivors.derived.spec.next.primes.list.nonEmpty)
    require(Calc.mod(
      SieveUtils.product(bySurvivors.derived.spec.next.filterValues),
      bySurvivors.derived.spec.next.head.value) != BigInt(0))
    require(bySurvivors.derived.spec.head.value >= 3)
    require(bySurvivors.derived.spec.tailPrimorial >= 2)

    val derived = bySurvivors.derived

    val nextCanonical = SpecDerivedSieveSequence(
      derived.spec.next, nextPeriod)
    val cNext = CycleSieveSequence(
      derived.spec.primes.next,
      nextCanonical.cycle.gapCycle)

    assert(assertCycleNextApplyEqualsSpecNext(bySurvivors, nextPeriod, k))
    assert(SpecDerivedCoreProperties.assertApplyMatches(nextCanonical, k))
    cNext.apply(k) == nextCanonical.cycle.apply(k)
  }.holds

  def assertRepeatedCycleProof(bySurvivors: SpecDerivedBySurvivors, nextPeriod: BigInt): Boolean = {
    require(nextPeriod > BigInt(1))
    require(bySurvivors.derived.spec.next(nextPeriod) ==
      bySurvivors.derived.spec.next.head.value + bySurvivors.derived.spec.next.tailPrimorial)
    require(bySurvivors.derived.spec.next.primes.nextPrime.value <
      bySurvivors.derived.spec.next.head.value * bySurvivors.derived.spec.next.head.value)
    require(bySurvivors.derived.spec.next.primes.list.nonEmpty)
    require(Calc.mod(
      SieveUtils.product(bySurvivors.derived.spec.next.filterValues),
      bySurvivors.derived.spec.next.head.value) != BigInt(0))
    require(bySurvivors.derived.spec.head.value >= 3)
    require(bySurvivors.derived.spec.tailPrimorial >= 2)

    val derived = bySurvivors.derived

    val h = derived.spec.head.value
    assert(SpecDerivedRepeatedCycleProperties.assertRepeatedCycleApplyMatches(derived, h, BigInt(0)))
    assert(SpecDerivedCoreProperties.assertSurvivorGapEqualsSpecNextGap(derived, nextPeriod, BigInt(0)))
    assert(assertCanonicalCycleNextMatchSpecNext(bySurvivors, nextPeriod))
    true
  }.holds
}
