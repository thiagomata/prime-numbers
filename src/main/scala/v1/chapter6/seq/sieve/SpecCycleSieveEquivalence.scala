package v1.chapter6.seq.sieve

import stainless.lang.*
import v1.chapter4.cycle.integral.recursive.CycleIntegral
import v1.chapter5.prime.PrimeUtils

/**
 * Local bridge lemmas for proving that the specification sieve and the
 * cycle-based sieve describe the same stream.
 *
 * The goal of this object is organizational as much as mathematical. Many of
 * the facts needed by the final equivalence theorem already exist elsewhere,
 * but importing them directly into one large proof makes the dependency shape
 * hard to see. These wrappers give the equivalence proof local names for each
 * prerequisite and verify, one by one, that the existing facts are usable from
 * this context.
 */
object SpecCycleSieveEquivalence {

  /**
   * Converts the prime-list correspondence assumption into head equality.
   *
   * `SpecSieveSequence` stores primes as `Prime` wrappers through
   * `AllPrimesSoFarList`; `CycleSieveSequence` stores the same stage as raw
   * `BigInt` values. When the cycle-side list is exactly
   * `PrimeUtils.primeValues(spec.primes.list.list)`, both sequence heads are
   * the same number.
   */
  def assertHeadsMatchFromPrimeValues(
    spec: SpecSieveSequence,
    cycle: CycleSieveSequence
  ): Boolean = {
    require(cycle.primes == PrimeUtils.primeValues(spec.primes.list.list))

    assert(spec.primes.list.list.nonEmpty)
    assert(PrimeUtils.primeValues(spec.primes.list.list).head == spec.head.value)
    assert(cycle.primes.head == spec.head.value)

    spec.head.value == cycle.head
  }.holds

  /**
   * Bridges the base case of the two `apply` methods.
   *
   * Both sequence implementations define index 0 as the current head. The only
   * representation work needed here is the head bridge above, which converts the
   * Spec `Prime` head into the cycle-side raw `BigInt` head.
   */
  def assertApplyZeroMatchesFromPrimeValues(
    spec: SpecSieveSequence,
    cycle: CycleSieveSequence
  ): Boolean = {
    require(cycle.primes == PrimeUtils.primeValues(spec.primes.list.list))

    assert(assertHeadsMatchFromPrimeValues(spec, cycle))
    assert(spec(BigInt(0)) == spec.head.value)
    assert(cycle(BigInt(0)) == cycle.head)

    spec(BigInt(0)) == cycle(BigInt(0))
  }.holds

  /**
   * Exposes the positive-index branch of `CycleSieveSequence.apply`.
   *
   * The cycle implementation treats index 0 specially as the current head. Every
   * positive index is reconstructed by the stored `CycleIntegral`, shifted by one
   * because integral position 0 corresponds to sequence index 1.
   */
  def assertCycleApplyPositiveIsIntegral(
    cycle: CycleSieveSequence,
    position: BigInt
  ): Boolean = {
    require(position > BigInt(0))

    cycle(position) == cycle.integral(position - BigInt(1))
  }.holds

  /**
   * Exposes the `CycleIntegral` stored by the cycle implementation.
   *
   * `CycleSieveSequence` defines its integral from the current head and the
   * stored gap cycle memory. Naming that equality locally lets later proofs
   * compare the Cycle-side integral with the Spec-side integral built from
   * `specGapCycle(period)` without repeatedly unfolding the class field.
   */
  def assertCycleIntegralUsesGapCycle(
    cycle: CycleSieveSequence
  ): Boolean = {
    cycle.integral == CycleIntegral(cycle.head, cycle.gapCycle.memCycle)
  }.holds

  /**
   * Proves positive-index apply equivalence from equal heads and equal gaps.
   *
   * This is the conditional checkpoint for the whole equivalence ticket. It
   * deliberately does not prove where the cycle-side gaps came from. Instead,
   * it states the smallest useful bridge: once the Spec stream and Cycle stream
   * have the same head and the same stored `MemCycle`, every positive `apply`
   * position is reconstructed by the same `CycleIntegral`.
   */
  def assertSpecCycleApplyPositiveMatchesFromSameHeadAndGaps(
    spec: SpecSieveSequence,
    cycle: CycleSieveSequence,
    period: BigInt,
    position: BigInt
  ): Boolean = {
    require(position > BigInt(0))
    require(period > BigInt(0))
    require(spec(period) == spec.head.value + spec.filterModulus)
    require(spec.head.value == cycle.head)
    require(spec.specGapCycle(period).memCycle == cycle.gapCycle.memCycle)

    val specGapCycle = spec.specGapCycle(period)
    val specIntegral = CycleIntegral(spec.head.value, specGapCycle.memCycle)

    assert(spec.assertSpecGapCycleIntegralMatchesApply(period, position))
    assert(assertCycleApplyPositiveIsIntegral(cycle, position))
    assert(assertCycleIntegralUsesGapCycle(cycle))
    assert(specIntegral == cycle.integral)

    spec(position) == cycle(position)
  }.holds

  /**
   * Proves apply equivalence for every index from equal heads and equal gaps.
   *
   * This is the all-index wrapper around the positive-index theorem above. At
   * index 0 both sequences return their head. At every positive index, both
   * sequences are reconstructed from the same initial value and the same stored
   * `MemCycle`, so the positive theorem applies directly.
   */
  def assertSpecCycleApplyMatchesFromSameHeadAndGaps(
    spec: SpecSieveSequence,
    cycle: CycleSieveSequence,
    period: BigInt,
    position: BigInt
  ): Boolean = {
    require(position >= BigInt(0))
    require(period > BigInt(0))
    require(spec(period) == spec.head.value + spec.filterModulus)
    require(spec.head.value == cycle.head)
    require(spec.specGapCycle(period).memCycle == cycle.gapCycle.memCycle)

    if (position == BigInt(0)) {
      assert(spec(BigInt(0)) == spec.head.value)
      assert(cycle(BigInt(0)) == cycle.head)
      spec(position) == cycle(position)
    } else {
      assert(
        assertSpecCycleApplyPositiveMatchesFromSameHeadAndGaps(
          spec,
          cycle,
          period,
          position
        )
      )
      spec(position) == cycle(position)
    }
  }.holds

  /**
   * Converts the prime-list correspondence assumption into filter equality.
   *
   * The cycle sequence keeps the head prime at `cycle.primes.head`, so its
   * active filters are `cycle.primes.tail`. The Spec sequence names the same
   * active filters as `spec.filterValues`. When the full prime lists correspond,
   * these two filter lists are equal.
   */
  def assertFilterValuesMatchTailPrimes(
    spec: SpecSieveSequence,
    cycle: CycleSieveSequence
  ): Boolean = {
    require(cycle.primes == PrimeUtils.primeValues(spec.primes.list.list))

    assert(spec.primes.list.list.nonEmpty)
    assert(
      PrimeUtils.primeValues(spec.primes.list.list).tail ==
        PrimeUtils.primeValues(spec.primes.list.list.tail)
    )
    assert(spec.filterPrimes == spec.primes.list.list.tail)
    assert(spec.filterValues == PrimeUtils.primeValues(spec.primes.list.list.tail))
    assert(cycle.primes.tail == spec.filterValues)

    cycle.primes.tail == spec.filterValues
  }.holds

  /**
   * Rewrites Spec acceptance into the cycle-side tail-coprime predicate.
   *
   * This is the first semantic bridge after the representation bridges above.
   * Spec acceptance is defined as "at or above the head and coprime to
   * `spec.filterValues`". Once the prime-list correspondence tells us that
   * `cycle.primes.tail` is the same list as `spec.filterValues`, the arithmetic
   * predicate is literally the same one used by the cycle-side residue pipeline.
   */
  def assertSpecAcceptsMatchesCycleTailCoprime(
    spec: SpecSieveSequence,
    cycle: CycleSieveSequence,
    value: BigInt
  ): Boolean = {
    require(cycle.primes == PrimeUtils.primeValues(spec.primes.list.list))
    require(value >= spec.head.value)

    assert(assertFilterValuesMatchTailPrimes(spec, cycle))
    assert(cycle.primes.tail == spec.filterValues)
    assert(spec.accepts(value) == SieveUtils.isCoprime(value, spec.filterValues))

    spec.accepts(value) == SieveUtils.isCoprime(value, cycle.primes.tail)
  }.holds
}
