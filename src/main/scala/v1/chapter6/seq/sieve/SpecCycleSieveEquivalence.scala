package v1.chapter6.seq.sieve

import stainless.lang.*
import v1.chapter2.div.Calc
import v1.chapter3.list.ListUtils
import v1.chapter4.cycle.gap.GapCycle
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
   * Exposes the raw-prime shape of `SpecSieveSequence.next`.
   *
   * The Spec next stage is built by prepending `spec.primes.nextPrime` to the
   * current complete-prime prefix. On the raw `BigInt` representation used by
   * `CycleSieveSequence`, that means the next Spec prime list has the next head
   * value at the front and the current Spec prime values as its tail.
   */
  def assertSpecNextPrimeValuesExtendCurrent(
    spec: SpecSieveSequence
  ): Boolean = {
    require(spec.primes.nextPrime.value < spec.head.value * spec.head.value)

    val nextSpec = spec.next
    val currentValues = PrimeUtils.primeValues(spec.primes.list.list)
    val nextValues = PrimeUtils.primeValues(nextSpec.primes.list.list)

    assert(nextValues.head == nextSpec.head.value)
    assert(nextValues.tail == currentValues)

    nextValues == nextSpec.head.value :: currentValues
  }.holds

  /**
   * Bridges the raw prime-list shape of the conditional next stage.
   *
   * This lemma does not prove that the cycle-side `apply(1)` is the Spec next
   * prime. That is the hard next-head theorem we still want to isolate. Instead,
   * it follows the conditional style used by `SpecSieveSequence.next` and
   * `CycleSieveSequence.nextWithGapCycle`: if the caller supplies that next-head
   * equality, and if the supplied gap cycle satisfies the constructor
   * obligations required by `nextWithGapCycle`, then the next Cycle stage stores
   * exactly the same raw prime values as `spec.next`.
   */
  def assertConditionalNextPrimeValuesMatch(
    spec: SpecSieveSequence,
    cycle: CycleSieveSequence,
    newGapCycle: GapCycle
  ): Boolean = {
    require(cycle.primes == PrimeUtils.primeValues(spec.primes.list.list))
    require(spec.primes.nextPrime.value < spec.head.value * spec.head.value)
    require(cycle.apply(BigInt(1)) == spec.next.head.value)
    require(SieveUtils.isCoprime(cycle.apply(BigInt(1)) + newGapCycle.memCycle(0), cycle.primes))
    require(Calc.mod(cycle.apply(BigInt(1)) + newGapCycle.memCycle(0), cycle.apply(BigInt(1))) != BigInt(0))
    require(Calc.mod(SieveUtils.product(cycle.primes), cycle.apply(BigInt(1))) != BigInt(0))

    val nextSpec = spec.next
    val nextCycle = cycle.nextWithGapCycle(newGapCycle)

    assert(assertSpecNextPrimeValuesExtendCurrent(spec))
    assert(PrimeUtils.primeValues(nextSpec.primes.list.list) == nextSpec.head.value :: PrimeUtils.primeValues(spec.primes.list.list))
    assert(nextCycle.primes == cycle.apply(BigInt(1)) :: cycle.primes)
    assert(nextCycle.primes == nextSpec.head.value :: PrimeUtils.primeValues(spec.primes.list.list))

    nextCycle.primes == PrimeUtils.primeValues(nextSpec.primes.list.list)
  }.holds

  /**
   * Proves next-stage apply equivalence for the verified conditional path.
   *
   * This lemma deliberately avoids `CycleSieveSequence.next()`, because that
   * method is still `@extern` and would be opaque to Stainless. Instead it uses
   * `nextWithGapCycle`, whose constructor path is verified under explicit
   * preconditions.
   *
   * The remaining hard facts are named as assumptions: the Cycle-side next head
   * must be the Spec next head, and the supplied gap cycle must match the Spec
   * next gap cycle for the requested period. Under those assumptions, the
   * previously verified same-head/same-gaps theorem proves equality for the
   * requested index.
   */
  def assertConditionalNextApplyMatchesFromSameHeadAndGaps(
    spec: SpecSieveSequence,
    cycle: CycleSieveSequence,
    newGapCycle: GapCycle,
    nextPeriod: BigInt,
    position: BigInt
  ): Boolean = {
    require(position >= BigInt(0))
    require(nextPeriod > BigInt(0))
    require(cycle.primes == PrimeUtils.primeValues(spec.primes.list.list))
    require(spec.primes.nextPrime.value < spec.head.value * spec.head.value)
    require(cycle.apply(BigInt(1)) == spec.next.head.value)
    require(SieveUtils.isCoprime(cycle.apply(BigInt(1)) + newGapCycle.memCycle(0), cycle.primes))
    require(Calc.mod(cycle.apply(BigInt(1)) + newGapCycle.memCycle(0), cycle.apply(BigInt(1))) != BigInt(0))
    require(Calc.mod(SieveUtils.product(cycle.primes), cycle.apply(BigInt(1))) != BigInt(0))

    val nextSpec = spec.next
    val nextCycle = cycle.nextWithGapCycle(newGapCycle)

    require(nextSpec(nextPeriod) == nextSpec.head.value + nextSpec.filterModulus)
    require(nextSpec.specGapCycle(nextPeriod).memCycle == nextCycle.gapCycle.memCycle)

    assert(assertConditionalNextPrimeValuesMatch(spec, cycle, newGapCycle))
    assert(nextCycle.primes == PrimeUtils.primeValues(nextSpec.primes.list.list))
    assert(assertHeadsMatchFromPrimeValues(nextSpec, nextCycle))
    assert(nextSpec.head.value == nextCycle.head)
    assert(
      assertSpecCycleApplyMatchesFromSameHeadAndGaps(
        nextSpec,
        nextCycle,
        nextPeriod,
        position
      )
    )

    nextSpec(position) == nextCycle(position)
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

  /**
   * Exposes one-value completeness of the residue list.
   *
   * The residue pipeline starts by enumerating every value in
   * `[0, modulus)` that is coprime to the filter list. `SieveUtils` already
   * verifies this through `assertGenerateResiduesContainsCoprime`; this local
   * alias names the exact shape needed by the Spec/Cycle equivalence proof.
   *
   * This is only the completeness half of the "residues are exactly coprime"
   * property: if a residue passes the filter, then the generated residue list
   * contains it. The soundness half, from membership back to coprimality, should
   * stay separate so Stainless can verify each direction independently.
   */
  def assertResiduesContainCoprimeBelowModulus(
    modulus: BigInt,
    filters: stainless.collection.List[BigInt],
    residue: BigInt
  ): Boolean = {
    require(residue >= BigInt(0))
    require(residue < modulus)
    require(modulus > BigInt(0))
    require(ListUtils.checkAllPositive(filters))
    require(SieveUtils.isCoprime(residue, filters))

    assert(SieveUtils.assertGenerateResiduesContainsCoprime(
      residue,
      BigInt(0),
      modulus,
      filters
    ))

    SieveUtils.residues(modulus, filters).contains(residue)
  }.holds

  /**
   * Proves one-value soundness for the recursive residue generator.
   *
   * `generateResidues(from, modulus, filters)` walks forward from `from` to
   * `modulus`, adding a value exactly when it is coprime to `filters`. This
   * helper exposes the membership direction of that construction: any value
   * found in the generated list must have passed the same coprime test.
   *
   * The public `residues` function is just `generateResidues(0, ...)`; keeping
   * this recursive helper separate makes the later top-level soundness alias a
   * direct call instead of a proof that has to rediscover the generator's shape.
   */
  def assertGenerateResiduesContainOnlyCoprime(
    modulus: BigInt,
    filters: stainless.collection.List[BigInt],
    residue: BigInt,
    from: BigInt
  ): Boolean = {
    require(from >= BigInt(0))
    require(from <= modulus)
    require(modulus > BigInt(0))
    require(ListUtils.checkAllPositive(filters))
    require(SieveUtils.generateResidues(from, modulus, filters).contains(residue))
    decreases(modulus - from)

    if (from == modulus) {
      false
    } else {
      val rest = SieveUtils.generateResidues(from + BigInt(1), modulus, filters)
      if (SieveUtils.isCoprime(from, filters)) {
        if (residue == from) {
          SieveUtils.isCoprime(residue, filters)
        } else {
          assert(rest.contains(residue))
          assert(assertGenerateResiduesContainOnlyCoprime(modulus, filters, residue, from + BigInt(1)))
          SieveUtils.isCoprime(residue, filters)
        }
      } else {
        assert(rest.contains(residue))
        assert(assertGenerateResiduesContainOnlyCoprime(modulus, filters, residue, from + BigInt(1)))
        SieveUtils.isCoprime(residue, filters)
      }
    }
  }.holds
}
