package v1.chapter6.seq.sieve

import stainless.lang.*
import v1.chapter2.div.Calc
import v1.chapter3.list.ListUtils
import v1.chapter5.prime.{Prime, PrimeUtils}

/**
 * Canonical correspondence between one specification sieve stage and its
 * cycle-based representation.
 *
 * `SpecSieveSequence` remains the mathematical source of truth. It defines the
 * accepted values, proves the gap sequence, and packages one verified period as
 * `specGapCycle(period)`. `CycleSieveSequence` remains responsible only for
 * generic cycle mechanics and invariants that apply to every valid cycle.
 *
 * This intermediate representation owns the relationship between those two
 * classes. It receives a Spec stage, extracts the exact prime values and gap
 * cycle certified by that stage, and constructs the corresponding Cycle stage.
 * All later alignment lemmas should live here so neither underlying sequence
 * needs to know how the other one is represented.
 *
 * The constructor requirements state the current proof boundary:
 *
 *  - `period` identifies one positive Spec gap period;
 *  - the period returns to the same tail-filter residue;
 *  - the direct next prime is below the current head squared, which is the
 *    conditional number-theory assumption used by `SpecSieveSequence.next`;
 *  - the current tail product is not divisible by the current head, matching
 *    the structural requirement of `CycleSieveSequence`.
 *
 * Once constructed, `cycle` is not an independently supplied optimized state.
 * It is derived from `spec` itself, so its prime list and stored gaps have one
 * canonical origin.
 */
case class CanonicalCycleSieve(
  spec: SpecSieveSequence,
  period: BigInt
) {
  require(period > BigInt(0))
  require(spec(period) == spec.head.value + spec.filterModulus)
  require(spec.primes.nextPrime.value < spec.head.value * spec.head.value)
  require(
    Calc.mod(
      SieveUtils.product(spec.filterValues),
      spec.head.value
    ) != BigInt(0)
  )

  /**
   * The exact Cycle representation extracted from `spec`.
   *
   * The raw prime list contains every current Spec prime value in the same
   * order. The gap cycle is `spec.specGapCycle(period)`, not a separately
   * discovered or caller-provided cycle. The assertions below translate the
   * Spec facts into the generic structural obligations required by
   * `CycleSieveSequence`.
   */
  val cycle: CycleSieveSequence = {
    val cyclePrimes = PrimeUtils.primeValues(spec.primes.list.list)
    val gapCycle = spec.specGapCycle(period)
    val firstNext = spec(BigInt(1))

    assert(cyclePrimes.head == spec.head.value)
    assert(cyclePrimes.tail == spec.filterValues)
    assert(ListUtils.checkAllPositive(cyclePrimes))
    assert(ListUtils.checkAllBiggerThanValue(cyclePrimes, BigInt(1)))
    assert(SieveUtils.assertProductEqualOrBiggerThanElements(cyclePrimes.tail))
    assert(SieveUtils.isCoprime(cyclePrimes.head, cyclePrimes.tail))

    assert(spec.assertMemCycleGapMatch(BigInt(0), period))
    assert(gapCycle.memCycle(BigInt(0)) == firstNext - spec.head.value)
    assert(cyclePrimes.head + gapCycle.memCycle(BigInt(0)) == firstNext)
    assert(firstNext > spec.head.value)
    assert(spec.accepts(firstNext))
    assert(SieveUtils.isCoprime(firstNext, cyclePrimes.tail))

    assert(spec.assertApplyOneEqualsNextPrime())
    assert(Prime.isPrime(firstNext))
    assert(
      Prime.noDivisorInRangeExcludesValue(
        firstNext,
        BigInt(2),
        firstNext,
        spec.head.value
      )
    )
    assert(Calc.mod(firstNext, spec.head.value) != BigInt(0))
    assert(
      Calc.mod(
        SieveUtils.product(cyclePrimes.tail),
        cyclePrimes.head
      ) != BigInt(0)
    )

    CycleSieveSequence(cyclePrimes, gapCycle)
  }

  /**
   * Proves the extracted Cycle representation generates exactly the Spec
   * stream at every non-negative index.
   *
   * Index zero is the shared head. At a positive index, the Cycle sequence uses
   * `CycleIntegral` over the exact `specGapCycle(period)` stored by this bridge,
   * while `SpecSieveSequence.assertSpecGapCycleIntegralMatchesApply` proves that
   * the same integral reconstructs `spec(k)`.
   */
  def assertApplyMatches(k: BigInt): Boolean = {
    require(k >= BigInt(0))

    if (k == BigInt(0)) {
      assert(cycle.head == spec.head.value)
      assert(spec(BigInt(0)) == spec.head.value)
      cycle(k) == spec(k)
    } else {
      val gapCycle = spec.specGapCycle(period)
      assert(cycle.gapCycle.memCycle == gapCycle.memCycle)
      assert(
        cycle.integral ==
          v1.chapter4.cycle.integral.recursive.CycleIntegral(
            spec.head.value,
            gapCycle.memCycle
          )
      )
      assert(spec.assertSpecGapCycleIntegralMatchesApply(period, k))
      cycle(k) == spec(k)
    }
  }.holds

  /**
   * Exposes that the canonical Cycle starts at the Spec head.
   */
  def assertHeadMatches(): Boolean = {
    cycle.head == spec.head.value
  }.holds

  /**
   * Exposes that the canonical Cycle stores exactly the Spec prime values.
   */
  def assertPrimesMatch(): Boolean = {
    cycle.primes == PrimeUtils.primeValues(spec.primes.list.list)
  }.holds

  /**
   * Exposes that the canonical Cycle stores the exact Spec-derived gap cycle.
   */
  def assertGapCycleMatches(): Boolean = {
    cycle.gapCycle.memCycle == spec.specGapCycle(period).memCycle
  }.holds

  /**
   * Proves the canonical Cycle chooses the same next head as `spec.next`.
   */
  def assertNextHeadMatches(): Boolean = {
    val nextSpec = spec.next

    assert(assertApplyMatches(BigInt(1)))
    assert(spec.assertApplyOneEqualsNextPrime())
    assert(cycle(BigInt(1)) == spec(BigInt(1)))
    assert(spec(BigInt(1)) == spec.primes.nextPrime.value)
    assert(nextSpec.head.value == spec.primes.nextPrime.value)

    cycle(BigInt(1)) == nextSpec.head.value
  }.holds

  /**
   * Proves `spec.next` accepts exactly the values coprime to the canonical
   * Cycle's current prime list.
   */
  def assertNextAcceptsMatches(value: BigInt): Boolean = {
    require(value >= spec.next.head.value)

    val nextSpec = spec.next

    assert(assertPrimesMatch())
    assert(nextSpec.primes.list.tail.list == spec.primes.list.list)
    assert(nextSpec.filterPrimes == nextSpec.primes.list.tail.list)
    assert(nextSpec.filterValues == PrimeUtils.primeValues(nextSpec.filterPrimes))
    assert(nextSpec.filterValues == PrimeUtils.primeValues(spec.primes.list.list))
    assert(nextSpec.filterValues == cycle.primes)
    assert(
      nextSpec.accepts(value) ==
        SieveUtils.isCoprime(value, nextSpec.filterValues)
    )

    nextSpec.accepts(value) == SieveUtils.isCoprime(value, cycle.primes)
  }.holds

  /**
   * Proves the raw prime list produced by a canonical Cycle next stage matches
   * the prime values stored by `spec.next`.
   */
  def assertNextPrimesMatch(): Boolean = {
    val nextSpec = spec.next

    assert(assertNextHeadMatches())
    assert(assertPrimesMatch())
    assert(cycle(BigInt(1)) == nextSpec.head.value)
    assert(cycle.primes == PrimeUtils.primeValues(spec.primes.list.list))
    assert(nextSpec.primes.list.tail.list == spec.primes.list.list)

    cycle(BigInt(1)) :: cycle.primes ==
      PrimeUtils.primeValues(nextSpec.primes.list.list)
  }.holds

  /**
   * Proves the walk decision condition is equivalent to next-stage acceptance.
   *
   * For k >= 1, the walk `collectGaps` keeps `cycle(k)` exactly when
   * `Calc.mod(cycle(k), cycle.head) != 0`. The next stage accepts `cycle(k)`
   * exactly when it is coprime to `cycle.primes`. Since `cycle(k)` already
   * passes the tail filter (because `spec(k)` passes it), coprimality to
   * `cycle.primes` reduces to the non-divisibility by `cycle.head`.
   *
   * This bridges the walk's branch condition to Spec.next's acceptance
   * predicate, enabling a later recursive gap equality proof.
   */
  def assertWalkDecisionMatchesNextAccept(k: BigInt): Boolean = {
    require(k >= BigInt(1))

    val v = cycle(k)

    assert(assertApplyMatches(k))
    assert(spec(k) == v)
    assert(spec.assertApplyMonotonic(BigInt(1), k))
    assert(spec(BigInt(1)) <= spec(k))
    assert(assertApplyMatches(BigInt(1)))
    assert(spec(BigInt(1)) == cycle(BigInt(1)))
    assert(assertNextHeadMatches())
    assert(cycle(BigInt(1)) == spec.next.head.value)
    assert(spec(BigInt(1)) == spec.next.head.value)
    assert(v >= spec.next.head.value)
    assert(spec(k) >= spec.head.value)
    assert(spec.accepts(spec(k)))
    assert(SieveUtils.isCoprime(spec(k), spec.filterValues))
    assert(assertPrimesMatch())
    assert(PrimeUtils.primeValues(spec.primes.list.list).tail ==
      PrimeUtils.primeValues(spec.primes.list.list.tail))
    assert(spec.filterValues == PrimeUtils.primeValues(spec.filterPrimes))
    assert(spec.filterPrimes == spec.primes.list.list.tail)
    assert(cycle.primes.tail == spec.filterValues)
    assert(SieveUtils.isCoprime(v, cycle.primes.tail))
    assert(assertNextAcceptsMatches(v))
    assert(spec.next.accepts(v) == SieveUtils.isCoprime(v, cycle.primes))

    val modNonZero = Calc.mod(v, cycle.head) != BigInt(0)

    modNonZero == spec.next.accepts(v)
  }.holds

  /**
   * Proves the canonical next-stage gap cycle values equal `spec.next.gapList`.
   *
   * This is true by construction: `specGapCycle(period)` creates a `GapCycle`
   * from `gapList(0, period)`. For the next stage, `spec.next.specGapCycle(nextPeriod)`
   * stores `gapList(0, nextPeriod)` as its values. Exposing this as a lemma
   * makes it available for downstream alignment proofs.
   */
  def assertNextGapCycleValuesEqualSpecNextGapList(nextPeriod: BigInt): Boolean = {
    require(nextPeriod > BigInt(0))
    require(spec.next(nextPeriod) == spec.next.head.value + spec.next.filterModulus)

    spec.next.specGapCycle(nextPeriod).memCycle.values == spec.next.gapList(BigInt(0), nextPeriod)
  }.holds

  /**
   * Proves the canonical next-stage apply matches `spec.next.apply(k)`.
   *
   * `spec.next.assertSpecGapCycleIntegralMatchesApply(nextPeriod, k)` proves
   * that the integral reconstruction using `specGapCycle(nextPeriod)` at index
   * `k` equals `spec.next(k)`. This integral reconstruction IS the canonical
   * cycle apply for the next stage (for positive indices), so this lemma
   * establishes the apply match without constructing a new
   * `CanonicalCycleSieve` instance.
   */
  def assertNextApplyMatches(nextPeriod: BigInt, k: BigInt): Boolean = {
    require(nextPeriod > BigInt(0))
    require(spec.next(nextPeriod) == spec.next.head.value + spec.next.filterModulus)
    require(k > BigInt(0))

    spec.next.assertSpecGapCycleIntegralMatchesApply(nextPeriod, k)
  }.holds
}
