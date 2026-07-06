package v1.chapter6.seq.sieve

import stainless.collection.List
import stainless.lang.BooleanDecorations
import stainless.lang.decreases
import v1.chapter2.div.Calc
import v1.chapter2.div.properties.ModOperations
import v1.chapter3.list.{ListBoundUtils, ListUtils}
import v1.chapter3.list.properties.ListRepeatProperties
import v1.chapter4.cycle.gap.GapCycle
import v1.chapter4.cycle.integral.recursive.CycleIntegral
import v1.chapter4.cycle.integral.recursive.properties.{
  CycleIntegralFilterProperties,
  CycleIntegralProperties,
  GapProperties
}
import v1.chapter4.cycle.memory.MemCycle
import v1.chapter4.cycle.memory.properties.MemCycleProperties
import v1.chapter5.prime.{AllPrimesSoFarList, Prime, PrimeUtils, SortedPrimeList}

/**
 * A `SpecDerivedCycleSieve` variant that stores `primes` as `AllPrimesSoFarList`
 * instead of `List[BigInt]`. This exposes the richer prime-type API for lemma
 * proofs — `nextPrime`, `noDivisorInRange`, primorial, etc. — all verified in
 * the prime chapter.
 *
 * The `cycle` field is a standard `CycleSieveSequence` (with `List[BigInt]`
 * primes, converted via `PrimeUtils.primeValues`). The APSFL version of the
 * prime list is available as `primesAPSFL` for proof use.
 *
 * Usage: construct from a `SpecSieveSequence` + `period`, then use the lemma
 * methods to discharge `nextFromWindow()` requires. Convert to `CycleSieveSequence`
 * via `cycle` when a concrete sequence is needed.
 */
case class SpecDerivedSieveSequence(
  spec: SpecSieveSequence,
  period: BigInt
) {
  require(period > BigInt(0))
  require(spec(period) == spec.head.value + spec.tailPrimorial)
  require(spec.primes.nextPrime.value < spec.head.value * spec.head.value)
  require(spec.primes.list.nonEmpty)
  require(
    Calc.mod(
      SieveUtils.product(spec.filterValues),
      spec.head.value
    ) != BigInt(0)
  )

  /** Gap cycle derived from the spec — same as SpecDerivedCycleSieve. */
  val gapCycle: GapCycle = spec.specGapCycle(period)

  /** Prime list as AllPrimesSoFarList — all lemmas from prime chapter available. */
  val primes: AllPrimesSoFarList = spec.primes

  /** Prime list as List[BigInt] for CycleSieveSequence construction. */
  val cyclePrimes: List[BigInt] = PrimeUtils.primeValues(primes.list.list)

  /** Standard CycleSieveSequence (for callers that need the concrete type). */
  val cycle: CycleSieveSequence = CycleSieveSequence(primes, gapCycle)

  /** Cycle integral — same as cycle.integral. */
  val integral: CycleIntegral = cycle.integral

  /**
   * Proves `cycle(k) == spec(k)` for all k — same as SpecDerivedCycleSieve's.
   * Delegates to the spec's certified gap cycle integral.
   */
  def assertApplyMatches(k: BigInt): Boolean = {
    require(k >= BigInt(0))
    if (k == BigInt(0)) {
      assert(cycle.head == spec.head.value)
      assert(spec(BigInt(0)) == spec.head.value)
      cycle(k) == spec(k)
    } else {
      assert(cycle.gapCycle.memCycle == gapCycle.memCycle)
      assert(cycle.integral ==
        v1.chapter4.cycle.integral.recursive.CycleIntegral(
          spec.head.value, gapCycle.memCycle))
      assert(spec.assertSpecGapCycleIntegralMatchesApply(period, k))
      cycle(k) == spec(k)
    }
  }.holds

  /**
   * Proves `cycle(1) == spec.next.head.value` — next head matches.
   * Mirrors SpecDerivedCycleSieve's version.
   */
  def assertNextHeadMatches(): Boolean = {
    assert(assertApplyMatches(BigInt(1)))
    assert(spec.assertApplyOneEqualsNextPrime())
    assert(cycle(BigInt(1)) == spec(BigInt(1)))
    assert(spec(BigInt(1)) == spec.primes.nextPrime.value)
    assert(spec.next.head.value == spec.primes.nextPrime.value)
    cycle(BigInt(1)) == spec.next.head.value
  }.holds

  /**
   * Proves `cycle(1) == spec(1)` and cycle's prime list matches spec's
   * filter values (for isCoprime compatibility).
   */
  def assertPrimesMatch(): Boolean = {
    assert(assertApplyMatches(BigInt(0)))
    assert(cycle.head == spec.head.value)
    assert(cyclePrimes == PrimeUtils.primeValues(primes.list.list))
    assert(primes.list.list == spec.primes.list.list)
    true
  }.holds

  def primorialMatchesProduct(primeList: v1.chapter5.prime.SortedPrimeList): Boolean = {
    require(primeList.list.nonEmpty)
    decreases(primeList.list.size)
    if (primeList.list.tail.isEmpty) {
      PrimeUtils.primorial(primeList.list) == PrimeUtils.primeValues(primeList.list).last
    } else {
      assert(primorialMatchesProduct(primeList.tail))
      PrimeUtils.primorial(primeList.list) == SieveUtils.product(PrimeUtils.primeValues(primeList.list))
    }
  }.holds

  def assertCycleModulusEqualsSpecTailPrimorial(): Boolean = {
    assert(primorialMatchesProduct(spec.primes.list.tail))
    cycle.modulus == spec.tailPrimorial
  }.holds

  /**
   * Per-index survivor-to-spec-next gap equality.
   *
   * Proves that for consecutive cycle survivors `pos1`, `pos2` corresponding
   * to `spec.next(k)` and `spec.next(k+1)`, the gap between survivors equals
   * the gap between the corresponding spec.next values.
   */
  def assertSurvivorGapEqualsSpecNextGap(nextPeriod: BigInt, k: BigInt): Boolean = {
    require(nextPeriod > BigInt(1))
    require(k >= BigInt(0))
    require(k + BigInt(1) < nextPeriod)
    require(spec.next(nextPeriod) == spec.next.head.value + spec.next.tailPrimorial)
    assert(spec.assertNextValueAcceptedByThis(k))
    assert(spec.assertNextValueAcceptedByThis(k + BigInt(1)))
    val pos1 = spec.indexOfAccepted(spec.next(k))
    val pos2 = spec.indexOfAccepted(spec.next(k + BigInt(1)))
    assert(assertApplyMatches(pos1))
    assert(assertApplyMatches(pos2))
    assert(spec(pos1) == spec.next(k))
    assert(spec(pos2) == spec.next(k + BigInt(1)))
    spec.next(k + BigInt(1)) - spec.next(k) == cycle(pos2) - cycle(pos1)
  }.holds

  /**
   * Canonical next-stage gap-cycle packaging.
   *
   * This lemma is intentionally about the Spec-certified next cycle, not about
   * the independent pipeline output. It records the construction fact that
   * `spec.next.specGapCycle(nextPeriod)` stores exactly
   * `spec.next.gapList(0, nextPeriod)` as its memory-cycle values. Keeping this
   * bridge explicit prevents future edits from mistaking the canonical
   * Spec-derived cycle proof for a proof about `nextRotatedGaps(cycle)`.
   */
  def assertNextGapCycleValuesEqualSpecNextGapList(nextPeriod: BigInt): Boolean = {
    require(nextPeriod > BigInt(0))
    require(spec.next(nextPeriod) == spec.next.head.value + spec.next.tailPrimorial)

    spec.next.specGapCycle(nextPeriod).memCycle.values == spec.next.gapList(BigInt(0), nextPeriod)
  }.holds

  /**
   * Canonical next-stage gap equality.
   *
   * The canonical wrapper for `spec.next` stores `spec.next.specGapCycle` as
   * its gap cycle. The earlier packaging lemma exposes that this gap cycle's
   * memory values are exactly `spec.next.gapList(0, nextPeriod)`.
   */
  def assertNextCycleGapsMatchSpecNext(nextPeriod: BigInt): Boolean = {
    require(nextPeriod > BigInt(0))
    require(spec.next(nextPeriod) == spec.next.head.value + spec.next.tailPrimorial)
    require(spec.next.primes.nextPrime.value < spec.next.head.value * spec.next.head.value)
    require(spec.next.primes.list.nonEmpty)
    require(Calc.mod(SieveUtils.product(spec.next.filterValues), spec.next.head.value) != BigInt(0))

    val nextCanonical = SpecDerivedSieveSequence(spec.next, nextPeriod)
    val nextSpecGapCycle = spec.next.specGapCycle(nextPeriod)

    assert(nextCanonical.cycle.gapCycle == nextSpecGapCycle)
    assert(assertNextGapCycleValuesEqualSpecNextGapList(nextPeriod))

    nextCanonical.cycle.gapCycle.memCycle.values == spec.next.gapList(BigInt(0), nextPeriod)
  }.holds

  /**
   * Builds the same B cycle with its gap period repeated `times` times.
   *
   * Math:
   *
   *   B      = cycle
   *   G      = B.gapCycle.memCycle.values
   *   times  > 0
   *   G^times = repeat(G, times)
   *
   *   repeatedCycle(times) = CycleSieveSequence(primes, GapCycle(G^times))
   *
   * Repeating the stored gap list does not change the semantic cycle: it only
   * changes the physical period length. This constructor is isolated so later
   * lemmas can compare the original and repeated cycles without reopening
   * `GapCycle` positivity/non-emptiness obligations.
   */
  def repeatedCycle(times: BigInt): CycleSieveSequence = {
    require(times > BigInt(0))

    val gaps = cycle.gapCycle.memCycle.values
    val repeatedGaps = ListRepeatProperties.repeat(gaps, times)

    assert(GapCycle.assertMemCycleValuesPositive(cycle.gapCycle))
    assert(ListRepeatProperties.assertRepeatAllGreaterThan(gaps, times, BigInt(0)))
    assert(ListRepeatProperties.assertRepeatSize(gaps, times))
    assert(repeatedGaps.size == gaps.size * times)
    assert(gaps.nonEmpty)
    assert(repeatedGaps.nonEmpty)
    assert(ListBoundUtils.allGreaterThan(repeatedGaps, BigInt(0)))

    CycleSieveSequence(primes, GapCycle(repeatedGaps))
  }

  /**
   * Bounded-index equality for B's repeated gap period.
   *
   * Math:
   *
   *   G = cycle.gapCycle.memCycle.values
   *   R = repeat(G, times)
   *
   *   times > 0
   *   0 <= index < size(G) * times
   *
   *   R(index) = G(mod(index, size(G)))
   *
   * If we physically repeat B's stored gap list `times` times, any index inside
   * that repeated list reads the same gap as the original list at the modulo
   * position. This is the list-level seed for proving the repeated cycle has
   * the same `apply` behavior as B.
   */
  def assertRepeatedGapListIndexMatches(times: BigInt, index: BigInt): Boolean = {
    require(times > BigInt(0))
    require(index >= BigInt(0))

    val gaps = cycle.gapCycle.memCycle.values
    require(index < gaps.size * times)

    val repeatedGaps = ListRepeatProperties.repeat(gaps, times)

    assert(GapCycle.assertMemCycleValuesPositive(cycle.gapCycle))
    assert(ListRepeatProperties.assertRepeatSize(gaps, times))
    assert(ListRepeatProperties.assertRepeatedIndex(gaps, times, index))

    repeatedGaps(index) == gaps(Calc.mod(index, gaps.size))
  }.holds

  /**
   * Repeating B's physical gap storage does not change B's gap cycle lookup.
   *
   * Math:
   *
   *   B      = cycle
   *   B_t    = repeatedCycle(times)
   *   G      = B.gapCycle.memCycle.values
   *   R      = repeat(G, times)
   *   n      = size(G)
   *   period = n * times
   *
   *   B_t.gap(position)
   *     = R(mod(position, period))
   *     = G(mod(mod(position, period), n))
   *     = G(mod(position, n))
   *     = B.gap(position)
   *
   * The repeated cycle has a larger memory period (`oldSize * times`), so its
   * raw position is first reduced by that larger period. The chapter-2 modular
   * bridge then reduces that index back to the same old-period index used by
   * B's original `MemCycle`. This is the exact fact future `apply` proofs need:
   * repeated storage is an implementation detail, not a semantic change.
   */
  def assertRepeatedCycleGapMatches(times: BigInt, position: BigInt): Boolean = {
    require(times > BigInt(0))
    require(position >= BigInt(0))

    val gaps = cycle.gapCycle.memCycle.values
    val repeated = repeatedCycle(times)
    val repeatedGaps = ListRepeatProperties.repeat(gaps, times)

    assert(GapCycle.assertMemCycleValuesPositive(cycle.gapCycle))
    assert(gaps.nonEmpty)
    assert(gaps.size > BigInt(0))
    assert(ListRepeatProperties.assertRepeatSize(gaps, times))
    assert(repeatedGaps.size == gaps.size * times)
    assert(repeated.gapCycle.memCycle.values == repeatedGaps)
    assert(repeated.gapCycle.memCycle.size == gaps.size * times)

    assert(MemCycleProperties.assertRepeatedValuesCycleMatches(
      cycle.gapCycle.memCycle,
      repeated.gapCycle.memCycle,
      times,
      position
    ))

    repeated.gapCycle.memCycle(position) == cycle.gapCycle.memCycle(position)
  }.holds

  /**
   * Repeating B's gap storage preserves B's cumulative integral.
   *
   * Math:
   *
   *   B   = cycle
   *   B_t = repeatedCycle(times)
   *
   *   integral_B(0)   = head(B)   + gap_B(0)
   *   integral_B(k)   = integral_B(k - 1)   + gap_B(k)
   *   integral_Bt(0)  = head(B_t) + gap_Bt(0)
   *   integral_Bt(k)  = integral_Bt(k - 1)  + gap_Bt(k)
   *
   *   head(B_t) = head(B)
   *   gap_Bt(k) = gap_B(k)
   *
   *   Therefore, by the generic repeated-values integral lemma:
   *
   *   integral_Bt(k) = integral_B(k)
   */
  def assertRepeatedCycleIntegralMatches(times: BigInt, position: BigInt): Boolean = {
    require(times > BigInt(0))
    require(position >= BigInt(0))

    val gaps = cycle.gapCycle.memCycle.values
    val repeated = repeatedCycle(times)
    val repeatedGaps = ListRepeatProperties.repeat(gaps, times)

    assert(GapCycle.assertMemCycleValuesPositive(cycle.gapCycle))
    assert(gaps.size > BigInt(0))
    assert(ListRepeatProperties.assertRepeatSize(gaps, times))
    assert(repeated.gapCycle.memCycle.values == repeatedGaps)
    assert(repeated.integral.initialValue == cycle.integral.initialValue)
    assert(CycleIntegralProperties.assertRepeatedValuesIntegralMatches(
      cycle.integral,
      repeated.integral,
      times,
      position
    ))

    repeated.integral(position) == cycle.integral(position)
  }.holds

  /**
   * Repeating B's gap period preserves B's sequence value at every position.
   * The proof is intentionally staged by lowering a positive sequence index
   * `k` to the strictly smaller integral index `k - 1`.
   *
   * Math:
   *
   *   B   = cycle
   *   B_t = repeatedCycle(times)
   *   times > 0, k >= 0
   *
   *   B(0)   = head(B)
   *   B_t(0) = head(B_t) = head(B)
   *
   *   For k > 0:
   *
   *   j      = k - 1, so 0 <= j < k
   *   B(k)   = integral_B(k - 1)
   *   B_t(k) = integral_Bt(k - 1)
   *          = integral_B(k - 1)
   *          = B(k)
   *
   * Therefore:
   *
   *   repeatedCycle(times)(k) = cycle(k)
   *
   * This is the semantic version of the repeated-storage fact: repeating a
   * physical gap period changes the memory representation only, not the
   * generated sequence.
   */
  def assertRepeatedCycleApplyMatches(times: BigInt, k: BigInt): Boolean = {
    require(times > BigInt(0))
    require(k >= BigInt(0))

    val repeated = repeatedCycle(times)

    if (k == BigInt(0)) {
      assert(repeated.head == cycle.head)
      assert(repeated(k) == repeated.head)
      assert(cycle(k) == cycle.head)
      assert(repeated(k) == cycle(k))

      repeated(k) == cycle(k)
    } else {
      val previousPosition = k - BigInt(1)
      assert(previousPosition >= BigInt(0))
      assert(previousPosition < k)
      assert(assertRepeatedCycleIntegralMatches(times, previousPosition))
      val repeatedValue = repeated(k)
      val originalValue = cycle(k)
      val repeatedIntegral = repeated.integral(previousPosition)
      val originalIntegral = cycle.integral(previousPosition)

      assert(repeatedIntegral == originalIntegral)
      assert(repeatedValue == repeatedIntegral)
      assert(originalValue == originalIntegral)
      assert(repeatedValue == originalValue)
      assert(repeated(k) == cycle(k))

      repeated(k) == cycle(k)
    }
  }.holds

  def assertNextHeadLessThanNewModulus(): Boolean = {
    require(spec.head.value >= 3)
    require(spec.tailPrimorial >= 2)

    assert(assertApplyMatches(BigInt(1)))
    assert(assertCycleModulusEqualsSpecTailPrimorial())
    assert(spec(BigInt(1)) <= spec.searchBound(BigInt(1)))
    assert(spec.head.value * spec.tailPrimorial > spec.head.value + spec.tailPrimorial)
    cycle(BigInt(1)) < cycle.head * cycle.modulus
  }.holds
}
