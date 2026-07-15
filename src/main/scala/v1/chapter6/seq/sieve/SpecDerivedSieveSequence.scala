package v1.chapter6.seq.sieve

import stainless.collection.List
import stainless.lang.BooleanDecorations
import stainless.lang.decreases
import v1.chapter2.div.Calc
import v1.chapter2.div.properties.AdditionAndMultiplication
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
   * Computes the number of survivors after applying the head filter
   * to the expanded residue interval, then proves the closed form.
   *
   * The body calls `spec.sameHeadSurvivorCount` which actually scans
   * the interval [head, head + head*tailPrimorial) and counts every
   * accepted value not divisible by the head. The ensuring proves
    * this count equals `period * (head - 1)`, the expected period of
    * the next stage's gap cycle.
   */
  def nextPeriod(): BigInt = {
    assert(primorialMatchesProduct(spec.primes.list.tail))
    spec.sameHeadSurvivorCount(period)
  }.ensuring(count => {
    count == period * (spec.head.value - BigInt(1))
  })

  def assertNextPeriodMatchesExpandedFilterCount(): Boolean = {
    assert(primorialMatchesProduct(spec.primes.list.tail))
    assert(Calc.mod(spec.tailPrimorial, spec.head.value) != BigInt(0))
    assert(spec.assertExpandedGeneratedHeadMultipleCount(period))

    val count = nextPeriod()

    count == period * (spec.head.value - BigInt(1))
  }.holds

  def assertNextPeriodMatchesShiftedWindowCount(): Boolean = {
    assert(primorialMatchesProduct(spec.primes.list.tail))
    assert(Calc.mod(spec.tailPrimorial, spec.head.value) != BigInt(0))
    assert(spec.assertSameHeadShiftedWindowCount(period))

    val count = nextPeriod()

    count == period * (spec.head.value - BigInt(1))
  }.holds

  /**
   * The gap cycle stores exactly `period` gaps, matching the spec's
   * canonical period.
   */
  def assertCyclePeriod(): Boolean = {
    assert(spec.assertGapListSize(BigInt(0), period))
    cycle.gapCycle.period == period
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
    assert(repeated.gapCycle.memCycle.period == gaps.size * times)

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

  def repeatedCycleMatchesSpecPrefix(times: BigInt, count: BigInt): Boolean = {
    require(times > BigInt(0))
    require(count >= BigInt(0))
    decreases(count)

    if (count == BigInt(0)) {
      true
    } else {
      val index = count - BigInt(1)
      repeatedCycleMatchesSpecPrefix(times, index) &&
        repeatedCycle(times)(index) == spec(index)
    }
  }

  def assertRepeatedCycleMatchesSpecPrefix(times: BigInt, count: BigInt): Boolean = {
    require(times > BigInt(0))
    require(count >= BigInt(0))
    decreases(count)

    if (count == BigInt(0)) {
      repeatedCycleMatchesSpecPrefix(times, count)
    } else {
      val index = count - BigInt(1)
      assert(index >= BigInt(0))
      assert(assertRepeatedCycleMatchesSpecPrefix(times, index))
      assert(repeatedCycleMatchesSpecPrefix(times, index))
      assert(assertRepeatedCycleApplyMatches(times, index))
      assert(assertApplyMatches(index))
      assert(repeatedCycle(times)(index) == cycle(index))
      assert(cycle(index) == spec(index))
      assert(repeatedCycle(times)(index) == spec(index))

      repeatedCycleMatchesSpecPrefix(times, count)
    }
  }.holds

  def repeatedCycleMatchesSpecFirstExpandedPeriod(): Boolean = {
    val count = period * spec.head.value
    repeatedCycleMatchesSpecPrefix(spec.head.value, count)
  }

  def assertRepeatedCycleMatchesSpecFirstExpandedPeriod(): Boolean = {
    val count = period * spec.head.value

    assert(spec.head.value > BigInt(0))
    assert(count >= BigInt(0))
    assert(assertRepeatedCycleMatchesSpecPrefix(spec.head.value, count))

    repeatedCycleMatchesSpecFirstExpandedPeriod()
  }.holds

  def assertRepeatedIntegralMatchesShiftedSpec(index: BigInt): Boolean = {
    require(index >= BigInt(0))

    val repeated = repeatedCycle(spec.head.value)
    val specIndex = index + BigInt(1)

    assert(spec.head.value > BigInt(0))
    assert(specIndex >= BigInt(1))
    assert(assertRepeatedCycleApplyMatches(spec.head.value, specIndex))
    assert(assertApplyMatches(specIndex))
    assert(repeated(specIndex) == repeated.integral(index))
    assert(repeated(specIndex) == cycle(specIndex))
    assert(cycle(specIndex) == spec(specIndex))

    repeated.integral(index) == spec(index + BigInt(1))
  }.holds

  def assertRepeatedCycleNextAcceptsMatchesHeadFilterFirstExpandedPeriod(count: BigInt): Boolean = {
    require(count >= BigInt(0))
    require(count <= period * spec.head.value)
    decreases(count)

    if (count == BigInt(0)) {
      true
    } else {
      val index = count - BigInt(1)
      val specIndex = index + BigInt(1)
      val repeated = repeatedCycle(spec.head.value)
      val value = repeated.integral(index)

      assert(index >= BigInt(0))
      assert(specIndex >= BigInt(1))
      assert(assertRepeatedCycleNextAcceptsMatchesHeadFilterFirstExpandedPeriod(index))
      assert(assertRepeatedCycleApplyMatches(spec.head.value, specIndex))
      assert(assertApplyMatches(specIndex))
      assert(repeated(specIndex) == repeated.integral(index))
      assert(repeated(specIndex) == cycle(specIndex))
      assert(cycle(specIndex) == spec(specIndex))
      assert(value == spec(specIndex))
      assert(assertNextHeadMatches())
      assert(assertApplyMatches(BigInt(1)))
      assert(cycle(BigInt(1)) == spec.next.head.value)
      assert(cycle(BigInt(1)) == spec(BigInt(1)))
      assert(spec(BigInt(1)) == spec.next.head.value)
      assert(spec.assertApplyMonotonic(BigInt(1), specIndex))
      assert(spec(BigInt(1)) <= spec(specIndex))
      assert(value >= spec.next.head.value)
      assert(spec.accepts(value))
      assert(spec.assertNextAcceptsMatchesHeadFilterForAcceptedValue(value))

      spec.next.accepts(value) == (Calc.mod(value, spec.head.value) != BigInt(0))
    }
  }.holds

  def assertRepeatedCycleNextAcceptsMatchesHeadFilterFullFirstExpandedPeriod(): Boolean = {
    val count = period * spec.head.value

    assert(spec.head.value > BigInt(0))
    assert(count >= BigInt(0))
    assert(assertRepeatedCycleNextAcceptsMatchesHeadFilterFirstExpandedPeriod(count))

    true
  }.holds

  def assertRepeatedFirstWindowStartsAtSpecNextHead(): Boolean = {
    val repeated = repeatedCycle(spec.head.value)
    val value = repeated.integral(BigInt(0))

    assert(spec.head.value > BigInt(0))
    assert(assertRepeatedCycleApplyMatches(spec.head.value, BigInt(1)))
    assert(assertNextHeadMatches())
    assert(repeated(BigInt(1)) == repeated.integral(BigInt(0)))
    assert(repeated(BigInt(1)) == cycle(BigInt(1)))
    assert(cycle(BigInt(1)) == spec.next.head.value)
    assert(spec.next(BigInt(0)) == spec.next.head.value)
    assert(value == spec.next(BigInt(0)))
    assert(spec.assertNextValueAcceptedByThis(BigInt(0)))

    value == spec.next(BigInt(0)) &&
      Calc.mod(value, spec.head.value) != BigInt(0)
  }.holds

  def assertRepeatedFirstWindowSurvivorsHeadMatchesSpecNext(): Boolean = {
    val repeated = repeatedCycle(spec.head.value)
    val steps = period * spec.head.value
    val survivors = CycleIntegralFilterProperties.survivorValues(
      repeated.integral,
      spec.head.value,
      BigInt(0),
      steps
    )

    assert(spec.head.value > BigInt(0))
    assert(period > BigInt(0))
    assert(steps > BigInt(0))
    assert(assertRepeatedFirstWindowStartsAtSpecNextHead())
    assert(Calc.mod(repeated.integral(BigInt(0)), spec.head.value) != BigInt(0))
    assert(GapProperties.assertFirstSurvivorIsHead(
      repeated.integral,
      spec.head.value,
      BigInt(0),
      steps
    ))
    assert(survivors.head == repeated.integral(BigInt(0)))
    assert(repeated.integral(BigInt(0)) == spec.next(BigInt(0)))

    survivors.head == spec.next(BigInt(0))
  }.holds

  def assertRepeatedExtendedWindowSurvivorsHeadMatchesSpecNext(): Boolean = {
    val repeated = repeatedCycle(spec.head.value)
    val steps = period * spec.head.value + BigInt(1)
    val survivors = CycleIntegralFilterProperties.survivorValues(
      repeated.integral,
      spec.head.value,
      BigInt(0),
      steps
    )

    assert(spec.head.value > BigInt(0))
    assert(period > BigInt(0))
    assert(steps > BigInt(0))
    assert(assertRepeatedFirstWindowStartsAtSpecNextHead())
    assert(Calc.mod(repeated.integral(BigInt(0)), spec.head.value) != BigInt(0))
    assert(GapProperties.assertFirstSurvivorIsHead(
      repeated.integral,
      spec.head.value,
      BigInt(0),
      steps
    ))
    assert(survivors.head == repeated.integral(BigInt(0)))
    assert(repeated.integral(BigInt(0)) == spec.next(BigInt(0)))

    survivors.head == spec.next(BigInt(0))
  }.holds

  def assertRepeatedFirstWindowFilteredCIMatchesSurvivors(
    newCI: CycleIntegral,
    position: BigInt
  ): Boolean = {
    require(position >= BigInt(0))

    val repeated = repeatedCycle(spec.head.value)
    val steps = period * spec.head.value
    val survivors = CycleIntegralFilterProperties.survivorValues(
      repeated.integral,
      spec.head.value,
      BigInt(0),
      steps
    )

    require(!survivors.isEmpty)
    require(survivors.size > position + BigInt(1))
    require(position < newCI.period)
    require(newCI.period > BigInt(0))
    require(newCI.initialValue == survivors.head)
    require(newCI.cycle.values == CycleIntegralFilterProperties.gapsFromValues(survivors))

    assert(CycleIntegralFilterProperties.assertNewCIMatchesSurvivors(
      survivors,
      newCI,
      position
    ))

    newCI(position) == survivors(position + BigInt(1))
  }.holds

  def assertRepeatedExtendedWindowFilteredCIMatchesSurvivors(
    newCI: CycleIntegral,
    position: BigInt
  ): Boolean = {
    require(position >= BigInt(0))

    val repeated = repeatedCycle(spec.head.value)
    val steps = period * spec.head.value + BigInt(1)
    val survivors = CycleIntegralFilterProperties.survivorValues(
      repeated.integral,
      spec.head.value,
      BigInt(0),
      steps
    )

    require(!survivors.isEmpty)
    require(survivors.size > position + BigInt(1))
    require(position < newCI.period)
    require(newCI.period > BigInt(0))
    require(newCI.initialValue == survivors.head)
    require(newCI.cycle.values == CycleIntegralFilterProperties.gapsFromValues(survivors))

    assert(CycleIntegralFilterProperties.assertNewCIMatchesSurvivors(
      survivors,
      newCI,
      position
    ))

    newCI(position) == survivors(position + BigInt(1))
  }.holds

  def assertRepeatedExtendedWindowGapMatchesSpecNextGapAt(index: BigInt): Boolean = {
    require(index >= BigInt(0))

    val repeated = repeatedCycle(spec.head.value)
    val steps = period * spec.head.value + BigInt(1)
    val survivors = CycleIntegralFilterProperties.survivorValues(
      repeated.integral,
      spec.head.value,
      BigInt(0),
      steps
    )

    require(!survivors.isEmpty)
    require(index + BigInt(1) < survivors.size)
    require(survivors(index) == spec.next(index))
    require(survivors(index + BigInt(1)) == spec.next(index + BigInt(1)))

    val gaps = CycleIntegralFilterProperties.gapsFromValues(survivors)
    val specGaps = spec.next.gapList(BigInt(0), index + BigInt(1))

    assert(CycleIntegralFilterProperties.assertGapsFromValuesAtIndex(
      survivors,
      index
    ))
    assert(spec.next.assertGapListApplyEqualsGapAtPosition(
      BigInt(0),
      index + BigInt(1),
      index
    ))
    assert(gaps(index) == survivors(index + BigInt(1)) - survivors(index))
    assert(specGaps(index) == spec.next(index + BigInt(1)) - spec.next(index))

    gaps(index) == specGaps(index)
  }.holds

  def assertRepeatedExtendedWindowNextValueFromGapAt(index: BigInt): Boolean = {
    require(index >= BigInt(0))

    val repeated = repeatedCycle(spec.head.value)
    val steps = period * spec.head.value + BigInt(1)
    val survivors = CycleIntegralFilterProperties.survivorValues(
      repeated.integral,
      spec.head.value,
      BigInt(0),
      steps
    )

    require(!survivors.isEmpty)
    require(index + BigInt(1) < survivors.size)
    require(survivors(index) == spec.next(index))

    val gaps = CycleIntegralFilterProperties.gapsFromValues(survivors)
    val specGaps = spec.next.gapList(BigInt(0), index + BigInt(1))

    require(index < gaps.size)
    require(index < specGaps.size)
    require(gaps(index) == specGaps(index))

    assert(CycleIntegralFilterProperties.assertGapsFromValuesAtIndex(
      survivors,
      index
    ))
    assert(spec.next.assertGapListApplyEqualsGapAtPosition(
      BigInt(0),
      index + BigInt(1),
      index
    ))
    assert(gaps(index) == survivors(index + BigInt(1)) - survivors(index))
    assert(specGaps(index) == spec.next(index + BigInt(1)) - spec.next(index))
    assert(survivors(index) == spec.next(index))

    survivors(index + BigInt(1)) == spec.next(index + BigInt(1))
  }.holds

  def repeatedExtendedWindowGapsMatchSpecNextPrefix(count: BigInt): Boolean = {
    require(count >= BigInt(0))

    val repeated = repeatedCycle(spec.head.value)
    val steps = period * spec.head.value + BigInt(1)
    val survivors = CycleIntegralFilterProperties.survivorValues(
      repeated.integral,
      spec.head.value,
      BigInt(0),
      steps
    )

    require(!survivors.isEmpty)
    require(count < survivors.size)
    decreases(count)

    if (count == BigInt(0)) {
      true
    } else {
      val index = count - BigInt(1)
      val gaps = CycleIntegralFilterProperties.gapsFromValues(survivors)
      val specGaps = spec.next.gapList(BigInt(0), count)

      assert(index >= BigInt(0))
      assert(index < count)
      assert(index < survivors.size)

      repeatedExtendedWindowGapsMatchSpecNextPrefix(index) &&
        gaps(index) == specGaps(index)
    }
  }

  def assertRepeatedExtendedWindowValuesMatchSpecNextFromGapPrefix(count: BigInt): Boolean = {
    require(count >= BigInt(0))

    val repeated = repeatedCycle(spec.head.value)
    val steps = period * spec.head.value + BigInt(1)
    val survivors = CycleIntegralFilterProperties.survivorValues(
      repeated.integral,
      spec.head.value,
      BigInt(0),
      steps
    )

    require(!survivors.isEmpty)
    require(count < survivors.size)
    require(repeatedExtendedWindowGapsMatchSpecNextPrefix(count))
    decreases(count)

    if (count == BigInt(0)) {
      assert(assertRepeatedExtendedWindowSurvivorsHeadMatchesSpecNext())
      assert(survivors.head == spec.next(BigInt(0)))
      assert(survivors(BigInt(0)) == survivors.head)

      survivors(count) == spec.next(count)
    } else {
      val index = count - BigInt(1)
      val gaps = CycleIntegralFilterProperties.gapsFromValues(survivors)
      val specGaps = spec.next.gapList(BigInt(0), count)

      assert(index >= BigInt(0))
      assert(index < count)
      assert(index + BigInt(1) == count)
      assert(index + BigInt(1) < survivors.size)
      assert(repeatedExtendedWindowGapsMatchSpecNextPrefix(index))
      assert(assertRepeatedExtendedWindowValuesMatchSpecNextFromGapPrefix(index))
      assert(survivors(index) == spec.next(index))
      assert(index < gaps.size)
      assert(index < specGaps.size)
      assert(gaps(index) == specGaps(index))
      assert(assertRepeatedExtendedWindowNextValueFromGapAt(index))

      survivors(count) == spec.next(count)
    }
  }.holds

  def assertRepeatedExtendedWindowFilteredCIMatchesSpecNextFromGapPrefix(
    newCI: CycleIntegral,
    position: BigInt
  ): Boolean = {
    require(position >= BigInt(0))

    val repeated = repeatedCycle(spec.head.value)
    val steps = period * spec.head.value + BigInt(1)
    val survivors = CycleIntegralFilterProperties.survivorValues(
      repeated.integral,
      spec.head.value,
      BigInt(0),
      steps
    )
    val count = position + BigInt(1)

    require(!survivors.isEmpty)
    require(survivors.size > count)
    require(position < newCI.period)
    require(newCI.period > BigInt(0))
    require(newCI.initialValue == survivors.head)
    require(newCI.cycle.values == CycleIntegralFilterProperties.gapsFromValues(survivors))
    require(repeatedExtendedWindowGapsMatchSpecNextPrefix(count))

    assert(assertRepeatedExtendedWindowFilteredCIMatchesSurvivors(
      newCI,
      position
    ))
    assert(newCI(position) == survivors(count))
    assert(assertRepeatedExtendedWindowValuesMatchSpecNextFromGapPrefix(count))
    assert(survivors(count) == spec.next(count))

    newCI(position) == spec.next(position + BigInt(1))
  }.holds

  def assertSpecNextValueAppearsInRepeatedExtendedWindowSurvivors(k: BigInt): Boolean = {
    require(k >= BigInt(0))

    val repeated = repeatedCycle(spec.head.value)
    val steps = period * spec.head.value + BigInt(1)
    val survivors = CycleIntegralFilterProperties.survivorValues(
      repeated.integral,
      spec.head.value,
      BigInt(0),
      steps
    )
    val value = spec.next(k)
    val oldIndex = spec.indexOfAccepted(value)

    require(oldIndex > BigInt(0))
    require(oldIndex <= steps)

    val position = oldIndex - BigInt(1)

    assert(spec.assertNextValueAcceptedByThis(k))
    assert(spec.accepts(value))
    assert(spec(oldIndex) == value)
    assert(position >= BigInt(0))
    assert(position < steps)
    assert(assertRepeatedIntegralMatchesShiftedSpec(position))
    assert(repeated.integral(position) == spec(position + BigInt(1)))
    assert(position + BigInt(1) == oldIndex)
    assert(repeated.integral(position) == value)
    assert(spec.next.accepts(value))
    assert(value >= spec.next.head.value)
    assert(spec.assertNextAcceptsMatchesHeadFilterForAcceptedValue(value))
    assert(Calc.mod(value, spec.head.value) != BigInt(0))
    assert(Calc.mod(repeated.integral(position), spec.head.value) != BigInt(0))
    assert(GapProperties.assertSurvivorValuesContainsNonMultipleAtPosition(
      repeated.integral,
      spec.head.value,
      BigInt(0),
      steps,
      position
    ))

    survivors.contains(value)
  }.holds

  def assertSpecNextValueAppearsInRepeatedExtendedWindowSurvivorsFromValueBound(k: BigInt): Boolean = {
    require(k >= BigInt(0))

    val repeated = repeatedCycle(spec.head.value)
    val steps = period * spec.head.value + BigInt(1)
    val survivors = CycleIntegralFilterProperties.survivorValues(
      repeated.integral,
      spec.head.value,
      BigInt(0),
      steps
    )
    val value = spec.next(k)

    require(value <= spec(steps))

    val oldIndex = spec.indexOfAccepted(value)

    assert(spec.assertNextValueAcceptedByThis(k))
    assert(spec.accepts(value))
    assert(spec.assertIndexOfAcceptedAtMost(value, steps))
    assert(oldIndex <= steps)
    assert(value >= spec.next.head.value)
    assert(spec.next.head.value > spec.head.value)
    assert(value > spec.head.value)
    if (oldIndex == BigInt(0)) {
      assert(spec(oldIndex) == spec.head.value)
      assert(spec(oldIndex) == value)
      assert(value == spec.head.value)
      assert(false)
    }
    assert(oldIndex > BigInt(0))
    assert(assertSpecNextValueAppearsInRepeatedExtendedWindowSurvivors(k))

    survivors.contains(value)
  }.holds

  def assertRepeatedIntegralSkippedRangeBetweenSpecNextValuesAllMultiples(
    k: BigInt,
    fromPos: BigInt,
    untilPos: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(fromPos >= BigInt(0))
    require(untilPos >= fromPos)

    val repeated = repeatedCycle(spec.head.value)
    val currentValue = spec.next(k)
    val nextValue = spec.next(k + BigInt(1))
    val currentOldIndex = spec.indexOfAccepted(currentValue)
    val nextOldIndex = spec.indexOfAccepted(nextValue)

    require(nextOldIndex > currentOldIndex)
    require(fromPos >= currentOldIndex)
    require(untilPos <= nextOldIndex - BigInt(1))
    decreases(untilPos - fromPos)

    assert(spec.assertNextValueAcceptedByThis(k))
    assert(spec.assertNextValueAcceptedByThis(k + BigInt(1)))

    if (fromPos == untilPos) {
      GapProperties.allMultiplesInRange(
        repeated.integral,
        spec.head.value,
        fromPos,
        untilPos
      )
    } else {
      val oldIndex = fromPos + BigInt(1)

      assert(fromPos < untilPos)
      assert(fromPos <= untilPos - BigInt(1))
      assert(untilPos - BigInt(1) <= nextOldIndex - BigInt(2))
      assert(fromPos <= nextOldIndex - BigInt(2))
      assert(oldIndex < nextOldIndex)
      assert(oldIndex > currentOldIndex)
      assert(spec(currentOldIndex) == currentValue)
      assert(spec(nextOldIndex) == nextValue)
      assert(spec.assertApplyStrictlyIncreasesBetween(currentOldIndex, oldIndex))
      assert(spec(currentOldIndex) < spec(oldIndex))
      assert(spec.assertApplyStrictlyIncreasesBetween(oldIndex, nextOldIndex))
      assert(spec(oldIndex) < spec(nextOldIndex))
      assert(spec.assertOldGeneratedValueBetweenNextValuesIsHeadMultiple(k, oldIndex))
      assert(Calc.mod(spec(oldIndex), spec.head.value) == BigInt(0))
      assert(assertRepeatedIntegralMatchesShiftedSpec(fromPos))
      assert(repeated.integral(fromPos) == spec(oldIndex))
      assert(Calc.mod(repeated.integral(fromPos), spec.head.value) == BigInt(0))
      assert(assertRepeatedIntegralSkippedRangeBetweenSpecNextValuesAllMultiples(
        k,
        fromPos + BigInt(1),
        untilPos
      ))
      assert(GapProperties.allMultiplesInRange(
        repeated.integral,
        spec.head.value,
        fromPos + BigInt(1),
        untilPos
      ))

      GapProperties.allMultiplesInRange(
        repeated.integral,
        spec.head.value,
        fromPos,
        untilPos
      )
    }
  }.holds

  def assertRepeatedExtendedWindowTailHeadMatchesSpecNextSuccessor(k: BigInt): Boolean = {
    require(k >= BigInt(0))

    val repeated = repeatedCycle(spec.head.value)
    val steps = period * spec.head.value + BigInt(1)
    val currentValue = spec.next(k)
    val nextValue = spec.next(k + BigInt(1))
    val currentOldIndex = spec.indexOfAccepted(currentValue)
    val nextOldIndex = spec.indexOfAccepted(nextValue)

    require(nextOldIndex <= steps)

    assert(spec.next.applyStrictlyIncreases(k))
    assert(currentValue < nextValue)
    assert(spec.assertNextValueAcceptedByThis(k))
    assert(spec.assertNextValueAcceptedByThis(k + BigInt(1)))
    assert(spec.accepts(currentValue))
    assert(spec.accepts(nextValue))
    assert(spec.assertIndexOfAcceptedStrictlyIncreasesForAcceptedValues(
      currentValue,
      nextValue
    ))
    assert(nextOldIndex > currentOldIndex)

    val count = steps - currentOldIndex
    val position = nextOldIndex - BigInt(1)
    val survivors = CycleIntegralFilterProperties.survivorValues(
      repeated.integral,
      spec.head.value,
      currentOldIndex,
      count
    )

    assert(spec.head.value > BigInt(0))
    assert(count > BigInt(0))
    assert(position >= currentOldIndex)
    assert(position < currentOldIndex + count)
    assert(assertRepeatedIntegralSkippedRangeBetweenSpecNextValuesAllMultiples(
      k,
      currentOldIndex,
      position
    ))
    assert(GapProperties.allMultiplesInRange(
      repeated.integral,
      spec.head.value,
      currentOldIndex,
      position
    ))
    assert(spec.assertNextValueAcceptedByThis(k + BigInt(1)))
    assert(spec.accepts(nextValue))
    assert(spec(nextOldIndex) == nextValue)
    assert(assertRepeatedIntegralMatchesShiftedSpec(position))
    assert(repeated.integral(position) == spec(position + BigInt(1)))
    assert(position + BigInt(1) == nextOldIndex)
    assert(repeated.integral(position) == nextValue)
    assert(spec.next.accepts(nextValue))
    assert(nextValue >= spec.next.head.value)
    assert(spec.assertNextAcceptsMatchesHeadFilterForAcceptedValue(nextValue))
    assert(spec.next.accepts(nextValue) ==
      (Calc.mod(nextValue, spec.head.value) != BigInt(0)))
    assert(Calc.mod(nextValue, spec.head.value) != BigInt(0))
    assert(Calc.mod(repeated.integral(position), spec.head.value) != BigInt(0))
    assert(GapProperties.assertFirstSurvivorAtPosition(
      repeated.integral,
      spec.head.value,
      currentOldIndex,
      count,
      position
    ))

    survivors.head == spec.next(k + BigInt(1))
  }.holds

  def assertRepeatedExtendedWindowTailHeadMatchesSpecNextSuccessorFromValueBound(k: BigInt): Boolean = {
    require(k >= BigInt(0))

    val repeated = repeatedCycle(spec.head.value)
    val steps = period * spec.head.value + BigInt(1)
    val currentValue = spec.next(k)
    val nextValue = spec.next(k + BigInt(1))
    val currentOldIndex = spec.indexOfAccepted(currentValue)
    val nextOldIndex = spec.indexOfAccepted(nextValue)

    require(nextValue <= spec(steps))

    assert(spec.next.applyStrictlyIncreases(k))
    assert(currentValue < nextValue)
    assert(currentValue <= spec(steps))
    assert(spec.assertNextValueAcceptedByThis(k))
    assert(spec.assertNextValueAcceptedByThis(k + BigInt(1)))
    assert(spec.accepts(currentValue))
    assert(spec.accepts(nextValue))
    assert(spec.assertIndexOfAcceptedAtMost(currentValue, steps))
    assert(spec.assertIndexOfAcceptedAtMost(nextValue, steps))
    assert(currentOldIndex <= steps)
    assert(nextOldIndex <= steps)
    assert(assertRepeatedExtendedWindowTailHeadMatchesSpecNextSuccessor(k))

    val count = steps - currentOldIndex
    val survivors = CycleIntegralFilterProperties.survivorValues(
      repeated.integral,
      spec.head.value,
      currentOldIndex,
      count
    )

    survivors.head == spec.next(k + BigInt(1))
  }.holds

  def assertSpecHeadRejectedByHeadFilter(): Boolean = {
    assert(spec.head.value > BigInt(0))
    assert(AdditionAndMultiplication.ATimesBSameMod(BigInt(0), spec.head.value, BigInt(1)))
    assert(Calc.mod(spec.head.value, spec.head.value) == BigInt(0))

    Calc.mod(spec.head.value, spec.head.value) == BigInt(0)
  }.holds

  def assertRepeatedCycleFullFirstExpandedEndpointRejected(): Boolean = {
    val count = period * spec.head.value
    val index = count - BigInt(1)
    val repeated = repeatedCycle(spec.head.value)
    val value = repeated.integral(index)

    assert(spec.head.value > BigInt(0))
    assert(count > BigInt(0))
    assert(index >= BigInt(0))
    assert(spec.assertBlockShiftMultiple(BigInt(0), spec.head.value, period))
    assert(spec(count) == spec.head.value + spec.head.value * spec.tailPrimorial)
    assert(assertRepeatedCycleNextAcceptsMatchesHeadFilterFullFirstExpandedPeriod())
    assert(assertRepeatedCycleApplyMatches(spec.head.value, count))
    assert(assertApplyMatches(count))
    assert(repeated(count) == repeated.integral(index))
    assert(repeated(count) == cycle(count))
    assert(cycle(count) == spec(count))
    assert(value == spec.head.value + spec.head.value * spec.tailPrimorial)
    assert(AdditionAndMultiplication.ATimesBSameMod(BigInt(0), spec.head.value, BigInt(1) + spec.tailPrimorial))
    assert(Calc.mod(spec.head.value * (BigInt(1) + spec.tailPrimorial), spec.head.value) == BigInt(0))
    assert(value == spec.head.value * (BigInt(1) + spec.tailPrimorial))
    assert(Calc.mod(value, spec.head.value) == BigInt(0))
    assert(spec.next.accepts(value) == (Calc.mod(value, spec.head.value) != BigInt(0)))

    !spec.next.accepts(value)
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
