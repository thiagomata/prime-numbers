package v1.chapter6.seq.sieve.properties

import stainless.lang.{BigInt, BooleanDecorations, decreases}
import v1.chapter2.div.Calc
import v1.chapter3.list.properties.ListRepeatProperties
import v1.chapter4.cycle.gap.GapCycle
import v1.chapter4.cycle.integral.recursive.properties.{CycleIntegralFilterProperties, CycleIntegralProperties, GapProperties, RepeatedGapIntegralProperties}
import v1.chapter4.cycle.memory.properties.MemCycleProperties
import v1.chapter6.seq.sieve.SpecDerivedSieveSequence

object SpecDerivedRepeatedCycleProperties {


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
  def assertRepeatedGapListIndexMatches(derived: SpecDerivedSieveSequence, times: BigInt, index: BigInt): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

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
   *   B_t    = derived.repeatedCycle(times)
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
  def assertRepeatedCycleGapMatches(derived: SpecDerivedSieveSequence, times: BigInt, position: BigInt): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    require(times > BigInt(0))
    require(position >= BigInt(0))

    val gaps = cycle.gapCycle.memCycle.values
    val repeated = derived.repeatedCycle(times)
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
   *   B_t = derived.repeatedCycle(times)
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
  def assertRepeatedCycleIntegralMatches(derived: SpecDerivedSieveSequence, times: BigInt, position: BigInt): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    require(times > BigInt(0))
    require(position >= BigInt(0))

    val gaps = cycle.gapCycle.memCycle.values
    val repeated = derived.repeatedCycle(times)
    val repeatedGaps = ListRepeatProperties.repeat(gaps, times)

    assert(GapCycle.assertMemCycleValuesPositive(cycle.gapCycle))
    assert(gaps.size > BigInt(0))
    assert(ListRepeatProperties.assertRepeatSize(gaps, times))
    assert(repeated.gapCycle.memCycle.values == repeatedGaps)
    assert(repeated.integral.initialValue == cycle.integral.initialValue)
    assert(RepeatedGapIntegralProperties.assertRepeatedValuesIntegralMatches(
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
   *   B_t = derived.repeatedCycle(times)
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
   *   derived.repeatedCycle(times)(k) = cycle(k)
   *
   * This is the semantic version of the repeated-storage fact: repeating a
   * physical gap period changes the memory representation only, not the
   * generated sequence.
   */
  def assertRepeatedCycleApplyMatches(derived: SpecDerivedSieveSequence, times: BigInt, k: BigInt): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    require(times > BigInt(0))
    require(k >= BigInt(0))

    val repeated = derived.repeatedCycle(times)

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
      assert(SpecDerivedRepeatedCycleProperties.assertRepeatedCycleIntegralMatches(derived, times, previousPosition))
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


  /**
   * Defines bounded prefix equality between a repeated cycle and the spec.
   *
   * For `count` entries, every index below `count` is required to satisfy
   * `derived.repeatedCycle(times)(index) == spec(index)`.
   */
  def repeatedCycleMatchesSpecPrefix(derived: SpecDerivedSieveSequence, times: BigInt, count: BigInt): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    require(times > BigInt(0))
    require(count >= BigInt(0))
    decreases(count)

    if (count == BigInt(0)) {
      true
    } else {
      val index = count - BigInt(1)
      SpecDerivedRepeatedCycleProperties.repeatedCycleMatchesSpecPrefix(derived, times, index) &&
        derived.repeatedCycle(times)(index) == spec(index)
    }
  }


  /**
   * Proves the bounded prefix predicate for a repeated cycle.
   *
   * The proof combines repeated-cycle apply equality with the core
   * `cycle(index) == spec(index)` fact, then recurses over the prefix length.
   */
  def assertRepeatedCycleMatchesSpecPrefix(derived: SpecDerivedSieveSequence, times: BigInt, count: BigInt): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    require(times > BigInt(0))
    require(count >= BigInt(0))
    decreases(count)

    if (count == BigInt(0)) {
      SpecDerivedRepeatedCycleProperties.repeatedCycleMatchesSpecPrefix(derived, times, count)
    } else {
      val index = count - BigInt(1)
      assert(index >= BigInt(0))
      assert(SpecDerivedRepeatedCycleProperties.assertRepeatedCycleMatchesSpecPrefix(derived, times, index))
      assert(SpecDerivedRepeatedCycleProperties.repeatedCycleMatchesSpecPrefix(derived, times, index))
      assert(SpecDerivedRepeatedCycleProperties.assertRepeatedCycleApplyMatches(derived, times, index))
      assert(SpecDerivedCoreProperties.assertApplyMatches(derived, index))
      assert(derived.repeatedCycle(times)(index) == cycle(index))
      assert(cycle(index) == spec(index))
      assert(derived.repeatedCycle(times)(index) == spec(index))

      SpecDerivedRepeatedCycleProperties.repeatedCycleMatchesSpecPrefix(derived, times, count)
    }
  }.holds


  /**
   * Defines the first expanded-period prefix predicate for `times == head`.
   *
   * The prefix length is `period * spec.head.value`, which is the scan length
   * used before applying the current head filter.
   */
  def repeatedCycleMatchesSpecFirstExpandedPeriod(derived: SpecDerivedSieveSequence): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    val count = period * spec.head.value
    SpecDerivedRepeatedCycleProperties.repeatedCycleMatchesSpecPrefix(derived, spec.head.value, count)
  }


  /**
   * Proves repeated-cycle/spec equality over the first expanded period.
   *
   * This packages the prefix proof at `times == head` and
   * `count == period * head`.
   */
  def assertRepeatedCycleMatchesSpecFirstExpandedPeriod(derived: SpecDerivedSieveSequence): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    val count = period * spec.head.value

    assert(spec.head.value > BigInt(0))
    assert(count >= BigInt(0))
    assert(SpecDerivedRepeatedCycleProperties.assertRepeatedCycleMatchesSpecPrefix(derived, spec.head.value, count))

    SpecDerivedRepeatedCycleProperties.repeatedCycleMatchesSpecFirstExpandedPeriod(derived)
  }.holds


  /**
   * Proves the shifted relation between repeated integral values and the spec.
   *
   * Since `apply(0)` is the current head, the integral value at `index` matches
   * the sequence value at `index + 1`: `repeated.integral(index) == spec(index + 1)`.
   */
  def assertRepeatedIntegralMatchesShiftedSpec(derived: SpecDerivedSieveSequence, index: BigInt): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    require(index >= BigInt(0))

    val repeated = derived.repeatedCycle(spec.head.value)
    val specIndex = index + BigInt(1)

    assert(spec.head.value > BigInt(0))
    assert(specIndex >= BigInt(1))
    assert(SpecDerivedRepeatedCycleProperties.assertRepeatedCycleApplyMatches(derived, spec.head.value, specIndex))
    assert(SpecDerivedCoreProperties.assertApplyMatches(derived, specIndex))
    assert(repeated(specIndex) == repeated.integral(index))
    assert(repeated(specIndex) == cycle(specIndex))
    assert(cycle(specIndex) == spec(specIndex))

    repeated.integral(index) == spec(index + BigInt(1))
  }.holds


  /**
   * Proves next-acceptance matches the current head filter on a bounded window.
   *
   * For every repeated integral value before `count`, `spec.next.accepts(value)`
   * is equivalent to `mod(value, spec.head.value) != 0`.
   */
  def assertRepeatedCycleNextAcceptsMatchesHeadFilterFirstExpandedPeriod(derived: SpecDerivedSieveSequence, count: BigInt): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    require(count >= BigInt(0))
    require(count <= period * spec.head.value)
    decreases(count)

    if (count == BigInt(0)) {
      true
    } else {
      val index = count - BigInt(1)
      val specIndex = index + BigInt(1)
      val repeated = derived.repeatedCycle(spec.head.value)
      val value = repeated.integral(index)

      assert(index >= BigInt(0))
      assert(specIndex >= BigInt(1))
      assert(SpecDerivedRepeatedCycleProperties.assertRepeatedCycleNextAcceptsMatchesHeadFilterFirstExpandedPeriod(derived, index))
      assert(SpecDerivedRepeatedCycleProperties.assertRepeatedCycleApplyMatches(derived, spec.head.value, specIndex))
      assert(SpecDerivedCoreProperties.assertApplyMatches(derived, specIndex))
      assert(repeated(specIndex) == repeated.integral(index))
      assert(repeated(specIndex) == cycle(specIndex))
      assert(cycle(specIndex) == spec(specIndex))
      assert(value == spec(specIndex))
      assert(SpecDerivedCoreProperties.assertNextHeadMatches(derived))
      assert(SpecDerivedCoreProperties.assertApplyMatches(derived, BigInt(1)))
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


  /**
   * Proves the head-filter acceptance bridge for the full first expanded window.
   *
   * This instantiates the bounded bridge at `count == period * head`.
   */
  def assertRepeatedCycleNextAcceptsMatchesHeadFilterFullFirstExpandedPeriod(derived: SpecDerivedSieveSequence): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    val count = period * spec.head.value

    assert(spec.head.value > BigInt(0))
    assert(count >= BigInt(0))
    assert(SpecDerivedRepeatedCycleProperties.assertRepeatedCycleNextAcceptsMatchesHeadFilterFirstExpandedPeriod(derived, count))

    true
  }.holds


  /**
   * Proves that the repeated integral scan starts at the next spec head.
   *
   * The first integral value of `derived.repeatedCycle(head)` is the same as
   * `cycle(1)`, which the core lemma identifies with `spec.next(0)`.
   */
  def assertRepeatedFirstWindowStartsAtSpecNextHead(derived: SpecDerivedSieveSequence): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    val repeated = derived.repeatedCycle(spec.head.value)
    val value = repeated.integral(BigInt(0))

    assert(spec.head.value > BigInt(0))
    assert(SpecDerivedRepeatedCycleProperties.assertRepeatedCycleApplyMatches(derived, spec.head.value, BigInt(1)))
    assert(SpecDerivedCoreProperties.assertNextHeadMatches(derived))
    assert(repeated(BigInt(1)) == repeated.integral(BigInt(0)))
    assert(repeated(BigInt(1)) == cycle(BigInt(1)))
    assert(cycle(BigInt(1)) == spec.next.head.value)
    assert(spec.next(BigInt(0)) == spec.next.head.value)
    assert(value == spec.next(BigInt(0)))
    assert(spec.assertNextValueAcceptedByThis(BigInt(0)))

    value == spec.next(BigInt(0)) &&
      Calc.mod(value, spec.head.value) != BigInt(0)
  }.holds


  /**
   * Proves that the first filtered survivor in the first scan window is
   * `spec.next(0)`.
   *
   * The first repeated integral value is the next head and it is not divisible by
   * the current head, so `survivorValues` keeps it as the survivor-list head.
   */
  def assertRepeatedFirstWindowSurvivorsHeadMatchesSpecNext(derived: SpecDerivedSieveSequence): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    val repeated = derived.repeatedCycle(spec.head.value)
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
    assert(SpecDerivedRepeatedCycleProperties.assertRepeatedFirstWindowStartsAtSpecNextHead(derived))
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
}
