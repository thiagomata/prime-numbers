package v1.chapter6.seq.sieve.properties

import stainless.lang.{BigInt, BooleanDecorations}
import v1.chapter4.cycle.gap.GapCycle
import v1.chapter4.cycle.integral.recursive.CycleIntegral
import v1.chapter4.cycle.integral.recursive.properties.CycleIntegralFilterProperties
import v1.chapter5.prime.PrimeUtils
import v1.chapter6.seq.sieve.{CycleSieveSequence, SpecDerivedSieveSequence}

object SpecDerivedRebuiltCycleProperties {

  /**
   * Proves the base rebuilt-integral value matches `spec.next(1)`.
   *
   * If `newCI` starts at the extended survivor head and stores
   * `gapsFromValues(survivors)`, then its position `0` reconstructs the second
   * survivor, which is `spec.next(1)` under the first-gap prefix bridge.
   */
  def assertRepeatedExtendedWindowFilteredCIPositionZeroMatchesSpecNextFromValueBound(
    derived: SpecDerivedSieveSequence,
    newCI: CycleIntegral
  ): Boolean = {
    val spec = derived.spec
    val period = derived.period
    require(spec.next(BigInt(1)) <= spec(period * spec.head.value + BigInt(1)))

    val repeated = derived.repeatedCycle(spec.head.value)
    val steps = period * spec.head.value + BigInt(1)
    val survivors = CycleIntegralFilterProperties.survivorValues(
      repeated.integral,
      spec.head.value,
      BigInt(0),
      steps
    )

    require(!survivors.isEmpty)
    require(survivors.size > BigInt(1))
    require(newCI.period > BigInt(0))
    require(newCI.initialValue == survivors.head)
    require(newCI.cycle.values == CycleIntegralFilterProperties.gapsFromValues(survivors))

    assert(SpecDerivedExtendedWindowProperties.assertRepeatedExtendedWindowFirstGapPrefixFromValueBound(derived))
    assert(SpecDerivedExtendedWindowProperties.repeatedExtendedWindowGapsMatchSpecNextPrefix(derived, BigInt(1)))
    assert(BigInt(0) < newCI.period)
    assert(SpecDerivedRebuiltCycleProperties.assertRepeatedExtendedWindowFilteredCIMatchesSpecNextFromGapPrefix(derived, 
      newCI,
      BigInt(0)
    ))

    newCI(BigInt(0)) == spec.next(BigInt(1))
  }.holds

  /**
   * Proves the base rebuilt-integral value for a supplied gap cycle.
   *
   * A `GapCycle` whose memory values are the extended survivor gaps induces a
   * `CycleIntegral` starting at `spec.next.head.value`; this lemma proves that
   * integral's position `0` is `spec.next(1)`.
   */
  def assertRepeatedExtendedWindowGapCycleIntegralPositionZeroMatchesSpecNextFromValueBound(
    derived: SpecDerivedSieveSequence,
    newGapCycle: GapCycle
  ): Boolean = {
    val spec = derived.spec
    val period = derived.period
    require(spec.next(BigInt(1)) <= spec(period * spec.head.value + BigInt(1)))

    val repeated = derived.repeatedCycle(spec.head.value)
    val steps = period * spec.head.value + BigInt(1)
    val survivors = CycleIntegralFilterProperties.survivorValues(
      repeated.integral,
      spec.head.value,
      BigInt(0),
      steps
    )

    require(!survivors.isEmpty)
    require(survivors.size > BigInt(1))
    require(newGapCycle.memCycle.values == CycleIntegralFilterProperties.gapsFromValues(survivors))

    val newCI = CycleIntegral(spec.next.head.value, newGapCycle.memCycle)

    assert(SpecDerivedExtendedWindowProperties.assertRepeatedExtendedWindowSurvivorsHeadMatchesSpecNext(derived))
    assert(survivors.head == spec.next.head.value)
    assert(newCI.initialValue == survivors.head)
    assert(newCI.cycle.values == CycleIntegralFilterProperties.gapsFromValues(survivors))
    assert(GapCycle.assertMemCyclePeriodPositive(newGapCycle))
    assert(newCI.period > BigInt(0))
    assert(assertRepeatedExtendedWindowFilteredCIPositionZeroMatchesSpecNextFromValueBound(
      derived,
      newCI
    ))

    newCI(BigInt(0)) == spec.next(BigInt(1))
  }.holds

  /**
   * Proves the concrete rebuilt next cycle matches `spec.next(1)`.
   *
   * When the supplied gap cycle stores the extended survivor gaps, the
   * `CycleSieveSequence` built with `spec.primes.next` has its position `1`
   * equal to the next spec sequence at position `1`.
   */
  def assertRepeatedExtendedWindowCyclePositionOneMatchesSpecNextFromValueBound(
    derived: SpecDerivedSieveSequence,
    newGapCycle: GapCycle
  ): Boolean = {
    val spec = derived.spec
    val period = derived.period
    require(spec.next(BigInt(1)) <= spec(period * spec.head.value + BigInt(1)))

    val repeated = derived.repeatedCycle(spec.head.value)
    val steps = period * spec.head.value + BigInt(1)
    val survivors = CycleIntegralFilterProperties.survivorValues(
      repeated.integral,
      spec.head.value,
      BigInt(0),
      steps
    )

    require(!survivors.isEmpty)
    require(survivors.size > BigInt(1))
    require(newGapCycle.memCycle.values == CycleIntegralFilterProperties.gapsFromValues(survivors))

    assert(PrimeUtils.primorialPositive(spec.primes.next.list.tail.list))
    val nextCycle = CycleSieveSequence(spec.primes.next, newGapCycle)

    assert(spec.next.primes == spec.primes.next)
    assert(nextCycle.head == spec.next.head.value)
    assert(nextCycle.integral.initialValue == spec.next.head.value)
    assert(nextCycle.integral.cycle == newGapCycle.memCycle)
    assert(assertRepeatedExtendedWindowGapCycleIntegralPositionZeroMatchesSpecNextFromValueBound(
      derived,
      newGapCycle
    ))
    assert(nextCycle.integral(BigInt(0)) == spec.next(BigInt(1)))

    nextCycle(BigInt(1)) == spec.next(BigInt(1))
  }.holds

  /**
   * Proves a rebuilt integral matches first-window survivor values.
   *
   * If `newCI` is built from the first-window survivor head and
   * `gapsFromValues(survivors)`, then `newCI(position)` reconstructs
   * `survivors(position + 1)`.
   */
  def assertRepeatedFirstWindowFilteredCIMatchesSurvivors(
    derived: SpecDerivedSieveSequence,
    newCI: CycleIntegral,
    position: BigInt
  ): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    require(position >= BigInt(0))

    val repeated = derived.repeatedCycle(spec.head.value)
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


  /**
   * Proves a rebuilt integral matches extended-window survivor values.
   *
   * This is the extended-window version of the generic reconstruction fact:
   * `newCI(position) == survivors(position + 1)` for the survivor list built
   * from the `period * head + 1` scan.
   */
  def assertRepeatedExtendedWindowFilteredCIMatchesSurvivors(
    derived: SpecDerivedSieveSequence,
    newCI: CycleIntegral,
    position: BigInt
  ): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    require(position >= BigInt(0))

    val repeated = derived.repeatedCycle(spec.head.value)
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


  /**
   * Proves a rebuilt integral value matches the next spec value by gap prefix.
   *
   * If the rebuilt integral uses the extended survivor gaps, and those gaps match
   * the `spec.next` gap prefix through `position + 1`, then
   * `newCI(position) == spec.next(position + 1)`.
   */
  def assertRepeatedExtendedWindowFilteredCIMatchesSpecNextFromGapPrefix(
    derived: SpecDerivedSieveSequence,
    newCI: CycleIntegral,
    position: BigInt
  ): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    require(position >= BigInt(0))

    val repeated = derived.repeatedCycle(spec.head.value)
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
    require(SpecDerivedExtendedWindowProperties.repeatedExtendedWindowGapsMatchSpecNextPrefix(derived, count))

    assert(SpecDerivedRebuiltCycleProperties.assertRepeatedExtendedWindowFilteredCIMatchesSurvivors(derived, 
      newCI,
      position
    ))
    assert(newCI(position) == survivors(count))
    assert(SpecDerivedExtendedWindowProperties.assertRepeatedExtendedWindowValuesMatchSpecNextFromGapPrefix(derived, count))
    assert(survivors(count) == spec.next(count))

    newCI(position) == spec.next(position + BigInt(1))
  }.holds
}
