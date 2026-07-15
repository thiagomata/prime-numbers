package v1.chapter6.seq.sieve.properties

import stainless.collection.List
import stainless.lang.{BigInt, BooleanDecorations, decreases}
import v1.chapter2.div.Calc
import v1.chapter3.list.properties.ListUtilsProperties
import v1.chapter4.cycle.integral.recursive.properties.{
  CycleIntegralFilterProperties,
  GapProperties
}
import v1.chapter6.seq.sieve.SpecDerivedSieveSequence

object SpecDerivedExtendedWindowProperties {

  /**
   * Proves that `spec.next(0)` has old accepted index `1`.
   *
   * The next head is the same value as `spec(1)`, so its accepted-index witness
   * in the old spec stream is exactly `1`.
   */
  def assertSpecNextHeadOldIndexIsOne(
    derived: SpecDerivedSieveSequence
  ): Boolean = {
    val spec = derived.spec
    val value = spec.next(BigInt(0))
    val oldIndex = spec.indexOfAccepted(value)

    assert(spec.next(BigInt(0)) == spec.next.head.value)
    assert(spec.next.head.value == spec.primes.nextPrime.value)
    assert(spec.assertApplyOneEqualsNextPrime())
    assert(spec(BigInt(1)) == spec.primes.nextPrime.value)
    assert(spec(BigInt(1)) == value)
    assert(spec.assertNextValueAcceptedByThis(BigInt(0)))
    assert(spec.accepts(value))
    assert(spec(oldIndex) == value)
    assert(spec(oldIndex) == spec(BigInt(1)))
    assert(spec.assertApplyInjective(oldIndex, BigInt(1)))

    oldIndex == BigInt(1)
  }.holds

  /**
   * Splits the extended survivor list at the next head.
   *
   * The first extended survivor is `spec.next(0)`, and the remaining list is the
   * survivor scan that starts at old accepted index `1`.
   */
  def assertRepeatedExtendedWindowSurvivorsSplitAtSpecNextHead(
    derived: SpecDerivedSieveSequence
  ): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val repeated = derived.repeatedCycle(spec.head.value)
    val steps = period * spec.head.value + BigInt(1)
    val survivors = CycleIntegralFilterProperties.survivorValues(
      repeated.integral,
      spec.head.value,
      BigInt(0),
      steps
    )
    val oldIndex = spec.indexOfAccepted(spec.next(BigInt(0)))

    assert(spec.head.value > BigInt(0))
    assert(period > BigInt(0))
    assert(steps > BigInt(0))
    assert(assertSpecNextHeadOldIndexIsOne(derived))
    assert(oldIndex == BigInt(1))
    assert(steps - oldIndex == steps - BigInt(1))
    val afterHead = CycleIntegralFilterProperties.survivorValues(
      repeated.integral,
      spec.head.value,
      BigInt(1),
      steps - BigInt(1)
    )

    assert(SpecDerivedRepeatedCycleProperties.assertRepeatedFirstWindowStartsAtSpecNextHead(derived))
    assert(repeated.integral(BigInt(0)) == spec.next(BigInt(0)))
    assert(Calc.mod(repeated.integral(BigInt(0)), spec.head.value) != BigInt(0))
    assert(GapProperties.allMultiplesInRange(
      repeated.integral,
      spec.head.value,
      BigInt(0),
      BigInt(0)
    ))
    assert(GapProperties.assertSurvivorValuesSplitAtFirstPosition(
      repeated.integral,
      spec.head.value,
      BigInt(0),
      steps,
      BigInt(0)
    ))

    survivors == spec.next(BigInt(0)) :: afterHead
  }.holds

  /**
   * Proves that the extended survivor tail is the first old-index tail scan.
   *
   * After splitting the full survivor list as `spec.next(0) :: firstTail`, the
   * normal list tail is exactly `firstTail`.
   */
  def assertRepeatedExtendedWindowSurvivorsTailIsFirstTail(
    derived: SpecDerivedSieveSequence
  ): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val repeated = derived.repeatedCycle(spec.head.value)
    val steps = period * spec.head.value + BigInt(1)
    val survivors = CycleIntegralFilterProperties.survivorValues(
      repeated.integral,
      spec.head.value,
      BigInt(0),
      steps
    )
    val firstTail = CycleIntegralFilterProperties.survivorValues(
      repeated.integral,
      spec.head.value,
      BigInt(1),
      steps - BigInt(1)
    )

    assert(assertRepeatedExtendedWindowSurvivorsSplitAtSpecNextHead(derived))
    assert(survivors == spec.next(BigInt(0)) :: firstTail)

    survivors.tail == firstTail
  }.holds

  /**
   * Splits the filtered tail scan at `spec.next(k + 1)`.
   *
   * Under the extended endpoint bound, every old generated value between
   * `spec.next(k)` and `spec.next(k + 1)` is removed by the current head filter,
   * so the tail survivor scan begins with `spec.next(k + 1)`.
   */
  def assertRepeatedExtendedWindowTailSplitsAtSpecNextSuccessorFromValueBound(
    derived: SpecDerivedSieveSequence,
    k: BigInt
  ): Boolean = {
    val spec = derived.spec
    val period = derived.period
    require(k >= BigInt(0))
    require(spec.next(k + BigInt(1)) <= spec(period * spec.head.value + BigInt(1)))

    val repeated = derived.repeatedCycle(spec.head.value)
    val steps = period * spec.head.value + BigInt(1)
    val currentValue = spec.next(k)
    val nextValue = spec.next(k + BigInt(1))

    assert(nextValue <= spec(steps))
    assert(spec.next.applyStrictlyIncreases(k))
    assert(currentValue < nextValue)
    assert(spec.assertNextValueAcceptedByThis(k))
    assert(spec.assertNextValueAcceptedByThis(k + BigInt(1)))
    assert(spec.accepts(currentValue))
    assert(spec.accepts(nextValue))

    val currentOldIndex = spec.indexOfAccepted(currentValue)
    val nextOldIndex = spec.indexOfAccepted(nextValue)

    assert(spec.assertIndexOfAcceptedAtMost(nextValue, steps))
    assert(nextOldIndex <= steps)
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
    val afterNext = CycleIntegralFilterProperties.survivorValues(
      repeated.integral,
      spec.head.value,
      nextOldIndex,
      steps - nextOldIndex
    )

    assert(spec.head.value > BigInt(0))
    assert(count > BigInt(0))
    assert(position >= currentOldIndex)
    assert(position < currentOldIndex + count)
    assert(currentOldIndex + count - position - BigInt(1) ==
      steps - nextOldIndex)
    assert(SpecDerivedExtendedWindowProperties.assertRepeatedIntegralSkippedRangeBetweenSpecNextValuesAllMultiples(derived,
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
    assert(spec(nextOldIndex) == nextValue)
    assert(SpecDerivedRepeatedCycleProperties.assertRepeatedIntegralMatchesShiftedSpec(derived, position))
    assert(repeated.integral(position) == spec(position + BigInt(1)))
    assert(position + BigInt(1) == nextOldIndex)
    assert(repeated.integral(position) == nextValue)
    assert(spec.next.accepts(nextValue))
    assert(nextValue >= spec.next.head.value)
    assert(spec.assertNextAcceptsMatchesHeadFilterForAcceptedValue(nextValue))
    assert(Calc.mod(nextValue, spec.head.value) != BigInt(0))
    assert(Calc.mod(repeated.integral(position), spec.head.value) != BigInt(0))
    assert(GapProperties.assertSurvivorValuesSplitAtFirstPosition(
      repeated.integral,
      spec.head.value,
      currentOldIndex,
      count,
      position
    ))

    survivors == spec.next(k + BigInt(1)) :: afterNext
  }.holds

  /**
   * Proves the list-index shift after a cons split.
   *
   * If `tailSurvivors == nextValue :: afterNext`, then the value one position
   * after the head in `tailSurvivors` equals `afterNext(index)`.
   */
  def assertTailValueFollowsConsSplit(
    tailSurvivors: List[BigInt],
    nextValue: BigInt,
    afterNext: List[BigInt],
    index: BigInt
  ): Boolean = {
    require(index >= BigInt(0))
    require(index < afterNext.size)
    require(tailSurvivors == nextValue :: afterNext)

    assert(tailSurvivors.tail == afterNext)
    assert(index < tailSurvivors.tail.size)
    assert(ListUtilsProperties.accessTailShiftRight(tailSurvivors, index))

    tailSurvivors(index + BigInt(1)) == afterNext(index)
  }.holds

  /**
   * Applies the cons-split index shift to the extended survivor tail.
   *
   * Once the tail scan after `spec.next(k)` is split at `spec.next(k + 1)`, this
   * lemma relates `tailSurvivors(index + 1)` to the peeled `afterNext(index)`.
   */
  def assertRepeatedExtendedWindowTailValueFollowsSplitFromValueBound(
    derived: SpecDerivedSieveSequence,
    k: BigInt,
    index: BigInt
  ): Boolean = {
    val spec = derived.spec
    val period = derived.period
    require(k >= BigInt(0))
    require(index >= BigInt(0))
    require(spec.next(k + BigInt(1)) <= spec(period * spec.head.value + BigInt(1)))

    val repeated = derived.repeatedCycle(spec.head.value)
    val steps = period * spec.head.value + BigInt(1)
    val currentValue = spec.next(k)
    val nextValue = spec.next(k + BigInt(1))

    assert(nextValue <= spec(steps))
    assert(spec.next.applyStrictlyIncreases(k))
    assert(currentValue < nextValue)
    assert(spec.assertNextValueAcceptedByThis(k))
    assert(spec.assertNextValueAcceptedByThis(k + BigInt(1)))
    assert(spec.accepts(currentValue))
    assert(spec.accepts(nextValue))

    val currentOldIndex = spec.indexOfAccepted(currentValue)
    val nextOldIndex = spec.indexOfAccepted(nextValue)

    assert(spec.assertIndexOfAcceptedAtMost(nextValue, steps))
    assert(nextOldIndex <= steps)
    assert(spec.assertIndexOfAcceptedStrictlyIncreasesForAcceptedValues(
      currentValue,
      nextValue
    ))
    assert(nextOldIndex > currentOldIndex)

    val count = steps - currentOldIndex
    val tailSurvivors = CycleIntegralFilterProperties.survivorValues(
      repeated.integral,
      spec.head.value,
      currentOldIndex,
      count
    )
    val afterNext = CycleIntegralFilterProperties.survivorValues(
      repeated.integral,
      spec.head.value,
      nextOldIndex,
      steps - nextOldIndex
    )

    if (index < afterNext.size) {
      assert(assertRepeatedExtendedWindowTailSplitsAtSpecNextSuccessorFromValueBound(derived, k))
      assert(tailSurvivors == nextValue :: afterNext)
      assertTailValueFollowsConsSplit(
        tailSurvivors,
        nextValue,
        afterNext,
        index
      )
    } else {
      true
    }
  }.holds

  /**
   * Proves the second extended survivor equals `spec.next(1)`.
   *
   * This is the first concrete value after the survivor-list head, using the
   * value-bound split at `k == 0`.
   */
  def assertRepeatedExtendedWindowSurvivorOneMatchesSpecNextFromValueBound(
    derived: SpecDerivedSieveSequence
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
    val firstTail = CycleIntegralFilterProperties.survivorValues(
      repeated.integral,
      spec.head.value,
      BigInt(1),
      steps - BigInt(1)
    )
    val nextValue = spec.next(BigInt(1))
    val currentOldIndex = spec.indexOfAccepted(spec.next(BigInt(0)))
    val nextOldIndex = spec.indexOfAccepted(nextValue)

    assert(nextValue <= spec(steps))
    assert(assertSpecNextHeadOldIndexIsOne(derived))
    assert(currentOldIndex == BigInt(1))
    assert(steps - currentOldIndex == steps - BigInt(1))
    assert(spec.assertNextValueAcceptedByThis(BigInt(1)))
    assert(spec.accepts(nextValue))
    assert(spec.assertIndexOfAcceptedAtMost(nextValue, steps))
    assert(nextOldIndex <= steps)

    val tailSurvivors = CycleIntegralFilterProperties.survivorValues(
      repeated.integral,
      spec.head.value,
      currentOldIndex,
      steps - currentOldIndex
    )
    val afterNext = CycleIntegralFilterProperties.survivorValues(
      repeated.integral,
      spec.head.value,
      nextOldIndex,
      steps - nextOldIndex
    )

    assert(firstTail == tailSurvivors)
    assert(assertRepeatedExtendedWindowSurvivorsTailIsFirstTail(derived))
    assert(survivors.tail == firstTail)
    assert(assertRepeatedExtendedWindowTailSplitsAtSpecNextSuccessorFromValueBound(derived, BigInt(0)))
    assert(tailSurvivors == nextValue :: afterNext)
    assert(firstTail == nextValue :: afterNext)
    assert(firstTail.head == nextValue)
    assert(firstTail.head == spec.next(BigInt(1)))
    assert(!firstTail.isEmpty)
    assert(BigInt(0) < survivors.tail.size)
    assert(ListUtilsProperties.accessTailShiftRight(survivors, BigInt(0)))

    survivors(BigInt(1)) == spec.next(BigInt(1))
  }.holds

  /**
   * Proves the first extended survivor gap matches the first next-spec gap.
   *
   * Once survivor values at indexes `0` and `1` match `spec.next(0)` and
   * `spec.next(1)`, their difference equals the first gap in
   * `spec.next.gapList(0, 1)`.
   */
  def assertRepeatedExtendedWindowFirstGapMatchesSpecNextFromValueBound(
    derived: SpecDerivedSieveSequence
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

    assert(spec.next(BigInt(1)) <= spec(steps))
    assert(SpecDerivedExtendedWindowProperties.assertRepeatedExtendedWindowSurvivorsHeadMatchesSpecNext(derived))
    assert(survivors(BigInt(0)) == spec.next(BigInt(0)))
    assert(assertRepeatedExtendedWindowSurvivorOneMatchesSpecNextFromValueBound(derived))
    assert(survivors(BigInt(1)) == spec.next(BigInt(1)))
    assert(BigInt(1) < survivors.size)
    assert(SpecDerivedExtendedWindowProperties.assertRepeatedExtendedWindowGapMatchesSpecNextGapAt(derived, BigInt(0)))

    val gaps = CycleIntegralFilterProperties.gapsFromValues(survivors)
    val specGaps = spec.next.gapList(BigInt(0), BigInt(1))

    gaps(BigInt(0)) == specGaps(BigInt(0))
  }.holds

  /**
   * Packages the first concrete gap equality as a gap-prefix fact.
   *
   * This proves `repeatedExtendedWindowGapsMatchSpecNextPrefix(1)` under the
   * same endpoint bound used by the first-gap bridge.
   */
  def assertRepeatedExtendedWindowFirstGapPrefixFromValueBound(
    derived: SpecDerivedSieveSequence
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

    assert(assertRepeatedExtendedWindowFirstGapMatchesSpecNextFromValueBound(derived))
    assert(BigInt(1) < survivors.size)
    assert(!survivors.isEmpty)

    val gaps = CycleIntegralFilterProperties.gapsFromValues(survivors)
    val specGaps = spec.next.gapList(BigInt(0), BigInt(1))

    assert(SpecDerivedExtendedWindowProperties.repeatedExtendedWindowGapsMatchSpecNextPrefix(derived, BigInt(0)))
    assert(gaps(BigInt(0)) == specGaps(BigInt(0)))

    SpecDerivedExtendedWindowProperties.repeatedExtendedWindowGapsMatchSpecNextPrefix(derived, BigInt(1))
  }.holds

  /**
   * Rebuilds `survivors(1) == spec.next(1)` from the gap-prefix bridge.
   *
   * The first gap prefix plus the generic values-from-gaps induction recovers
   * the first non-head survivor value.
   */
  def assertRepeatedExtendedWindowValueOneFromGapPrefixFromValueBound(
    derived: SpecDerivedSieveSequence
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

    assert(assertRepeatedExtendedWindowFirstGapPrefixFromValueBound(derived))
    assert(SpecDerivedExtendedWindowProperties.repeatedExtendedWindowGapsMatchSpecNextPrefix(derived, BigInt(1)))
    assert(BigInt(1) < survivors.size)
    assert(!survivors.isEmpty)
    assert(SpecDerivedExtendedWindowProperties.assertRepeatedExtendedWindowValuesMatchSpecNextFromGapPrefix(derived, BigInt(1)))

    survivors(BigInt(1)) == spec.next(BigInt(1))
  }.holds


  /**
   * Proves that the extended survivor list starts at `spec.next(0)`.
   *
   * The extended scan uses `period * head + 1` integral values. Its first value is
   * the repeated-cycle next head, and that value survives the current head filter.
   */
  def assertRepeatedExtendedWindowSurvivorsHeadMatchesSpecNext(derived: SpecDerivedSieveSequence): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    val repeated = derived.repeatedCycle(spec.head.value)
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


  /**
   * Converts adjacent survivor-value equality into one gap equality.
   *
   * If `survivors(index)` and `survivors(index + 1)` match the corresponding
   * `spec.next` values, then the generated survivor gap at `index` matches the
   * `spec.next` gap at the same index.
   */
  def assertRepeatedExtendedWindowGapMatchesSpecNextGapAt(derived: SpecDerivedSieveSequence, index: BigInt): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    require(index >= BigInt(0))

    val repeated = derived.repeatedCycle(spec.head.value)
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


  /**
   * Proves the next survivor value from a matching current value and gap.
   *
   * Given `survivors(index) == spec.next(index)` and a matching gap at `index`,
   * this proves `survivors(index + 1) == spec.next(index + 1)`.
   */
  def assertRepeatedExtendedWindowNextValueFromGapAt(derived: SpecDerivedSieveSequence, index: BigInt): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    require(index >= BigInt(0))

    val repeated = derived.repeatedCycle(spec.head.value)
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


  /**
   * Defines prefix equality between extended survivor gaps and next-spec gaps.
   *
   * For every index below `count`, the gap from
   * `gapsFromValues(extendedSurvivors)` equals the corresponding entry of
   * `spec.next.gapList(0, count)`.
   */
  def repeatedExtendedWindowGapsMatchSpecNextPrefix(derived: SpecDerivedSieveSequence, count: BigInt): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    require(count >= BigInt(0))

    val repeated = derived.repeatedCycle(spec.head.value)
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
      assert(CycleIntegralFilterProperties.assertGapsFromValuesSize(survivors))
      assert(gaps.size == survivors.size - BigInt(1))
      assert(index < gaps.size)
      assert(spec.next.assertGapListSize(BigInt(0), count))
      assert(specGaps.size == count)
      assert(index < specGaps.size)

      SpecDerivedExtendedWindowProperties.repeatedExtendedWindowGapsMatchSpecNextPrefix(derived, index) &&
        gaps(index) == specGaps(index)
    }
  }


  /**
   * Proves survivor-value prefix equality from the matching gap prefix.
   *
   * Starting from `survivors(0) == spec.next(0)`, each matching gap advances the
   * equality by one index, yielding `survivors(count) == spec.next(count)`.
   */
  def assertRepeatedExtendedWindowValuesMatchSpecNextFromGapPrefix(derived: SpecDerivedSieveSequence, count: BigInt): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    require(count >= BigInt(0))

    val repeated = derived.repeatedCycle(spec.head.value)
    val steps = period * spec.head.value + BigInt(1)
    val survivors = CycleIntegralFilterProperties.survivorValues(
      repeated.integral,
      spec.head.value,
      BigInt(0),
      steps
    )

    require(!survivors.isEmpty)
    require(count < survivors.size)
    require(SpecDerivedExtendedWindowProperties.repeatedExtendedWindowGapsMatchSpecNextPrefix(derived, count))
    decreases(count)

    if (count == BigInt(0)) {
      assert(SpecDerivedExtendedWindowProperties.assertRepeatedExtendedWindowSurvivorsHeadMatchesSpecNext(derived))
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
      assert(SpecDerivedExtendedWindowProperties.repeatedExtendedWindowGapsMatchSpecNextPrefix(derived, index))
      assert(SpecDerivedExtendedWindowProperties.assertRepeatedExtendedWindowValuesMatchSpecNextFromGapPrefix(derived, index))
      assert(survivors(index) == spec.next(index))
      assert(index < gaps.size)
      assert(index < specGaps.size)
      assert(gaps(index) == specGaps(index))
      assert(SpecDerivedExtendedWindowProperties.assertRepeatedExtendedWindowNextValueFromGapAt(derived, index))

      survivors(count) == spec.next(count)
    }
  }.holds


  /**
   * Proves a next-spec value appears in the extended survivor list.
   *
   * If the old accepted index of `spec.next(k)` lies inside the extended scan,
   * the shifted repeated-integral equality places that value at the matching old
   * position, and the current head filter keeps it.
   */
  def assertSpecNextValueAppearsInRepeatedExtendedWindowSurvivors(derived: SpecDerivedSieveSequence, k: BigInt): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    require(k >= BigInt(0))

    val repeated = derived.repeatedCycle(spec.head.value)
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
    assert(SpecDerivedRepeatedCycleProperties.assertRepeatedIntegralMatchesShiftedSpec(derived, position))
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


  /**
   * Proves survivor membership from a value bound instead of an old-index bound.
   *
   * If `spec.next(k) <= spec(steps)`, the old accepted index is at most `steps`,
   * so the membership bridge can be applied.
   */
  def assertSpecNextValueAppearsInRepeatedExtendedWindowSurvivorsFromValueBound(derived: SpecDerivedSieveSequence, k: BigInt): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    require(k >= BigInt(0))

    val repeated = derived.repeatedCycle(spec.head.value)
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
    assert(SpecDerivedExtendedWindowProperties.assertSpecNextValueAppearsInRepeatedExtendedWindowSurvivors(derived, k))

    survivors.contains(value)
  }.holds


  /**
   * Proves skipped repeated-integral values are current-head multiples.
   *
   * For old positions between the old accepted indexes of `spec.next(k)` and
   * `spec.next(k + 1)`, each repeated-integral value corresponds to an old
   * generated value strictly between consecutive next-spec values, so it is
   * removed by the current head filter.
   */
  def assertRepeatedIntegralSkippedRangeBetweenSpecNextValuesAllMultiples(
    derived: SpecDerivedSieveSequence,
    k: BigInt,
    fromPos: BigInt,
    untilPos: BigInt
  ): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    require(k >= BigInt(0))
    require(fromPos >= BigInt(0))
    require(untilPos >= fromPos)

    val repeated = derived.repeatedCycle(spec.head.value)
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
      assert(SpecDerivedRepeatedCycleProperties.assertRepeatedIntegralMatchesShiftedSpec(derived, fromPos))
      assert(repeated.integral(fromPos) == spec(oldIndex))
      assert(Calc.mod(repeated.integral(fromPos), spec.head.value) == BigInt(0))
      assert(SpecDerivedExtendedWindowProperties.assertRepeatedIntegralSkippedRangeBetweenSpecNextValuesAllMultiples(derived, 
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


  /**
   * Proves the filtered tail head is `spec.next(k + 1)`.
   *
   * Once skipped values before the next accepted old position are known to be
   * current-head multiples, the first non-multiple survivor in the tail scan is
   * exactly `spec.next(k + 1)`.
   */
  def assertRepeatedExtendedWindowTailHeadMatchesSpecNextSuccessor(derived: SpecDerivedSieveSequence, k: BigInt): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    require(k >= BigInt(0))

    val repeated = derived.repeatedCycle(spec.head.value)
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
    assert(SpecDerivedExtendedWindowProperties.assertRepeatedIntegralSkippedRangeBetweenSpecNextValuesAllMultiples(derived, 
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
    assert(SpecDerivedRepeatedCycleProperties.assertRepeatedIntegralMatchesShiftedSpec(derived, position))
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


  /**
   * Proves the tail-head bridge using an endpoint value bound.
   *
   * The value bound `spec.next(k + 1) <= spec(steps)` is converted into the old
   * index bound needed by `assertRepeatedExtendedWindowTailHeadMatchesSpecNextSuccessor`.
   */
  def assertRepeatedExtendedWindowTailHeadMatchesSpecNextSuccessorFromValueBound(derived: SpecDerivedSieveSequence, k: BigInt): Boolean = {
    val spec = derived.spec
    val period = derived.period
    val gapCycle = derived.gapCycle
    val primes = derived.primes
    val cyclePrimes = derived.cyclePrimes
    val cycle = derived.cycle
    val integral = derived.integral

    require(k >= BigInt(0))
    require(spec.next(k + BigInt(1)) <= spec(period * spec.head.value + BigInt(1)))

    val repeated = derived.repeatedCycle(spec.head.value)
    val steps = period * spec.head.value + BigInt(1)
    val currentValue = spec.next(k)
    val nextValue = spec.next(k + BigInt(1))

    assert(nextValue <= spec(steps))
    assert(spec.next.applyStrictlyIncreases(k))
    assert(currentValue < nextValue)
    assert(currentValue <= spec(steps))
    assert(spec.assertNextValueAcceptedByThis(k))
    assert(spec.assertNextValueAcceptedByThis(k + BigInt(1)))
    assert(spec.accepts(currentValue))
    assert(spec.accepts(nextValue))

    val currentOldIndex = spec.indexOfAccepted(currentValue)
    val nextOldIndex = spec.indexOfAccepted(nextValue)

    assert(spec.assertIndexOfAcceptedAtMost(currentValue, steps))
    assert(spec.assertIndexOfAcceptedAtMost(nextValue, steps))
    assert(currentOldIndex <= steps)
    assert(nextOldIndex <= steps)
    assert(SpecDerivedExtendedWindowProperties.assertRepeatedExtendedWindowTailHeadMatchesSpecNextSuccessor(derived, k))

    val count = steps - currentOldIndex
    val survivors = CycleIntegralFilterProperties.survivorValues(
      repeated.integral,
      spec.head.value,
      currentOldIndex,
      count
    )

    survivors.head == spec.next(k + BigInt(1))
  }.holds
}
