package v1.chapter4.cycle.integral.recursive.properties

import stainless.collection.List
import stainless.lang.*
import v1.chapter1.verification.Helper.{assert, equality}
import v1.chapter2.div.Calc
import v1.chapter3.list.{ListBoundUtils, ListUtils}
import v1.chapter3.list.properties.ListRepeatProperties
import v1.chapter3.list.properties.ListUtilsProperties
import v1.chapter4.cycle.CycleUtils
import v1.chapter4.cycle.integral.recursive.CycleIntegral
import v1.chapter4.cycle.memory.MemCycle
import v1.chapter4.cycle.memory.properties.MemCycleProperties

object CycleIntegralProperties {

  /**
   * Repeating the physical values of a cycle preserves the recursive integral
   * when the initial value is unchanged.
   *
   * Math:
   *
   *   C      = cycleIntegral
   *   C_t    = repeatedCycleIntegral
   *   times  > 0
   *
   *   C_t.initialValue = C.initialValue
   *   C_t.cycle.values = repeat(C.cycle.values, times)
   *
   *   C(0)   = C.initialValue   + C.cycle(0)
   *   C_t(0) = C_t.initialValue + C_t.cycle(0)
   *
   *   C(k)   = C(k - 1)   + C.cycle(k)
   *   C_t(k) = C_t(k - 1) + C_t.cycle(k)
   *
   *   C_t.cycle(k) = C.cycle(k)
   *
   * Therefore, by induction on `position`:
   *
   *   C_t(position) = C(position)
   *
   * The proof decreases `position`; the recursive step uses the already-proven
   * equality at `position - 1` plus the memory-cycle repeated-values lemma for
   * the current gap lookup.
   */
  def assertRepeatedValuesIntegralMatches(
    cycleIntegral: CycleIntegral,
    repeatedCycleIntegral: CycleIntegral,
    times: BigInt,
    position: BigInt
  ): Boolean = {
    require(times > BigInt(0))
    require(position >= BigInt(0))
    require(cycleIntegral.cycle.size > BigInt(0))
    require(repeatedCycleIntegral.initialValue == cycleIntegral.initialValue)
    require(repeatedCycleIntegral.cycle.values ==
      ListRepeatProperties.repeat(cycleIntegral.cycle.values, times))
    decreases(position)

    if (position == BigInt(0)) {
      assert(MemCycleProperties.assertRepeatedValuesCycleMatches(
        cycleIntegral.cycle,
        repeatedCycleIntegral.cycle,
        times,
        BigInt(0)
      ))
      assert(repeatedCycleIntegral.cycle(BigInt(0)) == cycleIntegral.cycle(BigInt(0)))
      assert(repeatedCycleIntegral(position) ==
        repeatedCycleIntegral.cycle(BigInt(0)) + repeatedCycleIntegral.initialValue)
      assert(cycleIntegral(position) ==
        cycleIntegral.cycle(BigInt(0)) + cycleIntegral.initialValue)
      assert(repeatedCycleIntegral(position) == cycleIntegral(position))

      repeatedCycleIntegral(position) == cycleIntegral(position)
    } else {
      assert(assertRepeatedValuesIntegralMatches(
        cycleIntegral,
        repeatedCycleIntegral,
        times,
        position - BigInt(1)
      ))
      assert(MemCycleProperties.assertRepeatedValuesCycleMatches(
        cycleIntegral.cycle,
        repeatedCycleIntegral.cycle,
        times,
        position
      ))

      val repeatedGap = repeatedCycleIntegral.cycle(position)
      val originalGap = cycleIntegral.cycle(position)
      val repeatedPrevious = repeatedCycleIntegral(position - BigInt(1))
      val originalPrevious = cycleIntegral(position - BigInt(1))

      assert(repeatedGap == originalGap)
      assert(repeatedPrevious == originalPrevious)
      assert(repeatedCycleIntegral(position) == repeatedGap + repeatedPrevious)
      assert(cycleIntegral(position) == originalGap + originalPrevious)
      assert(repeatedGap + repeatedPrevious == originalGap + originalPrevious)
      assert(repeatedCycleIntegral(position) == cycleIntegral(position))

      repeatedCycleIntegral(position) == cycleIntegral(position)
    }
  }.holds

  def assertCycleIntegralIncreasing(ci: CycleIntegral, a: BigInt, b: BigInt): Boolean = {
    require(a >= 0)
    require(b > a)
    require(ci.initialValue >= BigInt(0))
    require(ListBoundUtils.allGreaterThan(ci.cycle.values, BigInt(0)))
    require(ci.cycle.values.nonEmpty)
    require(ci.cycle.size > 0)
    decreases(b - a)
    if (a + 1 == b) {
      assert(assertDiffEqualsCycleValue(ci, a))
      assert(assertCycleValuePositive(ci, a + 1))
      ci(b) > ci(a)
    } else {
      assert(assertCycleIntegralIncreasing(ci, a, b - 1))
      assert(assertDiffEqualsCycleValue(ci, b - 1))
      assert(assertCycleValuePositive(ci, b))
      ci(b) > ci(a)
    }
  }.holds

  /**
   * The sum of the values of the cycle integral until that position is equal to
   * the current value of the cycle integral.
   *
   * In other words:
   * CycleIntegral(position) == sum(cycle(0), cycle(1), ..., Cycle(position))
   *
   * @param cycleIntegral CycleIntegral any cycle integral
   * @return Boolean true if the property holds
   */
  def assertCycleIntegralEqualsSumFirstPosition(cycleIntegral: CycleIntegral): Boolean = {
    val smallList = List(cycleIntegral.initialValue) ++ List(cycleIntegral.cycle(0))
    assert(ListUtils.sum(List()) == BigInt(0))
    ListUtils.listAddValueTail(List(), cycleIntegral.initialValue)
    ListUtils.listAddValueTail(List(cycleIntegral.initialValue), cycleIntegral.cycle(0))
    assert(ListUtils.sum(smallList) == cycleIntegral.initialValue + cycleIntegral.cycle(0))
    assert(cycleIntegral(0) == cycleIntegral.initialValue + cycleIntegral.cycle(0))
    assert(smallList == getFirstValuesAsSlice(cycleIntegral, 0))
    ListUtils.sum(getFirstValuesAsSlice(cycleIntegral, 0)) == cycleIntegral(0)
  }.holds

  /**
   * For every position from one until size less one, the cycle integral value is
   * the sum of the values from zero until that position, plus the initial cycle value
   *
   * cycleIntegral(position) == ListUtils.sum(getFirstValuesAsSlice(cycleIntegral, position))
   *
   * @param cycleIntegral CycleIntegral any cycle integral
   * @param position BigInt any position from zero to size less one
   * @return true if holds
   */
  def assertCycleIntegralEqualsSumSmallPositions(cycleIntegral: CycleIntegral, position: BigInt): Boolean = {
    require(position < cycleIntegral.size)
    require(position > 0)
    require(ListUtils.sum(getFirstValuesAsSlice(cycleIntegral, position - 1)) == cycleIntegral(position - 1))

    assert(assertNextPosition(cycleIntegral, position))
    assert(cycleIntegral(position) == cycleIntegral.cycle(position) + cycleIntegral(position - 1))
    assert(MemCycleProperties.smallValueInCycle(cycleIntegral.cycle, position))
    assert(cycleIntegral.cycle(position) == cycleIntegral.cycle.values(position))
    assert(ListUtils.sum(getFirstValuesAsSlice(cycleIntegral, position - 1)) == cycleIntegral(position - 1))

    val prev = getFirstValuesAsSlice(cycleIntegral, position - 1)
    val prevSum = ListUtils.sum(prev)
    assert(prevSum == cycleIntegral(position - 1))

    val currentList = List(cycleIntegral.cycle.values(position)) ++ prev
    val currentValue = cycleIntegral.cycle(position)
    val currentSum = ListUtils.sum(prev) + currentValue
    assert(ListUtils.listAddValueTail(prev, currentValue))
    assert(ListUtils.sum(prev) + currentValue == ListUtils.sum(currentList))
    assert(assertNextPosition(cycleIntegral = cycleIntegral, position = position))
    equality(
      cycleIntegral(position), //                                     is equals to
      cycleIntegral.cycle(position) + cycleIntegral(position - 1), // is equals to
      cycleIntegral.cycle(position) + prevSum, //                     is equals to
      cycleIntegral.cycle.values(position) + prevSum, //              is equals to
      currentSum, //                                                  is equals to
      ListUtils.sum(currentList), //                                  is equals to
      ListUtils.sum(getFirstValuesAsSlice(cycleIntegral, position))
    )

    ListUtils.sum(getFirstValuesAsSlice(cycleIntegral, position)) ==
      cycleIntegral(position)
  }.holds

  /**
   * For every position from zero until size less one, the cycle integral value is
   * the sum of the values from zero until that position, plus the initial cycle value
   *
   * cycleIntegral(position) == ListUtils.sum(getFirstValuesAsSlice(cycleIntegral, position))
   *
   * @param cycleIntegral CycleIntegral any cycle integral
   * @param position BigInt any position from zero to size less one
   * @return true if holds
   */
  def assertCycleIntegralEqualsSliceSum(cycleIntegral: CycleIntegral, position: BigInt): Boolean = {
    require(position < cycleIntegral.size)
    require(position >= 0)
    decreases(position)

    if (position == 0 ) {
      assert(assertCycleIntegralEqualsSumFirstPosition(cycleIntegral))
    } else {
      assert(assertCycleIntegralEqualsSliceSum(cycleIntegral = cycleIntegral, position = position - 1))
      assert(assertCycleIntegralEqualsSumSmallPositions(cycleIntegral = cycleIntegral, position = position))
    }
    ListUtils.sum(getFirstValuesAsSlice(cycleIntegral, position)) ==
      cycleIntegral(position)
  }.holds

  def assertNextPosition(cycleIntegral: CycleIntegral, position: BigInt): Boolean = {
    require(position > 0)
    cycleIntegral(position) == cycleIntegral(position - 1) + cycleIntegral.cycle(position)
  }.holds

  /**
   * Lemmas: The difference between two consecutive values in the cycle
   * pos and pos + 1 is equal to cycle.values at pos + 1.
   *
   * in other words
   * cycleIntegral(pos + 1) - cycleIntegral(pos) == cycleIntegral.cycle(pos + 1)
   *
   * @param cycleIntegral CycleIntegral any cycle integral
   * @param position BigInt any position bigger than or equals to zero
   * @return true if the property holds
   */
  def assertDiffEqualsCycleValue(cycleIntegral: CycleIntegral, position: BigInt): Boolean = {
    require(position >= 0)
    assert(cycleIntegral(position + 1) == cycleIntegral(position) + cycleIntegral.cycle(position + 1))
    cycleIntegral(position + 1) - cycleIntegral(position) == cycleIntegral.cycle(position + 1)
  }.holds

  /**
   * Lemmas: The difference between two consecutive values in the cycle
   * pos and pos + 1 is equal to the difference of the cycle values at the
   * pos + size and pos + size + 1.
   *
   * in other words
   * size == cycleIntegral.size
   * cycleIntegral(pos + 1) - cycleIntegral(pos) == cycleIntegral(pos + size + 1) - cycleIntegral(pos + size)
   *
   * @param iCycle CycleIntegral any cycle integral
   * @param position BigInt any position bigger than or equals to zero
   * @return Boolean true if the property holds
   */
  def assertSameDiffAfterCycle(iCycle: CycleIntegral, position: BigInt): Boolean = {
    require(position >= 0)

    val a = position
    val b = position + 1
    val c = a + iCycle.size
    val d = b + iCycle.size

    assertDiffEqualsCycleValue(cycleIntegral = iCycle, position = a)
    assert(iCycle(b) - iCycle(a) == iCycle.cycle(b))

    assertDiffEqualsCycleValue(cycleIntegral = iCycle, position = c)
    assert(iCycle(d) - iCycle(c) == iCycle.cycle(d))

    MemCycleProperties.valueMatchAfterManyLoopsInBoth(iCycle.cycle, a, 0, 1)
    MemCycleProperties.valueMatchAfterManyLoopsInBoth(iCycle.cycle, b, 0, 1)

    assert(iCycle.cycle(d) == iCycle.cycle(b))
    assert(iCycle.cycle(c) == iCycle.cycle(a))

    iCycle(b) - iCycle(a) == iCycle(d) - iCycle(c)
  }.holds

  def assertLastElementBeforeLoop(iCycle: CycleIntegral): Boolean = {
    assertCycleIntegralEqualsSliceSum(iCycle, iCycle.size - 1)
    iCycle(iCycle.size - 1) == ListUtils.sum(getFirstValuesAsSlice(iCycle, iCycle.size - 1))
  }.holds

  /**
   * Lemma: the current value of the cycle integral is equal to the sum of the
   * values of the cycle integral until that position. The current value of the
   * cycle integral is also equal to the previous value of the cycle integral
   * plus the value of the cycle at that position.
   *
   * In other words
   *
   * for any cycle integral, if cycle = cycleIntegral.cycle and position >= 0,
   * cycleIntegral(position) == cycleIntegral(position - 1) + Cycle(position) and
   * cycleIntegral(position) == sum(cycle(0), cycle(1), ..., Cycle(position))
   *
   * @param iCycle CycleIntegral
   * @param position BigInt position
   * @return true if the property holds
   */
  def assertSumModValueAsListEqualsCycleIntegralLoop(iCycle: CycleIntegral, position: BigInt): Boolean = {
    require(position >= 0)
    decreases(position)

    if (position == 0) {
      assert(iCycle(position) == ListUtils.sum(getModValuesAsList(iCycle, position)))
      iCycle(position) == iCycle.cycle(0) + iCycle.initialValue &&
        iCycle(position) == ListUtils.sum(getModValuesAsList(iCycle, position))
    } else {
      if (position > iCycle.size ) {
        assertSameDiffAfterCycle(iCycle, position - iCycle.size)
        assert(iCycle(position - iCycle.size) - iCycle(position - iCycle.size - 1) == iCycle(position) - iCycle(position - 1))
        assert(iCycle(position - 1) + iCycle(position - iCycle.size) - iCycle(position - iCycle.size - 1) == iCycle(position))
        assert(iCycle(position - 1) + iCycle.cycle(position - iCycle.size) == iCycle(position))
        assert(MemCycleProperties.valueMatchAfterManyLoopsInBoth(iCycle.cycle, position - iCycle.size, 0, 1))
      }
      assertSumModValueAsListEqualsCycleIntegralLoop(iCycle, position - 1)
      assert(iCycle(position - 1) == ListUtils.sum(getModValuesAsList(iCycle, position - 1)))
      assert(ListUtils.listAddValueTail(getModValuesAsList(iCycle, position - 1), iCycle.cycle(position)))
      iCycle(position) == iCycle.cycle(position) + iCycle(position - 1) &&
        iCycle(position) == ListUtils.sum(getModValuesAsList(iCycle, position))
    }
  }.holds


  /**
   * The sum of the values of the cycle integral until that position is equal to
   * the current value of the cycle integral.
   *
   * In other words
   *
   * for any cycle integral, if cycle = cycleIntegral.cycle and position >= 0,
   * cycleIntegral(position) == sum(cycle(0), cycle(1), ..., Cycle(position))
   *
   * @param iCycle CycleIntegral
   * @param position BigInt position
   * @return true if the property holds
   */
  def assertCycleIntegralEqualsSumOfModValuesAsList(iCycle: CycleIntegral, position: BigInt): Boolean = {
    require(position >= 0)
    assert(assertSumModValueAsListEqualsCycleIntegralLoop(iCycle, position))
    val listModValues = getModValuesAsList(iCycle, position)
    iCycle(position) == ListUtils.sum(listModValues)
  }.holds

  def getFirstValuesAsSlice(cycleIntegral: CycleIntegral, position: BigInt): List[BigInt] = {
    require(position >= 0)
    require(position < cycleIntegral.size)
    decreases(position)

    ListUtils.listAddValueTail(cycleIntegral.cycle.values, cycleIntegral.initialValue)
    val result = List(cycleIntegral.initialValue) ++
      ListUtils.slice(cycleIntegral.cycle.values, 0, position)

    if (position > 0 ) {
      val list = cycleIntegral.cycle.values
      assert(ListUtilsProperties.assertAppendToSlice(list, 0, position))

      assert(
        ListUtils.slice(list, 0, position) ==
          ListUtils.slice(list, 0, position - 1) ++ List(list(position))
      )

      equality(
        result,
        List(cycleIntegral.initialValue) ++
          ListUtils.slice(list, 0, position),
        List(cycleIntegral.initialValue) ++
          ListUtils.slice(list, 0, position - 1) ++ List(list(position)),
        getFirstValuesAsSlice(cycleIntegral, position - 1) ++ List(list(position)),
      )
    }

    result
  }

  /**
   * We can define a list that the sum of its values match the integral Cycle value.
   *
   * @param cycleIntegral CycleIntegral
   * @param position BigInt valid position
   * @return List of values of the cycle position after the initial value
   */
  def getModValuesAsList(cycleIntegral: CycleIntegral, position: BigInt): List[BigInt] = {
    require(position >= 0)
    decreases(position)

    if (position < cycleIntegral.size) {
      MemCycleProperties.smallValueInCycle(cycle = cycleIntegral.cycle, key = position)
    }

    if (position == 0) {
      assert(ListUtils.listAddValueTail(List(cycleIntegral.cycle(0)), cycleIntegral.initialValue))
      List(cycleIntegral.initialValue) ++ List(cycleIntegral.cycle(0))
    } else {
      val prev = getModValuesAsList(cycleIntegral, position - 1)
      assert(ListUtils.listAddValueTail(prev, cycleIntegral.cycle(position)))
      prev ++ List(cycleIntegral.cycle(position))
    }
  }

  /**
   * For small positions, valuesAsList is equals to firstValues.
   * Therefore the sum is also matching.
   *
   * @param cycleIntegral CycleIntegral
   * @param position BigInt zero or positive smaller than size value
   * @return true if holds
   */
  def assertFirstValuesAsSliceEqualsModValuesAsList(cycleIntegral: CycleIntegral, position: BigInt): Boolean = {
    require(position >= 0)
    require(position < cycleIntegral.size)
    decreases(position)

    val valuesAsList = getModValuesAsList(cycleIntegral,position)
    val firstValues = getFirstValuesAsSlice(cycleIntegral,position)
    if (position == 0) {

      assert(firstValues  == List(cycleIntegral.initialValue, cycleIntegral.cycle(0)))
      assert(valuesAsList == List(cycleIntegral.initialValue, cycleIntegral.cycle(0)))

    } else {
      MemCycleProperties.smallValueInCycle(cycleIntegral.cycle, position)
      assert(cycleIntegral.cycle.values(position) == cycleIntegral.cycle(position))

      assertFirstValuesAsSliceEqualsModValuesAsList(cycleIntegral, position - 1)
      assert(ListUtilsProperties.assertAppendToSlice(cycleIntegral.cycle.values, 0, position))

      val prevValuesAsList = getModValuesAsList(cycleIntegral,    position - 1)
      val prevFirstValues  = getFirstValuesAsSlice(cycleIntegral, position - 1)

      assert(firstValues  == prevFirstValues  ++ List(cycleIntegral.cycle(position)))
      assert(valuesAsList == prevValuesAsList ++ List(cycleIntegral.cycle.values(position)))

      assert(ListUtils.sum(prevValuesAsList) == ListUtils.sum(prevFirstValues))
      assert(prevValuesAsList == prevFirstValues)
    }
    ListUtils.sum(valuesAsList) == ListUtils.sum(firstValues) &&
    valuesAsList == firstValues
  }.holds

  def assertCycleValuePositive(ci: CycleIntegral, pos: BigInt): Boolean = {
    require(pos >= 0)
    require(ListBoundUtils.allGreaterThan(ci.cycle.values, BigInt(0)))
    require(ci.cycle.values.nonEmpty)
    require(ci.cycle.size > 0)
    val size = ci.cycle.size
    val idx = Calc.mod(pos, size)
    assert(idx >= 0)
    assert(idx < size)
    assert(MemCycleProperties.findValueInCycle(ci.cycle, pos))
    assert(ListBoundUtils.assertGreaterThanAtIndex(ci.cycle.values, BigInt(0), idx))
    ci.cycle(pos) > BigInt(0)
  }.holds

  def assertCycleIntegralPositive(ci: CycleIntegral, pos: BigInt): Boolean = {
    require(pos >= 0)
    require(ci.initialValue >= BigInt(0))
    require(ListBoundUtils.allGreaterThan(ci.cycle.values, BigInt(0)))
    require(ci.cycle.values.nonEmpty)
    require(ci.cycle.size > 0)
    decreases(pos)
    if (pos == 0) {
      assert(assertCycleValuePositive(ci, pos))
      ci(0) > BigInt(0)
    } else {
      assert(assertCycleIntegralPositive(ci, pos - 1))
      assert(assertCycleValuePositive(ci, pos))
      assert(assertNextPosition(ci, pos))
      ci(pos) > BigInt(0)
    }
  }.holds

  /**
   * Foundation for single-element merge: the difference across two consecutive
   * gaps equals their sum.
   *
   * {{{
   *   ci.apply(k+1) - ci.apply(k-1) == ci.cycle(k) + ci.cycle(k+1)
   * }}}
   *
   * This is the arithmetic the merge rests on: if we collapse gaps at positions
   * `k` and `k+1` into one gap `g_k + g_{k+1}`, the new single gap still spans
   * the same distance (`ci.apply(k+1) - ci.apply(k-1)`). So merging preserves
   * the total distance covered.
   *
   * Pure original-cycle reasoning — no merged cycle constructed. Proved via
   * `assertDiffEqualsCycleValue` applied twice.
   *
   * @param ci the cycle integral
   * @param k  the merge position, `k >= 1` and `k+1 < ci.size`
   * @return `true` (verified)
   */
  def assertConsecutiveGapSumEqualsDiff(
    ci: CycleIntegral,
    k: BigInt
  ): Boolean = {
    require(k >= BigInt(1))
    require(ci.cycle.size > k + BigInt(1))
    require(ci.cycle.values.nonEmpty)

    assert(assertDiffEqualsCycleValue(ci, k - BigInt(1)))
    assert(assertDiffEqualsCycleValue(ci, k))

    // From the two diff facts:
    //   ci(k)   - ci(k-1) == ci.cycle(k)
    //   ci(k+1) - ci(k)   == ci.cycle(k+1)
    // Adding: ci(k+1) - ci(k-1) == ci.cycle(k) + ci.cycle(k+1)
    ci(k + BigInt(1)) - ci(k - BigInt(1)) == ci.cycle(k) + ci.cycle(k + BigInt(1))
  }.holds
}
