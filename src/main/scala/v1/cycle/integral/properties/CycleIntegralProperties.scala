package v1.cycle.integral.properties

import stainless.collection.List
import stainless.lang.*
import v1.cycle.integral.CycleIntegral
import v1.cycle.properties.CycleProperties
import v1.list.ListUtils
import v1.list.properties.ListUtilsProperties
import verification.Helper.{assert, equality}

object CycleIntegralProperties {

  /**
   * The sum of the values of the cycle integral until that position is equal to
   * the current value of the cycle integral.
   *
   * In other words:
   * IntegralCycle(position) == sum(cycle(0), cycle(1), ..., Cycle(position))
   *
   * @param cycleIntegral CycleIntegral any cycle integral
   * @return Boolean true if the property holds
   */
  def assertCycleIntegralEqualsSumFirstPosition(cycleIntegral: CycleIntegral): Boolean = {
    val smallList = List(cycleIntegral.initialValue) ++ List(cycleIntegral.cycle(0))
    assert(ListUtils.sum(List()) == BigInt(0))
    ListUtilsProperties.listAddValueTail(List(), cycleIntegral.initialValue)
    ListUtilsProperties.listAddValueTail(List(cycleIntegral.initialValue), cycleIntegral.cycle(0))
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
    assert(CycleProperties.smallValueInCycle(cycleIntegral.cycle, position))
    assert(cycleIntegral.cycle(position) == cycleIntegral.cycle.values(position))
    assert(ListUtils.sum(getFirstValuesAsSlice(cycleIntegral, position - 1)) == cycleIntegral(position - 1))

    val prev = getFirstValuesAsSlice(cycleIntegral, position - 1)
    val prevSum = ListUtils.sum(prev)
    assert(prevSum == cycleIntegral(position - 1))

    val currentList = List(cycleIntegral.cycle.values(position)) ++ prev
    val currentValue = cycleIntegral.cycle(position)
    val currentSum = ListUtils.sum(prev) + currentValue
    assert(ListUtilsProperties.listAddValueTail(prev, currentValue))
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
   * integralCycle(pos + 1) - integralCycle(pos) == integralCycle(pos + size + 1) - integralCycle(pos + size)
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

    CycleProperties.valueMatchAfterManyLoopsInBoth(iCycle.cycle, a, 0, 1)
    CycleProperties.valueMatchAfterManyLoopsInBoth(iCycle.cycle, b, 0, 1)

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
  def assertSumModValueAsListEqualsIntegralCycleLoop(iCycle: CycleIntegral, position: BigInt): Boolean = {
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
        assert(CycleProperties.valueMatchAfterManyLoopsInBoth(iCycle.cycle, position - iCycle.size, 0, 1))
      }
      assertSumModValueAsListEqualsIntegralCycleLoop(iCycle, position - 1)
      assert(iCycle(position - 1) == ListUtils.sum(getModValuesAsList(iCycle, position - 1)))
      assert(ListUtilsProperties.listAddValueTail(getModValuesAsList(iCycle, position - 1), iCycle.cycle(position)))
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
   * integralCycle(position) == sum(cycle(0), cycle(1), ..., Cycle(position))
   *
   * @param iCycle CycleIntegral
   * @param position BigInt position
   * @return true if the property holds
   */
  def assertIntegralCycleEqualsSumOfModlValuesAsList(iCycle: CycleIntegral, position: BigInt): Boolean = {
    require(position >= 0)
    assert(assertSumModValueAsListEqualsIntegralCycleLoop(iCycle, position))
    val listModValues = getModValuesAsList(iCycle, position)
    iCycle(position) == ListUtils.sum(listModValues)
  }.holds

  def getFirstValuesAsSlice(cycleIntegral: CycleIntegral, position: BigInt): List[BigInt] = {
    require(position >= 0)
    require(position < cycleIntegral.size)
    decreases(position)

    ListUtilsProperties.listAddValueTail(cycleIntegral.cycle.values, cycleIntegral.initialValue)
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
      CycleProperties.smallValueInCycle(cycle = cycleIntegral.cycle, key = position)
    }

    if (position == 0) {
      assert(ListUtilsProperties.listAddValueTail(List(cycleIntegral.cycle(0)), cycleIntegral.initialValue))
      List(cycleIntegral.initialValue) ++ List(cycleIntegral.cycle(0))
    } else {
      val prev = getModValuesAsList(cycleIntegral, position - 1)
      assert(ListUtilsProperties.listAddValueTail(prev, cycleIntegral.cycle(position)))
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
  def assertFirstValuesAsSliceEqualsModValuesAsListt(cycleIntegral: CycleIntegral, position: BigInt): Boolean = {
    require(position >= 0)
    require(position < cycleIntegral.size)
    decreases(position)

    val valuesAsList = getModValuesAsList(cycleIntegral,position)
    val firstValues = getFirstValuesAsSlice(cycleIntegral,position)
    if (position == 0) {

      assert(firstValues  == List(cycleIntegral.initialValue, cycleIntegral.cycle(0)))
      assert(valuesAsList == List(cycleIntegral.initialValue, cycleIntegral.cycle(0)))

    } else {
      CycleProperties.smallValueInCycle(cycleIntegral.cycle, position)
      assert(cycleIntegral.cycle.values(position) == cycleIntegral.cycle(position))

      assertFirstValuesAsSliceEqualsModValuesAsListt(cycleIntegral, position - 1)
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
}
