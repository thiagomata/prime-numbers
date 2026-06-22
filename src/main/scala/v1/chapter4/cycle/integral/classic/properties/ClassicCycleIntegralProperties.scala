package v1.chapter4.cycle.integral.classic.properties

import stainless.collection.List
import stainless.lang.*
import v1.chapter1.verification.Helper.{assert, equality}
import v1.chapter3.list.ListUtils
import v1.chapter3.list.properties.ListUtilsProperties
import v1.chapter4.cycle.integral.classic.ClassicCycleIntegral
import v1.chapter4.cycle.memory.properties.MemCycleProperties

object ClassicCycleIntegralProperties {

  /**
   * The sum of the values of the cycle integral until that position is equal to
   * the current value of the cycle integral.
   *
   * In other words:
   * ClassicCycleIntegral(position) == sum(cycle(0), cycle(1), ..., Cycle(position))
   *
   * @param classicCycleIntegral ClassicCycleIntegral any cycle integral
   * @return Boolean true if the property holds
   */
  def assertCycleIntegralEqualsSumFirstPosition(classicCycleIntegral: ClassicCycleIntegral): Boolean = {
    val smallList = List(classicCycleIntegral.initialValue) ++ List(classicCycleIntegral.cycle(0))
    assert(ListUtils.sum(List()) == BigInt(0))
    ListUtilsProperties.listAddValueTail(List(), classicCycleIntegral.initialValue)
    ListUtilsProperties.listAddValueTail(List(classicCycleIntegral.initialValue), classicCycleIntegral.cycle(0))
    assert(ListUtils.sum(smallList) == classicCycleIntegral.initialValue + classicCycleIntegral.cycle(0))
    assert(classicCycleIntegral(0) == classicCycleIntegral.initialValue + classicCycleIntegral.cycle(0))
    assert(smallList == getFirstValuesAsSlice(classicCycleIntegral, 0))
    ListUtils.sum(getFirstValuesAsSlice(classicCycleIntegral, 0)) == classicCycleIntegral(0)
  }.holds

  /**
   * For every position from one until size less one, the cycle integral value is
   * the sum of the values from zero until that position, plus the initial cycle value
   *
   * classicCycleIntegral(position) == ListUtils.sum(getFirstValuesAsSlice(classicCycleIntegral, position))
   *
   * @param classicCycleIntegral ClassicCycleIntegral any cycle integral
   * @param position BigInt any position from zero to size less one
   * @return true if holds
   */
  def assertCycleIntegralEqualsSumSmallPositions(classicCycleIntegral: ClassicCycleIntegral, position: BigInt): Boolean = {
    require(position < classicCycleIntegral.size)
    require(position > 0)
    require(ListUtils.sum(getFirstValuesAsSlice(classicCycleIntegral, position - 1)) == classicCycleIntegral(position - 1))

    assert(assertNextPosition(classicCycleIntegral, position))
    assert(classicCycleIntegral(position) == classicCycleIntegral.cycle(position) + classicCycleIntegral(position - 1))
    assert(MemCycleProperties.smallValueInCycle(classicCycleIntegral.cycle, position))
    assert(classicCycleIntegral.cycle(position) == classicCycleIntegral.cycle.values(position))
    assert(ListUtils.sum(getFirstValuesAsSlice(classicCycleIntegral, position - 1)) == classicCycleIntegral(position - 1))

    val prev = getFirstValuesAsSlice(classicCycleIntegral, position - 1)
    val prevSum = ListUtils.sum(prev)
    assert(prevSum == classicCycleIntegral(position - 1))

    val currentList = List(classicCycleIntegral.cycle.values(position)) ++ prev
    val currentValue = classicCycleIntegral.cycle(position)
    val currentSum = ListUtils.sum(prev) + currentValue
    assert(ListUtilsProperties.listAddValueTail(prev, currentValue))
    assert(ListUtils.sum(prev) + currentValue == ListUtils.sum(currentList))
    assert(assertNextPosition(classicCycleIntegral = classicCycleIntegral, position = position))
    equality(
      classicCycleIntegral(position), //                                     is equals to
      classicCycleIntegral.cycle(position) + classicCycleIntegral(position - 1), // is equals to
      classicCycleIntegral.cycle(position) + prevSum, //                     is equals to
      classicCycleIntegral.cycle.values(position) + prevSum, //              is equals to
      currentSum, //                                                  is equals to
      ListUtils.sum(currentList), //                                  is equals to
      ListUtils.sum(getFirstValuesAsSlice(classicCycleIntegral, position))
    )

    ListUtils.sum(getFirstValuesAsSlice(classicCycleIntegral, position)) ==
      classicCycleIntegral(position)
  }.holds

  /**
   * For every position from zero until size less one, the cycle integral value is
   * the sum of the values from zero until that position, plus the initial cycle value
   *
   * classicCycleIntegral(position) == ListUtils.sum(getFirstValuesAsSlice(classicCycleIntegral, position))
   *
   * @param classicCycleIntegral ClassicCycleIntegral any cycle integral
   * @param position BigInt any position from zero to size less one
   * @return true if holds
   */
  def assertCycleIntegralEqualsSliceSum(classicCycleIntegral: ClassicCycleIntegral, position: BigInt): Boolean = {
    require(position < classicCycleIntegral.size)
    require(position >= 0)
    decreases(position)

    if (position == 0 ) {
      assert(assertCycleIntegralEqualsSumFirstPosition(classicCycleIntegral))
    } else {
      assert(assertCycleIntegralEqualsSliceSum(classicCycleIntegral = classicCycleIntegral, position = position - 1))
      assert(assertCycleIntegralEqualsSumSmallPositions(classicCycleIntegral = classicCycleIntegral, position = position))
    }
    ListUtils.sum(getFirstValuesAsSlice(classicCycleIntegral, position)) ==
      classicCycleIntegral(position)
  }.holds

  def assertNextPosition(classicCycleIntegral: ClassicCycleIntegral, position: BigInt): Boolean = {
    require(position > 0)
    classicCycleIntegral(position) == classicCycleIntegral(position - 1) + classicCycleIntegral.cycle(position)
  }.holds

  /**
   * Lemmas: The difference between two consecutive values in the cycle
   * pos and pos + 1 is equal to cycle.values at pos + 1.
   *
   * in other words
   * classicCycleIntegral(pos + 1) - classicCycleIntegral(pos) == classicCycleIntegral.cycle(pos + 1)
   *
   * @param classicCycleIntegral ClassicCycleIntegral any cycle integral
   * @param position BigInt any position bigger than or equals to zero
   * @return true if the property holds
   */
  def assertDiffEqualsCycleValue(classicCycleIntegral: ClassicCycleIntegral, position: BigInt): Boolean = {
    require(position >= 0)
    assert(classicCycleIntegral(position + 1) == classicCycleIntegral(position) + classicCycleIntegral.cycle(position + 1))
    classicCycleIntegral(position + 1) - classicCycleIntegral(position) == classicCycleIntegral.cycle(position + 1)
  }.holds

  /**
   * Lemmas: The difference between two consecutive values in the cycle
   * pos and pos + 1 is equal to the difference of the cycle values at the
   * pos + size and pos + size + 1.
   *
   * in other words
   * size == classicCycleIntegral.size
   * classicCycleIntegral(pos + 1) - classicCycleIntegral(pos) == classicCycleIntegral(pos + size + 1) - classicCycleIntegral(pos + size)
   *
   * @param iCycle ClassicCycleIntegral any cycle integral
   * @param position BigInt any position bigger than or equals to zero
   * @return Boolean true if the property holds
   */
  def assertSameDiffAfterCycle(iCycle: ClassicCycleIntegral, position: BigInt): Boolean = {
    require(position >= 0)

    val a = position
    val b = position + 1
    val c = a + iCycle.size
    val d = b + iCycle.size

    assertDiffEqualsCycleValue(classicCycleIntegral = iCycle, position = a)
    assert(iCycle(b) - iCycle(a) == iCycle.cycle(b))

    assertDiffEqualsCycleValue(classicCycleIntegral = iCycle, position = c)
    assert(iCycle(d) - iCycle(c) == iCycle.cycle(d))

    MemCycleProperties.valueMatchAfterManyLoopsInBoth(iCycle.cycle, a, 0, 1)
    MemCycleProperties.valueMatchAfterManyLoopsInBoth(iCycle.cycle, b, 0, 1)

    assert(iCycle.cycle(d) == iCycle.cycle(b))
    assert(iCycle.cycle(c) == iCycle.cycle(a))

    iCycle(b) - iCycle(a) == iCycle(d) - iCycle(c)
  }.holds

  def assertLastElementBeforeLoop(iCycle: ClassicCycleIntegral): Boolean = {
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
   * for any cycle integral, if cycle = classicCycleIntegral.cycle and position >= 0,
   * classicCycleIntegral(position) == classicCycleIntegral(position - 1) + Cycle(position) and
   * classicCycleIntegral(position) == sum(cycle(0), cycle(1), ..., Cycle(position))
   *
   * @param iCycle ClassicCycleIntegral
   * @param position BigInt position
   * @return true if the property holds
   */
  def assertSumModValueAsListEqualsCycleIntegralLoop(iCycle: ClassicCycleIntegral, position: BigInt): Boolean = {
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
   * for any cycle integral, if cycle = classicCycleIntegral.cycle and position >= 0,
   * classicCycleIntegral(position) == sum(cycle(0), cycle(1), ..., Cycle(position))
   *
   * @param iCycle ClassicCycleIntegral
   * @param position BigInt position
   * @return true if the property holds
   */
  def assertCycleIntegralEqualsSumOfModlValuesAsList(iCycle: ClassicCycleIntegral, position: BigInt): Boolean = {
    require(position >= 0)
    assert(assertSumModValueAsListEqualsCycleIntegralLoop(iCycle, position))
    val listModValues = getModValuesAsList(iCycle, position)
    iCycle(position) == ListUtils.sum(listModValues)
  }.holds

  def getFirstValuesAsSlice(classicCycleIntegral: ClassicCycleIntegral, position: BigInt): List[BigInt] = {
    require(position >= 0)
    require(position < classicCycleIntegral.size)
    decreases(position)

    ListUtilsProperties.listAddValueTail(classicCycleIntegral.cycle.values, classicCycleIntegral.initialValue)
    val result = List(classicCycleIntegral.initialValue) ++
      ListUtils.slice(classicCycleIntegral.cycle.values, 0, position)

    if (position > 0 ) {
      val list = classicCycleIntegral.cycle.values
      assert(ListUtilsProperties.assertAppendToSlice(list, 0, position))

      assert(
        ListUtils.slice(list, 0, position) ==
          ListUtils.slice(list, 0, position - 1) ++ List(list(position))
      )

      equality(
        result,
        List(classicCycleIntegral.initialValue) ++
          ListUtils.slice(list, 0, position),
        List(classicCycleIntegral.initialValue) ++
          ListUtils.slice(list, 0, position - 1) ++ List(list(position)),
        getFirstValuesAsSlice(classicCycleIntegral, position - 1) ++ List(list(position)),
      )
    }

    result
  }

  /**
   * We can define a list that the sum of its values match the integral Cycle value.
   *
   * @param classicCycleIntegral ClassicCycleIntegral
   * @param position BigInt valid position
   * @return List of values of the cycle position after the initial value
   */
  def getModValuesAsList(classicCycleIntegral: ClassicCycleIntegral, position: BigInt): List[BigInt] = {
    require(position >= 0)
    decreases(position)

    if (position < classicCycleIntegral.size) {
      MemCycleProperties.smallValueInCycle(cycle = classicCycleIntegral.cycle, key = position)
    }

    if (position == 0) {
      assert(ListUtilsProperties.listAddValueTail(List(classicCycleIntegral.cycle(0)), classicCycleIntegral.initialValue))
      List(classicCycleIntegral.initialValue) ++ List(classicCycleIntegral.cycle(0))
    } else {
      val prev = getModValuesAsList(classicCycleIntegral, position - 1)
      assert(ListUtilsProperties.listAddValueTail(prev, classicCycleIntegral.cycle(position)))
      prev ++ List(classicCycleIntegral.cycle(position))
    }
  }

  /**
   * For small positions, valuesAsList is equals to firstValues.
   * Therefore the sum is also matching.
   *
   * @param classicCycleIntegral ClassicCycleIntegral
   * @param position BigInt zero or positive smaller than size value
   * @return true if holds
   */
  def assertFirstValuesAsSliceEqualsModValuesAsList(classicCycleIntegral: ClassicCycleIntegral, position: BigInt): Boolean = {
    require(position >= 0)
    require(position < classicCycleIntegral.size)
    decreases(position)

    val valuesAsList = getModValuesAsList(classicCycleIntegral,position)
    val firstValues = getFirstValuesAsSlice(classicCycleIntegral,position)
    if (position == 0) {

      assert(firstValues  == List(classicCycleIntegral.initialValue, classicCycleIntegral.cycle(0)))
      assert(valuesAsList == List(classicCycleIntegral.initialValue, classicCycleIntegral.cycle(0)))

    } else {
      MemCycleProperties.smallValueInCycle(classicCycleIntegral.cycle, position)
      assert(classicCycleIntegral.cycle.values(position) == classicCycleIntegral.cycle(position))

      assertFirstValuesAsSliceEqualsModValuesAsList(classicCycleIntegral, position - 1)
      assert(ListUtilsProperties.assertAppendToSlice(classicCycleIntegral.cycle.values, 0, position))

      val prevValuesAsList = getModValuesAsList(classicCycleIntegral,    position - 1)
      val prevFirstValues  = getFirstValuesAsSlice(classicCycleIntegral, position - 1)

      assert(firstValues  == prevFirstValues  ++ List(classicCycleIntegral.cycle(position)))
      assert(valuesAsList == prevValuesAsList ++ List(classicCycleIntegral.cycle.values(position)))

      assert(ListUtils.sum(prevValuesAsList) == ListUtils.sum(prevFirstValues))
      assert(prevValuesAsList == prevFirstValues)
    }
    ListUtils.sum(valuesAsList) == ListUtils.sum(firstValues) &&
    valuesAsList == firstValues
  }.holds
}
