package v1.cycle.integral.properties

import stainless.collection.List
import v1.cycle.integral.CycleIntegral
import stainless.lang.*
import stainless.proof.check
import v1.Calc
import v1.cycle.properties.CycleProperties
import v1.list.ListUtils
import v1.list.properties.ListUtilsProperties
import verification.Helper.equality

import scala.annotation.tailrec

object CycleIntegralProperties {

  def assertCycleIntegralEqualsSumFirstPosition(cycleIntegral: CycleIntegral): Boolean = {
    val smallList = List(cycleIntegral.initialValue) ++ List(cycleIntegral.cycle(0))
    check(ListUtils.sum(List()) == BigInt(0))
    ListUtilsProperties.listAddValueTail(List(), cycleIntegral.initialValue)
    ListUtilsProperties.listAddValueTail(List(cycleIntegral.initialValue), cycleIntegral.cycle(0))
    check(ListUtils.sum(smallList) == cycleIntegral.initialValue + cycleIntegral.cycle(0))
    check(cycleIntegral(0) == cycleIntegral.initialValue + cycleIntegral.cycle(0))
    check(smallList == getFirstValuesAsSlice(cycleIntegral, 0))
    ListUtils.sum(getFirstValuesAsSlice(cycleIntegral, 0)) == cycleIntegral(0)
  }.holds

  def assertCycleIntegralEqualsSumSmallPositions(cycleIntegral: CycleIntegral, position: BigInt): Boolean = {
    require(position < cycleIntegral.size)
    require(position > 0)
    require(ListUtils.sum(getFirstValuesAsSlice(cycleIntegral, position - 1)) == cycleIntegral(position - 1))

    check(assertNextPosition(cycleIntegral, position))
    check(cycleIntegral(position) == cycleIntegral.cycle(position) + cycleIntegral(position - 1))
    check(CycleProperties.smallValueInCycle(cycleIntegral.cycle, position))
    check(cycleIntegral.cycle(position) == cycleIntegral.cycle.values(position))
    check(ListUtils.sum(getFirstValuesAsSlice(cycleIntegral, position - 1)) == cycleIntegral(position - 1))

    val prev = getFirstValuesAsSlice(cycleIntegral, position - 1)
    val prevSum = ListUtils.sum(prev)
    check(prevSum == cycleIntegral(position - 1))

    val currentList = List(cycleIntegral.cycle.values(position)) ++ prev
    val currentValue = cycleIntegral.cycle(position)
    val currentSum = ListUtils.sum(prev) + currentValue
    check(ListUtilsProperties.listAddValueTail(prev, currentValue))
    check(ListUtils.sum(prev) + currentValue == ListUtils.sum(currentList))
    check(assertNextPosition(cycleIntegral = cycleIntegral, position = position))
    check(
      equality(
        cycleIntegral(position), //                                     is equals to
        cycleIntegral.cycle(position) + cycleIntegral(position - 1), // is equals to
        cycleIntegral.cycle(position) + prevSum, //                     is equals to
        cycleIntegral.cycle.values(position) + prevSum, //              is equals to
        currentSum, //                                                  is equals to
        ListUtils.sum(currentList), //                                  is equals to
        ListUtils.sum(getFirstValuesAsSlice(cycleIntegral, position))
      )
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
  def assertCycleIntegralEqualsSum(cycleIntegral: CycleIntegral, position: BigInt): Boolean = {
    require(position < cycleIntegral.size)
    require(position >= 0)
    decreases(position)

    if (position == 0 ) {
      check(assertCycleIntegralEqualsSumFirstPosition(cycleIntegral))
    } else {
      check(assertCycleIntegralEqualsSum(cycleIntegral = cycleIntegral, position = position - 1))
      check(assertCycleIntegralEqualsSumSmallPositions(cycleIntegral = cycleIntegral, position = position))
    }
    ListUtils.sum(getFirstValuesAsSlice(cycleIntegral, position)) ==
      cycleIntegral(position)
  }.holds

  def assertNextPosition(cycleIntegral: CycleIntegral, position: BigInt): Boolean = {
    require(position > 0)
    cycleIntegral(position) == cycleIntegral(position - 1) + cycleIntegral.cycle(position)
  }.holds

  def assertDiffEqualsCycleValue(cycleIntegral: CycleIntegral, position: BigInt): Boolean = {
    require(position >= 0)
    check(cycleIntegral(position + 1) == cycleIntegral(position) + cycleIntegral.cycle(position + 1))
    cycleIntegral(position + 1) - cycleIntegral(position) == cycleIntegral.cycle(position + 1)
  }.holds

  def assertSameDiffAfterCycle(iCycle: CycleIntegral, position: BigInt): Boolean = {
    require(position >= 0)

    val a = position
    val b = position + 1
    val c = a + iCycle.size
    val d = b + iCycle.size

    assertDiffEqualsCycleValue(cycleIntegral = iCycle, position = a)
    check(iCycle(b) - iCycle(a) == iCycle.cycle(b))

    assertDiffEqualsCycleValue(cycleIntegral = iCycle, position = c)
    check(iCycle(d) - iCycle(c) == iCycle.cycle(d))

    CycleProperties.valueMatchAfterManyLoopsInBoth(iCycle.cycle, a, 0, 1)
    CycleProperties.valueMatchAfterManyLoopsInBoth(iCycle.cycle, b, 0, 1)

    check(iCycle.cycle(d) == iCycle.cycle(b))
    check(iCycle.cycle(c) == iCycle.cycle(a))

    iCycle(b) - iCycle(a) == iCycle(d) - iCycle(c)
  }.holds

  def assertLastElementBeforeLoop(iCycle: CycleIntegral): Boolean = {
    assertCycleIntegralEqualsSum(iCycle, iCycle.size - 1)
    iCycle(iCycle.size - 1) == ListUtils.sum(getFirstValuesAsSlice(iCycle, iCycle.size - 1))
  }.holds

  def assertNextLoop(iCycle: CycleIntegral, position: BigInt): Boolean = {
    require(position >= 0)
    decreases(position)

    //    if (position < iCycle.size) {
    //      assertCycleIntegralEqualsSum(iCycle, iCycle.size - 1)
    //      iCycle(position) == ListUtils.sum(getFirstValuesAsSlice(iCycle, position))
    if (position == 0) {
      check(iCycle(position) == ListUtils.sum(getModValuesAsList(iCycle, position)))
      iCycle(position) == iCycle.cycle(0) + iCycle.initialValue &&
        iCycle(position) == ListUtils.sum(getModValuesAsList(iCycle, position))
    } else {
      // 1000, [1,10,100]
      // 1001, 1011, 1111,   1112, 1122, 1222, 1223, 1233, 1333, ...

      if (position > iCycle.size ) {
        assertSameDiffAfterCycle(iCycle, position - iCycle.size)
        check(iCycle(position - iCycle.size) - iCycle(position - iCycle.size - 1) == iCycle(position) - iCycle(position - 1))
        check(iCycle(position - 1) + iCycle(position - iCycle.size) - iCycle(position - iCycle.size - 1) == iCycle(position))
        check(iCycle(position - 1) + iCycle.cycle(position - iCycle.size) == iCycle(position))
        check(CycleProperties.valueMatchAfterManyLoopsInBoth(iCycle.cycle, position - iCycle.size, 0, 1))
      }
      assertNextLoop(iCycle, position - 1)
      check(iCycle(position - 1) == ListUtils.sum(getModValuesAsList(iCycle, position - 1)))
      check(ListUtilsProperties.listAddValueTail(getModValuesAsList(iCycle, position - 1), iCycle.cycle(position)))
      iCycle(position) == iCycle.cycle(position) + iCycle(position - 1) &&
        iCycle(position) == ListUtils.sum(getModValuesAsList(iCycle, position))
    }
  }.holds


  def assertNextMatchSum(iCycle: CycleIntegral, position: BigInt): Boolean = {
    require(position >= 0)
    check(assertNextLoop(iCycle, position))
    val listModValues = getModValuesAsList(iCycle, position)
    ListUtilsProperties.assertSumIsSum(listModValues)
    iCycle(position) == ListUtils.sum(listModValues)
  }.holds

  def assertDivModCalcForCycleIntegral(cycleIntegral: CycleIntegral, position: BigInt): Boolean = {
    require(position >= 0)
    require(position < cycleIntegral.size)

    if (position < cycleIntegral.size) {
      check(Calc.div(position, cycleIntegral.size) == 0)
      check(Calc.mod(position, cycleIntegral.size) == position)
      check(assertCycleIntegralEqualsSum(cycleIntegral, position))
    }
    // else {... prove for position >

    cycleIntegral(position) ==
      Calc.div(position, cycleIntegral.size) * ListUtils.sum(cycleIntegral.cycle.values) +
        ListUtils.sum(
          getFirstValuesAsSlice(
            cycleIntegral = cycleIntegral,
            position = Calc.mod(position, cycleIntegral.size)
          )
        )
  }.holds

  def getFirstValuesAsSlice(cycleIntegral: CycleIntegral, position: BigInt): List[BigInt] = {
    require(position >= 0)
    require(position < cycleIntegral.size)
    ListUtilsProperties.listAddValueTail(cycleIntegral.cycle.values, cycleIntegral.initialValue)
    List(cycleIntegral.initialValue) ++
      ListUtils.slice(cycleIntegral.cycle.values, 0, position)
  }

  def getModValuesAsList(cycleIntegral: CycleIntegral, position: BigInt): List[BigInt] = {
    require(position >= 0)

    if (position == 0 ) {
      check(ListUtilsProperties.listAddValueTail(List(cycleIntegral.cycle(0)), cycleIntegral.initialValue))
      List(cycleIntegral.initialValue) ++ List(cycleIntegral.cycle(0))
    } else {
      val prev = getModValuesAsList(cycleIntegral, position - 1)
      check(ListUtilsProperties.listAddValueTail(prev, cycleIntegral.cycle(position)))
      List(cycleIntegral.cycle(position)) ++ prev
    }


//    ListUtilsProperties.listAddValueTail(cycleIntegral.cycle.values, cycleIntegral.initialValue)
//    List(cycleIntegral.initialValue) ++
//      ListUtils.slice(cycleIntegral.cycle.values, 0, position)
  }
}
