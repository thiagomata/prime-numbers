package v1.chapter4.cycle.integral.recursive.properties

import stainless.collection.List
import stainless.lang.*
import v1.chapter1.verification.Helper.{assert, equality}
import v1.chapter2.div.Calc
import v1.chapter3.list.{ListBoundUtils, ListUtils}
import v1.chapter3.list.properties.ListUtilsProperties
import v1.chapter4.cycle.CycleUtils
import v1.chapter4.cycle.integral.recursive.CycleIntegral
import v1.chapter4.cycle.memory.MemCycle
import v1.chapter4.cycle.memory.properties.MemCycleProperties

object CycleIntegralProperties {

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
    assert(MemCycleProperties.smallValueInCycle(cycleIntegral.cycle, position))
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
      MemCycleProperties.smallValueInCycle(cycle = cycleIntegral.cycle, key = position)
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
   * [TIMED OUT — attempt 1, 2026-06-25]
   *
   * Intended: a list-repeat helper and a lemma that repeating a cycle's gap
   * list `times` times produces a cycle integral generating the same stream.
   *
   * TIMEOUT (2 VCs, 241s) on:
   *   1. constructing `MemCycle(repeatList(...))` — the repeated list's
   *      preconditions (non-empty, etc.) are opaque to the solver because
   *      `repeatList`'s output isn't unfolded.
   *   2. the final `stretched(pos) == ci(pos)` equality.
   *
   * Lesson: building a new list via `repeatList` and proving the resulting
   * `MemCycle`/`CycleIntegral` equals the original hits the same list-builder
   * opacity that killed the walk attempts. The repeat step may be unnecessary
   * — alignment might be characterizable via the arsenal's closed form
   * directly, without constructing a stretched list. Reconsidering.
   */
//  def repeatList(list: List[BigInt], times: BigInt): List[BigInt] = {
//    require(list.nonEmpty)
//    require(times > BigInt(0))
//    decreases(times)
//    if (times == BigInt(1)) {
//      list
//    } else {
//      list ++ repeatList(list, times - BigInt(1))
//    }
//  }
//
//  def assertRepeatedCycleMatchesOriginal(
//    ci: CycleIntegral,
//    times: BigInt,
//    pos: BigInt
//  ): Boolean = {
//    require(times > BigInt(0))
//    require(pos >= BigInt(0))
//    require(ci.cycle.values.nonEmpty)
//
//    val stretched = CycleIntegral(ci.initialValue, MemCycle(repeatList(ci.cycle.values, times)))
//
//    stretched(pos) == ci(pos)
//  }.holds

  /**
   * [TIMED OUT — §5.2 Approach 2, 2026-06-25]
   *
   * Intended: §5.2 Invariance by x-fold Concatenation —
   * `CycleIntegral(init, MemCycle(repeatList(G, times))).apply(pos) ==
   *  CycleIntegral(init, MemCycle(G)).apply(pos)`.
   *
   * Attempted with smarter value-equality proof (via valueMatchAfterManyLoopsInBoth
   * + induction), but the timeouts (3 VCs, 362s) are ALL on constructing
   * `MemCycle(repeatList(...))` and accessing it. The list materialization
   * itself is opaque — regardless of how I prove the resulting values match.
   *
   * Lesson: ANY approach that constructs `MemCycle(someBuiltList)` will time
   * out, because the solver can't see through the built list's preconditions
   * or its relationship to the original. The only viable path is to NOT
   * materialize the stretched list — characterize the stretched cycle purely
   * abstractly (existence) or via the ModCycleIntegral closed form on the
   * ORIGINAL cycle (no new list).
   */
//  def assertXFoldConcatenationInvariance(
//    ci: CycleIntegral,
//    times: BigInt,
//    pos: BigInt
//  ): Boolean = {
//    require(times > BigInt(0))
//    require(pos >= BigInt(0))
//    require(ci.cycle.values.nonEmpty)
//    decreases(pos)
//
//    if (pos == BigInt(0)) {
//      val stretchedCycle = MemCycle(repeatList(ci.cycle.values, times))
//      assert(stretchedCycle(0) == ci.cycle(0))
//      CycleIntegral(ci.initialValue, stretchedCycle)(0) == ci(0)
//    } else {
//      assert(assertXFoldConcatenationInvariance(ci, times, pos - BigInt(1)))
//      val stretchedCycle = MemCycle(repeatList(ci.cycle.values, times))
//      assert(stretchedCycle(pos) == ci.cycle(pos))
//      CycleIntegral(ci.initialValue, stretchedCycle)(pos) == ci(pos)
//    }
//  }.holds
//
//  def repeatList(list: List[BigInt], times: BigInt): List[BigInt] = {
//    require(list.nonEmpty)
//    require(times > BigInt(0))
//    decreases(times)
//    if (times == BigInt(1)) {
//      list
//    } else {
//      list ++ repeatList(list, times - BigInt(1))
//    }
//  }

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
