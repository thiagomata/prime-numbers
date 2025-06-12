package v1.list.integral.properties

import stainless.collection.List
import v1.list.integral.Integral
import verification.Helper.assert
import stainless.lang.*
import v1.list.ListUtils
import v1.list.properties.ListUtilsProperties

object IntegralProperties {

  /**
   * Lemma: The first element of the accumulated list `acc` is equal to the
   * first element of the original list `list` plus the initial value.
   *
   * That is:
   * acc(0) == list(0) + init
   *
   * @param integral Integral the integral of the lemma
   * @return Boolean true if the property holds
   */
  def assertHeadValueMatchDefinition(integral: Integral): Boolean = {
    require(integral.list.nonEmpty)
    assert(integral.head == integral.list.head + integral.init)
    assert(integral.apply(0) == integral.head)
    assert(integral.acc(0) == integral.head)
    assert(integral.acc(0) == integral.apply(0))
    integral.head == integral.list.head + integral.init
  }.holds

  /**
   * Lemma: The difference between the first two accumulated values in Acc
   * equals the second element of the original list.
   *
   * That is:
   * acc(1) - acc(0) == list(1)
   *
   * Holds for all valid `position` where 0 <= position < list.size - 1.
   * @param integral Integral the integral of the lemma
   * @return Boolean true if the property holds
   */
  def assertAccDifferenceEqualsTailHead(integral: Integral): Boolean = {
    require(integral.list.size > 1)

    assert(integral.tail.head == Integral(integral.list.tail, integral.head).head)
    assert(integral.tail.head == integral.list.tail.head + integral.head)
    assert(
      integral.tail.head - integral.head ==
      integral.list.tail.head + integral.head - integral.head
    )
    assert(integral.acc(1)   == integral.tail.head)
    assert(integral.apply(1) == integral.tail.head)
    assert(integral.acc(0)   == integral.head)
    assert(integral.list(1)  == integral.list.tail.head)

    assert(integral.apply(0)  == integral.acc(0))
    assert(integral.apply(1)  == integral.acc(1))

    integral.apply(1) - integral.apply(0) == integral.list(1) &&
      integral.acc(1) - integral.acc(0)   == integral.list(1)
  }.holds


  /**
   * Lemma: The difference between two consecutive accumulated values in Acc
   * equals the corresponding value from the original list.
   *
   * That is:
   * acc(position + 1) - acc(position) == list(position + 1)
   *
   * Holds for all valid `position` where 0 <= position < list.size - 1.
   * @param integral Integral the integral of the lemma
   * @param position BigInt the position in the acc list
   * @return Boolean true if the property holds
   */
  def assertAccDiffMatchesList(integral: Integral, position: BigInt): Boolean = {
    require(integral.list.size > 1)
    require(position >= 0 && position < integral.list.size - 1)
    decreases(position)

    if (position == 0) {
      // base case
      assert(IntegralProperties.assertAccDifferenceEqualsTailHead(integral))
      assert(integral.apply(0) == integral.acc(0))
      assert(integral.apply(1) == integral.acc(1))
      assert(
        integral.acc(position + 1) - integral.acc(position) == integral.list(position + 1) &&
          integral.acc(position) == integral.apply(position)
      )
    } else {
      assert(position > 0 )
      assert(position < integral.list.size - 1)
      assert(position - 1 < integral.list.size )

      // Inductive step
      val next = Integral(integral.list.tail, integral.head)
      assert(next.size == integral.size - 1)
      assert(integral.tail == next.acc)
      assert(assertAccDiffMatchesList(next, position - 1))

      // link this values and next values
      assert(integral.apply(position)     == next.apply(position - 1))
      assert(integral.apply(position + 1) == next.apply(position))

      assert(integral.apply(position) == integral.acc(position))
      assert(integral.apply(position + 1) == integral.acc(position + 1))
    }
    integral.acc(position + 1) - integral.acc(position) == integral.list(position + 1) &&
      integral.acc(position + 1) == integral.apply(position + 1) &&
      integral.acc(position) == integral.apply(position)
  }.holds

  /**
   * Lemma: The `apply(position)` method returns the same value as the value at
   * index `position` in the accumulated list `acc`.
   *
   * That is:
   * apply(position) == acc(position)
   *
   * Holds for all valid `position` in the bounds of the list.
   * @param integral Integral the integral of the lemma
   * @param position BigInt the position in the acc list
   * @return Boolean true if the property holds
   */
  def assertAccMatchesApply(integral: Integral, position: BigInt): Boolean = {
    require(integral.list.nonEmpty)
    require(position >= 0 && position < integral.list.size)
    decreases(position)

    assert(assertSizeAccEqualsSizeList(integral.list, integral.init))
    assert(integral.list.size == integral.acc.size)

    if (position == 0) {
      // base case
      assert(integral.apply(0) == integral.head)
      assert(integral.acc(0) == integral.head)
      integral.acc(position) == integral.apply(position)
    } else {
      // inductive step
      assert(position > 0 )
      assert(position < integral.list.size)
      assert(position - 1 < integral.list.size - 1)

      val next = Integral(integral.list.tail, integral.head)
      assert(integral.tail == next.acc)

      assert(integral.apply(position) == next.apply(position - 1))
      assert(integral.acc == List(integral.head) ++ next.acc)
      assert(integral.acc.tail == next.acc)

      assert(integral.acc.nonEmpty)
      assert(integral.list.size == integral.acc.size)
      assert(position < integral.acc.size)
      assert(ListUtilsProperties.assertTailShiftLeft(integral.acc, position))
      assert(integral.acc.tail(position - 1) == integral.acc(position))
      assert(integral.acc(position) == integral.acc.tail(position - 1))
      assert(integral.acc.tail(position - 1) == next.acc(position - 1))

      assert(integral.acc(position) == next.acc(position - 1))
      assert(integral.apply(position) == next.apply(position - 1))

      assert(assertAccMatchesApply(next, position - 1))
      assert(next.acc(position - 1) == next.apply(position - 1))
      assert(integral.acc(position) == integral.apply(position))
    }
    integral.acc(position) == integral.apply(position)
  }.holds


  /**
   * Lemma: The size of the accumulated list `acc` is equal to the size of the
   * original list `list`.
   *
   * That is:
   * acc.size == list.size
   *
   * @param list List[BigInt] the original list
   * @param init BigInt the initial value for the accumulation
   * @return Boolean true if the property holds
   */
  def assertSizeAccEqualsSizeList(list: List[BigInt], init: BigInt = 0): Boolean = {
    decreases(list)

    val current = Integral(list, init)

    if (list.isEmpty) {
      // base case for empty list
      assert(current.list.size == 0)
      assert(current.acc.size == 0)
    }
    else if (list.size == 1) {
      // base case for single element list
      assert(current.list.size == 1)
      assert(current.acc.size == 1)
      assert(current.acc.size == current.list.size)
    } else {
      // inductive step for lists with more than one element
      val next = Integral(list.tail, current.head)

      assertSizeAccEqualsSizeList(next.list, next.init)
      assert(next.acc.size == next.list.size)
      assert(current.acc == List(current.head) ++ next.acc)
      assert(current.acc.size == 1 + next.acc.size)
      assert(1 + list.tail.size == list.size)
    }
    current.acc.size == current.list.size
  }.holds

  /**
   * Lemma: The last element of the accumulated list `acc` is equal to the sum
   * of all elements in the original list `list`.
   *
   * That is:
   * acc.last == init + ListUtils.sum(list)
   *
   * @param integral Integral the integral of the lemma
   * @return Boolean true if the property holds
   */
  def assertLastEqualsSum(integral: Integral): Boolean = {
    require(integral.list.nonEmpty)
    decreases(integral.list.size)

    if (integral.list.size == 1) {
      // base case
      assert(integral.last == integral.list.head + integral.init)
      assert(integral.last == integral.init + ListUtils.sum(integral.list))
    } else {
      // inductive step
      val next = Integral(integral.list.tail, integral.list.head + integral.init)
      assert(assertLastEqualsSum(next))
      assert(integral.tail == next.acc)
      assert(integral.tail.last == next.acc.last)
      assert(next.last == next.acc.last)
      assert(next.last == integral.last)
      assert(next.last == next.init + ListUtils.sum(next.list))
      assert(next.last == integral.init + integral.list.head + ListUtils.sum(next.list))
      assert(integral.last == integral.init + integral.list.head + ListUtils.sum(next.list))
      assert(ListUtilsProperties.listSumAddValue(next.list,integral.list.head))
      assert(integral.list.head + ListUtils.sum(next.list) == ListUtils.sum(List(integral.list.head) ++ integral.list.tail))
      assert(integral.list.head + ListUtils.sum(next.list) == ListUtils.sum(integral.list))
      assert(integral.last == integral.init + ListUtils.sum(integral.list))
    }
    integral.last == integral.init + ListUtils.sum(integral.list)
  }.holds

  /**
   * The integral of a list is defined as the sum of all elements in the list
   * plus the initial value.
   *
   * That is:
   * integral.apply(position) == init + ListUtils.sum(list[0..position])
   *
   * @param integral Integral the integral of the lemma
   * @param position BigInt the position in the list
   * @return Boolean true if the property holds
   */
  def assertIntegralEqualsSum(integral: Integral, position: BigInt): Boolean = {
    require(integral.list.nonEmpty)
    require(position >= 0 && position < integral.list.size)
    require(integral.list.size > 1)
    decreases(position)

    assert(assertSizeAccEqualsSizeList(integral.list, integral.init))

    if (position == 0) {
      assert(assertHeadValueMatchDefinition(integral))
      assert(ListUtils.slice(integral.list, 0, position) == List(integral.list.head))
      assert(integral.apply(0) == integral.init + ListUtils.sum(List(integral.list.head)))
      assert(integral.apply(0) == integral.init + ListUtils.sum(ListUtils.slice(integral.list, 0, position)))
    } else {
      assert(assertIntegralEqualsSum(integral, position - 1))
      assert(position > 0 )
      assert(position < integral.list.size)
      assert(position - 1 < integral.list.size - 1)
      assert(integral.list.size == integral.acc.size)
      assert(integral.list.size > 1)
      assert(assertAccDiffMatchesList(integral, position - 1))

      val prevList = ListUtils.slice(integral.list, 0, position - 1)
      val prevSum = ListUtils.sum(prevList)
      assert(integral.apply(position - 1) == integral.init + prevSum)
      assert(integral.apply(position) == integral.apply(position - 1) + integral.list(position))
      assert(integral.apply(position) == integral.init + prevSum + integral.list(position))
      assert(ListUtilsProperties.listSumAddValue(integral.list, integral.list(position)))
      assert(ListUtilsProperties.assertAppendToSlice(integral.list, 0, position))
      assert(ListUtils.slice(integral.list, 0, position) == ListUtils.slice(integral.list, 0, position - 1) ++ List(integral.list(position)))
      assert(integral.apply(position) == integral.init + ListUtils.sum(ListUtils.slice(integral.list, 0, position)))
    }
    integral.apply(position) == integral.init + ListUtils.sum(ListUtils.slice(integral.list, 0, position))
  }.holds


  /**
   * Lemma: The last element of the accumulated list `acc` is equal
   * to apply in the last position (size - 1).
   *
   * That is:
   * integral.acc.last == integral.acc(size - 1)
   *
   * @param integral Integral the integral of the lemma
   * @return Boolean true if the property holds
   */
  def assertLast(integral: Integral): Boolean = {
    require(integral.list.nonEmpty)
    assert(
      integral.last ==
        integral.acc.last
    )
    assert(ListUtilsProperties.assertLastEqualsLastPosition(integral.acc))
    assert(assertSizeAccEqualsSizeList(integral.list, integral.init))
    assert(
      integral.acc.last ==
        integral.acc(integral.acc.size - 1)
    )
    assertAccMatchesApply(integral, integral.size - 1)
    assert(
      integral.acc(integral.size - 1) ==
        integral.apply(integral.size - 1)
    )
    integral.apply(integral.size - 1) == integral.last
  }.holds
}
