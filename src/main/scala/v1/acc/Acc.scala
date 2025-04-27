package v1.acc

import stainless.collection.List
import stainless.lang.decreases
import stainless.lang.*
import stainless.proof.check
import v1.list.ListUtils
import v1.list.properties.ListUtilsProperties

case class Acc(list: List[BigInt], init: BigInt = 0) {

  def apply(position: BigInt): BigInt = {
    require(list.nonEmpty)
    require(position >= 0)
    require(position < list.size)
    if ( position == 0 ) {
      this.head
    } else {
      Acc(list.tail, this.head).apply(position - 1)
    }
  }

  def acc: List[BigInt] = {
    decreases(list.size)
    if (list.isEmpty) {
      list
    } else {
      List(this.head) ++ Acc(list.tail, this.head).acc
    }
  }

  def last: BigInt = {
    require(list.nonEmpty)
    acc.last
  }

  def head: BigInt = {
    require(list.nonEmpty)
    list.head + init
  }

  def tail: List[BigInt] = {
    require(list.nonEmpty)
    Acc(list.tail, this.head).acc
  }

  def isEmpty: Boolean = list.isEmpty

  def nonEmpty: Boolean = list.nonEmpty

  def size: BigInt = list.size

  def accDifferenceEqualsTailHead: Boolean = {
    require(list.size > 1)
    check(tail.head == Acc(list.tail, this.head).head)
    check(tail.head == list.tail.head + this.head)
    check(this.tail.head - this.head ==  list.tail.head + this.head - this.head)
    check(acc(1) == this.tail.head)
    check(apply(1) == this.tail.head)
    check(acc(0) == this.head)
    check(apply(1) == this.tail.head)
    check(list(1) == list.tail.head)

    check(apply(0)  == acc(0))
    check(apply(1)  == acc(1))

    apply(1) - apply(0) == list(1) &&
      acc(1) - acc(0)   == list(1)
  }.holds

  /**
   * Lemma: The difference between two consecutive accumulated values in Acc
   * equals the corresponding value from the original list.
   *
   * That is:
   * acc(position + 1) - acc(position) == list(position + 1)
   *
   * Holds for all valid `position` where 0 <= position < list.size - 1.
   */
  def accDiffMatchesList(position: BigInt): Boolean = {
    require(list.size > 1)
    require(position >= 0 && position < list.size - 1)
    decreases(position)

    if (position == 0) {
      // Base case
      check(accDifferenceEqualsTailHead)
      check(apply(0) == acc(0))
      check(apply(1) == acc(1))
      check(
        acc(position + 1) - acc(position) == list(position + 1) &&
        acc(position) == apply(position)
      )
    } else {
      check(position > 0 )
      check(position < list.size - 1)
      check(position - 1 < list.size )

      // Inductive step
      val next = Acc(list.tail, this.head)
      check(next.size == this.size - 1)
      check(this.tail == next.acc)
      check(next.accDiffMatchesList(position - 1))

      // link this values and next values
      check(apply(position)     == next.apply(position - 1))
      check(apply(position + 1) == next.apply(position))

      check(apply(position) == acc(position))
      check(apply(position + 1) == acc(position + 1))
    }
    acc(position + 1) - acc(position) == list(position + 1) &&
      acc(position + 1) == apply(position + 1) &&
      acc(position) == apply(position)
  }.holds

  /**
   * Lemma: The `apply(position)` method returns the same value as the value at
   * index `position` in the accumulated list `acc`.
   *
   * That is:
   * apply(position) == acc(position)
   *
   * Holds for all valid `position` in the bounds of the list.
   */
  def assertAccMatchesApply(position: BigInt): Boolean = {
    require(list.nonEmpty)
    require(position >= 0 && position < list.size)
    decreases(position)

    assertSizeAccEqualsSizeList(list, init)
    check(list.size == acc.size)

    if (position == 0) {
      check(apply(0) == head)
      check(acc(0) == head)
      acc(position) == apply(position)
    } else {
      check(position > 0 )
      check(position < list.size)
      check(position - 1 < list.size - 1)

      val next = Acc(list.tail, this.head)
      check(this.tail == next.acc)

      check(apply(position) == next.apply(position - 1))
      check(acc == List(this.head) ++ next.acc)
      check(acc.tail == next.acc)

      check(acc.nonEmpty)
      check(list.size == acc.size)
      check(position < acc.size)
      check(ListUtilsProperties.assertTailShiftPosition(acc, position))
      check(acc.tail(position - 1) == acc(position))
      check(acc(position) == acc.tail(position - 1))
      check(acc.tail(position - 1) == next.acc(position - 1))

      check(acc(position) == next.acc(position - 1))
      check(apply(position) == next.apply(position - 1))

      check(next.assertAccMatchesApply(position - 1))
      check(next.acc(position - 1) == next.apply(position - 1))
      check(acc(position) == apply(position))
    }
    acc(position) == apply(position)
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
   * @return true if the property holds
   */
  def assertSizeAccEqualsSizeList(list: List[BigInt], init: BigInt = 0): Boolean = {
    decreases(list)
    require(list.nonEmpty)

    val current = Acc(list, init)

    if (list.size == 1) {
      check(current.list.size == 1)
      check(current.acc.size == 1)
      check(current.acc.size == current.list.size)
    } else {
      val next = Acc(list.tail, current.head)

      assertSizeAccEqualsSizeList(next.list, next.init)
      check(next.acc.size == next.list.size)
      check(current.acc == List(current.head) ++ next.acc)
      check(current.acc.size == 1 + next.acc.size)
      check(1 + list.tail.size == list.size)
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
   * @return true if the property holds
   */
  def lastEqualsSum: Boolean = {
    require(list.nonEmpty)
    decreases(list.size)

    if (list.size == 1) {
      check(last == list.head + init)
      check(last == init + ListUtils.sum(list))
    } else {
      val next = Acc(list.tail, list.head + init)
      check(next.lastEqualsSum)
      check(this.tail == next.acc)
      check(this.tail.last == next.acc.last)
      check(next.last == next.acc.last)
      check(next.last == this.last)
      check(next.last == next.init + ListUtils.sum(next.list))
      check(next.last == init + list.head + ListUtils.sum(next.list))
      check(this.last == init + list.head + ListUtils.sum(next.list))
      check(ListUtilsProperties.listSumAddValue(next.list,list.head))
      check(list.head + ListUtils.sum(next.list) == ListUtils.sum(List(list.head) ++ list.tail))
      check(list.head + ListUtils.sum(next.list) == ListUtils.sum(list))
      check(this.last == init + ListUtils.sum(list))
    }
    last == init + ListUtils.sum(list)
  }.holds
}