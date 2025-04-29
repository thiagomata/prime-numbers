package v1.list.integral

import stainless.collection.List
import stainless.lang.*
import v1.list.ListUtils
import v1.list.properties.ListUtilsProperties
import verification.Helper.assert

case class Integral(list: List[BigInt], init: BigInt = 0) {

  def apply(position: BigInt): BigInt = {
    require(list.nonEmpty)
    require(position >= 0)
    require(position < list.size)
    if ( position == 0 ) {
      this.head
    } else {
      Integral(list.tail, this.head).apply(position - 1)
    }
  }

  def acc: List[BigInt] = {
    decreases(list.size)
    if (list.isEmpty) {
      list
    } else {
      List(this.head) ++ Integral(list.tail, this.head).acc
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
    Integral(list.tail, this.head).acc
  }

  def isEmpty: Boolean = list.isEmpty

  def nonEmpty: Boolean = list.nonEmpty

  def size: BigInt = list.size

  /**
   * Lemma: The difference between the first two accumulated values in Acc
   * equals the second element of the original list.
   *
   * That is:
   * acc(1) - acc(0) == list(1)
   *
   * Holds for all valid `position` where 0 <= position < list.size - 1.
   */
  def assertAccDifferenceEqualsTailHead: Boolean = {
    require(list.size > 1)
    assert(tail.head == Integral(list.tail, this.head).head)
    assert(tail.head == list.tail.head + this.head)
    assert(this.tail.head - this.head ==  list.tail.head + this.head - this.head)
    assert(acc(1) == this.tail.head)
    assert(apply(1) == this.tail.head)
    assert(acc(0) == this.head)
    assert(apply(1) == this.tail.head)
    assert(list(1) == list.tail.head)

    assert(apply(0)  == acc(0))
    assert(apply(1)  == acc(1))

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
  def assertAccDiffMatchesList(position: BigInt): Boolean = {
    require(list.size > 1)
    require(position >= 0 && position < list.size - 1)
    decreases(position)

    if (position == 0) {
      // Base case
      assert(assertAccDifferenceEqualsTailHead)
      assert(apply(0) == acc(0))
      assert(apply(1) == acc(1))
      assert(
        acc(position + 1) - acc(position) == list(position + 1) &&
        acc(position) == apply(position)
      )
    } else {
      assert(position > 0 )
      assert(position < list.size - 1)
      assert(position - 1 < list.size )

      // Inductive step
      val next = Integral(list.tail, this.head)
      assert(next.size == this.size - 1)
      assert(this.tail == next.acc)
      assert(next.assertAccDiffMatchesList(position - 1))

      // link this values and next values
      assert(apply(position)     == next.apply(position - 1))
      assert(apply(position + 1) == next.apply(position))

      assert(apply(position) == acc(position))
      assert(apply(position + 1) == acc(position + 1))
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
    assert(list.size == acc.size)

    if (position == 0) {
      assert(apply(0) == head)
      assert(acc(0) == head)
      acc(position) == apply(position)
    } else {
      assert(position > 0 )
      assert(position < list.size)
      assert(position - 1 < list.size - 1)

      val next = Integral(list.tail, this.head)
      assert(this.tail == next.acc)

      assert(apply(position) == next.apply(position - 1))
      assert(acc == List(this.head) ++ next.acc)
      assert(acc.tail == next.acc)

      assert(acc.nonEmpty)
      assert(list.size == acc.size)
      assert(position < acc.size)
      assert(ListUtilsProperties.assertTailShiftPosition(acc, position))
      assert(acc.tail(position - 1) == acc(position))
      assert(acc(position) == acc.tail(position - 1))
      assert(acc.tail(position - 1) == next.acc(position - 1))

      assert(acc(position) == next.acc(position - 1))
      assert(apply(position) == next.apply(position - 1))

      assert(next.assertAccMatchesApply(position - 1))
      assert(next.acc(position - 1) == next.apply(position - 1))
      assert(acc(position) == apply(position))
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
//    require(list.nonEmpty)

    val current = Integral(list, init)

    if (list.isEmpty) {
      assert(current.list.size == 0)
      assert(current.acc.size == 0)
    }
    else if (list.size == 1) {
      assert(current.list.size == 1)
      assert(current.acc.size == 1)
      assert(current.acc.size == current.list.size)
    } else {
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
   * @return true if the property holds
   */
  def assertLastEqualsSum: Boolean = {
    require(list.nonEmpty)
    decreases(list.size)

    if (list.size == 1) {
      assert(last == list.head + init)
      assert(last == init + ListUtils.sum(list))
    } else {
      val next = Integral(list.tail, list.head + init)
      assert(next.assertLastEqualsSum)
      assert(this.tail == next.acc)
      assert(this.tail.last == next.acc.last)
      assert(next.last == next.acc.last)
      assert(next.last == this.last)
      assert(next.last == next.init + ListUtils.sum(next.list))
      assert(next.last == init + list.head + ListUtils.sum(next.list))
      assert(this.last == init + list.head + ListUtils.sum(next.list))
      assert(ListUtilsProperties.listSumAddValue(next.list,list.head))
      assert(list.head + ListUtils.sum(next.list) == ListUtils.sum(List(list.head) ++ list.tail))
      assert(list.head + ListUtils.sum(next.list) == ListUtils.sum(list))
      assert(this.last == init + ListUtils.sum(list))
    }
    last == init + ListUtils.sum(list)
  }.holds
}