package v1.chapter3.list

import stainless.collection.List
import stainless.lang.decreases
import stainless.lang.BooleanDecorations

import scala.annotation.tailrec

object ListBoundUtils {

  @tailrec
  def allGreaterThan(list: List[BigInt], value: BigInt): Boolean = {
    decreases(list)
    if (list.isEmpty) true
    else list.head > value && allGreaterThan(list.tail, value)
  }

  def assertAppendGreaterThan(listA: List[BigInt], listB: List[BigInt], value: BigInt): Boolean = {
    require(allGreaterThan(listA, value))
    require(allGreaterThan(listB, value))
    decreases(listA.size)
    if (listA.isEmpty) {
      allGreaterThan(listA ++ listB, value)
    } else {
      assert(assertAppendGreaterThan(listA.tail, listB, value))
      assert(allGreaterThan(listA.tail ++ listB, value))
      assert(listA.head > value)
      allGreaterThan(listA ++ listB, value)
    }
  }.holds

  /**
   * Splitting a lower-bounded list preserves the bound on BOTH halves.
   *
   * `allGreaterThan(list, value)` and `(front, back) = splitAt(list, index)`
   * together imply `allGreaterThan(front, value) && allGreaterThan(back, value)`.
   *
   * This is the ch3 home for the bound-preservation fact that the rotation
   * theory needs; it mirrors the ch6 `SieveUtils.assertSplitAtPreservesAllGreaterThan`
   * (which will eventually delegate here once the move is complete).
   */
  def assertSplitAtPreservesAllGreaterThan(list: List[BigInt], index: BigInt, value: BigInt): Boolean = {
    require(index >= 0 && index <= list.size)
    require(allGreaterThan(list, value))
    decreases(index)
    val (front, back) = ListUtils.splitAt(list, index)
    if (index == BigInt(0)) {
      assert(front == List.empty[BigInt])
      assert(back == list)
      allGreaterThan(front, value) && allGreaterThan(back, value)
    } else {
      assert(list.nonEmpty)
      assert(list.head > value)
      assert(allGreaterThan(list.tail, value))
      assert(assertSplitAtPreservesAllGreaterThan(list.tail, index - BigInt(1), value))
      val (tailFront, tailBack) = ListUtils.splitAt(list.tail, index - BigInt(1))
      assert(front == list.head :: tailFront)
      assert(back == tailBack)
      assert(allGreaterThan(tailFront, value))
      assert(allGreaterThan(tailBack, value))
      allGreaterThan(front, value) && allGreaterThan(back, value)
    }
  }.holds

  def allNonNegative(list: List[BigInt]): Boolean = allGreaterThan(list, BigInt(-1))
  def allPositive(list: List[BigInt]): Boolean = allGreaterThan(list, BigInt(0))
  def allGreaterThanOne(list: List[BigInt]): Boolean = allGreaterThan(list, BigInt(1))

  @tailrec
  def checkNonNegative(list: List[BigInt]): Boolean = {
    decreases(list)
    if (list.isEmpty) true
    else list.head >= 0 && checkNonNegative(list.tail)
  }

  @tailrec
  def allLessThan(list: List[BigInt], bound: BigInt): Boolean = {
    decreases(list)
    if (list.isEmpty) true
    else list.head < bound && allLessThan(list.tail, bound)
  }

  def assertAppendLessThan(listA: List[BigInt], listB: List[BigInt], bound: BigInt): Boolean = {
    require(allLessThan(listA, bound))
    require(allLessThan(listB, bound))
    decreases(listA.size)
    if (listA.isEmpty) {
      allLessThan(listA ++ listB, bound)
    } else {
      assert(assertAppendLessThan(listA.tail, listB, bound))
      assert(allLessThan(listA.tail ++ listB, bound))
      assert(listA.head < bound)
      allLessThan(listA ++ listB, bound)
    }
  }.holds

  /**
   * Splitting an upper-bounded list preserves the bound on BOTH halves.
   *
   * Mirror of `assertSplitAtPreservesAllGreaterThan` for `allLessThan`.
   */
  def assertSplitAtPreservesAllLessThan(list: List[BigInt], index: BigInt, bound: BigInt): Boolean = {
    require(index >= 0 && index <= list.size)
    require(allLessThan(list, bound))
    decreases(index)
    val (front, back) = ListUtils.splitAt(list, index)
    if (index == BigInt(0)) {
      assert(front == List.empty[BigInt])
      assert(back == list)
      allLessThan(front, bound) && allLessThan(back, bound)
    } else {
      assert(list.nonEmpty)
      assert(list.head < bound)
      assert(allLessThan(list.tail, bound))
      assert(assertSplitAtPreservesAllLessThan(list.tail, index - BigInt(1), bound))
      val (tailFront, tailBack) = ListUtils.splitAt(list.tail, index - BigInt(1))
      assert(front == list.head :: tailFront)
      assert(back == tailBack)
      assert(allLessThan(tailFront, bound))
      assert(allLessThan(tailBack, bound))
      allLessThan(front, bound) && allLessThan(back, bound)
    }
  }.holds

  def assertTransitiveLessThan(list: List[BigInt], bound: BigInt, bound2: BigInt): Boolean = {
    require(allLessThan(list, bound))
    require(bound <= bound2)
    decreases(list)
    if (list.isEmpty) true
    else {
      assert(list.head < bound)
      assert(list.head < bound2)
      assert(allLessThan(list.tail, bound))
      assert(assertTransitiveLessThan(list.tail, bound, bound2))
      allLessThan(list, bound2)
    }
  }.holds

  def assertGreaterThanAtIndex(list: List[BigInt], value: BigInt, pos: BigInt): Boolean = {
    require(allGreaterThan(list, value))
    require(pos >= 0 && pos < list.size)
    decreases(pos)
    if (pos == BigInt(0)) {
      list.head > value
    } else {
      assert(assertGreaterThanAtIndex(list.tail, value, pos - 1))
      assert(assertTailShiftLeft(list, pos))
      list(pos) > value
    }
  }.holds

  def assertGreaterThanHeadTail(list: List[BigInt], value: BigInt): Boolean = {
    require(allGreaterThan(list, value))
    require(list.nonEmpty)
    list.head > value && allGreaterThan(list.tail, value)
  }.holds

  def assertTailShiftLeft[T](list: List[T], position: BigInt): Boolean = {
    require(list.nonEmpty)
    require(position >= 0 && position < list.size)
    decreases(position)

    if (position == 0) {
      list(position) == list.head
    } else {
      assert(list == List(list.head) ++ list.tail)
      assert(list(position) == list.apply(position))
      assert(assertTailShiftLeft(list.tail, position - 1))
      assert(list.apply(position) == list.tail.apply(position - 1))
      list(position) == list.tail(position - 1)
    }
  }.holds
}
