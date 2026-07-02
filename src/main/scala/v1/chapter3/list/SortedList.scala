package v1.chapter3.list

import stainless.collection.List
import stainless.lang.*

case class SortedList(list: List[BigInt]) {
  require(SortedList.isAscending(list))

  def isEmpty: Boolean = list.isEmpty
  def size: BigInt = list.size
  def head: BigInt = { require(list.nonEmpty); list.head }
  def last: BigInt = { require(list.nonEmpty); list.last }
  def apply(index: BigInt): BigInt = { require(index >= 0 && index < list.size); list(index) }

  def insert(x: BigInt): SortedList = {
    SortedList.assertInsertSortedAscending(x, list)
    SortedList(SortedList.insertSorted(x, list))
  }

  def remove(index: BigInt): SortedList = {
    require(index >= 0 && index < list.size)
    SortedList.assertRemoveKeepsAscending(list, index)
    SortedList(SortedList.removeAt(list, index))
  }

  def tail: SortedList = {
    require(list.nonEmpty)
    SortedList.assertTailAscending(list)
    SortedList(list.tail)
  }
}

object SortedList {
  def isAscending(list: List[BigInt]): Boolean = {
    decreases(list.size)
    if (list.isEmpty || list.tail.isEmpty) true
    else if (list.head >= list.tail.head) false
    else isAscending(list.tail)
  }

  def fromUnsorted(list: List[BigInt]): SortedList = {
    assert(assertSortFilteredAscending(list))
    SortedList(sortFiltered(list))
  }

  val empty: SortedList = SortedList(List.empty[BigInt])

  /**
   * Insert one value while preserving strict ascending order when the input
   * list is already sorted.
   *
   * Math:
   *
   *   isAscending(list) => isAscending(insertSorted(x, list))
   *
   * The postcondition is intentionally attached to the recursive producer so
   * later callers can reuse the sortedness fact without reopening the whole
   * insertion recursion.
   */
  def insertSorted(x: BigInt, list: List[BigInt]): List[BigInt] = {
    decreases(list.size)
    if (list.isEmpty) List(x)
    else if (x < list.head) x :: list
    else if (x == list.head) list
    else list.head :: insertSorted(x, list.tail)
  }.ensuring(res => !isAscending(list) || isAscending(res))

  /**
   * Sorting by repeated insertion always returns a strict ascending list.
   *
   * Math:
   *
   *   isAscending(sortFiltered(list))
   *
   * This postcondition is attached to the recursive producer so downstream
   * proofs can consume sortedness from the returned list directly instead of
   * unfolding `fromUnsorted`, `insertSorted`, and the recursive sort.
   */
  def sortFiltered(list: List[BigInt]): List[BigInt] = {
    decreases(list.size)
    if (list.isEmpty) List.empty
    else insertSorted(list.head, sortFiltered(list.tail))
  }.ensuring(res => isAscending(res))

  def removeAt(l: List[BigInt], i: BigInt): List[BigInt] = {
    require(i >= 0 && i < l.size)
    decreases(l.size)
    if (i == BigInt(0)) l.tail
    else l.head :: removeAt(l.tail, i - 1)
  }

  def assertSortFilteredAscending(list: List[BigInt]): Boolean = {
    decreases(list.size)
    if (list.isEmpty) isAscending(sortFiltered(list))
    else {
      assert(assertSortFilteredAscending(list.tail))
      assert(isAscending(sortFiltered(list.tail)))
      assert(assertInsertSortedAscending(list.head, sortFiltered(list.tail)))
      isAscending(sortFiltered(list))
    }
  }.holds

  def assertInsertSortedAscending(x: BigInt, list: List[BigInt]): Boolean = {
    require(isAscending(list))
    decreases(list.size)
    if (list.isEmpty) isAscending(insertSorted(x, list))
    else if (x < list.head) isAscending(insertSorted(x, list))
    else if (x == list.head) isAscending(list)
    else {
      assert(isAscending(list.tail))
      assert(assertInsertSortedAscending(x, list.tail))
      assert(isAscending(insertSorted(x, list.tail)))
      isAscending(insertSorted(x, list))
    }
  }.holds

  def assertTailAscending(list: List[BigInt]): Boolean = {
    require(isAscending(list))
    require(list.nonEmpty)
    decreases(list.size)
    if (list.tail.isEmpty) true
    else {
      assert(assertTailAscending(list.tail))
      isAscending(list.tail)
    }
  }.holds

  /**
   * `isAscending` implies strict ordering at any position:
   *   isAscending(list) && i+1 < list.size => list(i+1) > list(i)
   */
  def assertIsAscendingAtIndex(list: List[BigInt], i: BigInt): Boolean = {
    require(i >= 0)
    require(i + 1 < list.size)
    require(isAscending(list))
    decreases(i)
    if (i == BigInt(0)) {
      list(i + 1) > list(i)
    } else {
      assert(assertTailAscending(list))
      assert(isAscending(list.tail))
      assert(assertIsAscendingAtIndex(list.tail, i - 1))
      list(i + 1) > list(i)
    }
  }.holds

  def assertRemoveKeepsAscending(list: List[BigInt], index: BigInt): Boolean = {
    require(isAscending(list))
    require(index >= 0 && index < list.size)
    decreases(list.size)
    if (list.size == 1 || list.tail.isEmpty) {
      isAscending(removeAt(list, index))
    } else if (index == BigInt(0)) {
      assertTailAscending(list)
      isAscending(removeAt(list, index))
    } else {
      assert(isAscending(list.tail))
      assert(assertRemoveKeepsAscending(list.tail, index - 1))
      assert(list.head <= list.tail.head)
      isAscending(removeAt(list, index))
    }
  }.holds
}
