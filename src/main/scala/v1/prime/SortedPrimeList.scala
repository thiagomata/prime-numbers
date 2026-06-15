package v1.prime

import stainless.collection.List
import stainless.lang.*

import scala.annotation.tailrec

case class SortedPrimeList(list: List[Prime]) {
  require(SortedPrimeList.isDescending(list))

  def isEmpty: Boolean = list.isEmpty
  def nonEmpty: Boolean = list.nonEmpty
  def size: BigInt = list.size
  def head: Prime = { require(list.nonEmpty); list.head }
  def last: Prime = { require(list.nonEmpty); list.last }
  def apply(index: BigInt): Prime = {
    require(index >= 0 && index < list.size)
    list(index)
  }

  def insert(x: Prime): SortedPrimeList = {
    SortedPrimeList.assertInsertSortedDescending(x, list)
    SortedPrimeList(SortedPrimeList.insertSorted(x, list))
  }

  def remove(index: BigInt): SortedPrimeList = {
    require(index >= 0 && index < list.size)
    SortedPrimeList.assertRemoveKeepsDescending(list, index)
    SortedPrimeList(SortedPrimeList.removeAt(list, index))
  }

  def tail: SortedPrimeList = {
    require(list.nonEmpty)
    SortedPrimeList.assertTailDescending(list)
    SortedPrimeList(list.tail)
  }
}

object SortedPrimeList {

  @tailrec
  def isDescending(list: List[Prime]): Boolean = {
    decreases(list.size)
    if (list.isEmpty || list.tail.isEmpty) true
    else if (list.head.value <= list.tail.head.value) false
    else isDescending(list.tail)
  }

  def fromUnsorted(list: List[Prime]): SortedPrimeList = {
    assert(assertSortFilteredDescending(list))
    SortedPrimeList(sortFiltered(list))
  }

  val empty: SortedPrimeList = SortedPrimeList(List.empty[Prime])

  def insertSorted(x: Prime, list: List[Prime]): List[Prime] = {
    decreases(list.size)
    if (list.isEmpty) List(x)
    else if (x.value > list.head.value) x :: list
    else if (x.value == list.head.value) list
    else list.head :: insertSorted(x, list.tail)
  }

  def sortFiltered(list: List[Prime]): List[Prime] = {
    decreases(list.size)
    if (list.isEmpty) List.empty
    else insertSorted(list.head, sortFiltered(list.tail))
  }

  def removeAt(l: List[Prime], i: BigInt): List[Prime] = {
    require(i >= 0 && i < l.size)
    decreases(l.size)
    if (i == BigInt(0)) l.tail
    else l.head :: removeAt(l.tail, i - 1)
  }

  def assertSortFilteredDescending(list: List[Prime]): Boolean = {
    decreases(list.size)
    if (list.isEmpty) isDescending(sortFiltered(list))
    else {
      assert(assertSortFilteredDescending(list.tail))
      assert(isDescending(sortFiltered(list.tail)))
      assert(assertInsertSortedDescending(list.head, sortFiltered(list.tail)))
      isDescending(sortFiltered(list))
    }
  }.holds

  def assertInsertSortedDescending(x: Prime, list: List[Prime]): Boolean = {
    require(isDescending(list))
    decreases(list.size)

    if (list.isEmpty) {
      isDescending(insertSorted(x, list))
    } else if (x.value > list.head.value) {
      isDescending(insertSorted(x, list))
    } else {
      assert(isDescending(list.tail))
      assert(assertInsertSortedDescending(x, list.tail))
      assert(isDescending(insertSorted(x, list.tail)))
      isDescending(insertSorted(x, list))
    }
  }.holds

  def assertTailDescending(list: List[Prime]): Boolean = {
    require(isDescending(list))
    require(list.nonEmpty)
    decreases(list.size)

    if (list.tail.isEmpty) true
    else {
      assert(assertTailDescending(list.tail))
      isDescending(list.tail)
    }
  }.holds

  def assertRemoveKeepsDescending(list: List[Prime], index: BigInt): Boolean = {
    require(isDescending(list))
    require(index >= 0 && index < list.size)
    decreases(list.size)

    if (list.size == 1 || list.tail.isEmpty) {
      isDescending(removeAt(list, index))
    } else if (index == BigInt(0)) {
      assertTailDescending(list)
      isDescending(removeAt(list, index))
    } else {
      assert(isDescending(list.tail))
      assert(assertRemoveKeepsDescending(list.tail, index - 1))
      assert(list.head.value > list.tail.head.value)
      isDescending(removeAt(list, index))
    }
  }.holds
}