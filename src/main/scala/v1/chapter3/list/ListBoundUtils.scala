package v1.chapter3.list

import stainless.collection.List
import stainless.lang.decreases
import stainless.lang.BooleanDecorations
import v1.chapter3.list.properties.ListUtilsProperties.assertTailShiftLeft

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
}
