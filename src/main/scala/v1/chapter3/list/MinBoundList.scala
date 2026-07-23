package v1.chapter3.list

import stainless.collection.List
import stainless.lang.*

case class MinBoundList(list: List[BigInt], lowerBound: BigInt) {
  require(ListBoundUtils.allGreaterThan(list, lowerBound))

  def isEmpty: Boolean = list.isEmpty
  def size: BigInt = list.size
  def head: BigInt = { require(list.nonEmpty); list.head }
  def last: BigInt = { require(list.nonEmpty); list.last }
  def apply(index: BigInt): BigInt = { require(index >= 0 && index < list.size); list(index) }

  def filter(divisor: BigInt): MinBoundList = {
    require(divisor > 0)
    val filtered = list.filter(x => x % divisor != 0)
    MinBoundList.assertFilterPreservesGreaterThan(list, lowerBound, divisor)
    MinBoundList(filtered, lowerBound)
  }

  def tail: MinBoundList = {
    require(list.nonEmpty)
    MinBoundList.assertTailGreaterThan(list, lowerBound)
    MinBoundList(list.tail, lowerBound)
  }
}

object MinBoundList {
  def assertTailGreaterThan(list: List[BigInt], lowerBound: BigInt): Boolean = {
    require(ListBoundUtils.allGreaterThan(list, lowerBound))
    require(list.nonEmpty)
    decreases(list)
    if (list.tail.isEmpty) true
    else {
      assert(assertTailGreaterThan(list.tail, lowerBound))
      ListBoundUtils.allGreaterThan(list.tail, lowerBound)
    }
  }.holds

  def assertFilterPreservesGreaterThan(list: List[BigInt], lowerBound: BigInt, divisor: BigInt): Boolean = {
    require(ListBoundUtils.allGreaterThan(list, lowerBound))
    require(divisor > 0)
    decreases(list.size)
    if (list.isEmpty) {
      ListBoundUtils.allGreaterThan(List.empty, lowerBound)
    } else {
      assert(assertFilterPreservesGreaterThan(list.tail, lowerBound, divisor))
      ListBoundUtils.allGreaterThan(list.filter(x => x % divisor != 0), lowerBound)
    }
  }.holds
}
