package v1.chapter3.list

import stainless.collection.List
import stainless.lang.*

case class MaxBoundList(list: List[BigInt], upperBound: BigInt) {
  require(ListBoundUtils.allLessThan(list, upperBound))

  def isEmpty: Boolean = list.isEmpty
  def size: BigInt = list.size
  def head: BigInt = { require(list.nonEmpty); list.head }
  def last: BigInt = { require(list.nonEmpty); list.last }
  def apply(index: BigInt): BigInt = { require(index >= 0 && index < list.size); list(index) }

  def filter(divisor: BigInt): MaxBoundList = {
    require(divisor > 0)
    val filtered = list.filter(x => x % divisor != 0)
    MaxBoundList.assertFilterPreservesLessThan(list, upperBound, divisor)
    MaxBoundList(filtered, upperBound)
  }

  def tail: MaxBoundList = {
    require(list.nonEmpty)
    MaxBoundList.assertTailLessThan(list, upperBound)
    MaxBoundList(list.tail, upperBound)
  }
}

object MaxBoundList {
  def assertTailLessThan(list: List[BigInt], upperBound: BigInt): Boolean = {
    require(ListBoundUtils.allLessThan(list, upperBound))
    require(list.nonEmpty)
    decreases(list)
    if (list.tail.isEmpty) true
    else {
      assert(assertTailLessThan(list.tail, upperBound))
      ListBoundUtils.allLessThan(list.tail, upperBound)
    }
  }.holds

  def assertFilterPreservesLessThan(list: List[BigInt], upperBound: BigInt, divisor: BigInt): Boolean = {
    require(ListBoundUtils.allLessThan(list, upperBound))
    require(divisor > 0)
    decreases(list.size)
    if (list.isEmpty) {
      ListBoundUtils.allLessThan(List.empty, upperBound)
    } else {
      assert(assertFilterPreservesLessThan(list.tail, upperBound, divisor))
      ListBoundUtils.allLessThan(list.filter(x => x % divisor != 0), upperBound)
    }
  }.holds
}
