package v1.list

import stainless.collection.List
import stainless.lang.*
import v1.list.ListBoundUtils

case class MaxBoundList(list: List[BigInt], upperBound: BigInt) {
  require(ListBoundUtils.allLessThan(list, upperBound))

  def isEmpty: Boolean = list.isEmpty
  def size: BigInt = list.size
  def head: BigInt = { require(list.nonEmpty); list.head }
  def last: BigInt = { require(list.nonEmpty); list.last }
  def apply(index: BigInt): BigInt = { require(index >= 0 && index < list.size); list(index) }

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
}
