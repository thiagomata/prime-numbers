package v1.list

import stainless.collection.List
import stainless.lang.*
import v1.list.ListBoundUtils

case class MinBoundList(list: List[BigInt], lowerBound: BigInt) {
  require(ListBoundUtils.allGreaterThan(list, lowerBound))

  def isEmpty: Boolean = list.isEmpty
  def size: BigInt = list.size
  def head: BigInt = { require(list.nonEmpty); list.head }
  def last: BigInt = { require(list.nonEmpty); list.last }
  def apply(index: BigInt): BigInt = { require(index >= 0 && index < list.size); list(index) }

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
}
