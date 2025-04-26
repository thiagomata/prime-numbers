package v1.acc.properties

import v1.acc.Acc
import stainless.collection.List
import stainless.lang.*
import stainless.proof.check
import v1.list.ListUtils
import v1.list.properties.ListUtilsProperties

object AccProperties {
//  def diffEqualsList(list: List[BigInt], position: BigInt): Boolean = {
//    require(position >= 0)
//    require(position < list.size - 1)
//    require(list.size > 1)
//    val acc = Acc(list)
//    acc(position + 1) - acc(position) == list(position + 1)
//  }.holds

//  def lastEqualsSum(list: List[BigInt]): Boolean = {
//    require(list.nonEmpty)
//    decreases(list.size)
//    val acc = Acc(list)
//
//    if ( list.size == 1 ) {
//      check(ListUtils.sum(list) == acc.last)
//    } else {
//      lastEqualsSum(list.slice(0, list.size - 2))
//      // [1,2]
//      // [1,3]
//
//
//      // [1.2.3.4]
//      // [1,3,6,10]
//
//      // 1 2 3 4 list
//      // 4 3 2 1 list.reverse
//      // 3 2 1   list.reverse.tail
//      // 1 2 3
////      check(ListUtils.sum(list.tail) == acc.tail.last)
////      ListUtilsProperties.listAddValueTail(list.tail, list.head)
//    }
//    true
////    ListUtils.sum(list) == acc.last
//  }.holds
}
