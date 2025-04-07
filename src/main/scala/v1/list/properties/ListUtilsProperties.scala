package v1.list.properties

import stainless.collection.List
import stainless.lang.*
import stainless.proof.check
import v1.list.ListUtils

object ListUtilsProperties {
  def listSumAddValue(list: List[BigInt], value: BigInt): Boolean = {
    ListUtils.sum(List(value) ++ list) == value + ListUtils.sum(list)
  }.holds

  def listCombine(listA: List[BigInt], listB: List[BigInt]): Boolean = {
    decreases(listA.size)

    if (listA.isEmpty) {
      check(ListUtils.sum(listA) == BigInt(0))
      check(ListUtils.sum(listB) == BigInt(0) + ListUtils.sum(listB))
      check(ListUtils.sum(listB) == ListUtils.sum(listA) + ListUtils.sum(listB))
      check(listA ++ listB == listB)
    } else {
      listCombine(listA.tail, listB)
      val bigList = listA ++ listB
      check(bigList == List(listA.head) ++ listA.tail ++ listB)
      listSumAddValue(listA.tail ++ listB, listA.head)
    }
    ListUtils.sum(listA ++ listB) == ListUtils.sum(listA) + ListUtils.sum(listB)
  }.holds

  def listSwap(listA: List[BigInt], listB: List[BigInt]): Boolean = {
    listCombine(listA, listB)
    listCombine(listB, listA)
    check(ListUtils.sum(listA ++ listB) == ListUtils.sum(listA) + ListUtils.sum(listB))
    check(ListUtils.sum(listB ++ listA) == ListUtils.sum(listB) + ListUtils.sum(listA))
    check(ListUtils.sum(listA) + ListUtils.sum(listB) == ListUtils.sum(listB) + ListUtils.sum(listA))
    ListUtils.sum(listA ++ listB) == ListUtils.sum(listB ++ listA)
  }.holds

  def listAddValueTail(list: List[BigInt], value: BigInt): Boolean = {
    listSwap(list, List(value))
    listSumAddValue(list, value)
    check(ListUtils.sum(List(value) ++ list) == ListUtils.sum(list ++ List(value)))
    ListUtils.sum(list ++ List(value)) == value + ListUtils.sum(list) &&
      ListUtils.sum(List(value) ++ list) ==  ListUtils.sum(list) + value
  }.holds

  def assertAppendToSlice(list: List[BigInt], from: BigInt, to: BigInt): Boolean = {
    require(from >= 0)
    require(from < to)
    require(to < list.size)
    
    listSumAddValue(list, list(to))
    
    ListUtils.slice(list, from, to) ==
      ListUtils.slice(list, from, to - 1) ++ List(list(to))
  }.holds

}
