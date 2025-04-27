package v1.list.properties

import stainless.collection.List
import stainless.lang.*
//import verification.Helper.check
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

  /**
   * For every position in the list different from 0,
   * the value of the list in that position
   * is equal to the value of the tail in that position - 1.
   *
   * list(position) == list.tail(position - 1)
   *
   * @param list List[BigInt] any list of BigInt non empty
   * @param position BigInt the position of the element to check
   * @return true if the property holds
   */
  def assertTailShiftPosition(list: List[BigInt], position: BigInt): Boolean = {
    require(list.nonEmpty)
    require(position >= 0 && position < list.size)
    decreases(position)

    if (position == 0 ) {
      list(position) == list.head
    } else {
      check( list == List(list.head) ++ list.tail )
      check( list(position) == list.apply(position) )
      check(assertTailShiftPosition(list.tail, position - 1))
      check(list.apply(position) == list.tail.apply(position - 1))
      list(position) == list.tail(position - 1)
    }
  }.holds

  def accessTailShift[T](list: List[T], position: BigInt): Boolean = {
    require(list.nonEmpty && position >= 0 && position < list.tail.size)
    list.tail(position) == list(position + 1)
  }.holds
}
