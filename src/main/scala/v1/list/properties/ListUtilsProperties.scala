package v1.list.properties

import stainless.collection.List
import stainless.lang.*
import v1.list.ListUtils
import verification.Helper.assert

object ListUtilsProperties {

  /**
    * for every list `list`` and every value `value``,
    * the sum of the list `list` ++ `List(value)`
    * is equal to the sum of the `list` plus the `value`.
    * 
    * sum(list ++ List(value)) == sum(list) + value
    *
    * @param list List[BigInt] any list of BigInt
    * @param value BigInt the value to add to the list
    * @return Boolean true if the property holds
    */
  def listSumAddValue(list: List[BigInt], value: BigInt): Boolean = {
    ListUtils.sum(List(value) ++ list) == value + ListUtils.sum(list)
  }.holds

  /**
    * for every list A and B,
    * the sum of the list A ++ B
    * is equal to the sum of the list A plus the sum of the list B.
    * 
    * sum(listA ++ listB) == sum(listA) + sum(listB)
    *
    * @param listA List[BigInt] any list of BigInt
    * @param listB List[BigInt] any list of BigInt
    * @return Boolean true if the property holds
    */
  def listCombine(listA: List[BigInt], listB: List[BigInt]): Boolean = {
    decreases(listA.size)

    if (listA.isEmpty) {
      assert(ListUtils.sum(listA) == BigInt(0))
      assert(ListUtils.sum(listB) == BigInt(0) + ListUtils.sum(listB))
      assert(ListUtils.sum(listB) == ListUtils.sum(listA) + ListUtils.sum(listB))
      assert(listA ++ listB == listB)
    } else {
      listCombine(listA.tail, listB)
      val bigList = listA ++ listB
      assert(bigList == List(listA.head) ++ listA.tail ++ listB)
      listSumAddValue(listA.tail ++ listB, listA.head)
    }
    ListUtils.sum(listA ++ listB) == ListUtils.sum(listA) + ListUtils.sum(listB)
  }.holds

  /**
    * for every list A and B,
    * the sum of the list A ++ B
    * is equal to the sum of the list B plus the sum of the list A.
    * 
    * sum(listA ++ listB) == sum(listB) + sum(listA)
    *
    * @param listA List[BigInt] any list of BigInt
    * @param listB List[BigInt] any list of BigInt
    * @return Boolean true if the property holds
    */
  def listSwap(listA: List[BigInt], listB: List[BigInt]): Boolean = {
    listCombine(listA, listB)
    listCombine(listB, listA)
    assert(ListUtils.sum(listA ++ listB) == ListUtils.sum(listA) + ListUtils.sum(listB))
    assert(ListUtils.sum(listB ++ listA) == ListUtils.sum(listB) + ListUtils.sum(listA))
    assert(ListUtils.sum(listA) + ListUtils.sum(listB) == ListUtils.sum(listB) + ListUtils.sum(listA))
    ListUtils.sum(listA ++ listB) == ListUtils.sum(listB ++ listA)
  }.holds

  /**
    * The sum of the list prepending a value
    * is equal to the sum of the list plus the value.
    * 
    * sum(list ++ List(value)) == sum(list) + value
    *
    * @param list List[BigInt] any list of BigInt
    * @param value BigInt the value to add to the list
    * @return Boolean true if the property holds
    */
  def listAddValueTail(list: List[BigInt], value: BigInt): Boolean = {
    listSwap(list, List(value))
    listSumAddValue(list, value)
    assert(ListUtils.sum(List(value) ++ list) == ListUtils.sum(list ++ List(value)))
    ListUtils.sum(list ++ List(value)) == value + ListUtils.sum(list) &&
      ListUtils.sum(List(value) ++ list) ==  ListUtils.sum(list) + value
  }.holds

  /**
    * For every position in the list,
    * A slice of the list from position from i position j
    * is equal to the slice of the list from position i to j - 1
    * appending the element in position j.
    * 
    * list(i, j) == list(i, j - 1) ++ list(j)
    *
    * @param list List[BigInt] any list of BigInt
    * @param from BigInt the position of the first element to check
    * @param to BigInt the position of the last element to check
    * @return Boolean true if the property holds
    */
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
  def assertTailShiftLeft[T](list: List[T], position: BigInt): Boolean = {
    require(list.nonEmpty)
    require(position >= 0 && position < list.size)
    decreases(position)

    if (position == 0 ) {
      list(position) == list.head
    } else {
      assert( list == List(list.head) ++ list.tail )
      assert( list(position) == list.apply(position) )
      assert(assertTailShiftLeft(list.tail, position - 1))
      assert(list.apply(position) == list.tail.apply(position - 1))
      list(position) == list.tail(position - 1)
    }
  }.holds

  /**
    * For every position in the list different from 0,
    * the value of the list in that position
    * is equal to the value of the tail in that position + 1.
    * 
    *  list.tail(position) == list(position + 1)
    *
    * @param list List[T] any list of T non empty
    * @param position BigInt the position of the element to check
    * @return Boolean true if the property holds
    */
  def accessTailShiftRight[T](list: List[T], position: BigInt): Boolean = {
    require(list.nonEmpty && position >= 0 && position < list.tail.size)
    list.tail(position) == list(position + 1)
  }.holds

  /**
   * The last element of the list is equal to the last position of the list.
   * This property is true for every list of size > 0.
   *
   * list.last == list(list.size - 1)
   *
   * @param list List[BigInt] any list of BigInt non empty
   * @return true if the property holds
   */
  def assertLastEqualsLastPosition[T](list: List[T]): Boolean = {
    require(list.nonEmpty)
    decreases(list.size)

    if (list.size == 1) {
      assert(list.head == list.last)
    } else {
      assert(assertLastEqualsLastPosition(list.tail))
      assertTailShiftLeft(list, list.size - 1)
      assert(list.last == list(list.size - 1))
    }
    list.last == list(list.size - 1)
  }.holds
}
