package v1.chapter3.list.properties

import stainless.collection.List
import stainless.lang.*
import v1.chapter1.verification.Helper.assert
import v1.chapter3.list.{ListBoundUtils, ListUtils}

object ListUtilsProperties {

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
    
    ListUtils.listSumAddValue(list, list(to))
    
    ListUtils.slice(list, from, to) ==
      ListUtils.slice(list, from, to - 1) ++ List(list(to))
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
      assert(ListBoundUtils.assertTailShiftLeft(list, list.size - 1))
      assert(list.last == list(list.size - 1))
    }
    list.last == list(list.size - 1)
  }.holds

  /**
    * For every list where all elements are bigger than a value,
    * any element at a valid position is also bigger than that value.
    *
    * checkAllBiggerThanValue(list, value) => list(pos) > value
    *
    * @param list List[BigInt] — list of values
    * @param value BigInt — the lower bound value
    * @param pos BigInt — valid position in the list
    * @return Boolean true if the property holds
    */
  def checkAllBiggerThanValueAtIndex(list: List[BigInt], value: BigInt, pos: BigInt): Boolean = {
    require(ListUtils.checkAllBiggerThanValue(list, value))
    require(pos >= 0 && pos < list.size)
    ListBoundUtils.assertGreaterThanAtIndex(list, value, pos)
  }.holds

  /**
    * For every non-empty list where all elements are bigger than a value,
    * the head is bigger than that value and the tail also satisfies the property.
    *
    * checkAllBiggerThanValue(list, value) => list.head > value && checkAllBiggerThanValue(list.tail, value)
    *
    * @param list List[BigInt] — non-empty list of values
    * @param value BigInt — the lower bound value
    * @return Boolean true if the property holds
    */
  def checkAllBiggerThanValueHeadTail(list: List[BigInt], value: BigInt): Boolean = {
    require(ListUtils.checkAllBiggerThanValue(list, value))
    require(list.nonEmpty)
    ListBoundUtils.assertGreaterThanHeadTail(list, value)
  }.holds
}
