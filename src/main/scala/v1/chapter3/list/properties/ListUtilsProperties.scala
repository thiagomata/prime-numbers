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
   * Keystone recombination lemma for `splitAt`.
   *
   * Splitting a list at an index and concatenating the two halves in the
   * original order recovers the original list exactly:
   *
   *   front ++ back == list   where (front, back) = splitAt(list, index)
   *
   * This is the load-bearing fact that makes rotation a permutation: since
   * `rotateAt(list, index) = back ++ front`, the rotated list is a reordering
   * of the same elements (proven via this lemma together with the sum and
   * contains lemmas over `++`). Stated purely over `List[BigInt]`; no head,
   * no index-0, no cycle concepts.
   *
   * @param list  any list
   * @param index split point, `0 <= index <= list.size`
   * @return true iff `front ++ back == list`
   */
  def assertSplitAtRecombines(list: List[BigInt], index: BigInt): Boolean = {
    require(index >= 0 && index <= list.size)
    decreases(index)
    val (front, back) = ListUtils.splitAt(list, index)
    if (index == BigInt(0)) {
      assert(front == List.empty[BigInt])
      assert(back == list)
      front ++ back == list
    } else {
      assert(list.nonEmpty)
      val (tailFront, tailBack) = ListUtils.splitAt(list.tail, index - BigInt(1))
      assert(front == list.head :: tailFront)
      assert(back == tailBack)
      assert(assertSplitAtRecombines(list.tail, index - BigInt(1)))
      assert(tailFront ++ tailBack == list.tail)
      front ++ back == list
    }
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

  /**
   * `splitAt(list, 1)._2 == list.tail` and `splitAt(list, 1)._1 == List(list.head)`
   * for any non-empty list.
   */
  def assertSplitAtOne(list: List[BigInt]): Boolean = {
    require(list.nonEmpty)
    val (front, back) = ListUtils.splitAt(list, BigInt(1))
    front == List(list.head) && back == list.tail
  }.holds

  /**
   * Indexed access into the left side of a concatenation: for `k < left.size`,
   * `(left ++ right).apply(k) == left.apply(k)`.
   */
  def assertAppendApplyLeft[T](
    left: List[T],
    right: List[T],
    k: BigInt
  ): Boolean = {
    require(k >= 0)
    require(k < left.size)
    decreases(k)
    if (k == BigInt(0)) {
      (left ++ right).apply(0) == left.apply(0)
    } else {
      assert(assertAppendApplyLeft(left.tail, right, k - 1))
      (left ++ right).apply(k) == left.apply(k)
    }
  }.holds

  /**
   * Indexed access into the right side of a concatenation: for `k >= left.size`
   * and `k < left.size + right.size`, `(left ++ right).apply(k) == right.apply(k - left.size)`.
   */
  def assertAppendApplyRight[T](
    left: List[T],
    right: List[T],
    k: BigInt
  ): Boolean = {
    require(k >= left.size)
    require(k < left.size + right.size)
    decreases(k)
    if (left.isEmpty) {
      (left ++ right).apply(k) == right.apply(k - left.size)
    } else {
      assert(assertAppendApplyRight(left.tail, right, k - 1))
      (left ++ right).apply(k) == right.apply(k - left.size)
    }
  }.holds
}
