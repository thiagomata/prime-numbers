package v1.list.properties

import stainless.collection.*
import stainless.lang.*
import v1.list.ListUtils
import verification.Helper.assert

object SliceEquivalenceLemmas {

  /**
   * Creates a sublist of the list `list` from index `from` to index `to`, inclusive
   * using forward slice: builds from `from` to `to` using Cons.
   *
   * The precondition for this function is that:
   * 0 <= from && from <= to && to < list.length
   *
   * This function is a recursive implementation that constructs the sublist
   * by taking elements from the list `list` starting at index `from` and ending at index `to`.
   *
   * @param list the List from which to extract the sublist
   * @param from the starting index of the sublist (inclusive)
   * @param to the ending index of the sublist (inclusive)
   * @tparam A the type of elements in the list
   * @return a List[A] containing the elements from index `from` to index `to`
   */
  def headRecursiveSlice[A](list: List[A], from: BigInt, to: BigInt): List[A] = {
    require(0 <= from && from <= to && to < list.length)
    decreases(to - from)
    if (from == to) List(list(from))
    else Cons(list(from), headRecursiveSlice(list, from + 1, to))
  }

  /**
   * Creates a sublist of the list `list` from index `from` to index `to`, inclusive
   * using index-based access: builds from i to j using index access.
   *
   * The precondition for this function is that:
   * 0 <= from && from <= to && to < list.length
   *
   * This function is a recursive implementation that constructs the sublist
   * by taking elements from the list `list` starting at index `from` and ending at index `to`.
   *
   * @param list the List from which to extract the sublist
   * @param from the starting index of the sublist (inclusive)
   * @param to the ending index of the sublist (inclusive)
   * @tparam A the type of elements in the list
   * @return a List[A] containing the elements from index `from` to index `to`
   */
  def indexRangeValues[A](list: List[A], from: BigInt, to: BigInt): List[A] = {
    require(0 <= from && from <= to && to < list.length)
    decreases(to - from)
    if (from == to) List(list(from))
    else Cons(list(from), indexRangeValues(list, from + 1, to))
  }

  /**
   * Lemma: for every list `list` and indices `from` and `to` such that
   * 0 <= from && from <= to && to < list.length,
   * the slice of the list `list` from index `from` to index `to`
   * is equal to the list constructed using index-based access.
   *
   * In other words, the two methods of creating a sublist
   * are equivalent.
   *
   * for every list `list` and indices `from` and `to` such that
   * 0 <= from && from <= to && to < list.length,
   * the slice of the list `list` from index `from` to index `to`
   * is equal to the list constructed using index-based access.
   *
   * slice(list, from, to) == indexRangeValues(list, from, to)
   *
   * @param list the List from which to extract the sublist
   * @param from the starting index of the sublist (inclusive)
   * @param to the ending index of the sublist (inclusive)
   * @tparam A the type of elements in the list
   * @return Boolean true if the property holds
   */
  def sliceEqualsSpec[A](list: List[A], from: BigInt, to: BigInt): Boolean = {
    require(0 <= from && from <= to && to < list.length)
    decreases(to - from)

    if (from == to) {
      assert(headRecursiveSlice(list, from, to) == List(list(from)))
      assert(indexRangeValues(list, from, to) == List(list(from)))
    } else {
      assert(sliceEqualsSpec(list, from + 1, to))
      assert(headRecursiveSlice(list, from, to) == Cons(list(from), headRecursiveSlice(list, from + 1, to)))
      assert(indexRangeValues(list, from, to) == Cons(list(from), indexRangeValues(list, from + 1, to)))
    }
    headRecursiveSlice(list, from, to) == indexRangeValues(list, from, to)
  }.holds

  /**
   * Lemma: appending a single element to a list using `++` is equivalent to using `:+`.
   *
   * In other words:
   * list ++ List(element) == list :+ element
   *
   * @param list List[A] the list to which the element will be appended
   * @param element A the element to append to the list
   * @return Boolean true if the property holds
   */
  def appendOne[A](list: List[A], element: A): Boolean = {
    list ++ List(element) == list :+ element
  }.holds

  /**
   * Lemma: appending an element to a list using `:+` is equivalent to appending it to the tail of a `Cons` list.
   *
   * In other words:
   * Cons(head, tail) :+ element == Cons(head, tail :+ element)
   *
   * @param head A the head of the list
   * @param tail List[A] the tail of the list
   * @param element A the element to append to the list
   * @return Boolean true if the property holds
   */
  def appendCons[A](head: A, tail: List[A], element: A): Boolean = {
    (Cons(head, tail) :+ element) == Cons(head, tail :+ element)
  }.holds

  /**
   * Lemma: For all `list: List[BigInt]` and indices `from`, `to` such that
   * 0 <= from <= to < list.length, the following three slicing strategies produce
   * the same result:
   *
   * - Tail-recursive slice: ListUtils.slice
   * - Head-recursive slice: headRecursiveSlice
   * - Index-based slice: indexRangeValues
   *
   * Formally:
   *
   * ListUtils.slice(list, from, to) == headRecursiveSlice(list, from, to)
   * ListUtils.slice(list, from, to) == indexRangeValues(list, from, to)
   * headRecursiveSlice(list, from, to) == indexRangeValues(list, from, to)
   *
   * @param list the input list of BigInt
   * @param from inclusive start index
   * @param to   inclusive end index
   * @return true if all three slices are equal
   */
  def tailHeadAndIndexRangeSlicesAreEqual(list: List[BigInt], from: BigInt, to: BigInt): Boolean = {
    require(0 <= from && from <= to && to < list.length)
    decreases(to - from)

    val indexSlice = indexRangeValues(list, from, to)
    val tailSlice = ListUtils.slice(list, from, to)
    val headSlice = headRecursiveSlice(list, from, to)

    if (from == to) {
      assert(indexSlice == List(list(from)))
      assert(tailSlice == List(list(from)))
      assert(headSlice == List(list(from)))
    } else {
      assert(tailHeadAndIndexRangeSlicesAreEqual(list, from, to - 1))
      assert(tailHeadAndIndexRangeSlicesAreEqual(list, from + 1, to))
      val reconstructedTail = ListUtils.slice(list, from, to - 1) ++ List(list(to))
      assert(tailSlice == reconstructedTail)
      assert(tailSlice == indexSlice)
      assert(headSlice == indexSlice)
      assert(tailSlice == headSlice)
    }
    (
      tailSlice == headSlice &&
      tailSlice == indexSlice &&
      headSlice == indexSlice
    )
  }.holds

}
