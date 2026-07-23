package v1.chapter3.list

import stainless.collection.List
import stainless.lang.decreases
import stainless.lang.BooleanDecorations
import v1.chapter1.verification.Helper.assert
import scala.annotation.tailrec

object ListUtils {

  /**
   * Sums all elements in a list of BigInt.
   * Create the sum using tail recursion.
   * 
   * Assumes that the sum of an empty list is 0.
   * 
   * @param loopList List[BigInt] the list to sum
   * @return BigInt the sum of all elements in the list
   */
  def sum(loopList: List[BigInt]): BigInt = {
    if (loopList.isEmpty) {
      BigInt(0)
    } else {
      loopList.head + sum(loopList.tail)
    }
  }

  /**
   * Slices a list from index `from` to index `to`, inclusive.
   * Create the slice using tail recursion.
   * 
   * @param list List[BigInt] the list to slice
   * @param from BigInt the starting index (inclusive)
   * @param to BigInt the ending index (inclusive)
   * @return List[BigInt] the sliced list
   */
  def splitAt(list: List[BigInt], index: BigInt): (List[BigInt], List[BigInt]) = {
    require(index >= 0 && index <= list.size)
    decreases(index)
    if (index == BigInt(0)) (List.empty, list)
    else {
      val (front, back) = splitAt(list.tail, index - 1)
      (list.head :: front, back)
    }
  }

  /**
   * Rotates a list by an index, returning a cyclic permutation.
   *
   * `rotateAt(list, index) = back ++ front` where `(front, back) = splitAt(list, index)`.
   * This is a pure re-indexing of the same elements: the head value does not
   * change, only the viewing position shifts. The rotation theory (same
   * elements, same bounds, same sum, same size, same product) lives in
   * `RotationProperties`; it is stated entirely over flat `List[BigInt]` and
   * never mentions a head.
   */
  @tailrec
  def rotateAt(list: List[BigInt], index: BigInt): List[BigInt] = {
    require(index >= 0)
    decreases(index)
    if (list.isEmpty || index == BigInt(0)) list
    else if (index >= list.size) rotateAt(list, index - list.size)
    else {
      val (front, back) = splitAt(list, index)
      back ++ front
    }
  }

  def slice(list: List[BigInt], from: BigInt, to: BigInt): List[BigInt] = {
    require(from >= 0)
    require(to >= from)
    require(to < list.size)
    decreases(to)

    val current: BigInt = list(to)
    if (from == to) {
      List(current)
    } else {
      val prev = slice(list, from, to - 1)
      listAddValueTail(prev, current)
      prev ++ List(current)
    }
  }

  def listSumAddValue(list: List[BigInt], value: BigInt): Boolean = {
    sum(List(value) ++ list) == value + sum(list)
  }.holds

  def listCombine(listA: List[BigInt], listB: List[BigInt]): Boolean = {
    decreases(listA.size)

    if (listA.isEmpty) {
      assert(sum(listA) == BigInt(0))
      assert(sum(listB) == BigInt(0) + sum(listB))
      assert(sum(listB) == sum(listA) + sum(listB))
      assert(listA ++ listB == listB)
    } else {
      listCombine(listA.tail, listB)
      val bigList = listA ++ listB
      assert(bigList == List(listA.head) ++ listA.tail ++ listB)
      listSumAddValue(listA.tail ++ listB, listA.head)
    }
    sum(listA ++ listB) == sum(listA) + sum(listB)
  }.holds

  def listSwap(listA: List[BigInt], listB: List[BigInt]): Boolean = {
    listCombine(listA, listB)
    listCombine(listB, listA)
    assert(sum(listA ++ listB) == sum(listA) + sum(listB))
    assert(sum(listB ++ listA) == sum(listB) + sum(listA))
    assert(sum(listA) + sum(listB) == sum(listB) + sum(listA))
    sum(listA ++ listB) == sum(listB ++ listA)
  }.holds

  def listAddValueTail(list: List[BigInt], value: BigInt): Boolean = {
    listSwap(list, List(value))
    listSumAddValue(list, value)
    assert(sum(List(value) ++ list) == sum(list ++ List(value)))
    sum(list ++ List(value)) == value + sum(list) &&
      sum(List(value) ++ list) == sum(list) + value
  }.holds

  def checkAllBiggerThanValue(list: List[BigInt], value: BigInt): Boolean = {
    ListBoundUtils.allGreaterThan(list, value)
  }

  def checkAllPositive(list: List[BigInt]): Boolean = {
    checkAllBiggerThanValue(list, BigInt(0))
  }

  def checkAllBiggerThanOne(list: List[BigInt]): Boolean = {
    checkAllBiggerThanValue(list, BigInt(1))
  }
}
