package v1.list

import stainless.collection.List
import stainless.lang.decreases
import v1.list.ListBoundUtils
import v1.list.properties.ListUtilsProperties
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
      ListUtilsProperties.listAddValueTail(prev, current)
      prev ++ List(current)
    }
  }

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
