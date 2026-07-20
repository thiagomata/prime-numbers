package v1.chapter6.sieve.seq.spec

import stainless.collection.List
import stainless.lang.decreases

import scala.annotation.tailrec
import stainless.lang.BooleanDecorations
import v1.chapter3.list.ListBoundUtils

/**
 * Utility functions for SieveSequence.
 */
object CycleUtils {

  /**
   * Check that all elements in the list are positive (> 0).
   */
  @tailrec
  def checkPositive(list: List[BigInt]): Boolean = {
    decreases(list)
    if (list.isEmpty) true
    else list.head > 0 && checkPositive(list.tail)
  }

  /**
   * Check that all elements in the list are less than the given bound.
   */
  @tailrec
  def allLessThan(list: List[BigInt], bound: BigInt): Boolean = {
    decreases(list)
    if (list.isEmpty) true
    else list.head < bound && allLessThan(list.tail, bound)
  }

  def assertAllLessThanTransitive(list: List[BigInt], bound: BigInt, bound2: BigInt): Boolean = {
    require(allLessThan(list, bound))
    require(bound <= bound2)
    decreases(list)
    if (list.isEmpty) true
    else {
      assert(list.head < bound)
      assert(list.head < bound2)
      assert(allLessThan(list.tail, bound))
      assert(assertAllLessThanTransitive(list.tail, bound, bound2))
      allLessThan(list, bound2)
    }
  }.holds

  /**
   * Check that all elements in the list are non-negative (>= 0).
   */
  @tailrec
  def checkNonNegative(list: List[BigInt]): Boolean = {
    decreases(list)
    if (list.isEmpty) true
    else list.head >= 0 && checkNonNegative(list.tail)
  }

  def assertAllLessThanAppend(listA: List[BigInt], listB: List[BigInt], bound: BigInt): Boolean = {
    require(allLessThan(listA, bound))
    require(allLessThan(listB, bound))
    decreases(listA.size)
    if (listA.isEmpty) {
      allLessThan(listA ++ listB, bound)
    } else {
      assert(assertAllLessThanAppend(listA.tail, listB, bound))
      assert(allLessThan(listA.tail ++ listB, bound))
      assert(listA.head < bound)
      allLessThan(listA ++ listB, bound)
    }
  }.holds

  def assertCheckNonNegativeAppend(listA: List[BigInt], listB: List[BigInt]): Boolean = {
    require(checkNonNegative(listA))
    require(checkNonNegative(listB))
    decreases(listA.size)
    if (listA.isEmpty) {
      checkNonNegative(listA ++ listB)
    } else {
      assert(assertCheckNonNegativeAppend(listA.tail, listB))
      assert(checkNonNegative(listA.tail ++ listB))
      assert(listA.head >= 0)
      checkNonNegative(listA ++ listB)
    }
  }.holds

  /**
   * CycleUtils.allLessThan and ListBoundUtils.allLessThan are equivalent.
   * Both check that every element is less than the bound.
   */
  def assertAllLessThanEquivalent(list: List[BigInt], bound: BigInt): Boolean = {
    decreases(list.size)
    if (list.isEmpty) {
      CycleUtils.allLessThan(list, bound) ==
        ListBoundUtils.allLessThan(list, bound)
    } else {
      assert(assertAllLessThanEquivalent(list.tail, bound))
      CycleUtils.allLessThan(list, bound) ==
        ListBoundUtils.allLessThan(list, bound)
    }
  }.holds
}
