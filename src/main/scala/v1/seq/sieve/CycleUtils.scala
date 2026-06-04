package v1.seq.sieve

import stainless.collection.List
import stainless.lang.decreases

import scala.annotation.tailrec
import stainless.lang.BooleanDecorations

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
}
