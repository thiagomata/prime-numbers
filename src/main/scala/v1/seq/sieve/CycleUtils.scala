package v1.seq.sieve

import stainless.collection.List
import stainless.lang.decreases

import scala.annotation.tailrec

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
