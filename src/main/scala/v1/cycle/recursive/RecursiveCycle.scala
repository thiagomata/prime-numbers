package v1.cycle.recursive

import stainless.collection.List
import stainless.lang.decreases
import v1.cycle.CycleUtils

/**
 * Represents a recursive cycle of values.
 *
 * @param values List A non-empty list of BigInt 
 *  non-negative values that form the cycle.
 */
case class RecursiveCycle(values: List[BigInt]) {
  require(values.nonEmpty)
  require(CycleUtils.checkPositiveOrZero(values))

  def size: BigInt = values.size

  /**
    * Applies the recursive cycle to the given position.
    *  This method allows for accessing the cycle using 
    *  a position that may exceed the size of
    *  the cycle.
    * 
    * In other words,
    * RecursiveCycle(position) = if position < size 
    *   then values(position) 
    *   else RecursiveCycle(position - values.size)
    *
    * @param position
    * @return
    */
  def apply(position: BigInt): BigInt = {
    decreases(position)
    require(position >= 0)

    if (position < size) {
      values(position)
    } else {
      apply(position - values.size)
    }
  }
}
