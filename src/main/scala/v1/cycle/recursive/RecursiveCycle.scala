package v1.cycle.recursive

import stainless.collection.List
import stainless.lang.BooleanDecorations
import stainless.lang.decreases
import v1.cycle.CycleUtils
import v1.list.ListUtils
import v1.list.properties.ListUtilsProperties

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

  /**
    * Lemma: apply(position) equals values(position) for position < size,
    * and equals apply(position - size) for position >= size.
    */
  def applyStructure(pos: BigInt): Boolean = {
    require(pos >= 0)
    decreases(pos)
    if (pos < size) {
      apply(pos) == values(pos)
    } else {
      apply(pos) == apply(pos - size)
    }
  }.holds

  /**
    * Lemma: if all values in the list are bigger than x,
    * then applying the cycle at any position also gives a value > x.
    */
  def cycleValueBiggerThan(pos: BigInt, x: BigInt): Boolean = {
    require(ListUtils.checkAllBiggerThanValue(values, x))
    require(pos >= 0)
    decreases(pos)
    if (pos < size) {
      ListUtilsProperties.checkAllBiggerThanValueAtIndex(values, x, pos)
      apply(pos) > x
    } else {
      assert(applyStructure(pos))
      assert(cycleValueBiggerThan(pos - size, x))
      apply(pos) > x
    }
  }.holds
}
