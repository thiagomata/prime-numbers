package v1.chapter4.cycle.recursive

import stainless.collection.List
import stainless.lang.BooleanDecorations
import stainless.lang.decreases
import v1.chapter3.list.ListUtils
import v1.chapter3.list.properties.ListUtilsProperties
import v1.chapter4.cycle.CycleUtils
import v1.chapter4.cycle.mod.ModCycle
import v1.chapter4.cycle.properties.CycleProperties
import v1.chapter4.cycle.recursive.properties.RecursiveCycleMatchesModCycle

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

  def rotateAt(index: BigInt): RecursiveCycle = {
    require(index >= 0)
    if (index == BigInt(0)) this
    else {
      val rotated = CycleUtils.collectRotated(values, index, size)
      RecursiveCycle(rotated)
    }
  }

  def cycleValuePositiveOrZero(pos: BigInt): Boolean = {
    require(pos >= 0)
    decreases(pos)
    if (pos < size) {
      CycleUtils.checkPositiveOrZeroAtIndex(values, pos)
      apply(pos) >= BigInt(0)
    } else {
      assert(applyStructure(pos))
      assert(cycleValuePositiveOrZero(pos - size))
      apply(pos) >= BigInt(0)
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

  def rotateAtValue(k: BigInt, i: BigInt): Boolean = {
    require(k >= 0)
    require(i >= 0)

    val modCycle = ModCycle(values)
    val rotated = CycleUtils.collectRotated(values, k, size)
    val rotatedModCycle = ModCycle(rotated)

    CycleProperties.rotateAtValue(modCycle, k, i)
    assert(rotatedModCycle(i) == modCycle(k + i))

    RecursiveCycleMatchesModCycle.assertCycleAndRecursiveCycleMathForAnyValues(modCycle, k + i)
    assert(modCycle(k + i) == apply(k + i))

    RecursiveCycleMatchesModCycle.assertCycleAndRecursiveCycleMathForAnyValues(rotatedModCycle, i)
    assert(rotatedModCycle(i) == rotateAt(k).apply(i))

    rotateAt(k).apply(i) == apply(k + i)
  }.holds
}
