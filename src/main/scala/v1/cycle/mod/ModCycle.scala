package v1.cycle.mod

import stainless.collection.List
import stainless.lang.{BigInt, decreases}
import v1.Calc
import v1.cycle.CycleUtils
import v1.cycle.integral.mod.ModCycleIntegralProperties
import v1.list.ListUtils
import v1.list.properties.ListUtilsProperties
import verification.Helper.assert
import stainless.lang.BooleanDecorations
import scala.annotation.tailrec

/**
  * Represents a cycle of values that can be accessed using a modulo operation.
  *  This cycle is defined by a list of non-negative BigInt values.
  *
  * @param values A non-empty list of BigInt values that form the cycle.
  */
case class ModCycle(values: List[BigInt]) {
  require(CycleUtils.checkPositiveOrZero(values))
  require(values.nonEmpty)

  /**
    * Applies the modulo operation to the given value and 
    * returns the corresponding value from the cycle.
    *
    * In other words,
    * ModCycle(position) = values[position % L.size]
    * 
    * @param position The BigInt value to be used for accessing the cycle.
    * @return The value from the cycle corresponding to the modulo of the input value.
    */
  def apply(position: BigInt): BigInt = {
    require(position >= 0)
    val index = Calc.mod(position, values.size)
    assert(index >= 0)
    assert(index < values.size)
//    assert(checkPositiveOrZeroAtIndex(values, index))
    val res = values(index)
//    assert(res >= 0)
    res
  }

  def size: BigInt = values.size

  def sum(): BigInt = ListUtils.sum(values)

  def rotateAt(index: BigInt): ModCycle = {
    require(index >= 0)
    if (index == BigInt(0)) this
    else {
      val rotated = CycleUtils.collectRotated(values, index, size)
      ModCycle(rotated)
    }
  }

  @tailrec
  private def allValuesExistInList(listA: List[BigInt], listB: List[BigInt]): Boolean = {
    if (listA.isEmpty) true
    else if (valueExistInList(listA.head, listB)) allValuesExistInList(listA.tail, listB)
    else false
  }

  @tailrec
  private def valueExistInList(value: BigInt, list: List[BigInt]): Boolean = {
    if (list.isEmpty) false
    else if (list.head == value) true
    else valueExistInList(value, list.tail)
  }

  def checkPositiveOrZeroAtIndex(values: List[BigInt], idx: BigInt): Boolean = {
    require(CycleUtils.checkPositiveOrZero(values))
    require(idx >= 0 && idx < values.size)
    decreases(idx)
    if (idx == BigInt(0)) {
      values.head >= BigInt(0)
    } else {
      assert(checkPositiveOrZeroAtIndex(values.tail, idx - 1))
      assert(ListUtilsProperties.assertTailShiftLeft(values, idx))
      values(idx) >= BigInt(0)
    }
  }.holds
}