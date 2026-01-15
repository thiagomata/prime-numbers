package v1.cycle.mod

import stainless.collection.List
import v1.Calc
import v1.cycle.CycleUtils
import v1.list.ListUtils
import verification.Helper.assert

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
    values(index)
  }

  def size: BigInt = values.size

  def sum(): BigInt = ListUtils.sum(values)
}