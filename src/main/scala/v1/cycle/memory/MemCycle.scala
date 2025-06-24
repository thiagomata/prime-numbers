package v1.cycle.memory

import stainless.collection.List
import v1.Calc
import v1.cycle.CycleUtils
import v1.cycle.CycleUtils.{appendForNone, appendForSome}
import v1.list.ListUtils
import verification.Helper.assert

case class MemCycle(
  values: List[BigInt],
  modIsZeroForAllValues: List[BigInt] = stainless.collection.List.empty,
  modIsZeroForNoneValues: List[BigInt] = stainless.collection.List.empty,
  modIsZeroForSomeValues: List[BigInt] = stainless.collection.List.empty,
) {
  require(CycleUtils.isValid(
    values,
    modIsZeroForAllValues,
    modIsZeroForSomeValues,
    modIsZeroForNoneValues
  ))

  def isValid: Boolean = {
    CycleUtils.isValid(
      values,
      modIsZeroForAllValues,
      modIsZeroForSomeValues,
      modIsZeroForNoneValues
    )
  }

  def countModZero(dividend: BigInt): BigInt = {
    require(dividend > 0)
    require(this.values.nonEmpty)
    require(CycleUtils.checkPositiveOrZero(values))
    CycleUtils.countModZero(this.values, dividend)
  }

  def apply(value: BigInt): BigInt = {
    require(value >= 0)
    val index = Calc.mod(value, values.size)
    assert(index >= 0)
    assert(index < values.size)
    values(index)
  }

  def size: BigInt = values.size

  def sum(): BigInt = ListUtils.sum(values)

  def checkMod(dividend: BigInt): MemCycle = {
    require(dividend > 0)
    assert(this.isValid)

    if (this.evaluated(dividend)) {
      this
    } else {
      val totalModZero = CycleUtils.countModZero(this.values, dividend)

      if (totalModZero == this.values.size) {
        assert(this.countModZero(dividend) == this.values.size)
        CycleUtils.appendForAll(this, dividend)
      }
      else if (totalModZero == 0) {
        assert(this.countModZero(dividend) == 0)
        appendForNone(this, dividend)
      }
      else {
        assert(this.countModZero(dividend) != 0)
        assert(this.countModZero(dividend) != values.size)
        appendForSome(this, dividend)
      }
    }
  }

  def allModValuesAreZero(dividend: BigInt): Boolean = {
    require(dividend > 0)
    this.countModZero(dividend) == this.values.size
  }

  def noModValuesAreZero(dividend: BigInt): Boolean = {
    require(dividend > 0)
    this.countModZero(dividend) == 0
  }

  def someModValuesAreZero(dividend: BigInt): Boolean = {
    require(dividend > 0)
    this.countModZero(dividend) != 0 &&
      this.countModZero(dividend) != this.values.size
  }

  def evaluated(dividend: BigInt): Boolean = {
    this.modIsZeroForSomeValues.contains(dividend) ||
      this.modIsZeroForAllValues.contains(dividend) ||
      this.modIsZeroForNoneValues.contains(dividend)
  }
}