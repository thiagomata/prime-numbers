package v1.cycle.memory

import stainless.collection.List
import v1.cycle.CycleUtils
import v1.cycle.CycleUtils.{checkZeroForAll, checkZeroForNone}
import v1.cycle.mod.ModCycle
import verification.Helper.assert

case class MemCycle private (
    cycle: ModCycle,
    modIsZeroForAllValues: List[BigInt] = stainless.collection.List.empty,
    modIsZeroForNoneValues: List[BigInt] = stainless.collection.List.empty,
    modIsZeroForSomeValues: List[BigInt] = stainless.collection.List.empty,
) {
  require(CycleUtils.isValid(
    cycle.values,
    modIsZeroForAllValues,
    modIsZeroForSomeValues,
    modIsZeroForNoneValues
  ))

  def isValid: Boolean = {
    CycleUtils.isValid(
      cycle.values,
      modIsZeroForAllValues,
      modIsZeroForSomeValues,
      modIsZeroForNoneValues
    )
  }

  def countModZero(dividend: BigInt): BigInt = {
    require(dividend > 0)
    require(cycle.values.nonEmpty)
    require(CycleUtils.checkPositiveOrZero(cycle.values))
    CycleUtils.countModZero(cycle.values, dividend)
  }

  def apply(position: BigInt): BigInt = {
    require(position >= 0)
    cycle(position)
  }

  def values: List[BigInt] = cycle.values

  def size: BigInt = cycle.size

  def sum(): BigInt = cycle.sum()

  def checkMod(dividend: BigInt): MemCycle = {
    require(dividend > 0)
    assert(this.isValid)

    if (this.evaluated(dividend)) {
      this
    } else {
      val totalModZero = CycleUtils.countModZero(cycle.values, dividend)

      if (totalModZero == cycle.size) {
        assert(this.countModZero(dividend) == cycle.values.size)
        appendForAll(dividend)
      }
      else if (totalModZero == 0) {
        assert(this.countModZero(dividend) == 0)
        appendForNone(dividend)
      }
      else {
        assert(this.countModZero(dividend) != 0)
        assert(this.countModZero(dividend) != cycle.size)
        appendForSome(dividend)
      }
    }
  }

  def allModValuesAreZero(dividend: BigInt): Boolean = {
    require(dividend > 0)
    this.countModZero(dividend) == cycle.size
  }

  def noModValuesAreZero(dividend: BigInt): Boolean = {
    require(dividend > 0)
    this.countModZero(dividend) == 0
  }

  def someModValuesAreZero(dividend: BigInt): Boolean = {
    require(dividend > 0)
    this.countModZero(dividend) != 0 &&
      this.countModZero(dividend) != cycle.size
  }

  def evaluated(dividend: BigInt): Boolean = {
    this.modIsZeroForSomeValues.contains(dividend) ||
      this.modIsZeroForAllValues.contains(dividend) ||
      this.modIsZeroForNoneValues.contains(dividend)
  }

  private def appendForNone(dividend: BigInt): MemCycle = {
    require(dividend > 0)
    require(this.isValid)
    require(CycleUtils.countModZero(this.cycle.values, dividend) == 0)

    val newList = dividend :: this.modIsZeroForNoneValues
    assert(newList.tail == this.modIsZeroForNoneValues)
    assert(newList.head == dividend)
    assert(checkZeroForNone(newList, this.cycle.values))

    MemCycle(
      cycle = this.cycle,
      modIsZeroForAllValues = this.modIsZeroForAllValues,
      modIsZeroForNoneValues = newList,
      modIsZeroForSomeValues = this.modIsZeroForSomeValues,
    )
  }

  private def appendForSome(dividend: BigInt): MemCycle = {
    require(dividend > 0)
    require(this.isValid)
    require(CycleUtils.countModZero(this.cycle.values, dividend) != 0)
    require(CycleUtils.countModZero(this.cycle.values, dividend) != cycle.values.size)

    assert(CycleUtils.countModZero(this.cycle.values, dividend) != 0)
    assert(CycleUtils.countModZero(this.cycle.values, dividend) != cycle.values.size)
    assert(CycleUtils.checkZeroForSome(List(dividend), this.cycle.values))
    val newList = dividend :: this.modIsZeroForSomeValues
    assert(newList.tail == this.modIsZeroForSomeValues)
    assert(newList.head == dividend)
    assert(CycleUtils.checkZeroForSome(newList, this.cycle.values))

    MemCycle(
      cycle = this.cycle,
      modIsZeroForAllValues = this.modIsZeroForAllValues,
      modIsZeroForNoneValues = this.modIsZeroForNoneValues,
      modIsZeroForSomeValues = newList,
    )
  }

  private def appendForAll(dividend: BigInt): MemCycle = {
    require(dividend > 0)
    require(this.isValid)
    require(CycleUtils.countModZero(this.values, dividend) == this.values.size)

    val newList = dividend :: this.modIsZeroForAllValues
    assert(newList.tail == this.modIsZeroForAllValues)
    assert(newList.head == dividend)
    assert(checkZeroForAll(newList, this.values))

    MemCycle(
      cycle = this.cycle,
      modIsZeroForAllValues = newList,
      modIsZeroForNoneValues = this.modIsZeroForNoneValues,
      modIsZeroForSomeValues = this.modIsZeroForSomeValues,
    )
  }
}

object MemCycle {
  def apply(values: List[BigInt]): MemCycle = {
    require(values.nonEmpty)
    require(CycleUtils.checkPositiveOrZero(values))

    val cycle = ModCycle(values)
    MemCycle(
      cycle = cycle,
      modIsZeroForAllValues = List.empty,
      modIsZeroForNoneValues = List.empty,
      modIsZeroForSomeValues = List.empty,
    )
  }
}