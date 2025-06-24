package v1.cycle.mod

import stainless.collection.List
import v1.Calc
import v1.cycle.CycleUtils
import v1.list.ListUtils
import verification.Helper.assert

case class ModCycle(values: List[BigInt]) {
  require(CycleUtils.checkPositiveOrZero(values))
  require(values.nonEmpty)

  def apply(value: BigInt): BigInt = {
    require(value >= 0)
    val index = Calc.mod(value, values.size)
    assert(index >= 0)
    assert(index < values.size)
    values(index)
  }

  def size: BigInt = values.size

  def sum(): BigInt = ListUtils.sum(values)
}