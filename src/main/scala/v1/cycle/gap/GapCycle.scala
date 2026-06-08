package v1.cycle.gap

import stainless.collection.List
import stainless.lang.BooleanDecorations
import stainless.lang.decreases
import v1.cycle.CycleUtils
import v1.cycle.integral.recursive.CycleIntegral
import v1.cycle.integral.recursive.properties.CycleIntegralProperties
import v1.cycle.memory.MemCycle
import v1.list.ListBoundUtils
import v1.list.MinBoundList

case class GapCycle private (values: MinBoundList) {
  require(values.lowerBound == BigInt(0))
  require(values.list.nonEmpty)
  require(CycleUtils.checkPositiveOrZero(values.list))

  val memCycle: MemCycle = MemCycle(values.list)
  val integral: CycleIntegral = CycleIntegral(BigInt(0), memCycle)

  def gap(index: BigInt): BigInt = {
    require(index >= 0)
    memCycle(index)
  }

  def cumulativeSum(index: BigInt): BigInt = {
    require(index >= 0)
    integral(index)
  }

  def size: BigInt = values.size
  def sum: BigInt = memCycle.sum()
}

object GapCycle {

  def assertCumulativeSumPositive(gc: GapCycle, pos: BigInt): Boolean = {
    require(pos >= 0)
    assert(CycleIntegralProperties.assertCycleIntegralPositive(gc.integral, pos))
    gc.cumulativeSum(pos) > BigInt(0)
  }.holds

  def apply(list: List[BigInt]): GapCycle = {
    require(ListBoundUtils.allGreaterThan(list, BigInt(0)))
    require(list.nonEmpty)
    assert(assertAllGreaterThanImpliesCheckPositiveOrZero(list))
    GapCycle(MinBoundList(list, BigInt(0)))
  }

  def assertAllGreaterThanImpliesCheckPositiveOrZero(list: List[BigInt]): Boolean = {
    require(ListBoundUtils.allGreaterThan(list, BigInt(0)))
    decreases(list)
    if (list.isEmpty) {
      CycleUtils.checkPositiveOrZero(list)
    } else {
      assert(list.head > 0)
      assert(list.head >= 0)
      assert(assertAllGreaterThanImpliesCheckPositiveOrZero(list.tail))
      CycleUtils.checkPositiveOrZero(list)
    }
  }.holds
}
