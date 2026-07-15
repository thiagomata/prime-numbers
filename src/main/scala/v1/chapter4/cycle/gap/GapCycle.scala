package v1.chapter4.cycle.gap

import stainless.collection.List
import stainless.lang.BooleanDecorations
import stainless.lang.decreases
import v1.chapter3.list.{ListBoundUtils, MinBoundList}
import v1.chapter4.cycle.CycleUtils
import v1.chapter4.cycle.integral.recursive.CycleIntegral
import v1.chapter4.cycle.integral.recursive.properties.CycleIntegralProperties
import v1.chapter4.cycle.memory.MemCycle

case class GapCycle private (values: MinBoundList) {
  require(values.lowerBound == BigInt(0))
  require(values.list.nonEmpty)
  require(CycleUtils.checkPositiveOrZero(values.list))
  require(ListBoundUtils.allGreaterThan(values.list, BigInt(0)))

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

  def period: BigInt = values.size
  def sum: BigInt = memCycle.sum()
}

object GapCycle {

  /**
   * Exposes the positivity invariant through the public memory-cycle values.
   *
   * `GapCycle` stores its constructor list inside a `MemCycle`; callers usually
   * see `gc.memCycle.values`, not the private bounded-list wrapper. This lemma
   * keeps downstream proofs from having to rediscover that the public list is
   * the same positive gap list accepted by the constructor.
   */
  def assertMemCycleValuesPositive(gc: GapCycle): Boolean = {
    gc.memCycle.values == gc.values.list &&
      ListBoundUtils.allGreaterThan(gc.memCycle.values, BigInt(0))
  }.holds

  def assertMemCyclePeriodPositive(gc: GapCycle): Boolean = {
    assert(gc.memCycle.values == gc.values.list)
    assert(gc.values.list.nonEmpty)
    gc.memCycle.period > BigInt(0)
  }.holds

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
