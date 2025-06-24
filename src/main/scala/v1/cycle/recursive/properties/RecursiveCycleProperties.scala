package v1.cycle.recursive.properties

import stainless.lang.*
import v1.Calc
import v1.cycle.memory.MemCycle
import v1.cycle.recursive.RecursiveCycle
import v1.div.properties.{ModSmallDividend, ModSum}
import verification.Helper.assert

object RecursiveCycleProperties {
  /**
   * lemma: For values between zero and the list size,
   * recursive cycle and cycle from the same list match.
   *
   * in other words:
   *
   * for all key in [0, size),
   * recursiveCycle(key) == cycle(key)
   *
   * @param cycle Cycle
   * @param position BigInt
   * @return Boolean true if the property holds
   */
  def assertCycleAndRecursiveCycleMathForSmallValues(
    cycle: MemCycle,
    position: BigInt
  ): Boolean = {
    val list = cycle.values

    require(position >= 0)
    require(position < list.size)

    val recursiveCycle = RecursiveCycle(list)
    assert(position >= 0)
    assert(position < list.size)
    assert(list.size == cycle.size)
    assert(list.size == recursiveCycle.size)
    assert(ModSmallDividend.modSmallDividend(position, list.size))
    assert(Calc.mod(position, list.size) == position)
    cycle(position) == recursiveCycle(position)
  }.holds

  /**
   * lemma: For any position greater than or equal to zero,
   * recursive cycle and cycle from the same list match
   *
   * in other words:
   *
   * for all position >= 0,
   * recursiveCycle(position) == cycle(position)
   *
   * Therefore, the recursive cycle is a valid cycle
   *
   * @param cycle Cycle
   * @param position BigInt
   * @return Boolean true if the property holds
   */
  def assertCycleAndRecursiveCycleMathForAnyValues(
    cycle: MemCycle,
    position: BigInt
  ): Boolean = {
    decreases(position)
    val list = cycle.values

    require(position >= 0)
    require(list.size > 0)

    val recCycle = RecursiveCycle(list)

    if (position < list.size) {
      assertCycleAndRecursiveCycleMathForSmallValues(cycle, position)
    } else {
      assertCycleAndRecursiveCycleMathForAnyValues(cycle, position - list.size)
      assert(cycle(position - list.size) == recCycle(position - list.size))
      assert(ModSum.checkValueShift(position, list.size))
      assert(Calc.mod(position, list.size) == Calc.mod(position - list.size, list.size))
      assert(cycle(position) == cycle(position - list.size))
      assert(recCycle(position) == recCycle(position - list.size))
    }
    assert(cycle(position) == recCycle(position))
  }
}
