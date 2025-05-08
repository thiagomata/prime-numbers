package v1.cycle.acc

import v1.cycle.integral.CycleIntegral
import stainless.lang.*
import v1.Calc.{div, mod}
import v1.cycle.integral.properties.CycleIntegralProperties

object CycleAccProperties {

  /**
   * This function checks that the cycle accumulator and cycle integral are equal at a given position.
   *
   * in other words:
   *
   * For any position >= 0 => AccCycle(position) == CycleIntegral(position)
   *
   * Therefore, in the consumer point of view,
   * AccCycle and CycleIntegral are the same.
   *
   * @param cycleAcc CycleAcc any CycleAcc
   * @param cycleIntegral CycleIntegral any CycleIntegral with same cycle and initialValue
   * @param position BigInt any position bigger than or equal to 0
   * @return Boolean if the properties hold
   */
  def assertCycleAccEqualsCycleIntegral(
    cycleAcc: CycleAcc,
    cycleIntegral: CycleIntegral,
    position: BigInt,
  ): Boolean = {
    require(position >= 0)
    require(cycleAcc.cycle.values.nonEmpty)
    require(cycleIntegral.cycle.values.nonEmpty)
    require(cycleAcc.cycle.values == cycleIntegral.cycle.values)
    require(cycleAcc.cycle.size   == cycleIntegral.cycle.size)
    require(cycleAcc.initialValue == cycleIntegral.initialValue)
    decreases(position)

    assert(cycleAcc.cycle.size == cycleIntegral.cycle.size)
    val size = cycleAcc.cycle.size

    if (position == 0) {

      assert(div(position, size) == 0)
      assert(mod(position, size) == 0)
      assert(cycleAcc.integralValues(0) == cycleAcc.cycle.values.head)
      assert(cycleAcc(0) == div(position, size) * cycleAcc.integralValues.last + cycleAcc.integralValues(mod(position,size)) + cycleAcc.initialValue)
      assert(cycleAcc(0) == 0 + cycleAcc.integralValues(0) + cycleAcc.initialValue)
      assert(cycleAcc(0) == cycleAcc.cycle.values.head + cycleAcc.initialValue)

      assert(cycleIntegral(0) == cycleIntegral.cycle(0) + cycleIntegral.initialValue)
      assert(cycleIntegral(0) == cycleIntegral.cycle.values(mod(0, size)) + cycleIntegral.initialValue)
      assert(cycleIntegral(0) == cycleIntegral.cycle.values(0)            + cycleIntegral.initialValue)
      assert(cycleIntegral(0) == cycleIntegral.cycle.values.head          + cycleIntegral.initialValue)

      assert(cycleAcc(position) == cycleIntegral(position))
    } else {
      assertCycleAccEqualsCycleIntegral(
        cycleAcc,
        cycleIntegral,
        position - 1
      )

      cycleAcc.assertSimplifiedDiffValuesMatchCycle(position - 1)
      assert(
        cycleAcc(position) - cycleAcc(position - 1) ==
          cycleAcc.cycle.values(mod(position, cycleAcc.integralValues.size))
      )
      assert(cycleAcc.integralValues.size == size)

      assert(cycleAcc(position) == cycleAcc(position - 1) + cycleAcc.cycle(position))

      assert(cycleAcc(position - 1) == cycleIntegral(position - 1))

      CycleIntegralProperties.assertDiffEqualsCycleValue(cycleIntegral, position - 1)
      assert(cycleIntegral(position) == cycleIntegral(position - 1) + cycleIntegral.cycle(position))

      assert(cycleIntegral.cycle(position) == cycleIntegral.cycle.values(mod(position, size)))
      assert(cycleAcc.cycle(position) == cycleAcc.cycle.values(mod(position, size)))
      assert(cycleIntegral.cycle.values == cycleAcc.cycle.values)
      assert(cycleAcc.cycle.values(mod(position, size)) == cycleIntegral.cycle.values(mod(position, size)))
      assert(cycleAcc.cycle(position) == cycleAcc.cycle(position))

      assert(cycleIntegral(position) == cycleIntegral(position - 1) + cycleIntegral.cycle(position))
      assert(cycleIntegral(position) == cycleAcc(position - 1)      + cycleIntegral.cycle(position))
      assert(cycleIntegral(position) == cycleAcc(position - 1)      + cycleAcc.cycle(position))

      assert(cycleAcc(position) == cycleIntegral(position))
    }
    cycleAcc(position) == cycleIntegral(position)
  }.holds

}
