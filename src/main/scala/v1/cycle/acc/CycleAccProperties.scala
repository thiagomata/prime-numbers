package v1.cycle.acc

import v1.cycle.integral.CycleIntegral
import stainless.lang.*

object CycleAccProperties {
  def assertCycleAccEqualsCycleIntegral(
    cycleAcc: CycleAcc,
    cycleIntegral: CycleIntegral,
    position: BigInt,
  ): Boolean = {
    require(position >= 0)
    require(cycleAcc.cycle.values.nonEmpty)
    require(cycleIntegral.cycle.values.nonEmpty)
    require(cycleAcc.cycle == cycleIntegral.cycle)
    require(cycleAcc.initialValue == cycleIntegral.initialValue)

    if (position == 0) {
      assert(cycleAcc(position) == cycleIntegral(position))
    } else {
      assert(
        assertCycleAccEqualsCycleIntegral(
          cycleAcc,
          cycleIntegral,
          position - 1
        )
      )
      assert(cycleAcc(position - 1) == cycleIntegral(position - 1))
    }
    cycleAcc(position) == cycleIntegral(position)
  }.holds

}
