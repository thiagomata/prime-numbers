package v1.cycle.integral.mod

import stainless.lang.*
import v1.Calc
import v1.cycle.memory.MemCycle
import v1.div.DivMod
import v1.div.properties.{ModOperations, ModSmallDividend, Summary}
import v1.list.integral.Integral
import v1.list.integral.properties.IntegralProperties
import v1.list.properties.ListUtilsProperties
import verification.Helper.{assert, equality}

case class ModCycleIntegral(
  initialValue: BigInt,
  mCycle:         MemCycle,
) {
//  require(cycle.nonEmpty)

  val integralValues: Integral = Integral(
    list = mCycle.cycle.values,
  )

  /**
   * AccCycle(pos) = div(pos, integralValues.size) * integralValues.last + integralValues(mod(pos, integralValues.size)) + initialValue
   * @param position BigInt position in the cycle
   * @return BigInt value at the position in the cycle
   */
  def apply(position: BigInt): BigInt = {
    require(position >= 0)
    val divMod = DivMod(position, integralValues.size, 0, position).solve
    assert(divMod.mod >= 0)
    assert(divMod.div >= 0)
    assert(position == divMod.div * integralValues.size + divMod.mod)
    divMod.div * integralValues.last + integralValues(divMod.mod) + initialValue
  }
}
