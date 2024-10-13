package v1.properties

import v1.Calc
import stainless.lang._

object ModIdentity {
  def modIdentity(a: BigInt): Boolean = {
    require(a != 0)
    Calc.mod(a, a) == 0
  }.holds
}
