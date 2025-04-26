package v1.div.properties

import stainless.lang.*
//import verification.Helper.check
import stainless.proof.check
import v1.Calc
import v1.div.DivMod

import scala.language.postfixOps

object ModSmallDividend {
  def modSmallDividend(a: BigInt, b: BigInt): Boolean = {
    require(b > 0)
    require(b > a)
    require(a >= 0)
    val x = DivMod(a, b, 0, a)
    check(x.isFinal)
    check(x == x.solve)
    check(x.mod == a)
    check(x.div == 0)
    check(Calc.mod(a, b) == x.mod)
    check(Calc.div(a, b) == 0)
    Calc.mod(a, b) == a &&
    Calc.div(a, b) == 0
  }.holds
}
