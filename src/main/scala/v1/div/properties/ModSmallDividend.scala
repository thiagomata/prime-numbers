package v1.div.properties

import stainless.lang.*
import verification.Helper.assert
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
    assert(x.isFinal)
    assert(x == x.solve)
    assert(x.mod == a)
    assert(x.div == 0)
    assert(Calc.mod(a, b) == x.mod)
    assert(Calc.div(a, b) == 0)
    Calc.mod(a, b) == a &&
    Calc.div(a, b) == 0
  }.holds
}
