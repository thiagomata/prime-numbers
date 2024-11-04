package v1.properties

import v1.{Calc, DivMod}
import stainless.lang.*
import stainless.proof.check

import scala.language.postfixOps

object ModSmallDividend {
  def modSmallDividend(a: BigInt, b: BigInt): Boolean = {
    require(b != 0)
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
