package v1.properties

import v1.{Calc, Div}
import stainless.lang.*
import stainless.proof.check

import scala.language.postfixOps

object ModSmallDividend {
  def modSmallDividend(a: BigInt, b: BigInt): Boolean = {
    require(b != 0)
    require(b > a)
    require(a >= 0)
    val div = Div(a, b, 0, a)
    check(div.isFinal)
    val simplified = div.solve
    check(div == simplified)
    val result = simplified.mod
    check(result == a)
    check(Calc.mod(a, b) == result)
    Calc.mod(a, b) == a
  }.holds
}
