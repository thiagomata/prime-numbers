package v1.properties

import v1.Calc
import v1.Div
import stainless.lang._
import stainless.proof.check

object ModIdempotence {
  def modIdempotence(a: BigInt, b: BigInt): Boolean = {
    require(b > 0)
    require(a >= 0)

    val div = Div(a, b, 0, a)

    val simplified = div.solve
    check(simplified.isFinal)
    check(simplified.b == div.b)
    check(simplified.a == div.a)
    check(simplified.b > 0)
    check(simplified.mod < div.b)
    check(simplified.mod >= 0)

    val result = simplified.mod
    check(result <= a)
    check(result < b)
    check(result == Calc.mod(a, b))
    ModSmallDividend.modSmallDividend(result, b)

    check(Calc.mod(result, b) == result)
    check(Calc.mod(a, b) == Calc.mod(result, b))
    Calc.mod(a, b) == Calc.mod(Calc.mod(a, b), b)
  }.holds
}
