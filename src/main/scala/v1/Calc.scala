package v1

object Calc {

  def div(a: BigInt, b: BigInt): BigInt = {
    require(b != 0)
    val result = Div(a, b, 0, a)
    val simplified = result.solve
    simplified.div
  }

  def mod(a: BigInt, b: BigInt): BigInt = {
    require(b != 0)
    val result = Div(a, b, 0, a)
    val simplified = result.solve
    simplified.mod
  }

}
