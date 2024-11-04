package v1

import stainless.lang.BooleanDecorations

object Calc {

  def div(a: BigInt, b: BigInt): BigInt = {
    require(b != 0)
    val result = DivMod(a, b, 0, a)
    val solved = result.solve
    solved.div
  }

  def mod(a: BigInt, b: BigInt): BigInt = {
    require(b != 0)
    val result = DivMod(a, b, 0, a)
    val solved = result.solve
    solved.mod
  }.ensuring(
    mod => {
      val smallMod = if ( b > 0 ) 0 <= mod && mod < b else true
      val validMod = mod == DivMod(a, b, 0, a).solve.mod
      smallMod && validMod
    }
  )
}
