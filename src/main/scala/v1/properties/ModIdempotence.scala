package v1.properties

import v1.Calc
import v1.Div
import stainless.lang._
import stainless.proof.check

object ModIdempotence {
  def modIdempotence(a: BigInt, b: BigInt): Boolean = {
    require(b > 0)  // @todo check that also works for b < 0
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

  def modUniqueDiv(x: Div, y: Div): Boolean = {
    require(x.isValid)
    require(y.isValid)
    require(x.a == y.a)
    require(x.b == y.b)
    require(x.b > 0) // @todo check that also works for b < 0
    check(modUnique(x.a, x.b, x.div, x.mod, y.div, y.mod))
    x.solve == y.solve
  }.holds

  def modUnique(a: BigInt, b: BigInt, divx: BigInt, modx: BigInt, divy: BigInt, mody: BigInt): Boolean = {
    require(b > 0) // @todo check that also works for b < 0
    val divDiff = divx - divy
    val absDivDiff = if (divDiff < 0) -divDiff else divDiff
    decreases(absDivDiff)
    require(divx * b + modx == a)
    require(divy * b + mody == a)

    val x = Div(a, b, divx, modx)
    val y = Div(a, b, divy, mody)

    if (divx == divy) {
      check(modx == mody)
      check(x == y)
    }
    if (divx < divy) {
      check(modx > mody)
      DivModAdditionAndMultiplication.MoreDivLessMod(a, b, divx, modx)
      val next =  Div(a, b, divx + 1, modx - b)
      check(x.solve == next.solve)
      modUnique(a, b, divx + 1, modx - b, divy, mody)
      check(x.solve == y.solve)
    }
    if (divx > divy) {
      check(modx < mody)
      DivModAdditionAndMultiplication.LessDivMoreMod(a, b, divx, modx)
      val next =  Div(a, b, divx - 1, modx + b)
      check(x.solve == next.solve)
      modUnique(a, b, divx - 1, modx + b, divy, mody)
      check(x.solve == y.solve)
    }
    check(x.solve == y.solve)

    Div(a, b, divx, modx).solve == Div(a, b, divy, mody).solve
  }.holds

  def modAdd(a: BigInt, b: BigInt, c: BigInt): Boolean = {
    require(a >= 0)
    require(c >= 0)
    require(b > 0)

    val x = Div(a, b, 0, a)
    val solvedX = x.solve
    check(solvedX.isFinal)
    check(solvedX.isValid)
    check(solvedX.mod < solvedX.b)
    check(solvedX.mod < b)
    check(solvedX.a == a)
    check(solvedX.b == b)
    check(solvedX.a == solvedX.b * solvedX.div + solvedX.mod)
    check(solvedX.a - solvedX.b * solvedX.div == solvedX.mod)

    val y = Div(c, b, 0, c)
    val solvedY = y.solve
    check(solvedY.isFinal)
    check(solvedY.isValid)
    check(solvedY.mod < solvedY.b)
    check(solvedY.mod < b)
    check(solvedY.a == c)
    check(solvedY.b == b)
    check(solvedY.a == solvedY.b * solvedY.div + solvedY.mod)
    check(solvedY.a - solvedY.b * solvedY.div == solvedY.mod)

    val xy = Div(a + c, b, 0, a + c)
    val solvedXY = xy.solve
    check(solvedXY.isFinal)
    check(solvedXY.isValid)
    check(solvedXY.mod < solvedXY.b)
    check(solvedXY.mod < b)
    check(solvedXY.a == a + c)
    check(solvedXY.b == b)
    check(solvedXY.a == solvedXY.b * solvedXY.div + solvedXY.mod)
    check(a + c == b * solvedXY.div + solvedXY.mod)

    val z = Div( solvedX.mod + solvedY.mod, b, 0, solvedX.mod + solvedY.mod)
    check(z.a == z.b * z.div + z.mod)
    check(z.a == solvedX.mod + solvedY.mod)
    check(z.b == b)
    check(z.mod == solvedX.mod + solvedY.mod)
    check(z.div == 0)
    check(z.a == z.b * z.div + z.mod)

    val solvedZ = z.solve
    check(solvedZ.isValid && solvedZ.isFinal)
    check(solvedZ.mod < z.b)
    check(modUniqueDiv(z, solvedZ))
    check(z.solve.mod == solvedZ.mod)

    check(solvedX.mod + solvedY.mod == b * solvedZ.div + solvedZ.mod)
    check(solvedX.a - solvedX.b * solvedX.div + solvedY.a - solvedY.b * solvedY.div == b * solvedZ.div + solvedZ.mod)
    check(a - b * solvedX.div + c - b * solvedY.div == b * solvedZ.div + solvedZ.mod)
    check(a + c == b * solvedZ.div + b * solvedX.div + b * solvedY.div + solvedZ.mod)

    val bigDiv = solvedZ.div + solvedX.div + solvedY.div
    check(a + c == b * bigDiv + solvedZ.mod)
    val w = Div(a + c, b, bigDiv, solvedZ.mod)
    check(solvedZ.mod < b)
    check(w.mod == solvedZ.mod)
    check(w.isFinal)
    check(w.solve == w)
//    DivModAdditionAndMultiplication.APlusMultipleTimesBSameMod(a + c, b, bigDiv)
    // check(w.solve.mod == solvedZ.solve.mod)

    check(b > 0)
    check(a >= 0)
    check(bigDiv >= 0)
    DivModAdditionAndMultiplication.APlusMultipleTimesBSameMod(a + c, b, bigDiv)
    check( Calc.mod(a + c,b) == Calc.mod( a + c + b * bigDiv, b ))
    check(w.isValid)
    check(xy.isValid)
    check(w.a == xy.a)
    check(w.b == xy.b)
    check(w.b > 0) // @todo check that also works for b < 0
    check(modUniqueDiv(w, xy))
    check( w.solve == xy.solve)
    check( w.solve.mod == xy.solve.mod)
    check( xy.solve.mod == Calc.mod(a+c,b))
    check( xy.solve.mod == solvedZ.mod)


//    check(solvedW.isFinal)
//    check(solvedW.isValid)
//    check(modUniqueDiv(xy, w))
//    check(solvedW.mod == Calc.mod(a + c, b))


//    val solvedZ = z.solve
//    check(solvedZ.isFinal)
//    check(solvedZ.isValid)
//    check(solvedZ.mod < solvedZ.b)
//    check(solvedZ.mod < b)
//    check(solvedZ.a == solvedZ.b * solvedZ.div + solvedZ.mod)





    /*
     mod(a + c, b) = mod( (mod(a, b) + mod(c, b)) , b)
    mod(a + c, b) = mod( a + c , b)
                xy = mod( x + y, b)
     */
    true
  }.holds
}
