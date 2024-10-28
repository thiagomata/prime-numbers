package v1.div.properties

import v1.Calc
import v1.Div
import stainless.lang.*
import stainless.proof.check
import v1.properties.DivModAdditionAndMultiplication
import v1.properties.ModIdempotence.modUniqueDiv

object ModOperations {

  def modAdd(a: BigInt, b: BigInt, c: BigInt): Boolean = {
    require(b != 0)

    val absB = if (b < 0) -b else b

    val x = Div(a, b, 0, a)
    val solvedX = x.solve
    check(solvedX.isFinal)
    check(solvedX.isValid)
    check(solvedX.mod < absB)
    check(solvedX.a == a)
    check(solvedX.b == b)
    check(solvedX.a == solvedX.b * solvedX.div + solvedX.mod)
    check(solvedX.a - solvedX.b * solvedX.div == solvedX.mod)

    val y = Div(c, b, 0, c)
    val solvedY = y.solve
    check(solvedY.isFinal)
    check(solvedY.isValid)
    check(solvedY.mod < absB)
    check(solvedY.a == c)
    check(solvedY.b == b)
    check(solvedY.a == solvedY.b * solvedY.div + solvedY.mod)
    check(solvedY.a - solvedY.b * solvedY.div == solvedY.mod)

    val xy = Div(a + c, b, 0, a + c)
    val solvedXY = xy.solve
    check(solvedXY.isFinal)
    check(solvedXY.isValid)
    check(solvedXY.mod < absB)
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
    check(solvedZ.mod < absB)
    check(modUniqueDiv(z, solvedZ))
    check(z.solve.mod == solvedZ.mod)

    check(solvedX.mod + solvedY.mod == b * solvedZ.div + solvedZ.mod)
    check(solvedX.a - solvedX.b * solvedX.div + solvedY.a - solvedY.b * solvedY.div == b * solvedZ.div + solvedZ.mod)
    check(a - b * solvedX.div + c - b * solvedY.div == b * solvedZ.div + solvedZ.mod)
    check(a + c == b * solvedZ.div + b * solvedX.div + b * solvedY.div + solvedZ.mod)

    val bigDiv = solvedZ.div + solvedX.div + solvedY.div
    check(a + c == b * bigDiv + solvedZ.mod)

    val w = Div(a + c, b, bigDiv, solvedZ.mod)
    check(solvedZ.mod < absB)
    check(w.mod == solvedZ.mod)
    check(w.isFinal)
    check(w.solve == w)

    check(b != 0)
    DivModAdditionAndMultiplication.ATimesBSameMod(a + c, b, bigDiv)
    check( Calc.mod(a + c,b) == Calc.mod( a + c + b * bigDiv, b ))
    check(w.isValid)
    check(xy.isValid)
    check(w.a == xy.a)
    check(w.b == xy.b)
    check(modUniqueDiv(w, xy))
    check( w.solve == xy.solve)
    check( w.solve.mod == xy.solve.mod)
    check( xy.solve.mod == Calc.mod(a+c,b))
    check( xy.solve.mod == solvedZ.mod)

    Calc.mod(a + c, b) == Calc.mod(Calc.mod(a, b) + Calc.mod(c, b), b) &&
    Calc.div(a + c, b) == Calc.div(a, b) + Calc.div(c, b) + Calc.div(Calc.mod(a, b) + Calc.mod(c, b), b)
  }.holds

  def modZeroPlusC(a: BigInt, b: BigInt, c: BigInt): Boolean = {
    require(b != 0)
    require(Calc.mod(a, b) == 0)
    modAdd(a,b,c)
    Calc.mod(a + c, b) == Calc.mod(c, b)
  }.holds

  def modLess(a: BigInt, b: BigInt, c: BigInt): Boolean = {
    require(b != 0)
    modAdd(a - c, b, c)
    Calc.mod(a - c, b) == Calc.mod(Calc.mod(a, b) - Calc.mod(c, b), b) &&
    Calc.div(a - c, b) == Calc.div(a, b) - Calc.div(c, b) + Calc.div(Calc.mod(a, b) - Calc.mod(c, b), b)
  }.holds
}
