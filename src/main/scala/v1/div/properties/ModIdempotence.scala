package v1.properties

import v1.Calc
import v1.Div
import stainless.lang._
import stainless.proof.check

object ModIdempotence {
  def modIdempotence(a: BigInt, b: BigInt): Boolean = {
    require(b != 0)
    require(a >= 0)

    val div = Div(a, b, 0, a)
    val absB = if (b < 0) -b else b

    val solved = div.solve
    check(solved.isFinal)
    check(solved.b == div.b)
    check(solved.a == div.a)
    check(absB > 0)
    check(solved.mod < absB)
    check(solved.mod >= 0)

    val result = solved.mod
    check(result <= a)
    check(result < absB)
    check(result == Calc.mod(a, b))

    check(Calc.mod(result, b) == result)
    check(Calc.mod(a, b) == Calc.mod(result, b))
    Calc.mod(a, b) == Calc.mod(Calc.mod(a, b), b)
  }.holds

  def modUniqueDiv(x: Div, y: Div): Boolean = {
    require(x.isValid)
    require(y.isValid)
    require(x.a == y.a)
    require(x.b == y.b)
    require(x.b != 0)
    check(modUnique(x.a, x.b, x.div, x.mod, y.div, y.mod))
    x.solve == y.solve
  }.holds

  def modUnique(a: BigInt, b: BigInt, divx: BigInt, modx: BigInt, divy: BigInt, mody: BigInt): Boolean = {
    require(b != 0)
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
      DivModAdditionAndMultiplication.MoreDivLessMod(a, b, divx, modx)
      val next =  Div(a, b, divx + 1, modx - b)
      check(x.solve == next.solve)
      modUnique(a, b, divx + 1, modx - b, divy, mody)
      check(x.solve == y.solve)
    }
    if (divx > divy) {
      DivModAdditionAndMultiplication.LessDivMoreMod(a, b, divx, modx)
      val next =  Div(a, b, divx - 1, modx + b)
      check(x.solve == next.solve)
      modUnique(a, b, divx - 1, modx + b, divy, mody)
      check(x.solve == y.solve)
    }
    check(x.solve == y.solve)

    Div(a, b, divx, modx).solve == Div(a, b, divy, mody).solve
  }.holds
}
