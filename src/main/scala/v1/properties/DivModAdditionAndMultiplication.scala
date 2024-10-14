package v1.properties

import v1.Calc
import v1.Div
import stainless.lang.*
import stainless.proof.check

object DivModAdditionAndMultiplication {

  def APlusBSameModPlusDiv(a: BigInt, b: BigInt): Boolean = {
    require(b > 0)
    require(a >= 0)

    val input = Div(a, b, 0, a)
    val solved = input.solve

    check(solved.isFinal)
    check(solved.isValid)
    check(solved.a == a)
    check(solved.b == b)
    check(solved.div * solved.b + solved.mod == solved.a)
    check(solved.div * solved.b + solved.mod + solved.b - solved.b == solved.a)
    check(solved.div * solved.b + solved.mod + solved.b == solved.a + solved.b)
    check((solved.div + 1 ) * solved.b + solved.mod == (solved.a + solved.b))

    val next = Div(solved.a + solved.b, solved.b, solved.div + 1, solved.mod)
    check(next.b == b)
    check(next.mod == solved.mod)
    check(next.div == solved.div + 1)
    check(next.isFinal)

    Calc.mod(a,b) == Calc.mod(a+b,b) &&
    Calc.div(a,b) + 1 == Calc.div(a+b,b)
  }.holds

  def APlusMultipleTimesBSameMod(a: BigInt, b: BigInt, m: BigInt): Boolean = {
    require(b > 0)
    require(m >= 0)
    require(a >= 0)
    decreases(m)

    APlusBSameModPlusDiv(a, b)
    if (m > 1) {
      check(Calc.mod(a, b) == Calc.mod(a + b, b))
      check(APlusMultipleTimesBSameMod(a + b, b, m - 1))
      check(Calc.mod(a, b) == Calc.mod(a + b * m, b))
      check(Calc.div(a, b) + m == Calc.div(a + b * m, b))
    }

    Calc.mod(a,b) == Calc.mod(a+b*m,b) &&
    Calc.div(a,b) + m == Calc.div(a+b*m,b)
  }.holds


  def MoreDivLessMod(a: BigInt, b: BigInt, div: BigInt, mod: BigInt): Boolean = {
    require(b > 0)
    require(div * b + mod == a)
    val div1 = Div(a, b, div, mod)
    val div2 = Div(a, b, div + 1, mod - b)

    if ( div1.mod > 0 ) {
      check(div1.solve == div1.reduceMod)
      check(div1.ModLessB.solve == div1.reduceMod.solve)
      check(div1.ModLessB == div2)
      check(div1.solve == div2.solve)
    }

    if (div1.mod < 0) {
      check(div1.solve == div1.increaseMod)
      check(div1.ModPlusB.solve == div1.increaseMod.solve)
      check(div2.ModPlusB.solve == div1.solve)
      check(div1.solve == div2.solve)
    }

    if (div1.mod == 0) {
      check(div2.mod ==  mod - b)
      check(div2.mod < 0)
      check(!div2.isFinal)
      check(div2.solve == div2.increaseMod)
      check(div2.ModPlusB == div1)
      check(div1.isFinal)
      check(div2.solve == div2.ModPlusB)
      check(div1.solve == div1)
      check(div1.solve == div2.solve)
    }
    check(div1.solve == div2.solve)
    div1.solve == div2.solve
  }.holds

  def LessDivMoreMod(a: BigInt, b: BigInt, div: BigInt, mod: BigInt): Boolean = {
    require(b > 0)
    require(div * b + mod == a)
    Div(a, b, div, mod).solve == Div(a, b, div - 1, mod + b).solve
  }.holds

  def MoreDivLessModManyTimess(a: BigInt, b: BigInt, div: BigInt, mod: BigInt, m: BigInt): Boolean = {
    require(b > 0)
    require(div * b + mod == a)
    require(m >= 1)
    require(a >= 0)
    decreases(m)

    MoreDivLessMod(a, b, div, mod)

    val finalDiv = div + m
    val finalMod = mod - m * b

    if (m > 1) {
      val prevDiv = div + m - 1
      val prevMod = mod - m * b + b

      MoreDivLessMod(a, b, prevDiv, prevMod)

      check(Div(a, b, prevDiv, prevMod).solve == Div(a, b, finalDiv, finalMod).solve)
      check(MoreDivLessModManyTimess(a, b, div, mod, m - 1))

      check(Div(a, b, finalDiv, finalMod).solve == Div(a, b, div, mod).solve)
    }

    Div(a, b, finalDiv, finalMod).solve == Div(a, b, div, mod).solve
  }.holds

  def LessDivMoreModManyTimes(a: BigInt, b: BigInt, div: BigInt, mod: BigInt, m: BigInt): Boolean = {
    require(b > 0)
    require(div * b + mod == a)
    require(m > 0)
    decreases(m)

    LessDivMoreMod(a, b, div, mod)
    if (m > 1) {
      LessDivMoreModManyTimes(a, b, div - 1, mod + b, m - 1)
      check(Div(a, b, div - 1, mod + b).solve == Div(a, b, div, mod).solve)
    }
    Div(a, b, div - m, mod + m*b).solve == Div(a, b, div, mod).solve
  }.holds
}

